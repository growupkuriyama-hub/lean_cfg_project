from __future__ import annotations

import gzip
import io
import json
import zipfile
from dataclasses import dataclass
from pathlib import Path, PurePosixPath
from typing import Any, Iterator, Mapping

from .routes import cluster_by_route, route_signature
from .traces import TraceRecord, parse_jaeger_json, parse_otlp_json


_JSON_SUFFIXES = {".json", ".jsonl", ".ndjson"}
_ARCHIVE_SUFFIXES = {".zip"}
_GZIP_SUFFIXES = {".gz"}


@dataclass(frozen=True)
class TraceSource:
    """A parsed trace-bearing member with archive provenance.

    ``name`` is a stable logical path. Nested archives are separated by ``!``.
    ``run_id`` defaults to the first directory component inside the innermost
    archive, which matches the run-oriented layout used by many observability
    datasets. The empirical CLI can override this with a regex when necessary.
    """

    name: str
    traces: tuple[TraceRecord, ...]
    run_id: str = ""
    byte_size: int = 0


def _parse_payload(payload: Any) -> list[TraceRecord]:
    if isinstance(payload, list):
        traces: list[TraceRecord] = []
        for item in payload:
            traces.extend(_parse_payload(item))
        return traces
    if not isinstance(payload, Mapping):
        return []
    if "resourceSpans" in payload or "resource_spans" in payload:
        return parse_otlp_json(payload)
    if "data" in payload and isinstance(payload.get("data"), list):
        return parse_jaeger_json(payload)
    if "traceID" in payload and "spans" in payload:
        return parse_jaeger_json({"data": [payload]})
    return []


def _json_documents(text: str) -> Iterator[Any]:
    stripped = text.lstrip("\ufeff\n\r\t ")
    if not stripped:
        return
    try:
        yield json.loads(stripped)
        return
    except json.JSONDecodeError:
        pass

    # Jaeger exports are sometimes newline-delimited, and some research
    # archives concatenate one JSON object per line. Invalid lines are skipped
    # conservatively instead of aborting the whole mixed monitoring member.
    for line in stripped.splitlines():
        line = line.strip()
        if not line:
            continue
        try:
            yield json.loads(line)
        except json.JSONDecodeError:
            continue


def parse_json_bytes(data: bytes) -> list[TraceRecord]:
    text = data.decode("utf-8", errors="replace")
    traces: list[TraceRecord] = []
    for document in _json_documents(text):
        traces.extend(_parse_payload(document))
    return traces


def _looks_like_json(name: str, data: bytes) -> bool:
    suffix = PurePosixPath(name).suffix.lower()
    if suffix in _JSON_SUFFIXES:
        return True
    prefix = data[:4096].lstrip(b"\xef\xbb\xbf\n\r\t ")
    return prefix.startswith((b"{", b"["))


def _infer_run_id(logical_name: str) -> str:
    innermost = logical_name.rsplit("!", 1)[-1].lstrip("/")
    path = PurePosixPath(innermost)
    parts = [part for part in path.parts if part not in {".", ".."}]
    if len(parts) >= 2:
        return parts[0]
    if parts:
        return PurePosixPath(parts[0]).stem
    return "unknown-run"


@dataclass
class _ScanStats:
    candidate_members: int = 0
    skipped_large_members: int = 0
    parsed_bytes: int = 0


def _iter_zip_sources(
    archive: zipfile.ZipFile,
    logical_prefix: str,
    stats: _ScanStats,
    *,
    max_members: int | None,
    max_member_bytes: int,
    nested_depth: int,
    max_nested_depth: int,
) -> Iterator[TraceSource]:
    yielded = 0
    for info in sorted(archive.infolist(), key=lambda item: item.filename):
        if info.is_dir():
            continue
        logical_name = f"{logical_prefix}!{info.filename}" if logical_prefix else info.filename
        suffix = PurePosixPath(info.filename).suffix.lower()

        if info.file_size > max_member_bytes:
            # Large logs/metric dumps should not be read merely to discover that
            # they are not trace JSON. Known nested archives are also bounded.
            stats.skipped_large_members += 1
            continue

        with archive.open(info) as handle:
            data = handle.read()
        stats.parsed_bytes += len(data)

        if suffix in _GZIP_SUFFIXES:
            try:
                data = gzip.decompress(data)
                logical_name = logical_name[: -len(suffix)]
            except (OSError, EOFError):
                continue

        if suffix in _ARCHIVE_SUFFIXES and nested_depth < max_nested_depth:
            try:
                with zipfile.ZipFile(io.BytesIO(data)) as nested:
                    for source in _iter_zip_sources(
                        nested,
                        logical_name,
                        stats,
                        max_members=None if max_members is None else max_members - yielded,
                        max_member_bytes=max_member_bytes,
                        nested_depth=nested_depth + 1,
                        max_nested_depth=max_nested_depth,
                    ):
                        yield source
                        yielded += 1
                        if max_members is not None and yielded >= max_members:
                            return
            except zipfile.BadZipFile:
                pass
            continue

        if not _looks_like_json(logical_name, data):
            continue
        stats.candidate_members += 1
        traces = tuple(parse_json_bytes(data))
        if not traces:
            continue
        yield TraceSource(
            name=logical_name,
            traces=traces,
            run_id=_infer_run_id(logical_name),
            byte_size=len(data),
        )
        yielded += 1
        if max_members is not None and yielded >= max_members:
            return


def iter_trace_sources(
    path: str | Path,
    max_members: int | None = None,
    *,
    max_member_bytes: int = 256 * 1024 * 1024,
    max_nested_depth: int = 2,
) -> Iterator[TraceSource]:
    """Read Jaeger/OTLP JSON from a file, directory, ZIP, or nested ZIP.

    Candidate members are identified both by extension and by content sniffing,
    because public monitoring archives frequently omit a ``.json`` suffix.
    Unknown documents are skipped. Members above ``max_member_bytes`` are not
    loaded into memory; this prevents multi-gigabyte log files from derailing a
    trace-only pilot.
    """
    source_path = Path(path)
    stats = _ScanStats()

    if source_path.is_dir():
        yielded = 0
        for child in sorted(item for item in source_path.rglob("*") if item.is_file()):
            if child.stat().st_size > max_member_bytes:
                continue
            suffix = child.suffix.lower()
            if suffix == ".zip":
                with zipfile.ZipFile(child) as archive:
                    for source in _iter_zip_sources(
                        archive,
                        str(child.relative_to(source_path)),
                        stats,
                        max_members=None if max_members is None else max_members - yielded,
                        max_member_bytes=max_member_bytes,
                        nested_depth=0,
                        max_nested_depth=max_nested_depth,
                    ):
                        yield source
                        yielded += 1
                        if max_members is not None and yielded >= max_members:
                            return
                continue
            data = child.read_bytes()
            if suffix == ".gz":
                try:
                    data = gzip.decompress(data)
                except (OSError, EOFError):
                    continue
            if not _looks_like_json(child.name, data):
                continue
            traces = tuple(parse_json_bytes(data))
            if traces:
                logical_name = str(child.relative_to(source_path))
                yield TraceSource(logical_name, traces, _infer_run_id(logical_name), len(data))
                yielded += 1
                if max_members is not None and yielded >= max_members:
                    return
        return

    if zipfile.is_zipfile(source_path):
        with zipfile.ZipFile(source_path) as archive:
            yield from _iter_zip_sources(
                archive,
                "",
                stats,
                max_members=max_members,
                max_member_bytes=max_member_bytes,
                nested_depth=0,
                max_nested_depth=max_nested_depth,
            )
        return

    if source_path.stat().st_size > max_member_bytes:
        raise ValueError(f"trace source exceeds max_member_bytes: {source_path}")
    data = source_path.read_bytes()
    if source_path.suffix.lower() == ".gz":
        data = gzip.decompress(data)
    if _looks_like_json(source_path.name, data):
        traces = tuple(parse_json_bytes(data))
        if traces:
            yield TraceSource(source_path.name, traces, _infer_run_id(source_path.name), len(data))
        return
    raise ValueError(f"unsupported trace source: {source_path}")


@dataclass(frozen=True)
class DatasetProfile:
    source_files: int
    trace_count: int
    span_count: int
    route_count: int
    service_count: int
    top_routes: tuple[tuple[str, int, tuple[str, ...]], ...]
    run_count: int = 0
    route_run_counts: tuple[tuple[str, int], ...] = ()
    parsed_bytes: int = 0


def profile_trace_dataset(
    path: str | Path,
    max_members: int | None = None,
    *,
    max_member_bytes: int = 256 * 1024 * 1024,
    max_nested_depth: int = 2,
) -> DatasetProfile:
    sources = tuple(
        iter_trace_sources(
            path,
            max_members=max_members,
            max_member_bytes=max_member_bytes,
            max_nested_depth=max_nested_depth,
        )
    )
    traces = [trace for source in sources for trace in source.traces]
    clusters = cluster_by_route(traces)
    services = {span.service for trace in traces for span in trace.spans}
    ranked = sorted(clusters.items(), key=lambda item: (-len(item[1]), item[0].route_id))

    run_ids_by_trace = {
        trace.trace_id: source.run_id
        for source in sources
        for trace in source.traces
    }
    route_run_counts = []
    for signature, items in ranked:
        run_count = len({run_ids_by_trace.get(trace.trace_id, "") for trace in items})
        route_run_counts.append((signature.route_id, run_count))

    return DatasetProfile(
        source_files=len(sources),
        trace_count=len(traces),
        span_count=sum(len(trace.spans) for trace in traces),
        route_count=len(clusters),
        service_count=len(services),
        top_routes=tuple(
            (signature.route_id, len(items), signature.services)
            for signature, items in ranked[:20]
        ),
        run_count=len({source.run_id for source in sources}),
        route_run_counts=tuple(route_run_counts[:20]),
        parsed_bytes=sum(source.byte_size for source in sources),
    )


def source_route_rows(sources: tuple[TraceSource, ...]) -> list[dict[str, object]]:
    """Return a manifest row for every source/run/route combination."""
    rows: list[dict[str, object]] = []
    for source in sources:
        grouped: dict[str, list[TraceRecord]] = {}
        signatures = {}
        for trace in source.traces:
            signature = route_signature(trace)
            grouped.setdefault(signature.route_id, []).append(trace)
            signatures[signature.route_id] = signature
        for route_id, traces in sorted(grouped.items()):
            signature = signatures[route_id]
            rows.append(
                {
                    "source": source.name,
                    "run_id": source.run_id,
                    "route_id": route_id,
                    "trace_count": len(traces),
                    "span_count": sum(len(trace.spans) for trace in traces),
                    "services": "|".join(signature.services),
                    "roots": repr(signature.roots),
                    "edges": repr(signature.edges),
                }
            )
    return rows
