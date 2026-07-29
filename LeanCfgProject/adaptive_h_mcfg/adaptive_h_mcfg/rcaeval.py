from __future__ import annotations

import csv
import gzip
import hashlib
import io
import json
import math
import re
import sqlite3
import tempfile
import zipfile
from dataclasses import dataclass
from datetime import datetime, timezone
from pathlib import Path, PurePosixPath
from typing import Any, BinaryIO, Iterable, Iterator, Mapping, Sequence, TextIO

from .routes import LabeledTrace
from .traces import SpanRecord, TraceRecord


_TRACE_NAMES = {"traces.csv", "trace.csv", "spans.csv"}
_INJECT_NAMES = {"inject_time.txt", "injection_time.txt", "fault_time.txt"}


def _canon(name: str) -> str:
    return re.sub(r"[^a-z0-9]", "", name.lower())


_ALIASES: dict[str, tuple[str, ...]] = {
    "trace_id": ("traceid", "trace_id", "trace"),
    "span_id": ("spanid", "span_id"),
    "parent_span_id": ("parentspanid", "parent_span_id", "parentid", "parent_id"),
    "service": ("service", "servicename", "service_name", "microservice", "ms"),
    "operation": (
        "operation",
        "operationname",
        "operation_name",
        "spanname",
        "span_name",
        "name",
    ),
    "kind": ("kind", "spankind", "span_kind"),
    "status": (
        "status",
        "statuscode",
        "status_code",
        "responsecode",
        "response_code",
        "httpstatuscode",
        "http_status_code",
    ),
    "start": (
        "starttimeunixnano",
        "start_time_unix_nano",
        "starttimens",
        "start_time_ns",
        "starttime",
        "start_time",
        "timestamp",
        "time",
    ),
    "end": (
        "endtimeunixnano",
        "end_time_unix_nano",
        "endtimens",
        "end_time_ns",
        "endtime",
        "end_time",
    ),
    "duration": (
        "durationns",
        "duration_ns",
        "durationus",
        "duration_us",
        "durationms",
        "duration_ms",
        "duration",
        "latency",
    ),
}


def _row_with_embedded_json(row: Mapping[str, Any]) -> dict[str, Any]:
    cleaned = {str(key): value for key, value in row.items() if key is not None}
    nonempty = [value for value in cleaned.values() if value not in (None, "")]
    if len(nonempty) == 1 and isinstance(nonempty[0], str):
        candidate = nonempty[0].strip()
        if candidate.startswith("{"):
            try:
                payload = json.loads(candidate)
            except json.JSONDecodeError:
                return cleaned
            if isinstance(payload, Mapping):
                return {str(key): value for key, value in payload.items()}
    return cleaned


def _lookup(row: Mapping[str, Any], field: str) -> tuple[Any, str | None]:
    normalized = {_canon(key): (value, key) for key, value in row.items()}
    for alias in _ALIASES[field]:
        hit = normalized.get(_canon(alias))
        if hit is not None and hit[0] not in (None, ""):
            return hit
    return None, None


def _float(value: Any) -> float:
    if isinstance(value, (int, float)):
        return float(value)
    text = str(value).strip()
    if not text:
        raise ValueError("empty numeric value")
    return float(text)


def _datetime_ns(text: str) -> int | None:
    stripped = text.strip()
    if not stripped or not any(char in stripped for char in "-T:"):
        return None
    try:
        parsed = datetime.fromisoformat(stripped.replace("Z", "+00:00"))
    except ValueError:
        return None
    if parsed.tzinfo is None:
        parsed = parsed.replace(tzinfo=timezone.utc)
    return int(parsed.timestamp() * 1_000_000_000)


def timestamp_ns(value: Any, column_name: str | None = None) -> int:
    """Normalize common trace timestamps to nanoseconds since epoch.

    Explicit unit suffixes take priority. Otherwise magnitude is used:
    seconds (~1e9), milliseconds (~1e12), microseconds (~1e15), and
    nanoseconds (~1e18). ISO-8601 timestamps are also accepted.
    """
    if isinstance(value, str):
        parsed = _datetime_ns(value)
        if parsed is not None:
            return parsed
    number = _float(value)
    name = _canon(column_name or "")
    if "nano" in name or name.endswith("ns"):
        return int(number)
    if "micro" in name or name.endswith("us"):
        return int(number * 1_000)
    if "milli" in name or name.endswith("ms"):
        return int(number * 1_000_000)
    if "second" in name or name.endswith("sec"):
        return int(number * 1_000_000_000)
    magnitude = abs(number)
    if magnitude >= 1e17:
        return int(number)
    if magnitude >= 1e14:
        return int(number * 1_000)
    if magnitude >= 1e11:
        return int(number * 1_000_000)
    return int(number * 1_000_000_000)


def duration_ns(value: Any, column_name: str | None = None, default_unit: str = "ms") -> int:
    number = _float(value)
    name = _canon(column_name or "")
    if "nano" in name or name.endswith("ns"):
        multiplier = 1
    elif "micro" in name or name.endswith("us"):
        multiplier = 1_000
    elif "milli" in name or name.endswith("ms"):
        multiplier = 1_000_000
    elif "second" in name or name.endswith("sec"):
        multiplier = 1_000_000_000
    else:
        multipliers = {"ns": 1, "us": 1_000, "ms": 1_000_000, "s": 1_000_000_000}
        if default_unit not in multipliers:
            raise ValueError("default duration unit must be ns, us, ms, or s")
        multiplier = multipliers[default_unit]
    return max(0, int(number * multiplier))


def _status(value: Any) -> str:
    if value in (None, ""):
        return "UNSET"
    text = str(value).strip().upper()
    try:
        numeric = int(float(text))
    except ValueError:
        if any(marker in text for marker in ("ERROR", "FAIL", "EXCEPTION")):
            return "ERROR"
        if text in {"OK", "SUCCESS", "2XX"}:
            return "OK"
        return text
    return "ERROR" if numeric >= 400 else "OK"


def _parse_span(row: Mapping[str, Any], *, default_duration_unit: str) -> SpanRecord | None:
    row = _row_with_embedded_json(row)
    trace_id, _ = _lookup(row, "trace_id")
    span_id, _ = _lookup(row, "span_id")
    service, _ = _lookup(row, "service")
    start, start_col = _lookup(row, "start")
    if trace_id in (None, "") or span_id in (None, "") or service in (None, "") or start in (None, ""):
        return None
    operation, _ = _lookup(row, "operation")
    parent, _ = _lookup(row, "parent_span_id")
    kind, _ = _lookup(row, "kind")
    status, _ = _lookup(row, "status")
    end, end_col = _lookup(row, "end")
    duration, duration_col = _lookup(row, "duration")
    start_value = timestamp_ns(start, start_col)
    if end not in (None, ""):
        end_value = timestamp_ns(end, end_col)
    elif duration not in (None, ""):
        end_value = start_value + duration_ns(duration, duration_col, default_duration_unit)
    else:
        end_value = start_value + 1
    if end_value < start_value:
        end_value = start_value + 1
    return SpanRecord(
        trace_id=str(trace_id),
        span_id=str(span_id),
        parent_span_id="" if parent in (None, "", "0", 0) else str(parent),
        service=str(service),
        operation=str(operation or "unknown-operation"),
        kind=str(kind or "UNSPECIFIED").upper(),
        start_ns=start_value,
        end_ns=end_value,
        status=_status(status),
    )


def _infer_missing_parent_ids(spans: Sequence[SpanRecord]) -> tuple[SpanRecord, ...]:
    """Infer absent parent IDs from strict temporal containment.

    RCAEval's public description does not guarantee a parent-span column. When
    it is absent, the closest enclosing span is a conservative approximation.
    Existing explicit parents are never overwritten.
    """
    result: list[SpanRecord] = []
    for child in spans:
        if child.parent_span_id:
            result.append(child)
            continue
        candidates = [
            parent
            for parent in spans
            if parent.span_id != child.span_id
            and parent.start_ns <= child.start_ns
            and parent.end_ns >= child.end_ns
            and (parent.start_ns < child.start_ns or parent.end_ns > child.end_ns)
        ]
        if not candidates:
            result.append(child)
            continue
        parent = min(
            candidates,
            key=lambda span: (span.end_ns - span.start_ns, -span.start_ns, span.span_id),
        )
        result.append(
            SpanRecord(
                trace_id=child.trace_id,
                span_id=child.span_id,
                parent_span_id=parent.span_id,
                service=child.service,
                operation=child.operation,
                kind=child.kind,
                start_ns=child.start_ns,
                end_ns=child.end_ns,
                status=child.status,
                attributes=tuple(child.attributes) + (("adaptive.parent_inferred", True),),
            )
        )
    return tuple(result)


def parse_trace_csv(
    handle: TextIO,
    *,
    default_duration_unit: str = "ms",
    infer_missing_parents: bool = True,
    max_rows: int | None = None,
) -> tuple[TraceRecord, ...]:
    reader = csv.DictReader(handle)
    grouped: dict[str, list[SpanRecord]] = {}
    for index, row in enumerate(reader):
        if max_rows is not None and index >= max_rows:
            break
        span = _parse_span(row, default_duration_unit=default_duration_unit)
        if span is not None:
            grouped.setdefault(span.trace_id, []).append(span)
    traces: list[TraceRecord] = []
    for trace_id, spans in grouped.items():
        ordered = tuple(sorted(spans, key=lambda span: (span.start_ns, span.end_ns, span.span_id)))
        if infer_missing_parents and ordered and not any(span.parent_span_id for span in ordered):
            ordered = _infer_missing_parent_ids(ordered)
        traces.append(TraceRecord(trace_id, ordered))
    return tuple(sorted(traces, key=lambda trace: trace.trace_id))


def _parse_inject_time(data: bytes) -> int:
    text = data.decode("utf-8", errors="replace").strip()
    if not text:
        raise ValueError("empty injection time")
    # Some files contain a label followed by the value.
    candidates = re.findall(r"[-+]?\d+(?:\.\d+)?|\d{4}-\d{2}-\d{2}[^\n,;]*", text)
    for candidate in reversed(candidates or [text]):
        try:
            return timestamp_ns(candidate, "seconds")
        except (ValueError, OverflowError):
            continue
    raise ValueError(f"cannot parse injection time: {text!r}")


@dataclass(frozen=True)
class RCAEvalCase:
    case_id: str
    trace_source: str
    injection_source: str
    injection_time_ns: int
    traces: tuple[TraceRecord, ...]


@dataclass(frozen=True)
class RCAEvalCaseSummary:
    case_id: str
    trace_source: str
    injection_time_ns: int
    trace_count: int
    span_count: int
    normal_count: int
    anomaly_count: int
    ignored_count: int


def _logical_case_id(name: str) -> str:
    parent = str(PurePosixPath(name).parent)
    return parent if parent not in {"", "."} else PurePosixPath(name).stem


def _read_csv_bytes(data: bytes, *, default_duration_unit: str, max_rows: int | None) -> tuple[TraceRecord, ...]:
    if data[:2] == b"\x1f\x8b":
        data = gzip.decompress(data)
    return parse_trace_csv(
        io.StringIO(data.decode("utf-8", errors="replace")),
        default_duration_unit=default_duration_unit,
        max_rows=max_rows,
    )


def iter_rcaeval_cases(
    path: str | Path,
    *,
    default_duration_unit: str = "ms",
    max_cases: int | None = None,
    max_rows_per_case: int | None = None,
    max_member_bytes: int = 512 * 1024 * 1024,
) -> Iterator[RCAEvalCase]:
    """Read RCAEval case directories or ZIPs containing traces.csv/inject_time.txt."""
    root = Path(path)
    yielded = 0
    if root.is_dir():
        for trace_path in sorted(root.rglob("*")):
            if not trace_path.is_file() or trace_path.name.lower() not in _TRACE_NAMES:
                continue
            inject_path = next(
                (trace_path.parent / name for name in _INJECT_NAMES if (trace_path.parent / name).exists()),
                None,
            )
            if inject_path is None:
                continue
            if trace_path.stat().st_size > max_member_bytes:
                continue
            with trace_path.open("r", encoding="utf-8", errors="replace", newline="") as handle:
                traces = parse_trace_csv(
                    handle,
                    default_duration_unit=default_duration_unit,
                    max_rows=max_rows_per_case,
                )
            yield RCAEvalCase(
                case_id=str(trace_path.parent.relative_to(root)),
                trace_source=str(trace_path.relative_to(root)),
                injection_source=str(inject_path.relative_to(root)),
                injection_time_ns=_parse_inject_time(inject_path.read_bytes()),
                traces=traces,
            )
            yielded += 1
            if max_cases is not None and yielded >= max_cases:
                return
        return

    if not zipfile.is_zipfile(root):
        raise ValueError("RCAEval source must be a directory or ZIP archive")
    with zipfile.ZipFile(root) as archive:
        infos = {info.filename: info for info in archive.infolist() if not info.is_dir()}
        lower_names = {name.lower(): name for name in infos}
        for logical_name in sorted(infos):
            if PurePosixPath(logical_name).name.lower() not in _TRACE_NAMES:
                continue
            info = infos[logical_name]
            if info.file_size > max_member_bytes:
                continue
            parent = PurePosixPath(logical_name).parent
            inject_name = None
            for candidate in _INJECT_NAMES:
                lookup = str(parent / candidate).lower()
                if lookup in lower_names:
                    inject_name = lower_names[lookup]
                    break
            if inject_name is None:
                continue
            traces = _read_csv_bytes(
                archive.read(info),
                default_duration_unit=default_duration_unit,
                max_rows=max_rows_per_case,
            )
            yield RCAEvalCase(
                case_id=_logical_case_id(logical_name),
                trace_source=logical_name,
                injection_source=inject_name,
                injection_time_ns=_parse_inject_time(archive.read(inject_name)),
                traces=traces,
            )
            yielded += 1
            if max_cases is not None and yielded >= max_cases:
                return


def _trace_time_ns(trace: TraceRecord) -> int:
    return min((span.start_ns for span in trace.spans), default=0)


def _stable_cap(traces: Sequence[TraceRecord], limit: int | None) -> tuple[TraceRecord, ...]:
    if limit is None or len(traces) <= limit:
        return tuple(traces)
    return tuple(
        sorted(
            traces,
            key=lambda trace: hashlib.sha1(trace.trace_id.encode("utf-8")).hexdigest(),
        )[:limit]
    )


def labeled_examples_from_cases(
    cases: Iterable[RCAEvalCase],
    *,
    normal_window_seconds: float = 120.0,
    anomaly_window_seconds: float = 120.0,
    guard_seconds: float = 5.0,
    max_traces_per_label_per_case: int | None = 200,
) -> tuple[tuple[LabeledTrace, ...], tuple[RCAEvalCaseSummary, ...]]:
    if normal_window_seconds <= 0 or anomaly_window_seconds <= 0 or guard_seconds < 0:
        raise ValueError("windows must be positive and guard nonnegative")
    normal_ns = int(normal_window_seconds * 1_000_000_000)
    anomaly_ns = int(anomaly_window_seconds * 1_000_000_000)
    guard_ns = int(guard_seconds * 1_000_000_000)
    examples: list[LabeledTrace] = []
    summaries: list[RCAEvalCaseSummary] = []
    for case in cases:
        normal: list[TraceRecord] = []
        anomaly: list[TraceRecord] = []
        ignored = 0
        for trace in case.traces:
            delta = _trace_time_ns(trace) - case.injection_time_ns
            if -normal_ns <= delta <= -guard_ns:
                normal.append(trace)
            elif guard_ns <= delta <= anomaly_ns:
                anomaly.append(trace)
            else:
                ignored += 1
        normal_capped = _stable_cap(normal, max_traces_per_label_per_case)
        anomaly_capped = _stable_cap(anomaly, max_traces_per_label_per_case)
        examples.extend(LabeledTrace(trace, case.case_id, "normal") for trace in normal_capped)
        examples.extend(LabeledTrace(trace, case.case_id, "anomaly") for trace in anomaly_capped)
        summaries.append(
            RCAEvalCaseSummary(
                case_id=case.case_id,
                trace_source=case.trace_source,
                injection_time_ns=case.injection_time_ns,
                trace_count=len(case.traces),
                span_count=sum(len(trace.spans) for trace in case.traces),
                normal_count=len(normal_capped),
                anomaly_count=len(anomaly_capped),
                ignored_count=ignored,
            )
        )
    return tuple(examples), tuple(summaries)


@dataclass(frozen=True)
class TraceCSVWindowStats:
    rows_seen: int
    parsed_spans: int
    spooled_spans: int
    spooled_trace_count: int
    normal_trace_count: int
    anomaly_trace_count: int
    selected_normal_count: int
    selected_anomaly_count: int
    sqlite_bytes: int


@dataclass(frozen=True)
class StreamingCaseSummary:
    case_id: str
    benchmark: str | None
    root_cause_service: str | None
    fault_type: str | None
    instance: str | None
    trace_source: str
    injection_time_ns: int
    normal_count: int
    anomaly_count: int
    rows_seen: int
    parsed_spans: int
    spooled_spans: int
    spooled_trace_count: int
    sqlite_bytes: int


def parse_case_metadata(case_id: str) -> tuple[str | None, str | None, str | None, str | None]:
    """Parse the documented ``benchmark_service_fault_instance`` convention.

    Service names may contain hyphens; underscores are treated as structural
    separators.  Unknown layouts are retained without inventing labels.
    """
    base = PurePosixPath(case_id).name
    parts = [part for part in base.split("_") if part]
    if len(parts) < 4:
        return (parts[0] if parts else None, None, None, None)
    benchmark = parts[0]
    instance = parts[-1]
    fault_type = parts[-2]
    root_service = "_".join(parts[1:-2]) or None
    return benchmark, root_service, fault_type, instance


def _stable_trace_ids(rows: Sequence[tuple[str, int]], limit: int | None) -> tuple[str, ...]:
    if limit is None or len(rows) <= limit:
        return tuple(trace_id for trace_id, _ in rows)
    ranked = sorted(
        rows,
        key=lambda item: (
            hashlib.sha1(item[0].encode("utf-8")).hexdigest(),
            item[0],
        ),
    )
    return tuple(trace_id for trace_id, _ in ranked[:limit])


def parse_trace_csv_windowed(
    handle: TextIO,
    *,
    injection_time_ns: int,
    normal_window_seconds: float = 120.0,
    anomaly_window_seconds: float = 120.0,
    guard_seconds: float = 5.0,
    max_trace_margin_seconds: float = 30.0,
    max_traces_per_label: int | None = 200,
    default_duration_unit: str = "ms",
    infer_missing_parents: bool = True,
    batch_size: int = 10_000,
    scratch_dir: str | Path | None = None,
) -> tuple[tuple[TraceRecord, ...], tuple[TraceRecord, ...], TraceCSVWindowStats]:
    """Parse a large RCAEval trace CSV with bounded Python memory.

    Span rows are streamed into a temporary SQLite database rather than grouped
    in a Python dictionary.  Only rows in an expanded injection-time window are
    spooled.  The expansion preserves all spans of ordinary short distributed
    traces while keeping multi-hour telemetry files small.  Trace caps are
    selected by a stable hash of ``trace_id`` and therefore do not depend on CSV
    row order.
    """
    if normal_window_seconds <= 0 or anomaly_window_seconds <= 0:
        raise ValueError("normal and anomaly windows must be positive")
    if guard_seconds < 0 or max_trace_margin_seconds < 0:
        raise ValueError("guard and trace margin must be nonnegative")
    if batch_size < 1:
        raise ValueError("batch_size must be positive")

    normal_ns = int(normal_window_seconds * 1_000_000_000)
    anomaly_ns = int(anomaly_window_seconds * 1_000_000_000)
    guard_ns = int(guard_seconds * 1_000_000_000)
    margin_ns = int(max_trace_margin_seconds * 1_000_000_000)
    spool_low = injection_time_ns - normal_ns - margin_ns
    spool_high = injection_time_ns + anomaly_ns + margin_ns

    scratch = None if scratch_dir is None else str(Path(scratch_dir))
    temp = tempfile.NamedTemporaryFile(prefix="adaptive_h_trace_", suffix=".sqlite", dir=scratch, delete=False)
    db_path = Path(temp.name)
    temp.close()
    rows_seen = 0
    parsed_spans = 0
    spooled_spans = 0
    try:
        connection = sqlite3.connect(db_path)
        connection.execute("PRAGMA journal_mode=OFF")
        connection.execute("PRAGMA synchronous=OFF")
        connection.execute("PRAGMA temp_store=MEMORY")
        connection.execute(
            """
            CREATE TABLE spans (
                trace_id TEXT NOT NULL,
                span_id TEXT NOT NULL,
                parent_span_id TEXT NOT NULL,
                service TEXT NOT NULL,
                operation TEXT NOT NULL,
                kind TEXT NOT NULL,
                start_ns INTEGER NOT NULL,
                end_ns INTEGER NOT NULL,
                status TEXT NOT NULL
            )
            """
        )
        reader = csv.DictReader(handle)
        batch: list[tuple[object, ...]] = []
        for row in reader:
            rows_seen += 1
            span = _parse_span(row, default_duration_unit=default_duration_unit)
            if span is None:
                continue
            parsed_spans += 1
            if span.end_ns < spool_low or span.start_ns > spool_high:
                continue
            batch.append(
                (
                    span.trace_id,
                    span.span_id,
                    span.parent_span_id,
                    span.service,
                    span.operation,
                    span.kind,
                    span.start_ns,
                    span.end_ns,
                    span.status,
                )
            )
            if len(batch) >= batch_size:
                connection.executemany("INSERT INTO spans VALUES (?,?,?,?,?,?,?,?,?)", batch)
                spooled_spans += len(batch)
                batch.clear()
        if batch:
            connection.executemany("INSERT INTO spans VALUES (?,?,?,?,?,?,?,?,?)", batch)
            spooled_spans += len(batch)
        connection.commit()
        connection.execute("CREATE INDEX spans_trace_start ON spans(trace_id, start_ns)")

        grouped = list(
            connection.execute(
                "SELECT trace_id, MIN(start_ns) FROM spans GROUP BY trace_id ORDER BY trace_id"
            )
        )
        normal_rows: list[tuple[str, int]] = []
        anomaly_rows: list[tuple[str, int]] = []
        for raw_trace_id, raw_start in grouped:
            trace_id = str(raw_trace_id)
            start_ns = int(raw_start)
            delta = start_ns - injection_time_ns
            if -normal_ns <= delta <= -guard_ns:
                normal_rows.append((trace_id, start_ns))
            elif guard_ns <= delta <= anomaly_ns:
                anomaly_rows.append((trace_id, start_ns))
        normal_ids = _stable_trace_ids(normal_rows, max_traces_per_label)
        anomaly_ids = _stable_trace_ids(anomaly_rows, max_traces_per_label)
        selected_ids = set(normal_ids) | set(anomaly_ids)

        spans_by_trace: dict[str, list[SpanRecord]] = {trace_id: [] for trace_id in selected_ids}
        if selected_ids:
            # Scan the indexed spool once. This avoids SQLite's variable limit
            # when callers request more than a few hundred traces.
            for values in connection.execute(
                """
                SELECT trace_id, span_id, parent_span_id, service, operation,
                       kind, start_ns, end_ns, status
                FROM spans ORDER BY trace_id, start_ns, end_ns, span_id
                """
            ):
                trace_id = str(values[0])
                if trace_id not in selected_ids:
                    continue
                spans_by_trace[trace_id].append(
                    SpanRecord(
                        trace_id=trace_id,
                        span_id=str(values[1]),
                        parent_span_id=str(values[2]),
                        service=str(values[3]),
                        operation=str(values[4]),
                        kind=str(values[5]),
                        start_ns=int(values[6]),
                        end_ns=int(values[7]),
                        status=str(values[8]),
                    )
                )

        def build(trace_ids: Sequence[str]) -> tuple[TraceRecord, ...]:
            traces: list[TraceRecord] = []
            for trace_id in trace_ids:
                spans = tuple(spans_by_trace.get(trace_id, ()))
                if not spans:
                    continue
                if infer_missing_parents and not any(span.parent_span_id for span in spans):
                    spans = _infer_missing_parent_ids(spans)
                traces.append(TraceRecord(trace_id, spans))
            return tuple(traces)

        normal = build(normal_ids)
        anomaly = build(anomaly_ids)
        connection.close()
        sqlite_bytes = db_path.stat().st_size if db_path.exists() else 0
        stats = TraceCSVWindowStats(
            rows_seen=rows_seen,
            parsed_spans=parsed_spans,
            spooled_spans=spooled_spans,
            spooled_trace_count=len(grouped),
            normal_trace_count=len(normal_rows),
            anomaly_trace_count=len(anomaly_rows),
            selected_normal_count=len(normal),
            selected_anomaly_count=len(anomaly),
            sqlite_bytes=sqlite_bytes,
        )
        return normal, anomaly, stats
    finally:
        try:
            db_path.unlink()
        except FileNotFoundError:
            pass


def load_labeled_rcaeval_streaming(
    path: str | Path,
    *,
    normal_window_seconds: float = 120.0,
    anomaly_window_seconds: float = 120.0,
    guard_seconds: float = 5.0,
    max_trace_margin_seconds: float = 30.0,
    max_traces_per_label_per_case: int | None = 200,
    default_duration_unit: str = "ms",
    max_cases: int | None = None,
    scratch_dir: str | Path | None = None,
) -> tuple[tuple[LabeledTrace, ...], tuple[StreamingCaseSummary, ...]]:
    """Load RCAEval cases without materializing complete trace CSV members."""
    root = Path(path)
    examples: list[LabeledTrace] = []
    summaries: list[StreamingCaseSummary] = []

    def consume(
        case_id: str,
        trace_source: str,
        injection_source: str,
        injection_data: bytes,
        handle: TextIO,
    ) -> None:
        injection_ns = _parse_inject_time(injection_data)
        normal, anomaly, stats = parse_trace_csv_windowed(
            handle,
            injection_time_ns=injection_ns,
            normal_window_seconds=normal_window_seconds,
            anomaly_window_seconds=anomaly_window_seconds,
            guard_seconds=guard_seconds,
            max_trace_margin_seconds=max_trace_margin_seconds,
            max_traces_per_label=max_traces_per_label_per_case,
            default_duration_unit=default_duration_unit,
            scratch_dir=scratch_dir,
        )
        benchmark, root_service, fault_type, instance = parse_case_metadata(case_id)
        examples.extend(
            LabeledTrace(trace, case_id, "normal", fault_type=fault_type) for trace in normal
        )
        examples.extend(
            LabeledTrace(trace, case_id, "anomaly", fault_type=fault_type) for trace in anomaly
        )
        summaries.append(
            StreamingCaseSummary(
                case_id=case_id,
                benchmark=benchmark,
                root_cause_service=root_service,
                fault_type=fault_type,
                instance=instance,
                trace_source=trace_source,
                injection_time_ns=injection_ns,
                normal_count=len(normal),
                anomaly_count=len(anomaly),
                rows_seen=stats.rows_seen,
                parsed_spans=stats.parsed_spans,
                spooled_spans=stats.spooled_spans,
                spooled_trace_count=stats.spooled_trace_count,
                sqlite_bytes=stats.sqlite_bytes,
            )
        )

    if root.is_dir():
        trace_paths = [
            item for item in sorted(root.rglob("*"))
            if item.is_file() and item.name.lower() in _TRACE_NAMES
        ]
        for trace_path in trace_paths:
            if max_cases is not None and len(summaries) >= max_cases:
                break
            inject_path = next(
                (trace_path.parent / name for name in _INJECT_NAMES if (trace_path.parent / name).exists()),
                None,
            )
            if inject_path is None:
                continue
            with trace_path.open("r", encoding="utf-8", errors="replace", newline="") as handle:
                consume(
                    str(trace_path.parent.relative_to(root)),
                    str(trace_path.relative_to(root)),
                    str(inject_path.relative_to(root)),
                    inject_path.read_bytes(),
                    handle,
                )
        return tuple(examples), tuple(summaries)

    if not zipfile.is_zipfile(root):
        raise ValueError("RCAEval source must be a directory or ZIP archive")
    with zipfile.ZipFile(root) as archive:
        infos = {info.filename: info for info in archive.infolist() if not info.is_dir()}
        lower_names = {name.lower(): name for name in infos}
        for logical_name in sorted(infos):
            if max_cases is not None and len(summaries) >= max_cases:
                break
            if PurePosixPath(logical_name).name.lower() not in _TRACE_NAMES:
                continue
            parent = PurePosixPath(logical_name).parent
            inject_name = next(
                (
                    lower_names[str(parent / candidate).lower()]
                    for candidate in _INJECT_NAMES
                    if str(parent / candidate).lower() in lower_names
                ),
                None,
            )
            if inject_name is None:
                continue
            with archive.open(infos[logical_name], "r") as binary:
                with io.TextIOWrapper(binary, encoding="utf-8", errors="replace", newline="") as handle:
                    consume(
                        _logical_case_id(logical_name),
                        logical_name,
                        inject_name,
                        archive.read(inject_name),
                        handle,
                    )
    return tuple(examples), tuple(summaries)
