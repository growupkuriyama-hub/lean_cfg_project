from __future__ import annotations

import csv
import io
import zipfile
from pathlib import Path

from .synthetic_traces import make_chain_trace
from .traces import SpanRecord, TraceRecord


def _shift_trace(trace: TraceRecord, offset_ns: int, trace_id: str | None = None) -> TraceRecord:
    new_id = trace_id or trace.trace_id
    id_map = {span.span_id: f"{new_id}:{index}" for index, span in enumerate(trace.spans)}
    shifted = []
    for span in trace.spans:
        shifted.append(
            SpanRecord(
                trace_id=new_id,
                span_id=id_map[span.span_id],
                parent_span_id=id_map.get(span.parent_span_id, ""),
                service=span.service,
                operation=span.operation,
                kind=span.kind,
                start_ns=span.start_ns + offset_ns,
                end_ns=span.end_ns + offset_ns,
                status=span.status,
            )
        )
    return TraceRecord(new_id, tuple(shifted))


def _case_traces(case_index: int, injection_ns: int) -> tuple[TraceRecord, ...]:
    traces: list[TraceRecord] = []
    # Three pre-injection normal traces. Repetition counts vary across cases,
    # forcing the grammar to generalize across run-disjoint data.
    for local, seconds_before in enumerate((50, 30, 10)):
        n = 1 + ((case_index + local) % 3)
        base = make_chain_trace(n, f"normal-{case_index}-{local}")
        traces.append(
            _shift_trace(
                base,
                injection_ns - seconds_before * 1_000_000_000,
                f"normal-{case_index}-{local}",
            )
        )
    # Two post-injection same-route faults omit one terminal span while keeping
    # at least one normal terminal call, so the route edge set remains stable.
    for local, seconds_after in enumerate((10, 30)):
        n = 3 + ((case_index + local) % 2)
        base = make_chain_trace(n, f"fault-{case_index}-{local}", omit_terminal=1)
        traces.append(
            _shift_trace(
                base,
                injection_ns + seconds_after * 1_000_000_000,
                f"fault-{case_index}-{local}",
            )
        )
    return tuple(traces)


def _csv_bytes(traces: tuple[TraceRecord, ...]) -> bytes:
    output = io.StringIO()
    fieldnames = [
        "start_time_unix_nano",
        "trace_id",
        "span_id",
        "parent_span_id",
        "service_name",
        "operation",
        "duration_ns",
        "status_code",
        "span_kind",
    ]
    writer = csv.DictWriter(output, fieldnames=fieldnames)
    writer.writeheader()
    for trace in traces:
        for span in trace.spans:
            writer.writerow(
                {
                    "start_time_unix_nano": span.start_ns,
                    "trace_id": span.trace_id,
                    "span_id": span.span_id,
                    "parent_span_id": span.parent_span_id,
                    "service_name": span.service,
                    "operation": span.operation,
                    "duration_ns": span.duration_ns,
                    "status_code": 500 if span.status == "ERROR" else 200,
                    "span_kind": span.kind,
                }
            )
    return output.getvalue().encode("utf-8")


def write_synthetic_rcaeval_archive(path: str | Path, case_count: int = 9) -> Path:
    destination = Path(path)
    injection_seconds = 1_700_000_000
    injection_ns = injection_seconds * 1_000_000_000
    with zipfile.ZipFile(destination, "w", compression=zipfile.ZIP_DEFLATED) as archive:
        for case_index in range(case_count):
            case_id = f"RE2_ts-payment-service_delay_{case_index + 1}"
            traces = _case_traces(case_index, injection_ns + case_index * 1_000_000_000_000)
            archive.writestr(f"{case_id}/traces.csv", _csv_bytes(traces))
            archive.writestr(
                f"{case_id}/inject_time.txt",
                str(injection_seconds + case_index * 1_000),
            )
    return destination
