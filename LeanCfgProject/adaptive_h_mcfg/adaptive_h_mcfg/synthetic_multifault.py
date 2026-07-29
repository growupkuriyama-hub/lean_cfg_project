from __future__ import annotations

import csv
import io
import zipfile
from dataclasses import replace
from pathlib import Path
from typing import Callable, Sequence

from .synthetic_traces import make_chain_trace
from .traces import SpanRecord, TraceRecord

FAULT_TYPES = ("omission", "duplication", "routechange", "status", "latency")


def shift_trace(trace: TraceRecord, offset_ns: int, trace_id: str | None = None) -> TraceRecord:
    new_id = trace_id or trace.trace_id
    id_map = {span.span_id: f"{new_id}:{index}" for index, span in enumerate(trace.spans)}
    shifted: list[SpanRecord] = []
    for span in trace.spans:
        shifted.append(
            replace(
                span,
                trace_id=new_id,
                span_id=id_map[span.span_id],
                parent_span_id=id_map.get(span.parent_span_id, ""),
                start_ns=span.start_ns + offset_ns,
                end_ns=span.end_ns + offset_ns,
            )
        )
    return TraceRecord(new_id, tuple(shifted))


def _status_fault(trace: TraceRecord) -> TraceRecord:
    changed = False
    spans: list[SpanRecord] = []
    for span in trace.spans:
        if not changed and span.service == "shipping":
            spans.append(replace(span, status="ERROR"))
            changed = True
        else:
            spans.append(span)
    return TraceRecord(trace.trace_id, tuple(spans))


def _latency_fault(trace: TraceRecord) -> TraceRecord:
    """Pure duration fault that intentionally preserves START-event encoding."""
    changed = False
    spans: list[SpanRecord] = []
    for span in trace.spans:
        if not changed and span.service == "shipping":
            spans.append(replace(span, end_ns=span.end_ns + 5_000_000_000))
            changed = True
        else:
            spans.append(span)
    return TraceRecord(trace.trace_id, tuple(spans))


def make_fault_trace(fault_type: str, n: int, trace_id: str) -> TraceRecord:
    if fault_type == "omission":
        return make_chain_trace(n, trace_id, omit_terminal=1)
    if fault_type == "duplication":
        return make_chain_trace(n, trace_id, duplicate_terminal=1)
    if fault_type == "routechange":
        return make_chain_trace(
            n,
            trace_id,
            services=("gateway", "payment", "inventory", "notification"),
        )
    if fault_type == "status":
        return _status_fault(make_chain_trace(n, trace_id))
    if fault_type == "latency":
        return _latency_fault(make_chain_trace(n, trace_id))
    raise ValueError(f"unknown fault type: {fault_type}")


def case_traces(
    fault_type: str,
    instance: int,
    injection_ns: int,
) -> tuple[TraceRecord, ...]:
    traces: list[TraceRecord] = []
    # All fault strata expose the same normal length family. This isolates the
    # fault mechanism from the normal-data distribution while retaining
    # case-disjoint run identifiers.
    for local, seconds_before in enumerate((50, 30, 10)):
        n = 1 + ((instance + local) % 3)
        trace_id = f"normal-{fault_type}-{instance}-{local}"
        traces.append(
            shift_trace(
                make_chain_trace(n, trace_id),
                injection_ns - seconds_before * 1_000_000_000,
                trace_id,
            )
        )
    for local, seconds_after in enumerate((10, 30)):
        n = 3 + ((instance + local) % 2)
        trace_id = f"fault-{fault_type}-{instance}-{local}"
        traces.append(
            shift_trace(
                make_fault_trace(fault_type, n, trace_id),
                injection_ns + seconds_after * 1_000_000_000,
                trace_id,
            )
        )
    return tuple(traces)


def traces_csv_bytes(traces: Sequence[TraceRecord]) -> bytes:
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


def write_multifault_rcaeval_archive(
    path: str | Path,
    *,
    instances_per_fault: int = 6,
    fault_types: Sequence[str] = FAULT_TYPES,
) -> Path:
    if instances_per_fault < 3:
        raise ValueError("at least three instances per fault are required for stratified splitting")
    unknown = set(fault_types) - set(FAULT_TYPES)
    if unknown:
        raise ValueError(f"unknown fault types: {sorted(unknown)}")
    destination = Path(path)
    injection_seconds = 1_700_000_000
    with zipfile.ZipFile(destination, "w", compression=zipfile.ZIP_DEFLATED) as archive:
        case_index = 0
        for fault_type in fault_types:
            for instance in range(1, instances_per_fault + 1):
                case_index += 1
                case_injection_seconds = injection_seconds + case_index * 1_000
                injection_ns = case_injection_seconds * 1_000_000_000
                case_id = f"RE3_ts-payment-service_{fault_type}_{instance}"
                traces = case_traces(fault_type, instance, injection_ns)
                archive.writestr(f"{case_id}/traces.csv", traces_csv_bytes(traces))
                archive.writestr(f"{case_id}/inject_time.txt", str(case_injection_seconds))
    return destination
