from __future__ import annotations

import io
import json
import zipfile
from pathlib import Path
from typing import Iterable

from .synthetic_traces import make_chain_trace
from .traces import TraceRecord


def trace_to_jaeger_payload(trace: TraceRecord) -> dict[str, object]:
    processes: dict[str, dict[str, str]] = {}
    process_by_service: dict[str, str] = {}
    for index, service in enumerate(sorted({span.service for span in trace.spans})):
        process_id = f"p{index}"
        process_by_service[service] = process_id
        processes[process_id] = {"serviceName": service}

    spans = []
    for span in trace.spans:
        references = []
        if span.parent_span_id:
            references.append(
                {
                    "refType": "CHILD_OF",
                    "traceID": trace.trace_id,
                    "spanID": span.parent_span_id,
                }
            )
        tags = [{"key": "span.kind", "type": "string", "value": span.kind.lower()}]
        if span.status == "ERROR":
            tags.append({"key": "error", "type": "bool", "value": True})
        spans.append(
            {
                "traceID": trace.trace_id,
                "spanID": span.span_id,
                "operationName": span.operation,
                "references": references,
                "startTime": span.start_ns // 1_000,
                "duration": max(0, (span.end_ns - span.start_ns) // 1_000),
                "tags": tags,
                "processID": process_by_service[span.service],
            }
        )
    return {
        "data": [
            {
                "traceID": trace.trace_id,
                "spans": spans,
                "processes": processes,
            }
        ]
    }


def write_synthetic_archive(path: str | Path, *, nested_member: bool = True) -> Path:
    """Create a run-labeled Jaeger archive for end-to-end regression tests.

    Seed 9 yields the intended normal split: n=1,2 train; n=3 validation;
    n=4 test. Anomaly runs include two same-route structural faults and one
    alternate-route fault that should be rejected before grammar recognition.
    """
    output = Path(path)
    normal = {
        f"normal-n{n}": make_chain_trace(n, f"normal-n{n}")
        for n in range(1, 5)
    }
    anomalies = {
        "anomaly-omit": make_chain_trace(4, "anomaly-omit", omit_terminal=1),
        "anomaly-duplicate": make_chain_trace(4, "anomaly-duplicate", duplicate_terminal=1),
        "anomaly-route": make_chain_trace(
            2,
            "anomaly-route",
            services=("frontend", "catalog", "database"),
        ),
    }

    with zipfile.ZipFile(output, "w", compression=zipfile.ZIP_DEFLATED) as archive:
        for run_id, trace in normal.items():
            payload = json.dumps(trace_to_jaeger_payload(trace), separators=(",", ":"))
            if nested_member and run_id == "normal-n3":
                buffer = io.BytesIO()
                with zipfile.ZipFile(buffer, "w", compression=zipfile.ZIP_DEFLATED) as nested:
                    # Deliberately omit a JSON suffix to exercise content sniffing.
                    nested.writestr(f"{run_id}/Traces_export", payload)
                archive.writestr(f"{run_id}.zip", buffer.getvalue())
            else:
                archive.writestr(f"{run_id}/traces.json", payload)
        for run_id, trace in anomalies.items():
            payload = json.dumps(trace_to_jaeger_payload(trace), separators=(",", ":"))
            archive.writestr(f"{run_id}/traces.json", payload)
        archive.writestr("README.txt", "synthetic mixed monitoring archive")
        archive.writestr("normal-n1/metrics.json", '{"metric": 1}')
    return output


def write_synthetic_benchmark_archive(path: str | Path) -> Path:
    """Create a larger run-disjoint benchmark with explicit split names.

    Training contains only n=1,2; validation contains n=3; testing contains
    n=4,5,6. Replicated runs improve confidence intervals without changing the
    deduplicated positive language seen by the learner.
    """
    output = Path(path)
    members: dict[str, TraceRecord] = {}
    for n in (1, 2):
        for repetition in range(1, 4):
            run = f"normal-train-n{n}-r{repetition}"
            members[run] = make_chain_trace(n, run)
    for repetition in range(1, 5):
        run = f"normal-validation-n3-r{repetition}"
        members[run] = make_chain_trace(3, run)
    for n in (4, 5, 6):
        for repetition in range(1, 4):
            run = f"normal-test-n{n}-r{repetition}"
            members[run] = make_chain_trace(n, run)

    for n in (4, 5, 6):
        omit = f"anomaly-test-omit-n{n}"
        duplicate = f"anomaly-test-duplicate-n{n}"
        members[omit] = make_chain_trace(n, omit, omit_terminal=1)
        members[duplicate] = make_chain_trace(n, duplicate, duplicate_terminal=1)
    for repetition in range(1, 4):
        run = f"anomaly-test-route-r{repetition}"
        members[run] = make_chain_trace(
            2,
            run,
            services=("frontend", "catalog", "database"),
        )

    with zipfile.ZipFile(output, "w", compression=zipfile.ZIP_DEFLATED) as archive:
        for run_id, trace in sorted(members.items()):
            payload = json.dumps(trace_to_jaeger_payload(trace), separators=(",", ":"))
            archive.writestr(f"{run_id}/Traces_export", payload)
        archive.writestr("metadata/metrics.json", '{"metric": 1}')
        archive.writestr("README.txt", "run-disjoint adaptive-h benchmark")
    return output
