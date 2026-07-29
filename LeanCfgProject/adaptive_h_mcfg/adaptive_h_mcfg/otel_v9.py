from __future__ import annotations

from dataclasses import replace
from typing import Iterable

from .traces import SpanRecord, TraceRecord


SCHEDULE_SERVICE = "@schedule"


def _attr_dict(span: SpanRecord) -> dict[str, object]:
    return dict(span.attributes)


def _is_cross_service_entry(span: SpanRecord, by_id: dict[str, SpanRecord]) -> bool:
    parent = by_id.get(span.parent_span_id)
    if parent is None:
        return False
    if span.service == parent.service:
        return False
    # Prefer server/consumer entries where available. Some datasets omit or
    # normalize kind, so an explicit cross-service parent edge is sufficient.
    return span.kind.upper() in {"SERVER", "CONSUMER", "UNSPECIFIED", "SPAN_KIND_SERVER"}


def augment_with_schedule(
    trace: TraceRecord,
    service: str = SCHEDULE_SERVICE,
    target_services: set[str] | None = None,
) -> TraceRecord:
    """Add one pseudo-lifeline containing cross-service calls in start order.

    The original service lifelines preserve per-service local order and counts,
    but intentionally discard relative timing between services. The pseudo
    schedule block restores a finite, one-token-per-call projection without
    doubling the trace with every END event. Duplicate calls and call reordering
    remain route preserving because the set of service edges is unchanged.
    """
    by_id = {span.span_id: span for span in trace.spans}
    entries = [
        span
        for span in trace.spans
        if _is_cross_service_entry(span, by_id)
        and (target_services is None or span.service in target_services)
    ]
    entries.sort(key=lambda span: (span.start_ns, span.end_ns, span.service, span.operation, span.span_id))
    if not entries:
        return trace
    roots = [span for span in trace.spans if not span.parent_span_id]
    root_id = roots[0].span_id if roots else ""
    pseudo: list[SpanRecord] = []
    for index, entry in enumerate(entries):
        attrs = (
            ("schedule.target.service", entry.service),
            ("schedule.target.operation", entry.operation),
            ("schedule.ordinal", index),
        )
        pseudo.append(
            SpanRecord(
                trace_id=trace.trace_id,
                span_id=f"schedule-{index}-{entry.span_id}",
                parent_span_id=root_id,
                service=service,
                operation=f"{entry.service}:{entry.operation}",
                kind="SCHEDULE",
                start_ns=entry.start_ns,
                end_ns=max(entry.start_ns + 1, entry.end_ns),
                status=entry.status,
                attributes=attrs,
            )
        )
    spans = tuple(sorted((*trace.spans, *pseudo), key=lambda s: (s.start_ns, s.end_ns, s.service, s.span_id)))
    return TraceRecord(trace_id=trace.trace_id, spans=spans)


def strip_ground_truth_attributes(trace: TraceRecord) -> TraceRecord:
    """Remove experiment-only labels before any model-facing preprocessing."""
    spans = []
    for span in trace.spans:
        attrs = tuple(
            (key, value)
            for key, value in span.attributes
            if not key.startswith("mcfg.fault.")
        )
        spans.append(replace(span, attributes=attrs))
    return TraceRecord(trace_id=trace.trace_id, spans=tuple(spans))


def prepare_otel_traces(traces: Iterable[TraceRecord], add_schedule: bool = True) -> list[TraceRecord]:
    result = []
    for trace in traces:
        cleaned = strip_ground_truth_attributes(trace)
        result.append(augment_with_schedule(cleaned) if add_schedule else cleaned)
    return result
