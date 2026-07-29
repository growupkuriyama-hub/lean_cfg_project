from __future__ import annotations

from typing import Sequence

from .traces import SpanRecord, TraceRecord


def make_chain_trace(
    n: int,
    trace_id: str,
    services: Sequence[str] = ("gateway", "payment", "inventory", "shipping"),
    omit_terminal: int = 0,
    duplicate_terminal: int = 0,
) -> TraceRecord:
    """Create a repeated chain route with count-insensitive stable topology.

    Each transaction contributes one span per service.  Optional faults remove
    or duplicate terminal-service spans, preserving the unique route edge set
    whenever at least one normal terminal span remains.
    """
    if n < 1:
        raise ValueError("n must be positive")
    if omit_terminal < 0 or duplicate_terminal < 0 or omit_terminal >= n:
        raise ValueError("invalid fault counts")

    spans: list[SpanRecord] = []
    terminal_service = services[-1]
    keep_terminal = n - omit_terminal
    for transaction in range(n):
        parent_id = ""
        for depth, service in enumerate(services):
            if service == terminal_service and transaction >= keep_terminal:
                continue
            span_id = f"{trace_id}-{transaction}-{depth}"
            start = transaction * 1_000_000 + depth * 100_000
            end = start + 50_000
            spans.append(
                SpanRecord(
                    trace_id=trace_id,
                    span_id=span_id,
                    parent_span_id=parent_id,
                    service=service,
                    operation=f"{service}.handle",
                    kind="INTERNAL" if depth == 0 else "CLIENT",
                    start_ns=start,
                    end_ns=end,
                    status="UNSET",
                )
            )
            parent_id = span_id

    for extra in range(duplicate_terminal):
        transaction = extra % n
        parent_id = f"{trace_id}-{transaction}-{len(services)-2}"
        span_id = f"{trace_id}-dup-{extra}"
        start = (n + extra) * 1_000_000 + (len(services) - 1) * 100_000
        spans.append(
            SpanRecord(
                trace_id=trace_id,
                span_id=span_id,
                parent_span_id=parent_id,
                service=terminal_service,
                operation=f"{terminal_service}.handle",
                kind="CLIENT",
                start_ns=start,
                end_ns=start + 50_000,
                status="UNSET",
            )
        )
    return TraceRecord(trace_id=trace_id, spans=tuple(sorted(spans, key=lambda span: (span.start_ns, span.span_id))))
