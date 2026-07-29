from __future__ import annotations

from dataclasses import dataclass
from typing import Iterable

from .traces import SpanRecord, TraceRecord
from .otel_v9 import augment_with_schedule


@dataclass(frozen=True)
class CheckoutScenario:
    item_count: int
    fault: str = "none"
    trace_id: str = "trace"


def _span(
    trace_id: str,
    span_id: str,
    parent_id: str,
    service: str,
    operation: str,
    start: int,
    duration: int = 10,
    kind: str = "SERVER",
) -> SpanRecord:
    return SpanRecord(
        trace_id=trace_id,
        span_id=span_id,
        parent_span_id=parent_id,
        service=service,
        operation=operation,
        kind=kind,
        start_ns=start * 1_000_000,
        end_ns=(start + duration) * 1_000_000,
        status="UNSET",
        attributes=(),
    )


def checkout_trace(scenario: CheckoutScenario, add_schedule: bool = True) -> TraceRecord:
    """Source-derived abstraction of the official Checkout PlaceOrder flow.

    It follows the July 2026 Go implementation: GetCart, per-item GetProduct and
    Convert, GetQuote and shipping-cost Convert, Charge, ShipOrder, EmptyCart,
    and SendOrderConfirmation. Faults preserve the service-edge set.
    """
    n = scenario.item_count
    if n < 1:
        raise ValueError("item_count must be positive")
    tid = scenario.trace_id
    spans: list[SpanRecord] = [_span(tid, "root", "", "checkout", "PlaceOrder", 0, 1000)]
    cursor = 10

    def call(service: str, operation: str, suffix: str) -> None:
        nonlocal cursor
        spans.append(_span(tid, f"{service}-{suffix}", "root", service, operation, cursor))
        cursor += 10

    call("cart", "GetCart", "get")

    if scenario.fault == "reorder-quote-before-products":
        call("shipping", "GetQuote", "quote")
        call("currency", "ConvertShipping", "shipping")

    for i in range(n):
        call("product-catalog", "GetProduct", f"product-{i}")
        if scenario.fault == "duplicate-product-lookup" and i == n - 1:
            call("product-catalog", "GetProduct", "product-duplicate")
        call("currency", "ConvertProduct", f"product-{i}")

    if scenario.fault != "reorder-quote-before-products":
        call("shipping", "GetQuote", "quote")
        call("currency", "ConvertShipping", "shipping")

    call("payment", "Charge", "charge")
    if scenario.fault == "duplicate-payment":
        call("payment", "Charge", "charge-duplicate")
    call("shipping", "ShipOrder", "ship")
    if scenario.fault != "skip-empty-cart":
        call("cart", "EmptyCart", "empty")
    call("email", "SendOrderConfirmation", "email")
    if scenario.fault == "duplicate-email":
        call("email", "SendOrderConfirmation", "email-duplicate")

    trace = TraceRecord(trace_id=tid, spans=tuple(sorted(spans, key=lambda s: (s.start_ns, s.service, s.span_id))))
    return augment_with_schedule(trace) if add_schedule else trace


def make_checkout_dataset(
    counts: Iterable[int],
    fault: str = "none",
    prefix: str = "checkout",
    add_schedule: bool = True,
) -> list[TraceRecord]:
    return [
        checkout_trace(
            CheckoutScenario(item_count=n, fault=fault, trace_id=f"{prefix}-{fault}-{n}"),
            add_schedule=add_schedule,
        )
        for n in counts
    ]
