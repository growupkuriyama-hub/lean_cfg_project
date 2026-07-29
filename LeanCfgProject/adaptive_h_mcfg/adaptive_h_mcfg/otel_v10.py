from __future__ import annotations

from dataclasses import dataclass, replace
from typing import Iterable, Sequence

from .traces import SpanRecord, TraceRecord


@dataclass(frozen=True)
class CheckoutProjection:
    trace_id: str
    item_count: int
    word: str
    product_server_span_ids: tuple[str, ...]
    currency_server_span_ids: tuple[str, ...]
    currency_roles: tuple[tuple[str, str], ...]


def _service_matches(service: str, needles: Sequence[str]) -> bool:
    normalized = service.lower().replace("_", "-")
    return all(needle in normalized for needle in needles)


def _is_kind(span: SpanRecord, expected: str) -> bool:
    kind = span.kind.upper().removeprefix("SPAN_KIND_")
    return kind == expected


def _paired_cross_service_calls(
    trace: TraceRecord,
    checkout_needles: Sequence[str] = ("checkout",),
) -> list[tuple[SpanRecord, SpanRecord]]:
    """Return (checkout client span, downstream server span) pairs.

    OpenTelemetry normally models a cross-service RPC with a CLIENT span in the
    caller and a SERVER span in the callee. The server span's parent is the client
    span. Traces without this explicit relation are skipped rather than guessed.
    """
    by_id = {span.span_id: span for span in trace.spans}
    result: list[tuple[SpanRecord, SpanRecord]] = []
    for server in trace.spans:
        if not _is_kind(server, "SERVER"):
            continue
        client = by_id.get(server.parent_span_id)
        if client is None or not _is_kind(client, "CLIENT"):
            continue
        if not _service_matches(client.service, checkout_needles):
            continue
        result.append((client, server))
    return sorted(result, key=lambda pair: (
        pair[0].start_ns,
        pair[0].end_ns,
        pair[0].span_id,
        pair[1].span_id,
    ))


def checkout_phase_projection(
    trace: TraceRecord,
    checkout_needles: Sequence[str] = ("checkout",),
    product_needles: Sequence[str] = ("product",),
    currency_needles: Sequence[str] = ("currency",),
) -> CheckoutProjection | None:
    """Project a checkout trace to three synchronized strings.

    The blocks are:

      1. Product-catalog SERVER starts, encoded as ``p``.
      2. Currency SERVER starts. Currency calls are assigned roles by the
         checkout CLIENT order: all but the final currency call are product
         conversions ``c``; the final one is shipping conversion ``s``.
      3. Checkout CLIENT call schedule over the same RPC pairs, using ``p/c/s``.

    This projection uses caller order for semantic role assignment and callee
    order for the service-local lifeline. It can therefore reveal route-preserving
    client/server phase inversions without depending on operation-name variants.
    """
    pairs = _paired_cross_service_calls(trace, checkout_needles)
    product_pairs = [
        pair for pair in pairs
        if _service_matches(pair[1].service, product_needles)
    ]
    currency_pairs = [
        pair for pair in pairs
        if _service_matches(pair[1].service, currency_needles)
    ]
    if not product_pairs or len(currency_pairs) != len(product_pairs) + 1:
        return None

    shipping_client_id = currency_pairs[-1][0].span_id
    role_by_server: dict[str, str] = {
        server.span_id: ("s" if client.span_id == shipping_client_id else "c")
        for client, server in currency_pairs
    }

    product_servers = sorted(
        (server for _, server in product_pairs),
        key=lambda span: (span.start_ns, span.end_ns, span.span_id),
    )
    currency_servers = sorted(
        (server for _, server in currency_pairs),
        key=lambda span: (span.start_ns, span.end_ns, span.span_id),
    )

    schedule: list[str] = []
    selected_pairs = sorted(
        (*product_pairs, *currency_pairs),
        key=lambda pair: (pair[0].start_ns, pair[0].end_ns, pair[0].span_id),
    )
    for client, server in selected_pairs:
        if server.span_id in role_by_server:
            schedule.append(role_by_server[server.span_id])
        else:
            schedule.append("p")

    product_block = "p" * len(product_servers)
    currency_block = "".join(role_by_server[span.span_id] for span in currency_servers)
    schedule_block = "".join(schedule)
    return CheckoutProjection(
        trace_id=trace.trace_id,
        item_count=len(product_servers),
        word=f"{product_block}#{currency_block}#{schedule_block}",
        product_server_span_ids=tuple(span.span_id for span in product_servers),
        currency_server_span_ids=tuple(span.span_id for span in currency_servers),
        currency_roles=tuple(sorted(role_by_server.items())),
    )


def is_normal_checkout_projection(projection: CheckoutProjection) -> bool:
    n = projection.item_count
    return projection.word == f"{'p' * n}#{'c' * n}s#{'pc' * n}s"


def invert_final_currency_server_phase(trace: TraceRecord) -> TraceRecord:
    """Swap the callee start order of the final product and shipping conversions.

    Client spans and all service edges remain unchanged. Only the two downstream
    Currency SERVER intervals are exchanged. This models queueing, timestamp
    corruption, or asynchronous dispatch that makes the server-local phase order
    disagree with the caller schedule.

    A trace that lacks the explicit Checkout CLIENT -> Currency SERVER links is
    returned unchanged.
    """
    pairs = _paired_cross_service_calls(trace)
    currency_pairs = [
        pair for pair in pairs
        if _service_matches(pair[1].service, ("currency",))
    ]
    if len(currency_pairs) < 2:
        return trace
    product_pair = currency_pairs[-2]
    shipping_pair = currency_pairs[-1]
    product_server = product_pair[1]
    shipping_server = shipping_pair[1]

    product_duration = max(1, product_server.duration_ns)
    shipping_duration = max(1, shipping_server.duration_ns)
    early_start = min(product_server.start_ns, shipping_server.start_ns)
    late_start = max(product_server.start_ns, shipping_server.start_ns)
    if early_start == late_start:
        late_start = early_start + 1

    replacements = {
        product_server.span_id: replace(
            product_server,
            start_ns=late_start,
            end_ns=late_start + product_duration,
            attributes=tuple(sorted((*product_server.attributes, ("mcfg.mutation", "currency-phase-inversion")))),
        ),
        shipping_server.span_id: replace(
            shipping_server,
            start_ns=early_start,
            end_ns=early_start + shipping_duration,
            attributes=tuple(sorted((*shipping_server.attributes, ("mcfg.mutation", "currency-phase-inversion")))),
        ),
    }
    spans = tuple(sorted(
        (replacements.get(span.span_id, span) for span in trace.spans),
        key=lambda span: (span.start_ns, span.end_ns, span.service, span.span_id),
    ))
    return TraceRecord(trace_id=f"{trace.trace_id}-phase-inversion", spans=spans)


def drop_one_product_server_span(trace: TraceRecord) -> TraceRecord:
    """Remove the final Product SERVER span while retaining its CLIENT span."""
    pairs = _paired_cross_service_calls(trace)
    products = [
        server for _, server in pairs
        if _service_matches(server.service, ("product",))
    ]
    if not products:
        return trace
    target = products[-1].span_id
    return TraceRecord(
        trace_id=f"{trace.trace_id}-drop-product-server",
        spans=tuple(span for span in trace.spans if span.span_id != target),
    )


def make_paired_checkout_trace(item_count: int, trace_id: str = "checkout") -> TraceRecord:
    """Small deterministic CLIENT/SERVER fixture matching the checkout projection."""
    if item_count < 1:
        raise ValueError("item_count must be positive")
    spans: list[SpanRecord] = []
    root = SpanRecord(
        trace_id=trace_id,
        span_id="checkout-root",
        parent_span_id="",
        service="checkout",
        operation="PlaceOrder",
        kind="SERVER",
        start_ns=0,
        end_ns=10_000_000,
        status="UNSET",
        attributes=(),
    )
    spans.append(root)
    cursor = 100_000

    def rpc(target: str, ordinal: int) -> None:
        nonlocal cursor
        client_id = f"checkout-{target}-client-{ordinal}"
        server_id = f"{target}-server-{ordinal}"
        client = SpanRecord(
            trace_id=trace_id,
            span_id=client_id,
            parent_span_id=root.span_id,
            service="checkout",
            operation=f"call:{target}",
            kind="CLIENT",
            start_ns=cursor,
            end_ns=cursor + 40_000,
            status="UNSET",
            attributes=(),
        )
        server = SpanRecord(
            trace_id=trace_id,
            span_id=server_id,
            parent_span_id=client_id,
            service=target,
            operation="rpc",
            kind="SERVER",
            start_ns=cursor + 10_000,
            end_ns=cursor + 30_000,
            status="UNSET",
            attributes=(),
        )
        spans.extend((client, server))
        cursor += 100_000

    for index in range(item_count):
        rpc("product-catalog", index)
        rpc("currency", index)
    rpc("currency", item_count)  # shipping conversion
    return TraceRecord(
        trace_id=trace_id,
        spans=tuple(sorted(spans, key=lambda span: (
            span.start_ns, span.end_ns, span.service, span.span_id
        ))),
    )


def project_many(traces: Iterable[TraceRecord]) -> list[CheckoutProjection]:
    return [
        projection
        for trace in traces
        if (projection := checkout_phase_projection(trace)) is not None
    ]
