from __future__ import annotations

from dataclasses import dataclass
from typing import Iterable

from .otel_v10 import CheckoutProjection, checkout_phase_projection
from .traces import TraceRecord


@dataclass(frozen=True)
class ProjectionMutation:
    """A route-preserving mutation of one checkout projection.

    The mutation operates on server-side occurrence order/count while keeping the
    caller schedule block unchanged.  In the concrete trace experiment these
    correspond to offline span mutations; no application source is patched.
    """

    name: str
    word: str
    route_preserving: bool
    description: str


def _split(word: str) -> tuple[str, str, str]:
    parts = word.split("#")
    if len(parts) != 3:
        raise ValueError(f"expected three projection blocks, got {word!r}")
    return parts[0], parts[1], parts[2]


def projection_mutations(projection: CheckoutProjection) -> tuple[ProjectionMutation, ...]:
    """Generate controlled server-side mutations from a normal projection.

    All mutations leave the Checkout CLIENT schedule block unchanged.  For count
    mutations, the coarse service graph is preserved when at least one occurrence
    of the affected RPC remains.
    """

    product, currency, schedule = _split(projection.word)
    output: list[ProjectionMutation] = []

    # Diagnostic mutation: server-local Currency phase disagrees with caller
    # order while counts and service edges are unchanged.
    if currency.endswith("cs"):
        output.append(
            ProjectionMutation(
                name="currency-server-phase-inversion",
                word=f"{product}#{currency[:-2]}sc#{schedule}",
                route_preserving=True,
                description=(
                    "swap the final product-conversion and shipping-conversion "
                    "SERVER order while retaining Checkout CLIENT order"
                ),
            )
        )

    if len(product) >= 2:
        output.append(
            ProjectionMutation(
                name="drop-product-server-occurrence",
                word=f"{product[:-1]}#{currency}#{schedule}",
                route_preserving=True,
                description="drop one Product Catalog SERVER span; another product edge remains",
            )
        )
    if product:
        output.append(
            ProjectionMutation(
                name="duplicate-product-server-occurrence",
                word=f"{product}p#{currency}#{schedule}",
                route_preserving=True,
                description="duplicate one Product Catalog SERVER span without duplicating its CLIENT span",
            )
        )

    product_currency_count = currency.count("c")
    if product_currency_count >= 2:
        index = currency.rfind("c")
        output.append(
            ProjectionMutation(
                name="drop-product-currency-server-occurrence",
                word=f"{product}#{currency[:index]}{currency[index + 1:]}#{schedule}",
                route_preserving=True,
                description="drop one product-price Currency SERVER span; other Currency edges remain",
            )
        )
    if product_currency_count:
        shipping_index = currency.rfind("s")
        insert_at = shipping_index if shipping_index >= 0 else len(currency)
        output.append(
            ProjectionMutation(
                name="duplicate-product-currency-server-occurrence",
                word=f"{product}#{currency[:insert_at]}c{currency[insert_at:]}#{schedule}",
                route_preserving=True,
                description="duplicate one product-price Currency SERVER span",
            )
        )

    if "s" in currency:
        output.append(
            ProjectionMutation(
                name="duplicate-shipping-currency-server-occurrence",
                word=f"{product}#{currency}s#{schedule}",
                route_preserving=True,
                description="duplicate the shipping Currency SERVER span",
            )
        )

    # Stable order and no accidental duplicates.
    unique: dict[tuple[str, str], ProjectionMutation] = {}
    for mutation in output:
        if mutation.word != projection.word:
            unique[(mutation.name, mutation.word)] = mutation
    return tuple(unique[key] for key in sorted(unique))


def project_trace_with_mutations(trace: TraceRecord) -> tuple[CheckoutProjection, tuple[ProjectionMutation, ...]] | None:
    projection = checkout_phase_projection(trace)
    if projection is None:
        return None
    return projection, projection_mutations(projection)


def mutation_family_words(item_count: int) -> dict[str, str]:
    """Controlled abstract family used by the deterministic regression benchmark."""
    if item_count < 1:
        raise ValueError("item_count must be positive")
    normal = CheckoutProjection(
        trace_id=f"abstract-{item_count}",
        item_count=item_count,
        word=f"{'p' * item_count}#{'c' * item_count}s#{'pc' * item_count}s",
        product_server_span_ids=(),
        currency_server_span_ids=(),
        currency_roles=(),
    )
    return {mutation.name: mutation.word for mutation in projection_mutations(normal)}
