from __future__ import annotations

from collections import defaultdict
from dataclasses import dataclass
from hashlib import sha1
from random import Random
from typing import Iterable, Sequence

from .traces import SpanRecord, TraceRecord


@dataclass(frozen=True, order=True)
class RouteSignature:
    """A count-insensitive structural signature for one distributed trace route.

    Repeated calls collapse to one edge.  This lets traces with different loop or
    retry counts share a route model while separating genuinely different call
    topologies and root endpoints.
    """

    services: tuple[str, ...]
    roots: tuple[tuple[str, str], ...]
    edges: tuple[tuple[str, str, str, str], ...]
    basis: str = "callgraph"

    @property
    def route_id(self) -> str:
        payload = repr((self.basis, self.services, self.roots, self.edges)).encode("utf-8")
        return sha1(payload).hexdigest()[:12]


def _canonical_service_order(
    services: set[str],
    roots: set[tuple[str, str]],
    edges: set[tuple[str, str, str, str]],
) -> tuple[str, ...]:
    """Order lifelines by minimum call-graph depth, then by service name.

    Alphabetical order is stable but semantically arbitrary: it can place a
    downstream service before its caller and make cross-lifeline mutations hard
    to interpret. Minimum depth preserves root-to-leaf order for acyclic routes
    and remains deterministic when cycles or branches are present.
    """
    adjacency: dict[str, set[str]] = defaultdict(set)
    for parent_service, _, child_service, _ in edges:
        adjacency[parent_service].add(child_service)

    root_services = sorted(service for service, _ in roots)
    depth: dict[str, int] = {service: 0 for service in root_services}
    queue = list(root_services)
    cursor = 0
    while cursor < len(queue):
        service = queue[cursor]
        cursor += 1
        for child in sorted(adjacency.get(service, ())):
            candidate = depth[service] + 1
            if child not in depth or candidate < depth[child]:
                depth[child] = candidate
                queue.append(child)
    fallback = max(depth.values(), default=-1) + 1
    return tuple(sorted(services, key=lambda service: (depth.get(service, fallback), service)))


def _parent_was_inferred(span: SpanRecord) -> bool:
    return any(key == "adaptive.parent_inferred" and bool(value) for key, value in span.attributes)


@dataclass(frozen=True)
class RouteQuality:
    basis: str
    span_count: int
    service_count: int
    explicit_parent_links: int
    inferred_parent_links: int
    unresolved_roots: int

    @property
    def explicit_parent_fraction(self) -> float:
        return self.explicit_parent_links / max(1, self.span_count - 1)


def route_quality(trace: TraceRecord) -> RouteQuality:
    explicit = sum(
        bool(span.parent_span_id) and not _parent_was_inferred(span)
        for span in trace.spans
    )
    inferred = sum(
        bool(span.parent_span_id) and _parent_was_inferred(span)
        for span in trace.spans
    )
    roots = sum(not span.parent_span_id for span in trace.spans)
    return RouteQuality(
        basis="callgraph" if explicit else "temporal-service-order",
        span_count=len(trace.spans),
        service_count=len({span.service for span in trace.spans}),
        explicit_parent_links=explicit,
        inferred_parent_links=inferred,
        unresolved_roots=roots,
    )


def _temporal_route_signature(trace: TraceRecord) -> RouteSignature:
    earliest: dict[str, SpanRecord] = {}
    for span in sorted(trace.spans, key=lambda item: (item.start_ns, item.end_ns, item.service, item.operation)):
        earliest.setdefault(span.service, span)
    ordered = tuple(
        service for service, _ in sorted(
            earliest.items(),
            key=lambda item: (item[1].start_ns, item[1].end_ns, item[0], item[1].operation),
        )
    )
    roots: tuple[tuple[str, str], ...] = ()
    edges: list[tuple[str, str, str, str]] = []
    if ordered:
        first = earliest[ordered[0]]
        roots = ((first.service, first.operation),)
        for left, right in zip(ordered, ordered[1:]):
            parent = earliest[left]
            child = earliest[right]
            edges.append((parent.service, parent.operation, child.service, child.operation))
    return RouteSignature(
        services=ordered,
        roots=roots,
        edges=tuple(edges),
        basis="temporal-service-order",
    )


def route_signature(trace: TraceRecord) -> RouteSignature:
    quality = route_quality(trace)
    if quality.explicit_parent_links == 0:
        return _temporal_route_signature(trace)
    by_id: dict[str, SpanRecord] = {span.span_id: span for span in trace.spans}
    roots: set[tuple[str, str]] = set()
    edges: set[tuple[str, str, str, str]] = set()
    services = {span.service for span in trace.spans}
    for span in trace.spans:
        parent = by_id.get(span.parent_span_id)
        if parent is None:
            roots.add((span.service, span.operation))
        else:
            edges.add((parent.service, parent.operation, span.service, span.operation))
    return RouteSignature(
        services=_canonical_service_order(services, roots, edges),
        roots=tuple(sorted(roots)),
        edges=tuple(sorted(edges)),
        basis="callgraph",
    )


def cluster_by_route(traces: Iterable[TraceRecord]) -> dict[RouteSignature, list[TraceRecord]]:
    clusters: dict[RouteSignature, list[TraceRecord]] = defaultdict(list)
    for trace in traces:
        clusters[route_signature(trace)].append(trace)
    return {
        signature: sorted(items, key=lambda trace: trace.trace_id)
        for signature, items in sorted(clusters.items(), key=lambda item: item[0].route_id)
    }


@dataclass(frozen=True)
class LabeledTrace:
    trace: TraceRecord
    run_id: str
    label: str = "normal"
    fault_type: str | None = None

    def __post_init__(self) -> None:
        if self.label not in {"normal", "anomaly"}:
            raise ValueError("label must be 'normal' or 'anomaly'")


@dataclass(frozen=True)
class RunSplit:
    train_runs: tuple[str, ...]
    validation_runs: tuple[str, ...]
    test_runs: tuple[str, ...]

    def partition(self, examples: Sequence[LabeledTrace]) -> tuple[list[LabeledTrace], list[LabeledTrace], list[LabeledTrace]]:
        train_set = set(self.train_runs)
        validation_set = set(self.validation_runs)
        test_set = set(self.test_runs)
        if train_set & validation_set or train_set & test_set or validation_set & test_set:
            raise ValueError("run partitions must be disjoint")
        train = [example for example in examples if example.run_id in train_set]
        validation = [example for example in examples if example.run_id in validation_set]
        test = [example for example in examples if example.run_id in test_set]
        return train, validation, test


def deterministic_run_split(
    examples: Sequence[LabeledTrace],
    train_fraction: float = 0.5,
    validation_fraction: float = 0.25,
    seed: int = 0,
) -> RunSplit:
    """Split by run identifier, never by individual trace.

    This avoids leakage among near-duplicate traces emitted by the same fault or
    load-generation run.
    """
    if not 0 < train_fraction < 1:
        raise ValueError("train_fraction must be between zero and one")
    if not 0 <= validation_fraction < 1:
        raise ValueError("validation_fraction must be in [0, 1)")
    if train_fraction + validation_fraction >= 1:
        raise ValueError("train and validation fractions must leave a test partition")

    runs = sorted({example.run_id for example in examples})
    Random(seed).shuffle(runs)
    n = len(runs)
    if n < 3:
        raise ValueError("at least three runs are required")
    n_train = max(1, int(n * train_fraction))
    n_validation = max(1, int(n * validation_fraction))
    if n_train + n_validation >= n:
        n_validation = 1
        n_train = n - 2
    return RunSplit(
        train_runs=tuple(sorted(runs[:n_train])),
        validation_runs=tuple(sorted(runs[n_train:n_train + n_validation])),
        test_runs=tuple(sorted(runs[n_train + n_validation:])),
    )


def deterministic_stratified_run_split(
    examples: Sequence[LabeledTrace],
    train_fraction: float = 0.5,
    validation_fraction: float = 0.25,
    seed: int = 0,
) -> RunSplit:
    """Run-disjoint split stratified by ``fault_type`` when available.

    RCAEval RE3 contains repeated instances for each fault family.  A global
    shuffle can accidentally leave a fault family out of the test partition,
    making per-fault recall incomparable across seeds.  This splitter applies
    the ordinary deterministic run split independently inside every fault
    family and then unions the partitions.
    """
    by_run: dict[str, str] = {}
    for example in examples:
        label = example.fault_type or "unknown"
        previous = by_run.setdefault(example.run_id, label)
        if previous != label:
            raise ValueError(f"run {example.run_id!r} has inconsistent fault labels")
    grouped: dict[str, list[str]] = defaultdict(list)
    for run_id, label in by_run.items():
        grouped[label].append(run_id)
    train: list[str] = []
    validation: list[str] = []
    test: list[str] = []
    for label in sorted(grouped):
        runs = sorted(grouped[label])
        if len(runs) < 3:
            raise ValueError(
                f"fault stratum {label!r} needs at least three runs, found {len(runs)}"
            )
        # Salt each stratum deterministically without depending on Python's hash.
        salt = int(sha1(label.encode("utf-8")).hexdigest()[:8], 16)
        Random(seed ^ salt).shuffle(runs)
        n = len(runs)
        n_train = max(1, int(n * train_fraction))
        n_validation = max(1, int(n * validation_fraction))
        if n_train + n_validation >= n:
            n_validation = 1
            n_train = n - 2
        train.extend(runs[:n_train])
        validation.extend(runs[n_train:n_train + n_validation])
        test.extend(runs[n_train + n_validation:])
    return RunSplit(tuple(sorted(train)), tuple(sorted(validation)), tuple(sorted(test)))
