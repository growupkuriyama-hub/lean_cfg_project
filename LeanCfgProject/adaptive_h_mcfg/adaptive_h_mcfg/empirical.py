from __future__ import annotations

import math
import re
from collections import Counter, defaultdict
from dataclasses import asdict, dataclass
from typing import Iterable, Sequence

from .datasets import TraceSource
from .mutations import encoded_unseen_mutants
from .pipeline import RouteExperimentConfig, RouteModelBundle, fit_route_model
from .routes import (
    LabeledTrace,
    RouteSignature,
    RunSplit,
    deterministic_run_split,
    deterministic_stratified_run_split,
    route_signature,
)
from .traces import TraceRecord


@dataclass(frozen=True)
class LabelRules:
    """Explicit provenance-based dataset labeling rules.

    Research archives use heterogeneous folder names, so the prototype refuses
    to guess labels. A source is normal/anomalous only when its logical path or
    inferred run id matches the corresponding regular expression. Matches to
    both expressions are rejected as ambiguous.
    """

    normal_regex: str
    anomaly_regex: str

    def classify(self, source: TraceSource) -> str | None:
        text = f"{source.run_id}\n{source.name}"
        normal = re.search(self.normal_regex, text, flags=re.IGNORECASE) is not None
        anomaly = re.search(self.anomaly_regex, text, flags=re.IGNORECASE) is not None
        if normal and anomaly:
            raise ValueError(f"ambiguous normal/anomaly label for source {source.name!r}")
        if normal:
            return "normal"
        if anomaly:
            return "anomaly"
        return None




@dataclass(frozen=True)
class PilotSplitRules:
    train_regex: str
    validation_regex: str
    test_regex: str

    def build(self, normal: Sequence[LabeledTrace]) -> RunSplit:
        runs = sorted({item.run_id for item in normal})
        train = tuple(run for run in runs if re.search(self.train_regex, run, re.IGNORECASE))
        validation = tuple(run for run in runs if re.search(self.validation_regex, run, re.IGNORECASE))
        test = tuple(run for run in runs if re.search(self.test_regex, run, re.IGNORECASE))
        selected = [*train, *validation, *test]
        if len(selected) != len(set(selected)):
            raise ValueError("explicit run split regexes overlap")
        unmatched = set(runs) - set(selected)
        if unmatched:
            raise ValueError(f"normal runs unmatched by explicit split: {sorted(unmatched)}")
        if not train or not validation or not test:
            raise ValueError("explicit run split must make all three partitions nonempty")
        return RunSplit(train, validation, test)

def labeled_examples_from_sources(
    sources: Iterable[TraceSource],
    rules: LabelRules,
) -> tuple[LabeledTrace, ...]:
    examples: list[LabeledTrace] = []
    for source in sources:
        label = rules.classify(source)
        if label is None:
            continue
        for trace in source.traces:
            examples.append(LabeledTrace(trace=trace, run_id=source.run_id, label=label))
    return tuple(examples)


@dataclass(frozen=True)
class RouteCoverage:
    route_id: str
    signature: RouteSignature
    normal_traces: int
    anomaly_traces: int
    normal_runs: int
    anomaly_runs: int


def route_coverage(examples: Sequence[LabeledTrace]) -> tuple[RouteCoverage, ...]:
    grouped: dict[RouteSignature, list[LabeledTrace]] = defaultdict(list)
    for example in examples:
        grouped[route_signature(example.trace)].append(example)
    rows: list[RouteCoverage] = []
    for signature, items in grouped.items():
        normal = [item for item in items if item.label == "normal"]
        anomaly = [item for item in items if item.label == "anomaly"]
        rows.append(
            RouteCoverage(
                route_id=signature.route_id,
                signature=signature,
                normal_traces=len(normal),
                anomaly_traces=len(anomaly),
                normal_runs=len({item.run_id for item in normal}),
                anomaly_runs=len({item.run_id for item in anomaly}),
            )
        )
    return tuple(
        sorted(
            rows,
            key=lambda row: (
                -row.normal_runs,
                -row.normal_traces,
                -row.anomaly_traces,
                row.route_id,
            ),
        )
    )


def choose_pilot_route(
    coverage: Sequence[RouteCoverage],
    *,
    route_id: str | None = None,
    min_normal_runs: int = 3,
    min_normal_traces: int = 3,
) -> RouteCoverage:
    candidates = [
        row
        for row in coverage
        if row.normal_runs >= min_normal_runs and row.normal_traces >= min_normal_traces
    ]
    if route_id is not None:
        candidates = [row for row in candidates if row.route_id == route_id]
    if not candidates:
        raise ValueError(
            "no route satisfies the pilot requirements; inspect the route manifest "
            "or lower min_normal_runs/min_normal_traces"
        )
    return candidates[0]


def wilson_interval(successes: int, total: int, z: float = 1.959963984540054) -> tuple[float, float]:
    if total <= 0:
        return (0.0, 0.0)
    p = successes / total
    denominator = 1.0 + z * z / total
    center = (p + z * z / (2.0 * total)) / denominator
    radius = z * math.sqrt((p * (1.0 - p) + z * z / (4.0 * total)) / total) / denominator
    return (max(0.0, center - radius), min(1.0, center + radius))


def _unknown_rate(bundle: RouteModelBundle, traces: Sequence[TraceRecord]) -> float:
    token = bundle.encoder.unknown_token
    unknown = 0
    events = 0
    for trace in traces:
        encoded = bundle.encoder.encode(trace)
        unknown += encoded.count(token)
        events += len(encoded.replace(bundle.encoder.separator, ""))
    return unknown / max(1, events)


@dataclass(frozen=True)
class PilotMetrics:
    normal_total: int
    normal_accepted: int
    anomaly_total: int
    anomaly_rejected: int
    grammar_anomaly_total: int
    grammar_anomaly_rejected: int
    route_mismatch_anomalies: int
    precision: float
    recall: float
    f1: float
    normal_acceptance_ci_low: float
    normal_acceptance_ci_high: float
    anomaly_recall_ci_low: float
    anomaly_recall_ci_high: float
    unknown_event_rate: float
    unseen_mutant_total: int
    unseen_mutant_rejected: int


@dataclass(frozen=True)
class FaultMetrics:
    fault_type: str
    total: int
    rejected: int
    recall: float
    grammar_total: int
    grammar_rejected: int
    route_mismatch_rejected: int


@dataclass(frozen=True)
class CaseMetrics:
    run_id: str
    fault_type: str
    normal_total: int
    normal_accepted: int
    anomaly_total: int
    anomaly_rejected: int
    route_mismatch_rejected: int

    @property
    def normal_acceptance(self) -> float:
        return self.normal_accepted / max(1, self.normal_total)

    @property
    def anomaly_recall(self) -> float:
        return self.anomaly_rejected / max(1, self.anomaly_total)


@dataclass(frozen=True)
class PilotResult:
    route_id: str
    services: tuple[str, ...]
    split_seed: int
    train_runs: tuple[str, ...]
    validation_runs: tuple[str, ...]
    test_normal_runs: tuple[str, ...]
    anomaly_runs: tuple[str, ...]
    strict_case_disjoint: bool
    stratified_split: bool
    selected_observers: tuple[str, ...]
    candidate_observers: tuple[str, ...]
    rule_count: int
    unit_rule_count: int
    observed_type_count: int
    metrics: PilotMetrics
    fault_metrics: tuple[FaultMetrics, ...]
    case_metrics: tuple[CaseMetrics, ...]
    selection_history: tuple[dict[str, object], ...]

    def as_dict(self) -> dict[str, object]:
        output = asdict(self)
        output["metrics"] = asdict(self.metrics)
        return output


def run_route_pilot(
    examples: Sequence[LabeledTrace],
    *,
    route_id: str | None = None,
    seed: int = 0,
    config: RouteExperimentConfig = RouteExperimentConfig(),
    min_normal_runs: int = 3,
    min_normal_traces: int = 3,
    split_rules: PilotSplitRules | None = None,
    stratify_fault_types: bool = False,
    strict_case_disjoint: bool = True,
) -> PilotResult:
    coverage = route_coverage(examples)
    selected_route = choose_pilot_route(
        coverage,
        route_id=route_id,
        min_normal_runs=min_normal_runs,
        min_normal_traces=min_normal_traces,
    )
    route_examples = [
        example
        for example in examples
        if route_signature(example.trace) == selected_route.signature
    ]
    normal = [example for example in route_examples if example.label == "normal"]

    if split_rules is not None:
        split = split_rules.build(normal)
    elif stratify_fault_types:
        split = deterministic_stratified_run_split(normal, seed=seed)
    else:
        split = deterministic_run_split(normal, seed=seed)
    train, validation, test_normal = split.partition(normal)
    if not train or not validation or not test_normal:
        raise ValueError("run split produced an empty normal partition")

    bundle = fit_route_model(
        [item.trace for item in train],
        [item.trace for item in validation],
        config,
    )

    test_run_set = set(split.test_runs)
    anomaly_pool = [example for example in examples if example.label == "anomaly"]
    all_anomalies = (
        [example for example in anomaly_pool if example.run_id in test_run_set]
        if strict_case_disjoint
        else anomaly_pool
    )
    anomalies_same_route = [
        example
        for example in all_anomalies
        if route_signature(example.trace) == selected_route.signature
    ]

    test_normal_traces = [item.trace for item in test_normal]
    same_route_anomaly_traces = [item.trace for item in anomalies_same_route]
    normal_words = [bundle.encoder.encode(trace) for trace in test_normal_traces]
    anomaly_words = [bundle.encoder.encode(trace) for trace in same_route_anomaly_traces]
    decisions = bundle.model.accepts_many_guided([*normal_words, *anomaly_words])
    unseen_words = encoded_unseen_mutants(normal_words, bundle.encoder.separator)
    unseen_decisions = bundle.model.accepts_many_guided(unseen_words) if unseen_words else {}

    normal_accepted = sum(decisions[word] for word in normal_words)
    grammar_rejected = sum(not decisions[word] for word in anomaly_words)
    mismatch_anomalies = sum(
        route_signature(item.trace) != selected_route.signature for item in all_anomalies
    )
    anomaly_total = len(all_anomalies)
    anomaly_rejected = grammar_rejected + mismatch_anomalies
    false_positive = len(normal_words) - normal_accepted
    precision = anomaly_rejected / max(1, anomaly_rejected + false_positive)
    recall = anomaly_rejected / max(1, anomaly_total)
    f1 = 2.0 * precision * recall / max(1e-15, precision + recall)
    normal_ci = wilson_interval(normal_accepted, len(normal_words))
    anomaly_ci = wilson_interval(anomaly_rejected, anomaly_total)

    fault_rows: list[FaultMetrics] = []
    for fault_type in sorted({item.fault_type or "unknown" for item in all_anomalies}):
        items = [item for item in all_anomalies if (item.fault_type or "unknown") == fault_type]
        grammar_items = [
            item for item in items if route_signature(item.trace) == selected_route.signature
        ]
        mismatch = len(items) - len(grammar_items)
        grammar_words = [bundle.encoder.encode(item.trace) for item in grammar_items]
        grammar_decisions = (
            bundle.model.accepts_many_guided(grammar_words) if grammar_words else {}
        )
        grammar_rejected_by_type = sum(
            not grammar_decisions[word] for word in grammar_words
        )
        rejected_by_type = mismatch + grammar_rejected_by_type
        fault_rows.append(
            FaultMetrics(
                fault_type=fault_type,
                total=len(items),
                rejected=rejected_by_type,
                recall=rejected_by_type / max(1, len(items)),
                grammar_total=len(grammar_items),
                grammar_rejected=grammar_rejected_by_type,
                route_mismatch_rejected=mismatch,
            )
        )

    case_rows: list[CaseMetrics] = []
    for run_id in split.test_runs:
        normal_items = [item for item in test_normal if item.run_id == run_id]
        anomaly_items = [item for item in all_anomalies if item.run_id == run_id]
        normal_hits = sum(
            decisions[bundle.encoder.encode(item.trace)] for item in normal_items
        )
        anomaly_hits = 0
        mismatch_hits = 0
        for item in anomaly_items:
            if route_signature(item.trace) != selected_route.signature:
                anomaly_hits += 1
                mismatch_hits += 1
            else:
                word = bundle.encoder.encode(item.trace)
                anomaly_hits += int(not decisions[word])
        labels = {item.fault_type or "unknown" for item in [*normal_items, *anomaly_items]}
        case_rows.append(
            CaseMetrics(
                run_id=run_id,
                fault_type=next(iter(labels)) if len(labels) == 1 else "mixed",
                normal_total=len(normal_items),
                normal_accepted=normal_hits,
                anomaly_total=len(anomaly_items),
                anomaly_rejected=anomaly_hits,
                route_mismatch_rejected=mismatch_hits,
            )
        )

    history = tuple(
        {
            "selected": item.selected,
            "normal_accuracy": item.normal_accuracy,
            "mutation_recall": item.mutant_recall,
            "rule_count": item.rule_count,
            "observed_type_count": item.observed_type_count,
            "objective": item.objective,
        }
        for item in bundle.selection.history
    )
    return PilotResult(
        route_id=selected_route.route_id,
        services=selected_route.signature.services,
        split_seed=seed,
        train_runs=split.train_runs,
        validation_runs=split.validation_runs,
        test_normal_runs=split.test_runs,
        anomaly_runs=tuple(sorted({item.run_id for item in all_anomalies})),
        strict_case_disjoint=strict_case_disjoint,
        stratified_split=stratify_fault_types,
        selected_observers=tuple(observer.name for observer in bundle.selected_observers),
        candidate_observers=tuple(observer.name for observer in bundle.library.candidates),
        rule_count=bundle.model.rule_count,
        unit_rule_count=sum(len(targets) for targets in bundle.model.unit_rules.values()),
        observed_type_count=bundle.model.observed_type_count,
        metrics=PilotMetrics(
            normal_total=len(normal_words),
            normal_accepted=normal_accepted,
            anomaly_total=anomaly_total,
            anomaly_rejected=anomaly_rejected,
            grammar_anomaly_total=len(anomaly_words),
            grammar_anomaly_rejected=grammar_rejected,
            route_mismatch_anomalies=mismatch_anomalies,
            precision=precision,
            recall=recall,
            f1=f1,
            normal_acceptance_ci_low=normal_ci[0],
            normal_acceptance_ci_high=normal_ci[1],
            anomaly_recall_ci_low=anomaly_ci[0],
            anomaly_recall_ci_high=anomaly_ci[1],
            unknown_event_rate=_unknown_rate(bundle, [*test_normal_traces, *same_route_anomaly_traces]),
            unseen_mutant_total=len(unseen_words),
            unseen_mutant_rejected=sum(not unseen_decisions[word] for word in unseen_words),
        ),
        fault_metrics=tuple(fault_rows),
        case_metrics=tuple(case_rows),
        selection_history=history,
    )


@dataclass(frozen=True)
class StabilityRow:
    observer: str
    selected_count: int
    seed_count: int
    selection_rate: float


@dataclass(frozen=True)
class StabilityResult:
    route_id: str
    seeds: tuple[int, ...]
    rows: tuple[StabilityRow, ...]
    successful_runs: int
    failed_runs: tuple[tuple[int, str], ...]


def observer_stability(
    examples: Sequence[LabeledTrace],
    seeds: Sequence[int],
    *,
    route_id: str | None = None,
    config: RouteExperimentConfig = RouteExperimentConfig(),
    stratify_fault_types: bool = False,
    strict_case_disjoint: bool = True,
) -> StabilityResult:
    counts: Counter[str] = Counter()
    failures: list[tuple[int, str]] = []
    results: list[PilotResult] = []
    for seed in seeds:
        try:
            result = run_route_pilot(
                examples,
                route_id=route_id,
                seed=seed,
                config=config,
                stratify_fault_types=stratify_fault_types,
                strict_case_disjoint=strict_case_disjoint,
            )
        except (ValueError, RuntimeError) as exc:
            failures.append((seed, str(exc)))
            continue
        results.append(result)
        counts.update(result.selected_observers)
    if not results:
        raise ValueError("all stability runs failed")
    route = results[0].route_id
    all_observers = sorted({name for result in results for name in result.candidate_observers})
    rows = tuple(
        StabilityRow(
            observer=name,
            selected_count=counts[name],
            seed_count=len(results),
            selection_rate=counts[name] / len(results),
        )
        for name in all_observers
    )
    return StabilityResult(
        route_id=route,
        seeds=tuple(seeds),
        rows=rows,
        successful_runs=len(results),
        failed_runs=tuple(failures),
    )
