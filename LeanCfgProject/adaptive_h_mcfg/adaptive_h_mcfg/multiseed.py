from __future__ import annotations

import math
from collections import Counter, defaultdict
from dataclasses import dataclass
from typing import Mapping, Sequence

from .baselines import ExactTemplateModel, IsolationForestAnomalyModel, NGramAnomalyModel
from .empirical import choose_pilot_route, route_coverage
from .mutations import encoded_unseen_mutants
from .pipeline import RouteExperimentConfig, fit_route_model
from .routes import (
    LabeledTrace,
    deterministic_run_split,
    deterministic_stratified_run_split,
    route_signature,
)


@dataclass(frozen=True)
class SeedModelMetrics:
    seed: int
    model: str
    selected_observers: str
    normal_accepted: int
    normal_total: int
    anomaly_rejected: int
    anomaly_total: int
    same_route_rejected: int
    same_route_total: int
    route_mismatch_rejected: int
    unseen_rejected: int
    unseen_total: int
    precision: float
    recall: float
    f1: float


@dataclass(frozen=True)
class SeedFaultMetrics:
    seed: int
    model: str
    fault_type: str
    rejected: int
    total: int
    recall: float
    route_mismatch_rejected: int


@dataclass(frozen=True)
class SeedCaseMetrics:
    seed: int
    model: str
    run_id: str
    fault_type: str
    normal_accepted: int
    normal_total: int
    anomaly_rejected: int
    anomaly_total: int
    route_mismatch_rejected: int

    @property
    def normal_acceptance(self) -> float:
        return self.normal_accepted / max(1, self.normal_total)

    @property
    def anomaly_recall(self) -> float:
        return self.anomaly_rejected / max(1, self.anomaly_total)

    @property
    def balanced_accuracy(self) -> float:
        return (self.normal_acceptance + self.anomaly_recall) / 2.0


@dataclass(frozen=True)
class SeedBenchmark:
    seed: int
    route_id: str
    train_runs: tuple[str, ...]
    validation_runs: tuple[str, ...]
    test_runs: tuple[str, ...]
    selected_observers: tuple[str, ...]
    model_metrics: tuple[SeedModelMetrics, ...]
    fault_metrics: tuple[SeedFaultMetrics, ...]
    case_metrics: tuple[SeedCaseMetrics, ...]


def _precision_recall_f1(
    normal_accepted: int,
    normal_total: int,
    anomaly_rejected: int,
    anomaly_total: int,
) -> tuple[float, float, float]:
    false_positive = normal_total - normal_accepted
    precision = anomaly_rejected / max(1, anomaly_rejected + false_positive)
    recall = anomaly_rejected / max(1, anomaly_total)
    f1 = 2.0 * precision * recall / max(1e-15, precision + recall)
    return precision, recall, f1


def evaluate_seed(
    examples: Sequence[LabeledTrace],
    *,
    seed: int,
    config: RouteExperimentConfig,
    route_id: str | None = None,
    stratify_fault_types: bool = True,
    include_isolation_forest: bool = True,
) -> SeedBenchmark:
    route = choose_pilot_route(route_coverage(examples), route_id=route_id)
    route_normal = [
        item
        for item in examples
        if item.label == "normal" and route_signature(item.trace) == route.signature
    ]
    split = (
        deterministic_stratified_run_split(route_normal, seed=seed)
        if stratify_fault_types
        else deterministic_run_split(route_normal, seed=seed)
    )
    train, validation, test_normal = split.partition(route_normal)
    if not train or not validation or not test_normal:
        raise ValueError("run split produced an empty partition")
    test_runs = set(split.test_runs)
    test_anomalies = [
        item for item in examples if item.label == "anomaly" and item.run_id in test_runs
    ]
    same_route_anomalies = [
        item for item in test_anomalies if route_signature(item.trace) == route.signature
    ]
    mismatch_items = [
        item for item in test_anomalies if route_signature(item.trace) != route.signature
    ]

    bundle = fit_route_model(
        [item.trace for item in train],
        [item.trace for item in validation],
        config,
    )
    normal_words = [bundle.encoder.encode(item.trace) for item in test_normal]
    anomaly_words = [bundle.encoder.encode(item.trace) for item in same_route_anomalies]
    unseen_words = list(encoded_unseen_mutants(normal_words, bundle.encoder.separator))
    all_words = [*normal_words, *anomaly_words, *unseen_words]

    decisions_by_model: dict[str, Mapping[str, bool]] = {}
    decisions_by_model["route-only"] = {word: True for word in dict.fromkeys(all_words)}
    exact = ExactTemplateModel.fit(bundle.train_words)
    decisions_by_model["exact-template"] = exact.accepts_many(all_words)
    for order in (2, 3):
        model = NGramAnomalyModel(order=order).fit(bundle.train_words)
        model.select_threshold(bundle.validation_words, bundle.validation_mutants)
        decisions_by_model[f"{order}-gram"] = model.accepts_many(all_words)
    if include_isolation_forest:
        isolation = IsolationForestAnomalyModel(
            separator=bundle.encoder.separator,
            random_state=seed,
        ).fit(bundle.train_words)
        isolation.select_threshold(bundle.validation_words, bundle.validation_mutants)
        decisions_by_model["isolation-forest"] = isolation.accepts_many(all_words)
    decisions_by_model["adaptive-fanout2-mcfg"] = bundle.model.accepts_many_guided(all_words)

    model_rows: list[SeedModelMetrics] = []
    fault_rows: list[SeedFaultMetrics] = []
    case_rows: list[SeedCaseMetrics] = []
    mismatch_count = len(mismatch_items)
    selected = " x ".join(observer.name for observer in bundle.selected_observers)

    for model_name, decisions in decisions_by_model.items():
        normal_accepted = sum(decisions[word] for word in normal_words)
        same_route_rejected = sum(not decisions[word] for word in anomaly_words)
        anomaly_rejected = same_route_rejected + mismatch_count
        unseen_rejected = sum(not decisions[word] for word in unseen_words)
        precision, recall, f1 = _precision_recall_f1(
            normal_accepted,
            len(normal_words),
            anomaly_rejected,
            len(test_anomalies),
        )
        model_rows.append(
            SeedModelMetrics(
                seed=seed,
                model=model_name,
                selected_observers=selected if model_name == "adaptive-fanout2-mcfg" else "",
                normal_accepted=normal_accepted,
                normal_total=len(normal_words),
                anomaly_rejected=anomaly_rejected,
                anomaly_total=len(test_anomalies),
                same_route_rejected=same_route_rejected,
                same_route_total=len(anomaly_words),
                route_mismatch_rejected=mismatch_count,
                unseen_rejected=unseen_rejected,
                unseen_total=len(unseen_words),
                precision=precision,
                recall=recall,
                f1=f1,
            )
        )

        for fault_type in sorted({item.fault_type or "unknown" for item in test_anomalies}):
            items = [
                item
                for item in test_anomalies
                if (item.fault_type or "unknown") == fault_type
            ]
            mismatch = [item for item in items if route_signature(item.trace) != route.signature]
            grammar = [item for item in items if route_signature(item.trace) == route.signature]
            rejected = len(mismatch) + sum(
                not decisions[bundle.encoder.encode(item.trace)] for item in grammar
            )
            fault_rows.append(
                SeedFaultMetrics(
                    seed=seed,
                    model=model_name,
                    fault_type=fault_type,
                    rejected=rejected,
                    total=len(items),
                    recall=rejected / max(1, len(items)),
                    route_mismatch_rejected=len(mismatch),
                )
            )

        for run_id in split.test_runs:
            normals = [item for item in test_normal if item.run_id == run_id]
            anomalies = [item for item in test_anomalies if item.run_id == run_id]
            normal_hits = sum(decisions[bundle.encoder.encode(item.trace)] for item in normals)
            anomaly_hits = 0
            mismatch_hits = 0
            for item in anomalies:
                if route_signature(item.trace) != route.signature:
                    anomaly_hits += 1
                    mismatch_hits += 1
                else:
                    anomaly_hits += int(not decisions[bundle.encoder.encode(item.trace)])
            labels = {item.fault_type or "unknown" for item in [*normals, *anomalies]}
            case_rows.append(
                SeedCaseMetrics(
                    seed=seed,
                    model=model_name,
                    run_id=run_id,
                    fault_type=next(iter(labels)) if len(labels) == 1 else "mixed",
                    normal_accepted=normal_hits,
                    normal_total=len(normals),
                    anomaly_rejected=anomaly_hits,
                    anomaly_total=len(anomalies),
                    route_mismatch_rejected=mismatch_hits,
                )
            )

    return SeedBenchmark(
        seed=seed,
        route_id=route.route_id,
        train_runs=split.train_runs,
        validation_runs=split.validation_runs,
        test_runs=split.test_runs,
        selected_observers=tuple(observer.name for observer in bundle.selected_observers),
        model_metrics=tuple(model_rows),
        fault_metrics=tuple(fault_rows),
        case_metrics=tuple(case_rows),
    )


@dataclass(frozen=True)
class AggregateMetric:
    model: str
    metric: str
    seed_count: int
    mean: float
    sample_std: float
    minimum: float
    maximum: float


def aggregate_seed_metrics(results: Sequence[SeedBenchmark]) -> tuple[AggregateMetric, ...]:
    grouped: dict[tuple[str, str], list[float]] = defaultdict(list)
    for result in results:
        for row in result.model_metrics:
            values = {
                "normal_acceptance": row.normal_accepted / max(1, row.normal_total),
                "anomaly_recall": row.anomaly_rejected / max(1, row.anomaly_total),
                "same_route_recall": row.same_route_rejected / max(1, row.same_route_total),
                "unseen_recall": row.unseen_rejected / max(1, row.unseen_total),
                "precision": row.precision,
                "f1": row.f1,
            }
            for metric, value in values.items():
                grouped[(row.model, metric)].append(value)
    output: list[AggregateMetric] = []
    for (model, metric), values in sorted(grouped.items()):
        mean = sum(values) / len(values)
        std = (
            math.sqrt(sum((value - mean) ** 2 for value in values) / (len(values) - 1))
            if len(values) > 1
            else 0.0
        )
        output.append(
            AggregateMetric(model, metric, len(values), mean, std, min(values), max(values))
        )
    return tuple(output)


@dataclass(frozen=True)
class ObserverStabilityMetric:
    observer: str
    selected_count: int
    seed_count: int
    selection_rate: float


def observer_stability_metrics(
    results: Sequence[SeedBenchmark],
) -> tuple[ObserverStabilityMetric, ...]:
    counts: Counter[str] = Counter()
    for result in results:
        counts.update(result.selected_observers)
    observers = sorted(counts)
    return tuple(
        ObserverStabilityMetric(name, counts[name], len(results), counts[name] / max(1, len(results)))
        for name in observers
    )
