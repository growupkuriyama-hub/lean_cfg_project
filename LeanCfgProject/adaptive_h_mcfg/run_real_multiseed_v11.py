#!/usr/bin/env python3
"""Run strict run-disjoint V11 evaluation on projected OpenTelemetry traces."""
from __future__ import annotations

import argparse
import csv
import json
import math
import random
from collections import Counter, defaultdict
from dataclasses import dataclass
from pathlib import Path
from statistics import mean, pstdev

from adaptive_h_mcfg.baselines import ExactTemplateModel, NGramAnomalyModel
from adaptive_h_mcfg.binary_learner import BoundedCanonicalMCFGLearner
from adaptive_h_mcfg.observers import (
    ModularCountObserver,
    ProductObserver,
    TrivialObserver,
    block_envelope_observer,
)
from adaptive_h_mcfg.selection import greedy_select


DIAGNOSTIC_MUTATION = "currency-server-phase-inversion"


@dataclass(frozen=True)
class Row:
    run_id: str
    label: str
    item_count: int
    word: str
    mutation: str


def load_rows(path: Path) -> list[Row]:
    rows: list[Row] = []
    with path.open(newline="", encoding="utf-8") as handle:
        for raw in csv.DictReader(handle):
            rows.append(Row(
                run_id=raw["run_id"],
                label=raw["label"],
                item_count=int(raw["item_count"]),
                word=raw["word"],
                mutation=raw["mutation"],
            ))
    return rows


def split_runs(run_ids: list[str], seed: int) -> tuple[set[str], set[str], set[str]]:
    shuffled = list(run_ids)
    random.Random(seed).shuffle(shuffled)
    n = len(shuffled)
    if n < 5:
        raise ValueError("at least five runs are required for 3/1/1-style splitting")
    n_train = max(3, math.floor(0.6 * n))
    n_validation = max(1, math.floor(0.2 * n))
    if n_train + n_validation >= n:
        n_train = n - 2
        n_validation = 1
    return (
        set(shuffled[:n_train]),
        set(shuffled[n_train:n_train + n_validation]),
        set(shuffled[n_train + n_validation:]),
    )


def unique_words(rows: list[Row]) -> tuple[str, ...]:
    return tuple(dict.fromkeys(row.word for row in rows))


def candidate_observers():
    return (
        block_envelope_observer(
            (("p",), ("c", "s"), ("p", "c", "s")),
            name="checkout-phase-envelope",
        ),
        ModularCountObserver(("s",), 2, "shipping-phase-count-mod-2"),
        ModularCountObserver(("p",), 2, "product-count-mod-2"),
        ModularCountObserver(("c",), 2, "currency-product-count-mod-2"),
        ModularCountObserver(("#",), 2, "separator-parity-decoy"),
    )


def choose_anchor_words(rows: list[Row], anchor_counts: tuple[int, ...]) -> tuple[str, ...] | None:
    by_count: dict[int, list[str]] = defaultdict(list)
    for row in rows:
        if row.label == "normal":
            by_count[row.item_count].append(row.word)
    selected: list[str] = []
    for count in anchor_counts:
        candidates = list(dict.fromkeys(by_count.get(count, ())))
        if not candidates:
            return None
        selected.append(candidates[0])
    return tuple(dict.fromkeys(selected))


_MCFG_DECISION_CACHE: dict[tuple[object, ...], bool] = {}

def decide_mcfg(model, words: tuple[str, ...]) -> dict[str, bool]:
    """Recognize each distinct word once across split seeds."""
    output: dict[str, bool] = {}
    missing: list[str] = []
    base_key = (model.observer_name, model.training_words, model.rule_count)
    for word in dict.fromkeys(words):
        key = (*base_key, word)
        if key in _MCFG_DECISION_CACHE:
            output[word] = _MCFG_DECISION_CACHE[key]
        else:
            missing.append(word)
    if missing:
        computed = model.accepts_many_guided(missing)
        for word, value in computed.items():
            _MCFG_DECISION_CACHE[(*base_key, word)] = value
            output[word] = value
    return output


def evaluate_rows(name: str, decisions: dict[str, bool], rows: list[Row], train_counts: set[int]) -> list[dict[str, object]]:
    output: list[dict[str, object]] = []
    normal = [row for row in rows if row.label == "normal"]
    normal_seen = [row for row in normal if row.item_count in train_counts]
    normal_unseen = [row for row in normal if row.item_count not in train_counts]
    groups = [
        ("normal-all", normal, True),
        ("normal-seen-size", normal_seen, True),
        ("normal-unseen-size", normal_unseen, True),
    ]
    mutations = sorted({row.mutation for row in rows if row.label == "anomaly"})
    for mutation in mutations:
        fault_rows = [row for row in rows if row.label == "anomaly" and row.mutation == mutation]
        seen = [row for row in fault_rows if row.item_count in train_counts]
        unseen = [row for row in fault_rows if row.item_count not in train_counts]
        groups.extend([
            (f"fault:{mutation}:all", fault_rows, False),
            (f"fault:{mutation}:seen-size", seen, False),
            (f"fault:{mutation}:unseen-size", unseen, False),
        ])
    for group, selected, expected_accept in groups:
        if not selected:
            continue
        correct = sum(decisions[row.word] == expected_accept for row in selected)
        output.append({
            "model": name,
            "group": group,
            "correct": correct,
            "count": len(selected),
            "rate": correct / len(selected),
        })
    return output


def run_seed(rows: list[Row], seed: int, anchor_counts: tuple[int, ...]) -> dict[str, object] | None:
    run_ids = sorted({row.run_id for row in rows if row.label == "normal"})
    train_runs, validation_runs, test_runs = split_runs(run_ids, seed)
    train_rows = [row for row in rows if row.run_id in train_runs and row.label == "normal"]
    validation_rows = [row for row in rows if row.run_id in validation_runs]
    test_rows = [row for row in rows if row.run_id in test_runs]

    train = choose_anchor_words(train_rows, anchor_counts)
    if train is None:
        return None
    train_counts = set(anchor_counts)

    all_validation_normal = [row for row in validation_rows if row.label == "normal"]
    # Model selection should test extrapolation without forcing the closure to
    # the longest available cart size.  Use the smallest unseen size (normally
    # n=3) and one diagnostic seen-size phase mutant.
    unseen_counts = sorted({row.item_count for row in all_validation_normal if row.item_count not in train_counts})
    target_normal_count = unseen_counts[0] if unseen_counts else min(row.item_count for row in all_validation_normal)
    validation_normal_rows = [
        row for row in all_validation_normal if row.item_count == target_normal_count
    ][:1]
    diagnostic_count = max(train_counts)
    validation_fault_rows = [
        row for row in validation_rows
        if row.label == "anomaly"
        and row.mutation == DIAGNOSTIC_MUTATION
        and row.item_count == diagnostic_count
    ][:1]
    if not validation_normal_rows or not validation_fault_rows:
        return None
    validation_normal = unique_words(validation_normal_rows)
    validation_fault = unique_words(validation_fault_rows)

    learner = BoundedCanonicalMCFGLearner(fanout=3)
    basis = learner.prepare(train)
    candidates = candidate_observers()
    selection = greedy_select(
        learner,
        train,
        validation_normal,
        validation_fault,
        candidates,
        budget=2,
        complexity_weight=1e-8,
        type_weight=1e-6,
        guided=False,
    )
    models = {
        "adaptive-f3-mcfg": selection.model,
        "trivial-f3-mcfg": learner.fit_prepared(basis, TrivialObserver()),
        "full-product-f3-mcfg": learner.fit_prepared(basis, ProductObserver(candidates)),
    }

    test_words = unique_words(test_rows)
    metrics: list[dict[str, object]] = []
    model_meta: list[dict[str, object]] = []
    for name, model in models.items():
        decisions = decide_mcfg(model, test_words)
        metrics.extend(evaluate_rows(name, decisions, test_rows, train_counts))
        model_meta.append({
            "model": name,
            "rule_count": model.rule_count,
            "unit_rule_count": sum(len(v) for v in model.unit_rules.values()),
            "observed_type_count": model.observed_type_count,
        })

    exact = ExactTemplateModel.fit(train)
    ng2 = NGramAnomalyModel(2).fit(train)
    ng2.select_threshold(validation_normal, validation_fault)
    ng3 = NGramAnomalyModel(3).fit(train)
    ng3.select_threshold(validation_normal, validation_fault)
    for name, model in (("exact-template", exact), ("2-gram", ng2), ("3-gram", ng3)):
        decisions = {word: model.accepts(word) for word in test_words}
        metrics.extend(evaluate_rows(name, decisions, test_rows, train_counts))

    return {
        "seed": seed,
        "train_runs": sorted(train_runs),
        "validation_runs": sorted(validation_runs),
        "test_runs": sorted(test_runs),
        "training_words": list(train),
        "selected_observers": [observer.name for observer in selection.selected_observers],
        "selection_history": [entry.__dict__ for entry in selection.history],
        "metrics": metrics,
        "model_meta": model_meta,
        "test_trace_count": len(test_rows),
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("projections_csv", type=Path)
    parser.add_argument("--output", type=Path, default=Path("mcfg-v11-real-result"))
    parser.add_argument("--seeds", type=int, default=5)
    parser.add_argument("--anchor-counts", default="1,2")
    args = parser.parse_args()
    args.output.mkdir(parents=True, exist_ok=True)
    anchor_counts = tuple(int(value) for value in args.anchor_counts.split(",") if value)
    rows = load_rows(args.projections_csv)

    seed_results: list[dict[str, object]] = []
    for seed in range(args.seeds):
        result = run_seed(rows, seed, anchor_counts)
        if result is not None:
            seed_results.append(result)
    if not seed_results:
        raise SystemExit(
            "no valid split: need >=5 runs, training normals at all anchor counts, "
            "and a validation phase mutant at a seen item count"
        )

    metric_rows: list[dict[str, object]] = []
    meta_rows: list[dict[str, object]] = []
    for result in seed_results:
        for row in result["metrics"]:
            metric_rows.append({"seed": result["seed"], **row})
        for row in result["model_meta"]:
            meta_rows.append({"seed": result["seed"], **row})

    with (args.output / "seed_metrics.csv").open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=list(metric_rows[0]))
        writer.writeheader()
        writer.writerows(metric_rows)
    with (args.output / "model_complexity.csv").open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=list(meta_rows[0]))
        writer.writeheader()
        writer.writerows(meta_rows)

    grouped: dict[tuple[str, str], list[float]] = defaultdict(list)
    for row in metric_rows:
        grouped[(str(row["model"]), str(row["group"]))].append(float(row["rate"]))
    aggregate = [
        {
            "model": model,
            "group": group,
            "seed_count": len(values),
            "mean_rate": mean(values),
            "sd_rate": pstdev(values),
            "min_rate": min(values),
            "max_rate": max(values),
        }
        for (model, group), values in sorted(grouped.items())
    ]
    with (args.output / "aggregate_metrics.csv").open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=list(aggregate[0]))
        writer.writeheader()
        writer.writerows(aggregate)

    summary = {
        "strict_run_disjoint": True,
        "anchor_counts": anchor_counts,
        "requested_seeds": args.seeds,
        "completed_seeds": len(seed_results),
        "run_ids": sorted({row.run_id for row in rows if row.label == "normal"}),
        "normal_item_count_distribution": dict(sorted(Counter(
            row.item_count for row in rows if row.label == "normal"
        ).items())),
        "mutation_distribution": dict(sorted(Counter(
            row.mutation for row in rows if row.label == "anomaly"
        ).items())),
        "selected_observers_by_seed": {
            str(result["seed"]): result["selected_observers"] for result in seed_results
        },
        "seed_results": seed_results,
        "aggregate": aggregate,
    }
    (args.output / "summary.json").write_text(json.dumps(summary, indent=2), encoding="utf-8")
    print(json.dumps({
        "completed_seeds": len(seed_results),
        "selected_observers_by_seed": summary["selected_observers_by_seed"],
        "outputs": str(args.output),
    }, indent=2))


if __name__ == "__main__":
    main()
