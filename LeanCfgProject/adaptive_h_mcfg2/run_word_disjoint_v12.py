#!/usr/bin/env python3
"""Evaluate ADP MCFG v5 on count-held-out, projected-word-disjoint data."""
from __future__ import annotations

import argparse
import csv
import json
import os
import platform
import resource
import sys
import time
from collections import defaultdict
from pathlib import Path
from typing import Any, Callable, Iterable, Sequence

from adaptive_h_mcfg.baselines import (
    ExactTemplateModel,
    IsolationForestAnomalyModel,
    NGramAnomalyModel,
)
from adaptive_h_mcfg.binary_learner import BoundedCanonicalMCFGLearner
from adaptive_h_mcfg.observers import (
    ModularCountObserver,
    ProductObserver,
    TrivialObserver,
    block_envelope_observer,
)
from adaptive_h_mcfg.selection import greedy_select
from adaptive_h_mcfg.v12_baselines import CheckoutCountPhaseInvariantModel, KTailsAutomatonModel
from adaptive_h_mcfg.v12_protocol import (
    ProjectionRow,
    audit_word_disjoint_protocol,
    load_projection_rows,
    parse_int_spec,
    partition_rows_by_count,
)

DIAGNOSTIC_MUTATION = "currency-server-phase-inversion"
EXPECTED_MUTATIONS = (
    "currency-server-phase-inversion",
    "drop-product-server-occurrence",
    "duplicate-product-server-occurrence",
    "drop-product-currency-server-occurrence",
    "duplicate-product-currency-server-occurrence",
    "duplicate-shipping-currency-server-occurrence",
)


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


def unique_words(rows: Iterable[ProjectionRow]) -> tuple[str, ...]:
    return tuple(dict.fromkeys(row.word for row in rows))


def timed(call: Callable[[], Any]) -> tuple[Any, float]:
    started = time.perf_counter()
    result = call()
    return result, time.perf_counter() - started


def peak_rss_mib() -> float:
    raw = float(resource.getrusage(resource.RUSAGE_SELF).ru_maxrss)
    return raw / (1024.0 * 1024.0) if sys.platform == "darwin" else raw / 1024.0


def total_memory_mib() -> float | None:
    try:
        for line in Path("/proc/meminfo").read_text(encoding="utf-8").splitlines():
            if line.startswith("MemTotal:"):
                return int(line.split()[1]) / 1024.0
    except OSError:
        return None
    return None


def mcfg_decisions(
    model: Any,
    words: Sequence[str],
    max_values_per_nt: int,
    max_total_values: int,
) -> dict[str, bool]:
    if hasattr(model, "accepts_many_guided"):
        return dict(model.accepts_many_guided(
            tuple(words),
            max_values_per_nt=max_values_per_nt,
            max_total_values=max_total_values,
        ))
    if hasattr(model, "accepts_many"):
        return dict(model.accepts_many(tuple(words)))
    return {word: bool(model.accepts(word)) for word in words}


def model_metadata(name: str, model: Any) -> dict[str, Any]:
    unit_rules = getattr(model, "unit_rules", {})
    if isinstance(unit_rules, dict):
        unit_rule_count = sum(len(value) for value in unit_rules.values())
    else:
        unit_rule_count = ""
    return {
        "model": name,
        "rule_count": getattr(model, "rule_count", ""),
        "unit_rule_count": unit_rule_count,
        "observed_type_count": getattr(model, "observed_type_count", ""),
        "occurrence_count": getattr(model, "occurrence_count", ""),
        "state_count": getattr(model, "state_count", ""),
        "transition_count": getattr(model, "transition_count", ""),
        "threshold": getattr(model, "threshold", ""),
    }


def metric_groups(rows: Sequence[ProjectionRow]) -> list[tuple[str, list[ProjectionRow], bool]]:
    groups: list[tuple[str, list[ProjectionRow], bool]] = []
    normal = [row for row in rows if row.label == "normal"]
    anomaly = [row for row in rows if row.label == "anomaly"]
    groups.append(("normal-all", normal, True))
    groups.append(("fault-all", anomaly, False))
    for mutation in sorted({row.mutation for row in anomaly}):
        selected = [row for row in anomaly if row.mutation == mutation]
        groups.append((f"fault:{mutation}", selected, False))
    for count in sorted({row.item_count for row in rows}):
        selected_normal = [
            row for row in normal if row.item_count == count
        ]
        selected_fault = [
            row for row in anomaly if row.item_count == count
        ]
        groups.append((f"count:{count}:normal", selected_normal, True))
        groups.append((f"count:{count}:fault", selected_fault, False))
    return groups


def dedupe_evaluation_rows(rows: Sequence[ProjectionRow]) -> list[ProjectionRow]:
    # One representative per model-visible labeled projected word.  Including
    # the label/mutation prevents accidental collapse of semantically different
    # rows should a future mutation generator produce the same surface word.
    seen: set[tuple[str, str, int, str]] = set()
    output: list[ProjectionRow] = []
    for row in rows:
        key = (row.label, row.mutation, row.item_count, row.word)
        if key not in seen:
            seen.add(key)
            output.append(row)
    return output


def evaluate(
    name: str,
    decisions: dict[str, bool],
    rows: Sequence[ProjectionRow],
    evaluation_unit: str,
) -> list[dict[str, Any]]:
    output: list[dict[str, Any]] = []
    for group, selected, expected_accept in metric_groups(rows):
        if not selected:
            continue
        correct = sum(decisions[row.word] == expected_accept for row in selected)
        output.append(
            {
                "evaluation_unit": evaluation_unit,
                "model": name,
                "group": group,
                "correct": correct,
                "count": len(selected),
                "rate": correct / len(selected),
            }
        )
    return output


def write_csv(path: Path, rows: Sequence[dict[str, Any]], fieldnames: Sequence[str] | None = None) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    if fieldnames is None:
        fieldnames = list(rows[0]) if rows else []
    with path.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=list(fieldnames))
        if fieldnames:
            writer.writeheader()
            writer.writerows(rows)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("projections_csv", type=Path)
    parser.add_argument("--output", type=Path, default=Path("mcfg-v12-results"))
    parser.add_argument("--train-counts", default="1,2")
    parser.add_argument("--validation-counts", default="3")
    parser.add_argument("--test-counts", default="4-10")
    parser.add_argument("--minimum-replicas", type=int, default=5)
    parser.add_argument("--selection-budget", type=int, default=2)
    parser.add_argument("--epsilon", type=float, default=1e-9)
    parser.add_argument("--complexity-weight", type=float, default=1e-8)
    parser.add_argument("--type-weight", type=float, default=1e-6)
    parser.add_argument("--max-values-per-nt", type=int, default=25000)
    parser.add_argument("--max-total-values", type=int, default=2000000)
    args = parser.parse_args()

    args.output.mkdir(parents=True, exist_ok=True)
    train_counts = parse_int_spec(args.train_counts)
    validation_counts = parse_int_spec(args.validation_counts)
    test_counts = parse_int_spec(args.test_counts)
    rows = load_projection_rows(args.projections_csv)
    audit = audit_word_disjoint_protocol(
        rows,
        train_counts=train_counts,
        validation_counts=validation_counts,
        test_counts=test_counts,
        diagnostic_mutation=DIAGNOSTIC_MUTATION,
        expected_mutations=EXPECTED_MUTATIONS,
        minimum_replicas_per_count=args.minimum_replicas,
    )
    (args.output / "protocol_audit.json").write_text(
        json.dumps(audit, indent=2), encoding="utf-8"
    )
    if not audit["ready_for_word_disjoint_evaluation"]:
        raise SystemExit("refusing to evaluate: projected-word-disjoint audit failed")

    parts = partition_rows_by_count(rows, train_counts, validation_counts, test_counts)
    training_words = unique_words(row for row in parts["train"] if row.label == "normal")
    validation_normal = unique_words(
        row for row in parts["validation"] if row.label == "normal"
    )
    validation_fault = unique_words(
        row
        for row in parts["validation"]
        if row.label == "anomaly" and row.mutation == DIAGNOSTIC_MUTATION
    )
    test_rows = parts["test"]
    test_unique_rows = dedupe_evaluation_rows(test_rows)
    test_words = unique_words(test_rows)

    learner = BoundedCanonicalMCFGLearner(fanout=3)
    basis, basis_seconds = timed(lambda: learner.prepare(training_words))
    candidates = candidate_observers()
    selection, selection_seconds = timed(
        lambda: greedy_select(
            learner,
            training_words,
            validation_normal,
            validation_fault,
            candidates,
            budget=args.selection_budget,
            min_improvement=args.epsilon,
            complexity_weight=args.complexity_weight,
            type_weight=args.type_weight,
            guided=False,
        )
    )

    models: dict[str, Any] = {"adaptive-f3-mcfg": selection.model}
    fit_seconds: dict[str, float] = {"adaptive-f3-mcfg": selection_seconds}
    models["trivial-f3-mcfg"], fit_seconds["trivial-f3-mcfg"] = timed(
        lambda: learner.fit_prepared(basis, TrivialObserver())
    )
    models["full-product-f3-mcfg"], fit_seconds["full-product-f3-mcfg"] = timed(
        lambda: learner.fit_prepared(basis, ProductObserver(candidates))
    )
    models["exact-template"], fit_seconds["exact-template"] = timed(
        lambda: ExactTemplateModel.fit(training_words)
    )

    for order in (2, 3):
        name = f"{order}-gram"
        model, fit_time = timed(lambda order=order: NGramAnomalyModel(order).fit(training_words))
        _, threshold_time = timed(
            lambda model=model: model.select_threshold(validation_normal, validation_fault)
        )
        models[name] = model
        fit_seconds[name] = fit_time + threshold_time

    for k in (2, 3):
        name = f"k-tails-{k}"
        models[name], fit_seconds[name] = timed(
            lambda k=k: KTailsAutomatonModel.fit(training_words, k=k)
        )
    models["direct-count-phase-invariant"], fit_seconds[
        "direct-count-phase-invariant"
    ] = timed(lambda: CheckoutCountPhaseInvariantModel.fit(training_words))
    isolation, isolation_fit = timed(
        lambda: IsolationForestAnomalyModel(random_state=0).fit(training_words)
    )
    _, isolation_threshold = timed(
        lambda: isolation.select_threshold(validation_normal, validation_fault)
    )
    models["isolation-forest-trace-features"] = isolation
    fit_seconds["isolation-forest-trace-features"] = isolation_fit + isolation_threshold

    instance_metrics: list[dict[str, Any]] = []
    unique_metrics: list[dict[str, Any]] = []
    complexity_rows: list[dict[str, Any]] = []
    decision_rows: list[dict[str, Any]] = []
    recognition_scaling_rows: list[dict[str, Any]] = []

    for name, model in models.items():
        decisions: dict[str, bool] = {}
        recognition_seconds = 0.0
        for count in sorted({row.item_count for row in test_rows}):
            count_words = unique_words(row for row in test_rows if row.item_count == count)
            count_decisions, count_seconds = timed(
                lambda model=model, count_words=count_words: mcfg_decisions(
                    model, count_words, args.max_values_per_nt, args.max_total_values
                )
            )
            decisions.update(count_decisions)
            recognition_seconds += count_seconds
            recognition_scaling_rows.append({
                "model": name,
                "item_count": count,
                "max_word_length": max(map(len, count_words), default=0),
                "unique_word_count": len(count_words),
                "recognition_seconds": count_seconds,
                "seconds_per_unique_word": count_seconds / max(1, len(count_words)),
            })
        instance_metrics.extend(evaluate(name, decisions, test_rows, "trace-instance"))
        unique_metrics.extend(evaluate(name, decisions, test_unique_rows, "unique-projection"))
        meta = model_metadata(name, model)
        meta.update(
            {
                "basis_construction_seconds": basis_seconds if "mcfg" in name else "",
                "fit_or_selection_seconds": fit_seconds[name],
                "recognition_seconds": recognition_seconds,
                "recognition_seconds_per_unique_word": recognition_seconds / max(1, len(test_words)),
                "peak_rss_mib_after_model": peak_rss_mib(),
            }
        )
        complexity_rows.append(meta)
        for row in test_unique_rows:
            expected = row.label == "normal"
            accepted = decisions[row.word]
            decision_rows.append(
                {
                    "model": name,
                    "item_count": row.item_count,
                    "label": row.label,
                    "mutation": row.mutation,
                    "word": row.word,
                    "accepted": accepted,
                    "expected_accept": expected,
                    "correct": accepted == expected,
                }
            )

    write_csv(args.output / "metrics_trace_instance.csv", instance_metrics)
    write_csv(args.output / "metrics_unique_projection.csv", unique_metrics)
    write_csv(args.output / "model_complexity_and_runtime.csv", complexity_rows)
    write_csv(args.output / "decisions_by_unique_word.csv", decision_rows)
    write_csv(args.output / "recognition_scaling_by_count.csv", recognition_scaling_rows)

    environment = {
        "platform": platform.platform(),
        "python": sys.version,
        "cpu_count": os.cpu_count(),
        "total_memory_mib": total_memory_mib(),
    }
    (args.output / "environment.json").write_text(
        json.dumps(environment, indent=2), encoding="utf-8"
    )

    summary = {
        "protocol": "ADP-MCFG-v5 / internal V12 projected-word-disjoint evaluation",
        "train_counts": list(train_counts),
        "validation_counts": list(validation_counts),
        "test_counts": list(test_counts),
        "training_words": list(training_words),
        "validation_normal_words": list(validation_normal),
        "validation_fault_words": list(validation_fault),
        "test_trace_instance_rows": len(test_rows),
        "test_unique_labeled_projection_rows": len(test_unique_rows),
        "test_unique_surface_words": len(test_words),
        "selected_observers": [observer.name for observer in selection.selected_observers],
        "selection_history": [entry.__dict__ for entry in selection.history],
        "environment": environment,
        "recognition_resource_caps": {
            "max_values_per_nonterminal": args.max_values_per_nt,
            "max_total_values": args.max_total_values,
        },
        "selection_parameters": {
            "budget": args.selection_budget,
            "epsilon": args.epsilon,
            "complexity_weight": args.complexity_weight,
            "type_weight": args.type_weight,
            "tie_breaking": "candidate library order, because greedy_select replaces only on strict objective improvement",
        },
        "basis_construction_seconds": basis_seconds,
        "peak_rss_mib_final": peak_rss_mib(),
        "protocol_audit": audit,
        "instance_metrics": instance_metrics,
        "unique_projection_metrics": unique_metrics,
        "model_complexity_and_runtime": complexity_rows,
        "recognition_scaling_by_count": recognition_scaling_rows,
    }
    (args.output / "summary.json").write_text(
        json.dumps(summary, indent=2), encoding="utf-8"
    )
    print(
        json.dumps(
            {
                "ready": True,
                "selected_observers": summary["selected_observers"],
                "test_unique_surface_words": len(test_words),
                "outputs": str(args.output),
            },
            indent=2,
        )
    )


if __name__ == "__main__":
    main()
