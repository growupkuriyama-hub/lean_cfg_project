#!/usr/bin/env python3
"""Retrospective audit of the V11/V4 random run-disjoint evaluation."""
from __future__ import annotations

import argparse
import csv
import json
import math
import random
from collections import Counter
from pathlib import Path

DIAGNOSTIC_MUTATION = "currency-server-phase-inversion"


def split_runs(run_ids: list[str], seed: int) -> tuple[set[str], set[str], set[str]]:
    shuffled = list(run_ids)
    random.Random(seed).shuffle(shuffled)
    n = len(shuffled)
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


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("projections_csv", type=Path)
    parser.add_argument("--seeds", type=int, default=5)
    parser.add_argument("--anchor-counts", default="1,2")
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()

    with args.projections_csv.open(newline="", encoding="utf-8") as handle:
        rows = list(csv.DictReader(handle))
    anchor_counts = {int(value) for value in args.anchor_counts.split(",") if value}
    run_ids = sorted({row["run_id"] for row in rows if row["label"] == "normal"})
    split_reports = []
    for seed in range(args.seeds):
        train_runs, validation_runs, test_runs = split_runs(run_ids, seed)
        validation = [row for row in rows if row["run_id"] in validation_runs]
        test = [row for row in rows if row["run_id"] in test_runs]
        validation_normals = [row for row in validation if row["label"] == "normal"]
        unseen_counts = sorted({int(row["item_count"]) for row in validation_normals if int(row["item_count"]) not in anchor_counts})
        target_normal_count = unseen_counts[0] if unseen_counts else min(int(row["item_count"]) for row in validation_normals)
        selected_normal = [row for row in validation_normals if int(row["item_count"]) == target_normal_count][:1]
        diagnostic_count = max(anchor_counts)
        selected_fault = [
            row for row in validation
            if row["label"] == "anomaly"
            and row["mutation"] == DIAGNOSTIC_MUTATION
            and int(row["item_count"]) == diagnostic_count
        ][:1]
        selected_validation_words = {row["word"] for row in selected_normal + selected_fault}
        test_words = {row["word"] for row in test}
        split_reports.append({
            "seed": seed,
            "train_runs": sorted(train_runs),
            "validation_runs": sorted(validation_runs),
            "test_runs": sorted(test_runs),
            "selected_validation_normal_words": [row["word"] for row in selected_normal],
            "selected_validation_fault_words": [row["word"] for row in selected_fault],
            "validation_test_word_overlap": sorted(selected_validation_words & test_words),
            "has_projection_leakage": bool(selected_validation_words & test_words),
        })

    report = {
        "rows": len(rows),
        "normal_rows": sum(row["label"] == "normal" for row in rows),
        "anomaly_rows": sum(row["label"] == "anomaly" for row in rows),
        "unique_words_total": len({row["word"] for row in rows}),
        "unique_normal_words": len({row["word"] for row in rows if row["label"] == "normal"}),
        "unique_anomaly_words": len({row["word"] for row in rows if row["label"] == "anomaly"}),
        "normal_item_count_distribution": dict(sorted(Counter(int(row["item_count"]) for row in rows if row["label"] == "normal").items())),
        "test_run_frequency": dict(sorted(Counter(run for item in split_reports for run in item["test_runs"]).items())),
        "validation_run_frequency": dict(sorted(Counter(run for item in split_reports for run in item["validation_runs"]).items())),
        "splits_with_projection_leakage": sum(item["has_projection_leakage"] for item in split_reports),
        "split_reports": split_reports,
    }
    text = json.dumps(report, indent=2)
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(text, encoding="utf-8")
    print(text)


if __name__ == "__main__":
    main()
