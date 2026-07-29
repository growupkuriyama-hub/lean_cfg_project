#!/usr/bin/env python3
from __future__ import annotations

import argparse
import csv
import json
from collections import Counter, defaultdict
from pathlib import Path


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("projections_csv", type=Path)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    run_counts: dict[str, Counter[int]] = defaultdict(Counter)
    mutations: Counter[str] = Counter()
    normal = 0
    anomaly = 0
    with args.projections_csv.open(newline="", encoding="utf-8") as handle:
        for row in csv.DictReader(handle):
            if row["label"] == "normal":
                normal += 1
                run_counts[row["run_id"]][int(row["item_count"])] += 1
            else:
                anomaly += 1
                mutations[row["mutation"]] += 1
    run_ids = sorted(run_counts)
    runs_with_1_2 = [run for run in run_ids if run_counts[run][1] and run_counts[run][2]]
    report = {
        "valid_csv": bool(run_ids and normal),
        "run_count": len(run_ids),
        "normal_rows": normal,
        "anomaly_rows": anomaly,
        "runs_with_item_counts_1_and_2": runs_with_1_2,
        "run_item_count_coverage": {
            run: dict(sorted(counts.items())) for run, counts in sorted(run_counts.items())
        },
        "mutation_counts": dict(sorted(mutations.items())),
        "ready_for_default_5_seed_pilot": (
            len(run_ids) >= 5
            and len(runs_with_1_2) >= 3
            and mutations["currency-server-phase-inversion"] > 0
        ),
    }
    text = json.dumps(report, indent=2)
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(text, encoding="utf-8")
    print(text)


if __name__ == "__main__":
    main()
