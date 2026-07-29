#!/usr/bin/env python3
"""Build, validate, and evaluate an already collected V12 run directory."""
from __future__ import annotations

import argparse
import subprocess
import sys
from pathlib import Path


def invoke(command: list[str], cwd: Path) -> None:
    print("+", " ".join(command), flush=True)
    subprocess.run(command, cwd=cwd, check=True)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("normal_runs", type=Path)
    parser.add_argument("--output", type=Path, default=Path("mcfg-v12-experiment"))
    parser.add_argument("--train-counts", default="1,2")
    parser.add_argument("--validation-counts", default="3")
    parser.add_argument("--test-counts", default="4-10")
    parser.add_argument("--minimum-replicas", type=int, default=5)
    args = parser.parse_args()

    root = Path(__file__).resolve().parent
    dataset = args.output.resolve() / "dataset"
    results = args.output.resolve() / "results"
    common = [
        "--train-counts", args.train_counts,
        "--validation-counts", args.validation_counts,
        "--test-counts", args.test_counts,
    ]
    invoke(
        [sys.executable, "otel_demo/build_v12_dataset.py", str(args.normal_runs.resolve()), "--output", str(dataset), *common],
        root,
    )
    invoke(
        [sys.executable, "validate_v12_dataset.py", str(dataset / "projections.csv"), "--output", str(dataset / "validation_report.json"), *common, "--minimum-replicas", str(args.minimum_replicas)],
        root,
    )
    invoke(
        [sys.executable, "run_word_disjoint_v12.py", str(dataset / "projections.csv"), "--output", str(results), *common, "--minimum-replicas", str(args.minimum_replicas)],
        root,
    )
    invoke(
        [sys.executable, "run_scaling_v12.py", str(dataset / "projections.csv"), "--output", str(results / "training_scaling.csv"), "--max-training-count", "4", "--memory-gib", "12", "--timeout-seconds", "600"],
        root,
    )


if __name__ == "__main__":
    main()
