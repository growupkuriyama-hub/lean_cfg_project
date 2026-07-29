#!/usr/bin/env python3
"""One-command collection, mutation construction, validation, and evaluation."""
from __future__ import annotations

import argparse
import subprocess
import sys
from pathlib import Path


def call(command: list[str], cwd: Path) -> None:
    print("+", " ".join(command), flush=True)
    subprocess.run(command, cwd=cwd, check=True)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("demo_root", type=Path)
    parser.add_argument("--output", type=Path, default=Path("mcfg-v11-experiment"))
    parser.add_argument("--runs", type=int, default=5)
    parser.add_argument("--warmup-seconds", type=int, default=45)
    parser.add_argument("--collect-seconds", type=int, default=90)
    parser.add_argument("--seeds", type=int, default=5)
    parser.add_argument("--minimal", action="store_true")
    parser.add_argument("--skip-collection", action="store_true")
    args = parser.parse_args()

    root = Path(__file__).resolve().parent
    output = args.output.resolve()
    normal_runs = output / "normal-runs"
    dataset = output / "dataset"
    results = output / "results"
    output.mkdir(parents=True, exist_ok=True)

    if not args.skip_collection:
        command = [
            sys.executable, str(root / "otel_demo" / "run_normal_v11.py"),
            str(args.demo_root), "--output", str(normal_runs),
            "--runs", str(args.runs),
            "--warmup-seconds", str(args.warmup_seconds),
            "--collect-seconds", str(args.collect_seconds),
        ]
        if args.minimal:
            command.append("--minimal")
        call(command, root)
    if not normal_runs.exists():
        raise SystemExit(f"normal run directory not found: {normal_runs}")

    call([
        sys.executable, str(root / "otel_demo" / "build_v11_dataset.py"),
        str(normal_runs), "--output", str(dataset),
    ], root)
    call([
        sys.executable, str(root / "validate_v11_dataset.py"),
        str(dataset / "projections.csv"),
        "--output", str(dataset / "validation_report.json"),
    ], root)
    call([
        sys.executable, str(root / "run_real_multiseed_v11.py"),
        str(dataset / "projections.csv"),
        "--output", str(results),
        "--seeds", str(args.seeds),
    ], root)
    print(f"V11 experiment complete: {output}")


if __name__ == "__main__":
    main()
