#!/usr/bin/env python3
"""Isolated grammar-construction scaling benchmark for V12.

Predictive evaluation remains count-held-out.  This script may use additional
normal words solely to measure construction cost; it emits no accuracy metric.
Each point runs in a fresh subprocess with an explicit address-space cap.
"""
from __future__ import annotations

import argparse
import csv
import json
import os
import resource
import subprocess
import sys
import time
from pathlib import Path
from typing import Any

from adaptive_h_mcfg.binary_learner import BoundedCanonicalMCFGLearner
from adaptive_h_mcfg.observers import (
    ModularCountObserver,
    ProductObserver,
    TrivialObserver,
    block_envelope_observer,
)
from adaptive_h_mcfg.v12_protocol import load_projection_rows


def candidates():
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


def observer_for(name: str):
    if name == "trivial":
        return TrivialObserver()
    if name == "shipping-phase-count-mod-2":
        return ModularCountObserver(("s",), 2, "shipping-phase-count-mod-2")
    if name == "full-product":
        return ProductObserver(candidates())
    raise ValueError(name)


def set_memory_cap(memory_gib: float) -> None:
    if memory_gib <= 0 or not hasattr(resource, "RLIMIT_AS"):
        return
    limit = int(memory_gib * 1024**3)
    resource.setrlimit(resource.RLIMIT_AS, (limit, limit))


def worker(args: argparse.Namespace) -> int:
    set_memory_cap(args.memory_gib)
    rows = load_projection_rows(args.projections_csv)
    by_count: dict[int, str] = {}
    for row in rows:
        if row.label == "normal" and row.item_count <= args.max_training_count:
            by_count.setdefault(row.item_count, row.word)
    expected = set(range(1, args.max_training_count + 1))
    if set(by_count) != expected:
        raise RuntimeError(f"normal count coverage mismatch: expected {sorted(expected)}, got {sorted(by_count)}")
    words = tuple(by_count[count] for count in sorted(by_count))
    learner = BoundedCanonicalMCFGLearner(fanout=3)
    started = time.perf_counter()
    basis = learner.prepare(words)
    basis_seconds = time.perf_counter() - started
    started = time.perf_counter()
    model = learner.fit_prepared(basis, observer_for(args.observer))
    fit_seconds = time.perf_counter() - started
    unit_rules = getattr(model, "unit_rules", {})
    result = {
        "status": "ok",
        "max_training_count": args.max_training_count,
        "training_counts": list(sorted(by_count)),
        "training_word_count": len(words),
        "max_training_word_length": max(map(len, words)),
        "observer": args.observer,
        "basis_seconds": basis_seconds,
        "fit_seconds": fit_seconds,
        "total_seconds": basis_seconds + fit_seconds,
        "rule_count": getattr(model, "rule_count", ""),
        "unit_rule_count": sum(len(value) for value in unit_rules.values()) if isinstance(unit_rules, dict) else "",
        "observed_type_count": getattr(model, "observed_type_count", ""),
        "occurrence_count": getattr(model, "occurrence_count", ""),
        "peak_rss_mib": float(resource.getrusage(resource.RUSAGE_SELF).ru_maxrss) / 1024.0,
        "memory_cap_gib": args.memory_gib,
    }
    print(json.dumps(result))
    return 0


def parent(args: argparse.Namespace) -> int:
    rows: list[dict[str, Any]] = []
    script = Path(__file__).resolve()
    for max_count in range(1, args.max_training_count + 1):
        for observer in args.observers.split(","):
            observer = observer.strip()
            if not observer:
                continue
            command = [
                sys.executable,
                str(script),
                str(args.projections_csv.resolve()),
                "--worker",
                "--max-training-count",
                str(max_count),
                "--observer",
                observer,
                "--memory-gib",
                str(args.memory_gib),
            ]
            started = time.perf_counter()
            try:
                completed = subprocess.run(
                    command,
                    text=True,
                    capture_output=True,
                    timeout=args.timeout_seconds,
                    check=False,
                    env={**os.environ, "PYTHONUNBUFFERED": "1"},
                )
                elapsed = time.perf_counter() - started
                if completed.returncode == 0:
                    payload = json.loads(completed.stdout.strip().splitlines()[-1])
                    payload["wall_seconds_parent"] = elapsed
                    payload["timeout_seconds"] = args.timeout_seconds
                    rows.append(payload)
                else:
                    rows.append({
                        "status": "failed",
                        "max_training_count": max_count,
                        "observer": observer,
                        "memory_cap_gib": args.memory_gib,
                        "timeout_seconds": args.timeout_seconds,
                        "wall_seconds_parent": elapsed,
                        "returncode": completed.returncode,
                        "stderr_tail": completed.stderr[-2000:],
                    })
            except subprocess.TimeoutExpired as exc:
                rows.append({
                    "status": "timeout",
                    "max_training_count": max_count,
                    "observer": observer,
                    "memory_cap_gib": args.memory_gib,
                    "timeout_seconds": args.timeout_seconds,
                    "wall_seconds_parent": time.perf_counter() - started,
                    "stderr_tail": (exc.stderr or "")[-2000:] if isinstance(exc.stderr, str) else "",
                })

    fieldnames = sorted({key for row in rows for key in row})
    args.output.parent.mkdir(parents=True, exist_ok=True)
    with args.output.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=fieldnames)
        writer.writeheader()
        writer.writerows(rows)
    summary = {
        "protocol": "V12 isolated grammar-construction scaling; no predictive use of held-out words",
        "points": rows,
        "all_points_ok": all(row["status"] == "ok" for row in rows),
    }
    args.output.with_suffix(".json").write_text(json.dumps(summary, indent=2), encoding="utf-8")
    print(json.dumps({"output": str(args.output), "points": len(rows), "all_points_ok": summary["all_points_ok"]}, indent=2))
    return 0


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("projections_csv", type=Path)
    parser.add_argument("--output", type=Path, default=Path("mcfg-v12-results/training_scaling.csv"))
    parser.add_argument("--max-training-count", type=int, default=4)
    parser.add_argument("--observers", default="trivial,shipping-phase-count-mod-2,full-product")
    parser.add_argument("--observer", default="trivial", help=argparse.SUPPRESS)
    parser.add_argument("--memory-gib", type=float, default=12.0)
    parser.add_argument("--timeout-seconds", type=int, default=600)
    parser.add_argument("--worker", action="store_true", help=argparse.SUPPRESS)
    args = parser.parse_args()
    if args.max_training_count < 1:
        raise SystemExit("max-training-count must be positive")
    return worker(args) if args.worker else parent(args)


if __name__ == "__main__":
    raise SystemExit(main())
