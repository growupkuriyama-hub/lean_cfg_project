#!/usr/bin/env python3
"""Build a run-labelled, route-preserving mutation dataset from normal Jaeger exports."""
from __future__ import annotations

import argparse
import csv
import json
import re
import sys
from collections import Counter
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from adaptive_h_mcfg.otel_v10 import checkout_phase_projection, is_normal_checkout_projection
from adaptive_h_mcfg.otel_v11 import projection_mutations
from adaptive_h_mcfg.traces import parse_jaeger_json

RUN_RE = re.compile(r"run[-_](\d+)", re.IGNORECASE)


def infer_run_id(source: Path, root: Path) -> str:
    for part in reversed(source.relative_to(root).parts):
        match = RUN_RE.search(part)
        if match:
            return f"run-{int(match.group(1)):02d}"
    return source.stem


def load_traces(path: Path):
    for source in sorted(path.rglob("*.json")):
        if source.name in {"manifest.json", "dataset_summary.json"}:
            continue
        try:
            payload = json.loads(source.read_text(encoding="utf-8"))
        except (OSError, json.JSONDecodeError):
            continue
        run_id = infer_run_id(source, path)
        for trace in parse_jaeger_json(payload):
            yield source, run_id, trace


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("normal_runs", type=Path)
    parser.add_argument("--output", type=Path, default=Path("mcfg-v11-dataset"))
    parser.add_argument("--max-per-run-item-count", type=int, default=100)
    args = parser.parse_args()
    args.output.mkdir(parents=True, exist_ok=True)

    rows: list[dict[str, object]] = []
    accepted: Counter[tuple[str, int]] = Counter()
    skipped_noncanonical = 0
    mutation_counts: Counter[str] = Counter()

    for source, run_id, trace in load_traces(args.normal_runs):
        projection = checkout_phase_projection(trace)
        if projection is None or not is_normal_checkout_projection(projection):
            skipped_noncanonical += 1
            continue
        key = (run_id, projection.item_count)
        if accepted[key] >= args.max_per_run_item_count:
            continue
        accepted[key] += 1
        base = {
            "source": str(source),
            "run_id": run_id,
            "source_trace_id": trace.trace_id,
            "item_count": projection.item_count,
            "route_preserving": True,
        }
        rows.append({
            **base,
            "trace_id": trace.trace_id,
            "label": "normal",
            "word": projection.word,
            "mutation": "none",
            "description": "unmodified normal trace projection",
        })
        for mutation in projection_mutations(projection):
            mutation_counts[mutation.name] += 1
            rows.append({
                **base,
                "trace_id": f"{trace.trace_id}-{mutation.name}",
                "label": "anomaly",
                "word": mutation.word,
                "mutation": mutation.name,
                "route_preserving": mutation.route_preserving,
                "description": mutation.description,
            })

    fieldnames = [
        "source", "run_id", "source_trace_id", "trace_id", "label",
        "item_count", "word", "mutation", "route_preserving", "description",
    ]
    with (args.output / "projections.csv").open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=fieldnames)
        writer.writeheader()
        writer.writerows(rows)

    normal_counts = Counter(int(row["item_count"]) for row in rows if row["label"] == "normal")
    run_counts = Counter(str(row["run_id"]) for row in rows if row["label"] == "normal")
    summary = {
        "normal_projection_counts": dict(sorted(normal_counts.items())),
        "normal_rows_by_run": dict(sorted(run_counts.items())),
        "normal_rows": sum(row["label"] == "normal" for row in rows),
        "mutant_rows": sum(row["label"] == "anomaly" for row in rows),
        "mutation_counts": dict(sorted(mutation_counts.items())),
        "skipped_noncanonical_traces": skipped_noncanonical,
        "run_ids": sorted(run_counts),
    }
    (args.output / "dataset_summary.json").write_text(
        json.dumps(summary, indent=2), encoding="utf-8"
    )
    print(json.dumps(summary, indent=2))


if __name__ == "__main__":
    main()
