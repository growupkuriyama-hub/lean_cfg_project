#!/usr/bin/env python3
"""Build the V12 count-held-out projection/mutation dataset from its manifest."""
from __future__ import annotations

import argparse
import csv
import json
import sys
from collections import Counter
from pathlib import Path
from typing import Any

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from adaptive_h_mcfg.otel_v10 import checkout_phase_projection, is_normal_checkout_projection
from adaptive_h_mcfg.otel_v11 import projection_mutations
from adaptive_h_mcfg.traces import parse_jaeger_json
from adaptive_h_mcfg.v12_protocol import parse_int_spec, role_for_count


def resolve_source(raw_path: str, manifest_path: Path) -> Path:
    candidate = Path(raw_path)
    if candidate.exists():
        return candidate
    candidate = manifest_path.parent / candidate.name
    if candidate.exists():
        return candidate
    raise FileNotFoundError(raw_path)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("normal_runs", type=Path)
    parser.add_argument("--output", type=Path, default=Path("mcfg-v12-dataset"))
    parser.add_argument("--train-counts", default="1,2")
    parser.add_argument("--validation-counts", default="3")
    parser.add_argument("--test-counts", default="4-10")
    parser.add_argument(
        "--allow-multiple-matching-traces",
        action="store_true",
        help="Diagnostic escape hatch; strict mode requires exactly one matching trace per run.",
    )
    args = parser.parse_args()

    manifest_path = args.normal_runs / "manifest.json"
    manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
    train_counts = parse_int_spec(args.train_counts)
    validation_counts = parse_int_spec(args.validation_counts)
    test_counts = parse_int_spec(args.test_counts)
    args.output.mkdir(parents=True, exist_ok=True)

    rows: list[dict[str, Any]] = []
    rejected: list[dict[str, Any]] = []
    mutation_counts: Counter[str] = Counter()
    normal_counts: Counter[int] = Counter()

    for run_meta in manifest.get("runs", []):
        run_id = str(run_meta["run_id"])
        expected_count = int(run_meta["expected_item_count"])
        replica = int(run_meta["replica"])
        role = role_for_count(expected_count, train_counts, validation_counts, test_counts)
        source = resolve_source(str(run_meta["path"]), manifest_path)
        payload = json.loads(source.read_text(encoding="utf-8"))
        candidates = []
        candidate_diagnostics: list[dict[str, Any]] = []
        for trace in parse_jaeger_json(payload):
            projection = checkout_phase_projection(trace)
            if projection is None:
                continue
            canonical = is_normal_checkout_projection(projection)
            candidate_diagnostics.append(
                {
                    "trace_id": trace.trace_id,
                    "item_count": projection.item_count,
                    "word": projection.word,
                    "canonical": canonical,
                }
            )
            if canonical and projection.item_count == expected_count:
                candidates.append((trace, projection))

        if len(candidates) != 1 and not args.allow_multiple_matching_traces:
            rejected.append(
                {
                    "run_id": run_id,
                    "expected_item_count": expected_count,
                    "matching_trace_count": len(candidates),
                    "candidates": candidate_diagnostics,
                }
            )
            continue
        if not candidates:
            rejected.append(
                {
                    "run_id": run_id,
                    "expected_item_count": expected_count,
                    "matching_trace_count": 0,
                    "candidates": candidate_diagnostics,
                }
            )
            continue
        trace, projection = candidates[0]
        base = {
            "source": str(source),
            "run_id": run_id,
            "source_trace_id": trace.trace_id,
            "item_count": expected_count,
            "route_preserving": True,
            "split_role": role,
            "replica": replica,
        }
        rows.append(
            {
                **base,
                "trace_id": trace.trace_id,
                "label": "normal",
                "word": projection.word,
                "mutation": "none",
                "description": "unmodified count-controlled normal trace projection",
            }
        )
        normal_counts[expected_count] += 1
        for mutation in projection_mutations(projection):
            mutation_counts[mutation.name] += 1
            rows.append(
                {
                    **base,
                    "trace_id": f"{trace.trace_id}-{mutation.name}",
                    "label": "anomaly",
                    "word": mutation.word,
                    "mutation": mutation.name,
                    "route_preserving": mutation.route_preserving,
                    "description": mutation.description,
                }
            )

    fieldnames = [
        "source",
        "run_id",
        "source_trace_id",
        "trace_id",
        "label",
        "item_count",
        "word",
        "mutation",
        "route_preserving",
        "description",
        "split_role",
        "replica",
    ]
    with (args.output / "projections.csv").open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=fieldnames)
        writer.writeheader()
        writer.writerows(rows)

    summary = {
        "protocol": "ADP-MCFG-v5 / internal V12 count-held-out dataset",
        "manifest": str(manifest_path),
        "train_counts": list(train_counts),
        "validation_counts": list(validation_counts),
        "test_counts": list(test_counts),
        "requested_runs": len(manifest.get("runs", [])),
        "accepted_runs": sum(normal_counts.values()),
        "rejected_runs": len(rejected),
        "normal_projection_counts": dict(sorted(normal_counts.items())),
        "normal_rows": sum(row["label"] == "normal" for row in rows),
        "mutant_rows": sum(row["label"] == "anomaly" for row in rows),
        "unique_normal_words": len({row["word"] for row in rows if row["label"] == "normal"}),
        "unique_mutant_words": len({row["word"] for row in rows if row["label"] == "anomaly"}),
        "mutation_counts": dict(sorted(mutation_counts.items())),
        "strict_one_matching_trace_per_run": not args.allow_multiple_matching_traces,
        "rejections": rejected,
    }
    (args.output / "dataset_summary.json").write_text(
        json.dumps(summary, indent=2), encoding="utf-8"
    )
    print(json.dumps(summary, indent=2))
    if rejected and not args.allow_multiple_matching_traces:
        raise SystemExit(
            f"strict dataset build rejected {len(rejected)} run(s); inspect dataset_summary.json"
        )


if __name__ == "__main__":
    main()
