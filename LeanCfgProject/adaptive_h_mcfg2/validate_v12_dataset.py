#!/usr/bin/env python3
"""Fail-closed validator for the V12 projected-word-disjoint protocol."""
from __future__ import annotations

import argparse
import json
from pathlib import Path

from adaptive_h_mcfg.v12_protocol import (
    audit_word_disjoint_protocol,
    load_projection_rows,
    parse_int_spec,
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


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("projections_csv", type=Path)
    parser.add_argument("--output", type=Path)
    parser.add_argument("--train-counts", default="1,2")
    parser.add_argument("--validation-counts", default="3")
    parser.add_argument("--test-counts", default="4-10")
    parser.add_argument("--minimum-replicas", type=int, default=5)
    parser.add_argument("--report-only", action="store_true")
    args = parser.parse_args()

    report = audit_word_disjoint_protocol(
        load_projection_rows(args.projections_csv),
        train_counts=parse_int_spec(args.train_counts),
        validation_counts=parse_int_spec(args.validation_counts),
        test_counts=parse_int_spec(args.test_counts),
        diagnostic_mutation=DIAGNOSTIC_MUTATION,
        expected_mutations=EXPECTED_MUTATIONS,
        minimum_replicas_per_count=args.minimum_replicas,
    )
    text = json.dumps(report, indent=2)
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(text, encoding="utf-8")
    print(text)
    if not report["ready_for_word_disjoint_evaluation"] and not args.report_only:
        raise SystemExit("V12 dataset validation failed closed")


if __name__ == "__main__":
    main()
