from __future__ import annotations

import csv
from collections import Counter, defaultdict
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable, Sequence


@dataclass(frozen=True)
class ProjectionRow:
    source: str
    run_id: str
    source_trace_id: str
    trace_id: str
    label: str
    item_count: int
    word: str
    mutation: str
    route_preserving: bool
    description: str
    split_role: str = ""
    replica: int = -1


def parse_int_spec(spec: str) -> tuple[int, ...]:
    """Parse comma-separated integers and inclusive ranges, e.g. ``1,3-5``."""
    values: list[int] = []
    for raw_part in spec.split(","):
        part = raw_part.strip()
        if not part:
            continue
        if "-" in part:
            left, right = part.split("-", 1)
            start, end = int(left), int(right)
            if start > end:
                raise ValueError(f"descending range is not allowed: {part!r}")
            values.extend(range(start, end + 1))
        else:
            values.append(int(part))
    unique = tuple(dict.fromkeys(values))
    if not unique or any(value < 1 for value in unique):
        raise ValueError("count specifications must contain positive integers")
    return unique


def role_for_count(
    item_count: int,
    train_counts: Sequence[int],
    validation_counts: Sequence[int],
    test_counts: Sequence[int],
) -> str:
    memberships = [
        name
        for name, values in (
            ("train", set(train_counts)),
            ("validation", set(validation_counts)),
            ("test", set(test_counts)),
        )
        if item_count in values
    ]
    if len(memberships) != 1:
        raise ValueError(
            f"item count {item_count} must belong to exactly one split role; got {memberships}"
        )
    return memberships[0]


def load_projection_rows(path: Path) -> list[ProjectionRow]:
    rows: list[ProjectionRow] = []
    with path.open(newline="", encoding="utf-8") as handle:
        for raw in csv.DictReader(handle):
            route_raw = str(raw.get("route_preserving", "true")).strip().lower()
            rows.append(
                ProjectionRow(
                    source=str(raw.get("source", "")),
                    run_id=str(raw["run_id"]),
                    source_trace_id=str(raw.get("source_trace_id", raw.get("trace_id", ""))),
                    trace_id=str(raw.get("trace_id", "")),
                    label=str(raw["label"]),
                    item_count=int(raw["item_count"]),
                    word=str(raw["word"]),
                    mutation=str(raw.get("mutation", "none")),
                    route_preserving=route_raw in {"1", "true", "yes"},
                    description=str(raw.get("description", "")),
                    split_role=str(raw.get("split_role", "")),
                    replica=int(raw.get("replica", -1) or -1),
                )
            )
    return rows


def unique_words(rows: Iterable[ProjectionRow]) -> tuple[str, ...]:
    return tuple(dict.fromkeys(row.word for row in rows))


def partition_rows_by_count(
    rows: Sequence[ProjectionRow],
    train_counts: Sequence[int],
    validation_counts: Sequence[int],
    test_counts: Sequence[int],
) -> dict[str, list[ProjectionRow]]:
    output: dict[str, list[ProjectionRow]] = {"train": [], "validation": [], "test": []}
    for row in rows:
        role = role_for_count(row.item_count, train_counts, validation_counts, test_counts)
        if row.split_role and row.split_role != role:
            raise ValueError(
                f"stored split_role mismatch for {row.trace_id}: {row.split_role!r} != {role!r}"
            )
        output[role].append(row)
    return output


def _intersection_report(named_sets: dict[str, set[str]]) -> dict[str, list[str]]:
    keys = tuple(named_sets)
    output: dict[str, list[str]] = {}
    for index, left in enumerate(keys):
        for right in keys[index + 1 :]:
            output[f"{left}_vs_{right}"] = sorted(named_sets[left] & named_sets[right])
    return output


def audit_word_disjoint_protocol(
    rows: Sequence[ProjectionRow],
    train_counts: Sequence[int],
    validation_counts: Sequence[int],
    test_counts: Sequence[int],
    diagnostic_mutation: str,
    expected_mutations: Sequence[str] | None = None,
    minimum_replicas_per_count: int = 1,
) -> dict[str, object]:
    parts = partition_rows_by_count(
        rows, train_counts=train_counts, validation_counts=validation_counts, test_counts=test_counts
    )
    normal_by_role = {
        role: [row for row in selected if row.label == "normal"]
        for role, selected in parts.items()
    }
    # The learner sees positive normal words during training. Validation reserves
    # every word at its held-out count, while testing uses every test-count word.
    protocol_word_sets = {
        "train": set(unique_words(normal_by_role["train"])),
        "validation": set(unique_words(parts["validation"])),
        "test": set(unique_words(parts["test"])),
    }
    run_sets = {role: {row.run_id for row in selected} for role, selected in parts.items()}
    source_trace_sets = {
        role: {row.source_trace_id for row in selected if row.source_trace_id}
        for role, selected in parts.items()
    }
    word_intersections = _intersection_report(protocol_word_sets)
    run_intersections = _intersection_report(run_sets)
    trace_intersections = _intersection_report(source_trace_sets)

    normal_rows = [row for row in rows if row.label == "normal"]
    anomaly_rows = [row for row in rows if row.label == "anomaly"]
    run_to_normals: dict[str, list[ProjectionRow]] = defaultdict(list)
    for row in normal_rows:
        run_to_normals[row.run_id].append(row)

    per_count_replicas = Counter(row.item_count for row in normal_rows)
    duplicate_normal_words_by_count = {
        str(count): len({row.word for row in normal_rows if row.item_count == count})
        for count in sorted(per_count_replicas)
    }
    mutations = Counter(row.mutation for row in anomaly_rows)
    expected = tuple(expected_mutations or sorted(mutations))
    missing_mutation_count_pairs: list[dict[str, object]] = []
    mutation_coverage_counts = sorted(set(validation_counts) | set(test_counts))
    for count in mutation_coverage_counts:
        available = {
            row.mutation
            for row in anomaly_rows
            if row.item_count == count and row.label == "anomaly"
        }
        for mutation in expected:
            if mutation not in available:
                missing_mutation_count_pairs.append({"item_count": count, "mutation": mutation})

    validation_diagnostic_words = {
        row.word
        for row in parts["validation"]
        if row.label == "anomaly" and row.mutation == diagnostic_mutation
    }
    test_words = protocol_word_sets["test"]
    validation_diagnostic_test_overlap = sorted(validation_diagnostic_words & test_words)

    errors: list[str] = []
    if not rows:
        errors.append("dataset is empty")
    if any(word_intersections.values()):
        errors.append("projected words overlap across train/validation/test")
    if any(run_intersections.values()):
        errors.append("run IDs overlap across train/validation/test")
    if any(trace_intersections.values()):
        errors.append("source trace IDs overlap across train/validation/test")
    if validation_diagnostic_test_overlap:
        errors.append("validation diagnostic mutation words reappear in test")
    if any(len(values) != 1 for values in run_to_normals.values()):
        errors.append("each count-controlled run must contribute exactly one normal projection")
    if missing_mutation_count_pairs:
        errors.append("one or more mutation families are missing for an item count")
    required_counts = set(train_counts) | set(validation_counts) | set(test_counts)
    missing_counts = sorted(required_counts - set(per_count_replicas))
    if missing_counts:
        errors.append(f"missing required item counts: {missing_counts}")
    low_replication = {
        str(count): per_count_replicas[count]
        for count in sorted(required_counts)
        if per_count_replicas[count] < minimum_replicas_per_count
    }
    if low_replication:
        errors.append(f"insufficient normal replicas per count: {low_replication}")
    if not validation_diagnostic_words:
        errors.append(f"validation lacks diagnostic mutation {diagnostic_mutation!r}")

    return {
        "protocol": "ADP-MCFG-v5 / internal V12 count-held-out evaluation",
        "train_counts": list(train_counts),
        "validation_counts": list(validation_counts),
        "test_counts": list(test_counts),
        "normal_rows": len(normal_rows),
        "anomaly_rows": len(anomaly_rows),
        "unique_normal_words": len({row.word for row in normal_rows}),
        "unique_anomaly_words": len({row.word for row in anomaly_rows}),
        "unique_words_total": len({row.word for row in rows}),
        "normal_replicas_by_count": dict(sorted(per_count_replicas.items())),
        "unique_normal_words_by_count": duplicate_normal_words_by_count,
        "mutation_rows_by_family": dict(sorted(mutations.items())),
        "protocol_unique_words_by_role": {
            role: len(words) for role, words in protocol_word_sets.items()
        },
        "runs_by_role": {role: sorted(values) for role, values in run_sets.items()},
        "source_trace_count_by_role": {
            role: len(values) for role, values in source_trace_sets.items()
        },
        "word_intersections": word_intersections,
        "run_intersections": run_intersections,
        "source_trace_intersections": trace_intersections,
        "validation_diagnostic_words": sorted(validation_diagnostic_words),
        "validation_diagnostic_test_overlap": validation_diagnostic_test_overlap,
        "missing_mutation_count_pairs": missing_mutation_count_pairs,
        "minimum_replicas_per_count": minimum_replicas_per_count,
        "errors": errors,
        "ready_for_word_disjoint_evaluation": not errors,
    }
