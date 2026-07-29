from __future__ import annotations

import math
from dataclasses import dataclass
from typing import Mapping, Sequence


@dataclass(frozen=True)
class McNemarResult:
    baseline_better: int
    proposed_better: int
    discordant: int
    exact_two_sided_p: float


def exact_mcnemar(
    baseline_correct: Sequence[bool], proposed_correct: Sequence[bool]
) -> McNemarResult:
    if len(baseline_correct) != len(proposed_correct):
        raise ValueError("paired outcomes must have equal length")
    baseline_better = sum(b and not p for b, p in zip(baseline_correct, proposed_correct))
    proposed_better = sum(p and not b for b, p in zip(baseline_correct, proposed_correct))
    discordant = baseline_better + proposed_better
    if discordant == 0:
        p_value = 1.0
    else:
        lower = min(baseline_better, proposed_better)
        tail = sum(math.comb(discordant, index) for index in range(lower + 1)) / (2 ** discordant)
        p_value = min(1.0, 2.0 * tail)
    return McNemarResult(baseline_better, proposed_better, discordant, p_value)


@dataclass(frozen=True)
class BootstrapInterval:
    estimate: float
    lower: float
    upper: float
    replicates: int


def _percentile(sorted_values: Sequence[float], probability: float) -> float:
    if not sorted_values:
        raise ValueError("at least one value is required")
    if probability <= 0:
        return sorted_values[0]
    if probability >= 1:
        return sorted_values[-1]
    position = probability * (len(sorted_values) - 1)
    left = int(math.floor(position))
    right = int(math.ceil(position))
    if left == right:
        return sorted_values[left]
    weight = position - left
    return sorted_values[left] * (1.0 - weight) + sorted_values[right] * weight


def cluster_bootstrap_mean(
    values_by_cluster: Mapping[str, float],
    *,
    replicates: int = 5000,
    seed: int = 0,
    confidence: float = 0.95,
) -> BootstrapInterval:
    """Percentile bootstrap over independent case/run clusters."""
    if not values_by_cluster:
        raise ValueError("at least one cluster is required")
    if replicates < 100:
        raise ValueError("replicates must be at least 100")
    if not 0 < confidence < 1:
        raise ValueError("confidence must be between zero and one")
    from random import Random

    clusters = sorted(values_by_cluster)
    estimate = sum(values_by_cluster[key] for key in clusters) / len(clusters)
    rng = Random(seed)
    samples: list[float] = []
    for _ in range(replicates):
        drawn = [clusters[rng.randrange(len(clusters))] for _ in clusters]
        samples.append(sum(values_by_cluster[key] for key in drawn) / len(drawn))
    samples.sort()
    alpha = (1.0 - confidence) / 2.0
    return BootstrapInterval(
        estimate=estimate,
        lower=_percentile(samples, alpha),
        upper=_percentile(samples, 1.0 - alpha),
        replicates=replicates,
    )


def cluster_bootstrap_paired_difference(
    baseline_by_cluster: Mapping[str, float],
    proposed_by_cluster: Mapping[str, float],
    *,
    replicates: int = 5000,
    seed: int = 0,
    confidence: float = 0.95,
) -> BootstrapInterval:
    """Case-clustered percentile CI for proposed minus baseline performance."""
    if set(baseline_by_cluster) != set(proposed_by_cluster):
        raise ValueError("paired cluster keys must match")
    differences = {
        key: proposed_by_cluster[key] - baseline_by_cluster[key]
        for key in proposed_by_cluster
    }
    return cluster_bootstrap_mean(
        differences,
        replicates=replicates,
        seed=seed,
        confidence=confidence,
    )
