from __future__ import annotations

import math
from collections import Counter, defaultdict
from dataclasses import dataclass
from typing import Iterable, Mapping, Sequence


@dataclass(frozen=True)
class ThresholdSelection:
    threshold: float
    normal_acceptance: float
    mutation_recall: float
    balanced_accuracy: float


class NGramAnomalyModel:
    """Character n-gram language model with a validation-selected threshold.

    The model is intentionally small and transparent.  It is a conventional
    sequence baseline for the trace experiments, not a replacement for the
    grammar learner.  Add-one smoothing makes every encoded trace scoreable.
    """

    def __init__(self, order: int = 2, alpha: float = 1.0) -> None:
        if order < 1:
            raise ValueError("order must be positive")
        if alpha <= 0:
            raise ValueError("alpha must be positive")
        self.order = order
        self.alpha = float(alpha)
        self._counts: dict[tuple[str, ...], Counter[str]] = defaultdict(Counter)
        self._totals: Counter[tuple[str, ...]] = Counter()
        self._alphabet: tuple[str, ...] = ()
        self.threshold: float | None = None

    @property
    def bos(self) -> str:
        return "<BOS>"

    @property
    def eos(self) -> str:
        return "<EOS>"

    def fit(self, words: Iterable[str]) -> "NGramAnomalyModel":
        words_tuple = tuple(words)
        if not words_tuple:
            raise ValueError("at least one training word is required")
        alphabet = {token for word in words_tuple for token in word}
        alphabet.add(self.eos)
        self._alphabet = tuple(sorted(alphabet))
        width = self.order - 1
        for word in words_tuple:
            sequence = [self.bos] * width + list(word) + [self.eos]
            for index in range(width, len(sequence)):
                context = tuple(sequence[index - width:index]) if width else ()
                token = sequence[index]
                self._counts[context][token] += 1
                self._totals[context] += 1
        return self

    def score(self, word: str) -> float:
        if not self._alphabet:
            raise RuntimeError("fit the model first")
        width = self.order - 1
        sequence = [self.bos] * width + list(word) + [self.eos]
        vocabulary = len(self._alphabet) + 1  # reserve one unknown symbol
        loss = 0.0
        steps = 0
        for index in range(width, len(sequence)):
            context = tuple(sequence[index - width:index]) if width else ()
            token = sequence[index]
            numerator = self._counts.get(context, Counter()).get(token, 0) + self.alpha
            denominator = self._totals.get(context, 0) + self.alpha * vocabulary
            loss -= math.log(numerator / denominator)
            steps += 1
        return loss / max(1, steps)

    def select_threshold(
        self,
        validation_normal: Sequence[str],
        validation_mutants: Sequence[str],
    ) -> ThresholdSelection:
        if not validation_normal or not validation_mutants:
            raise ValueError("nonempty validation normals and mutants are required")
        normal_scores = [self.score(word) for word in validation_normal]
        mutant_scores = [self.score(word) for word in validation_mutants]
        values = sorted(set([*normal_scores, *mutant_scores]))
        candidates = [values[0] - 1e-12]
        candidates.extend((left + right) / 2.0 for left, right in zip(values, values[1:]))
        candidates.append(values[-1] + 1e-12)
        best: tuple[tuple[float, float, float], ThresholdSelection] | None = None
        for threshold in candidates:
            normal_acceptance = sum(score <= threshold for score in normal_scores) / len(normal_scores)
            mutation_recall = sum(score > threshold for score in mutant_scores) / len(mutant_scores)
            balanced = (normal_acceptance + mutation_recall) / 2.0
            result = ThresholdSelection(threshold, normal_acceptance, mutation_recall, balanced)
            key = (balanced, normal_acceptance, -threshold)
            if best is None or key > best[0]:
                best = (key, result)
        assert best is not None
        self.threshold = best[1].threshold
        return best[1]

    def accepts(self, word: str) -> bool:
        if self.threshold is None:
            raise RuntimeError("select a threshold first")
        return self.score(word) <= self.threshold

    def accepts_many(self, words: Sequence[str]) -> Mapping[str, bool]:
        return {word: self.accepts(word) for word in dict.fromkeys(words)}


@dataclass(frozen=True)
class ExactTemplateModel:
    words: frozenset[str]

    @classmethod
    def fit(cls, words: Iterable[str]) -> "ExactTemplateModel":
        return cls(frozenset(words))

    def accepts(self, word: str) -> bool:
        return word in self.words

    def accepts_many(self, words: Sequence[str]) -> Mapping[str, bool]:
        return {word: word in self.words for word in dict.fromkeys(words)}


def _select_score_threshold(
    normal_scores: Sequence[float], mutant_scores: Sequence[float]
) -> ThresholdSelection:
    if not normal_scores or not mutant_scores:
        raise ValueError("nonempty validation scores are required")
    values = sorted(set([*normal_scores, *mutant_scores]))
    candidates = [values[0] - 1e-12]
    candidates.extend((left + right) / 2.0 for left, right in zip(values, values[1:]))
    candidates.append(values[-1] + 1e-12)
    best: tuple[tuple[float, float, float], ThresholdSelection] | None = None
    for threshold in candidates:
        normal_acceptance = sum(score <= threshold for score in normal_scores) / len(normal_scores)
        mutation_recall = sum(score > threshold for score in mutant_scores) / len(mutant_scores)
        balanced = (normal_acceptance + mutation_recall) / 2.0
        result = ThresholdSelection(threshold, normal_acceptance, mutation_recall, balanced)
        key = (balanced, normal_acceptance, -threshold)
        if best is None or key > best[0]:
            best = (key, result)
    assert best is not None
    return best[1]


class TraceFeatureExtractor:
    """Deterministic count/bigram features for classical anomaly baselines."""

    def __init__(self, separator: str = "#") -> None:
        self.separator = separator
        self.tokens: tuple[str, ...] = ()
        self.bigrams: tuple[str, ...] = ()

    def fit(self, words: Iterable[str]) -> "TraceFeatureExtractor":
        words_tuple = tuple(words)
        self.tokens = tuple(sorted({token for word in words_tuple for token in word}))
        self.bigrams = tuple(
            sorted({word[index:index + 2] for word in words_tuple for index in range(len(word) - 1)})
        )
        return self

    def transform(self, words: Sequence[str]):
        import numpy as np

        token_index = {token: index for index, token in enumerate(self.tokens)}
        bigram_index = {bigram: index for index, bigram in enumerate(self.bigrams)}
        width = 4 + len(self.tokens) + len(self.bigrams)
        matrix = np.zeros((len(words), width), dtype=float)
        for row, word in enumerate(words):
            length = max(1, len(word))
            blocks = word.split(self.separator)
            block_lengths = [len(block) for block in blocks]
            matrix[row, 0] = len(word)
            matrix[row, 1] = len(blocks)
            matrix[row, 2] = min(block_lengths, default=0)
            matrix[row, 3] = max(block_lengths, default=0)
            for token in word:
                index = token_index.get(token)
                if index is not None:
                    matrix[row, 4 + index] += 1.0 / length
            offset = 4 + len(self.tokens)
            for index in range(len(word) - 1):
                hit = bigram_index.get(word[index:index + 2])
                if hit is not None:
                    matrix[row, offset + hit] += 1.0 / max(1, length - 1)
        return matrix


class IsolationForestAnomalyModel:
    """Classical feature baseline with mutation-selected decision threshold."""

    def __init__(self, separator: str = "#", random_state: int = 0) -> None:
        self.extractor = TraceFeatureExtractor(separator)
        self.random_state = random_state
        self.model = None
        self.threshold: float | None = None

    def fit(self, words: Sequence[str]) -> "IsolationForestAnomalyModel":
        if not words:
            raise ValueError("at least one training word is required")
        try:
            from sklearn.ensemble import IsolationForest
        except ImportError as exc:  # pragma: no cover - optional dependency
            raise RuntimeError("scikit-learn is required for IsolationForest baseline") from exc
        self.extractor.fit(words)
        features = self.extractor.transform(words)
        self.model = IsolationForest(
            n_estimators=200,
            contamination="auto",
            random_state=self.random_state,
            n_jobs=1,
        ).fit(features)
        return self

    def score_many(self, words: Sequence[str]) -> list[float]:
        if self.model is None:
            raise RuntimeError("fit the model first")
        # sklearn's decision_function is larger for inliers. Negate it so a
        # larger value consistently means more anomalous.
        return list(-self.model.decision_function(self.extractor.transform(words)))

    def select_threshold(
        self, validation_normal: Sequence[str], validation_mutants: Sequence[str]
    ) -> ThresholdSelection:
        result = _select_score_threshold(
            self.score_many(validation_normal), self.score_many(validation_mutants)
        )
        self.threshold = result.threshold
        return result

    def accepts_many(self, words: Sequence[str]) -> Mapping[str, bool]:
        if self.threshold is None:
            raise RuntimeError("select a threshold first")
        unique = list(dict.fromkeys(words))
        scores = self.score_many(unique)
        return {word: score <= self.threshold for word, score in zip(unique, scores)}
