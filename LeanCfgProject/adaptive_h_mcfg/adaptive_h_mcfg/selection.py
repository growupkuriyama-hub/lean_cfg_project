from __future__ import annotations

from dataclasses import dataclass
from typing import Iterable, Sequence

from .learner import LearnedModel, RestrictedTypedTupleLearner
from .observers import Observer, ProductObserver


@dataclass(frozen=True)
class Evaluation:
    selected: tuple[str, ...]
    normal_false_rejects: int
    mutant_false_accepts: int
    normal_count: int
    mutant_count: int
    rule_count: int
    occurrence_count: int
    observed_type_count: int
    objective: float

    @property
    def normal_accuracy(self) -> float:
        return 1.0 - self.normal_false_rejects / max(1, self.normal_count)

    @property
    def mutant_recall(self) -> float:
        return 1.0 - self.mutant_false_accepts / max(1, self.mutant_count)


@dataclass
class SelectionResult:
    selected_observers: tuple[Observer, ...]
    model: LearnedModel
    history: list[Evaluation]


def evaluate_model(
    learner: RestrictedTypedTupleLearner,
    train_positive: Sequence[str],
    validation_positive: Sequence[str],
    validation_mutants: Sequence[str],
    factors: Sequence[Observer],
    complexity_weight: float,
    type_weight: float = 0.0,
    guided: bool = False,
) -> tuple[Evaluation, LearnedModel]:
    observer = ProductObserver(factors)
    model = learner.fit(train_positive, observer)
    all_words = tuple(validation_positive) + tuple(validation_mutants)
    if guided and hasattr(model, "accepts_many_guided"):
        accepted = model.accepts_many_guided(all_words)
    else:
        accepted = model.accepts_many(all_words)
    false_rejects = sum(not accepted[word] for word in validation_positive)
    false_accepts = sum(accepted[word] for word in validation_mutants)
    error = false_rejects / max(1, len(validation_positive)) + false_accepts / max(1, len(validation_mutants))
    objective = (
        error
        + complexity_weight * model.rule_count
        + type_weight * model.observed_type_count
    )
    evaluation = Evaluation(
        selected=tuple(f.name for f in factors),
        normal_false_rejects=false_rejects,
        mutant_false_accepts=false_accepts,
        normal_count=len(validation_positive),
        mutant_count=len(validation_mutants),
        rule_count=model.rule_count,
        occurrence_count=model.occurrence_count,
        observed_type_count=model.observed_type_count,
        objective=objective,
    )
    return evaluation, model


def greedy_select(
    learner: RestrictedTypedTupleLearner,
    train_positive: Sequence[str],
    validation_positive: Sequence[str],
    validation_mutants: Sequence[str],
    candidates: Iterable[Observer],
    budget: int = 3,
    min_improvement: float = 1e-9,
    complexity_weight: float = 1e-6,
    type_weight: float = 0.0,
    guided: bool = False,
) -> SelectionResult:
    candidates_tuple = tuple(candidates)
    selected: list[Observer] = []
    history: list[Evaluation] = []

    current_eval, current_model = evaluate_model(
        learner,
        train_positive,
        validation_positive,
        validation_mutants,
        selected,
        complexity_weight,
        type_weight,
        guided,
    )
    history.append(current_eval)

    while len(selected) < budget:
        best: tuple[Evaluation, LearnedModel, Observer] | None = None
        for candidate in candidates_tuple:
            if candidate in selected:
                continue
            evaluation, model = evaluate_model(
                learner,
                train_positive,
                validation_positive,
                validation_mutants,
                [*selected, candidate],
                complexity_weight,
                type_weight,
                guided,
            )
            if best is None or evaluation.objective < best[0].objective:
                best = (evaluation, model, candidate)
        if best is None:
            break
        best_eval, best_model, best_candidate = best
        if current_eval.objective - best_eval.objective < min_improvement:
            break
        selected.append(best_candidate)
        current_eval = best_eval
        current_model = best_model
        history.append(best_eval)

    return SelectionResult(tuple(selected), current_model, history)
