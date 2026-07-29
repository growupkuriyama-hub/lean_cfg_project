from __future__ import annotations

from dataclasses import dataclass
from typing import Sequence

from .binary_learner import BoundedCanonicalMCFGLearner, CanonicalBinaryModel
from .mutations import encoded_selection_mutants, encoded_unseen_mutants
from .observers import Observer
from .routes import RouteSignature, route_signature
from .schema import ObserverLibrary, observers_from_encoder
from .selection import Evaluation, SelectionResult, greedy_select
from .traces import LifelineEncoder, TraceRecord


@dataclass(frozen=True)
class RouteExperimentConfig:
    fanout: int = 2
    budget: int = 2
    complexity_weight: float = 1e-8
    type_weight: float = 1e-6
    include_phase_observers: bool = False
    moduli: tuple[int, ...] = (2,)
    phases: tuple[str, ...] = ("START",)
    include_status: bool = False
    include_duration_bucket: bool = False
    duration_multiplier: float = 2.0
    candidate_names: tuple[str, ...] | None = None
    max_unique_train_words: int | None = 2


@dataclass
class RouteModelBundle:
    signature: RouteSignature
    encoder: LifelineEncoder
    library: ObserverLibrary
    selection: SelectionResult
    train_words: tuple[str, ...]
    validation_words: tuple[str, ...]
    validation_mutants: tuple[str, ...]

    @property
    def model(self) -> CanonicalBinaryModel:
        return self.selection.model  # type: ignore[return-value]

    @property
    def selected_observers(self) -> tuple[Observer, ...]:
        return self.selection.selected_observers


@dataclass(frozen=True)
class RouteEvaluation:
    normal_count: int
    anomaly_count: int
    normal_accepted: int
    anomaly_rejected: int
    route_mismatch_rejected: int
    unseen_mutant_rejected: int
    unseen_mutant_count: int

    @property
    def normal_accuracy(self) -> float:
        return self.normal_accepted / max(1, self.normal_count)

    @property
    def anomaly_recall(self) -> float:
        return self.anomaly_rejected / max(1, self.anomaly_count)


def _require_one_route(traces: Sequence[TraceRecord]) -> RouteSignature:
    signatures = {route_signature(trace) for trace in traces}
    if len(signatures) != 1:
        raise ValueError(f"expected one route signature, found {len(signatures)}")
    return next(iter(signatures))


def fit_route_model(
    train_normal: Sequence[TraceRecord],
    validation_normal: Sequence[TraceRecord],
    config: RouteExperimentConfig = RouteExperimentConfig(),
) -> RouteModelBundle:
    if not train_normal or not validation_normal:
        raise ValueError("nonempty training and validation normal traces are required")
    signature = _require_one_route([*train_normal, *validation_normal])
    encoder = LifelineEncoder(
        service_order=signature.services,
        phases=config.phases,
        include_status=config.include_status,
        include_duration_bucket=config.include_duration_bucket,
        duration_multiplier=config.duration_multiplier,
    ).fit(train_normal)
    all_train_words = tuple(sorted(set(encoder.encode(trace) for trace in train_normal), key=lambda word: (len(word), word)))
    if config.max_unique_train_words is not None:
        if config.max_unique_train_words < 1:
            raise ValueError("max_unique_train_words must be positive or None")
        train_words = all_train_words[: config.max_unique_train_words]
    else:
        train_words = all_train_words
    validation_words = tuple(sorted(set(encoder.encode(trace) for trace in validation_normal)))
    validation_mutants = tuple(encoded_selection_mutants(validation_words, encoder.separator))
    if not validation_mutants:
        raise ValueError("mutation generation produced no validation mutants")

    library = observers_from_encoder(
        encoder,
        include_phase=config.include_phase_observers,
        moduli=config.moduli,
    )
    if config.candidate_names is not None:
        allowed = set(config.candidate_names)
        library = ObserverLibrary(
            tuple(candidate for candidate in library.candidates if candidate.name in allowed),
            library.block_tokens,
        )
        missing = allowed - {candidate.name for candidate in library.candidates}
        if missing:
            raise ValueError(f"unknown requested observers: {sorted(missing)}")
    selection = greedy_select(
        BoundedCanonicalMCFGLearner(fanout=config.fanout),
        train_words,
        validation_words,
        validation_mutants,
        library.candidates,
        budget=config.budget,
        complexity_weight=config.complexity_weight,
        type_weight=config.type_weight,
        guided=False,
    )
    return RouteModelBundle(
        signature=signature,
        encoder=encoder,
        library=library,
        selection=selection,
        train_words=train_words,
        validation_words=validation_words,
        validation_mutants=validation_mutants,
    )


def evaluate_route_model(
    bundle: RouteModelBundle,
    normal: Sequence[TraceRecord],
    anomalies: Sequence[TraceRecord],
) -> RouteEvaluation:
    normal_words: list[str] = []
    anomaly_words: list[str] = []
    mismatch_rejected = 0
    for trace in normal:
        if route_signature(trace) == bundle.signature:
            normal_words.append(bundle.encoder.encode(trace))
    for trace in anomalies:
        if route_signature(trace) != bundle.signature:
            mismatch_rejected += 1
        else:
            anomaly_words.append(bundle.encoder.encode(trace))

    decisions = bundle.model.accepts_many_guided([*normal_words, *anomaly_words])
    unseen = encoded_unseen_mutants(normal_words, bundle.encoder.separator)
    unseen_decisions = bundle.model.accepts_many_guided(unseen) if unseen else {}
    grammar_rejected = sum(not decisions[word] for word in anomaly_words)
    return RouteEvaluation(
        normal_count=len(normal),
        anomaly_count=len(anomalies),
        normal_accepted=sum(decisions[word] for word in normal_words),
        anomaly_rejected=mismatch_rejected + grammar_rejected,
        route_mismatch_rejected=mismatch_rejected,
        unseen_mutant_rejected=sum(not unseen_decisions[word] for word in unseen),
        unseen_mutant_count=len(unseen),
    )


def selection_history(bundle: RouteModelBundle) -> tuple[Evaluation, ...]:
    return tuple(bundle.selection.history)
