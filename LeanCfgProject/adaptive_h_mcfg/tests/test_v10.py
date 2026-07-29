from __future__ import annotations

from adaptive_h_mcfg.binary_learner import BoundedCanonicalMCFGLearner
from adaptive_h_mcfg.observers import (
    ModularCountObserver,
    TrivialObserver,
    block_envelope_observer,
)
from adaptive_h_mcfg.otel_v10 import (
    checkout_phase_projection,
    invert_final_currency_server_phase,
    make_paired_checkout_trace,
)
from adaptive_h_mcfg.selection import greedy_select


def normal_word(n: int) -> str:
    return "p" * n + "#" + "c" * n + "s" + "#" + "pc" * n + "s"


def phase_inversion_word(n: int) -> str:
    return "p" * n + "#" + "c" * (n - 1) + "sc" + "#" + "pc" * n + "s"


def test_span_mutation_matches_phase_projection() -> None:
    trace = make_paired_checkout_trace(2)
    normal = checkout_phase_projection(trace)
    mutant = checkout_phase_projection(invert_final_currency_server_phase(trace))
    assert normal is not None
    assert mutant is not None
    assert normal.word == normal_word(2)
    assert mutant.word == phase_inversion_word(2)


def test_adaptive_observer_blocks_trivial_overgeneralization() -> None:
    train = (normal_word(1), normal_word(2))
    learner = BoundedCanonicalMCFGLearner(fanout=3)
    candidates = (
        block_envelope_observer(
            (("p",), ("c", "s"), ("p", "c", "s")),
            name="checkout-phase-envelope",
        ),
        ModularCountObserver(("s",), 2, "shipping-phase-count-mod-2"),
    )
    result = greedy_select(
        learner,
        train,
        (normal_word(3),),
        (phase_inversion_word(2),),
        candidates,
        budget=1,
        complexity_weight=1e-8,
        type_weight=1e-6,
        guided=False,
    )
    trivial = learner.fit(train, TrivialObserver())
    assert trivial.accepts_one_guided(phase_inversion_word(2))
    assert not result.model.accepts_one_guided(phase_inversion_word(2))
    assert result.model.accepts_one_guided(normal_word(4))
    assert result.selected_observers
