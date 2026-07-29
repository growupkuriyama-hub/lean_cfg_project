"""Minimal research prototype for mutation-guided finite-observation selection.

This package intentionally implements a restricted, schema-free fragment of the
fixed-h tuple-substitution learner.  It is suitable for controlled synthetic
experiments, not yet for the full JSS distributed-trace evaluation.
"""

from .observers import (
    Observer,
    ProductObserver,
    TrivialObserver,
    ModularCountObserver,
    DFATransitionObserver,
    parallel_envelope_observer,
)
from .learner import RestrictedTypedTupleLearner, LearnedModel
from .selection import greedy_select

__all__ = [
    "Observer",
    "ProductObserver",
    "TrivialObserver",
    "ModularCountObserver",
    "DFATransitionObserver",
    "parallel_envelope_observer",
    "RestrictedTypedTupleLearner",
    "LearnedModel",
    "greedy_select",
]
