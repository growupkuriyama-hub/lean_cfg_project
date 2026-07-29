from __future__ import annotations

from collections import defaultdict, deque
from dataclasses import dataclass
from typing import Iterable


@dataclass(frozen=True)
class CheckoutCountPhaseInvariantModel:
    """Domain-informed upper baseline for the checkout projection family.

    This baseline intentionally encodes the direct invariant
    ``p^n # c^n s # (pc)^n s``.  It is not presented as a learned general
    specification miner; it answers the reviewer-facing question of whether a
    simple count-and-phase rule already solves this particular projection.
    """

    training_words: tuple[str, ...]

    @classmethod
    def fit(cls, words: Iterable[str]) -> "CheckoutCountPhaseInvariantModel":
        training = tuple(dict.fromkeys(words))
        if not training:
            raise ValueError("at least one training word is required")
        model = cls(training)
        if not all(model.accepts(word) for word in training):
            raise ValueError("training data do not satisfy the checkout count/phase invariant")
        return model

    def accepts(self, word: str) -> bool:
        parts = word.split("#")
        if len(parts) != 3:
            return False
        product, currency, schedule = parts
        n = len(product)
        return (
            n >= 1
            and product == "p" * n
            and currency == "c" * n + "s"
            and schedule == "pc" * n + "s"
        )


@dataclass(frozen=True)
class KTailsAutomatonModel:
    """Positive-only k-tails state-merging automaton.

    Prefix-tree states with identical accepted suffixes of length at most ``k``
    are merged.  Merging can create nondeterminism, so recognition performs NFA
    reachability.  This is a compact, deterministic implementation intended as
    a directly relevant automaton baseline rather than a production miner.
    """

    k: int
    start_state: int
    accepting_states: frozenset[int]
    transitions: dict[tuple[int, str], frozenset[int]]
    state_count: int
    transition_count: int

    @classmethod
    def fit(cls, words: Iterable[str], k: int = 2) -> "KTailsAutomatonModel":
        if k < 0:
            raise ValueError("k must be nonnegative")
        training = tuple(dict.fromkeys(words))
        if not training:
            raise ValueError("at least one training word is required")

        prefixes: set[str] = {""}
        raw_transitions: dict[tuple[str, str], str] = {}
        accepting_prefixes: set[str] = set()
        for word in training:
            prefix = ""
            for symbol in word:
                next_prefix = prefix + symbol
                prefixes.add(next_prefix)
                raw_transitions[(prefix, symbol)] = next_prefix
                prefix = next_prefix
            accepting_prefixes.add(prefix)

        outgoing: dict[str, list[tuple[str, str]]] = defaultdict(list)
        for (source, symbol), target in raw_transitions.items():
            outgoing[source].append((symbol, target))

        def tails(state: str) -> frozenset[str]:
            found: set[str] = set()
            queue: deque[tuple[str, str]] = deque([(state, "")])
            visited: set[tuple[str, str]] = set()
            while queue:
                current, suffix = queue.popleft()
                marker = (current, suffix)
                if marker in visited:
                    continue
                visited.add(marker)
                if current in accepting_prefixes:
                    found.add(suffix)
                if len(suffix) == k:
                    continue
                for symbol, target in outgoing.get(current, ()):
                    queue.append((target, suffix + symbol))
            return frozenset(found)

        signatures = {state: tails(state) for state in prefixes}
        signature_to_group: dict[frozenset[str], int] = {}
        state_to_group: dict[str, int] = {}
        for state in sorted(prefixes, key=lambda value: (len(value), value)):
            signature = signatures[state]
            group = signature_to_group.setdefault(signature, len(signature_to_group))
            state_to_group[state] = group

        merged: dict[tuple[int, str], set[int]] = defaultdict(set)
        for (source, symbol), target in raw_transitions.items():
            merged[(state_to_group[source], symbol)].add(state_to_group[target])
        accepting_groups = frozenset(state_to_group[state] for state in accepting_prefixes)
        frozen_transitions = {key: frozenset(value) for key, value in merged.items()}
        return cls(
            k=k,
            start_state=state_to_group[""],
            accepting_states=accepting_groups,
            transitions=frozen_transitions,
            state_count=len(signature_to_group),
            transition_count=sum(len(value) for value in frozen_transitions.values()),
        )

    def accepts(self, word: str) -> bool:
        current = {self.start_state}
        for symbol in word:
            next_states: set[int] = set()
            for state in current:
                next_states.update(self.transitions.get((state, symbol), ()))
            if not next_states:
                return False
            current = next_states
        return bool(current & self.accepting_states)
