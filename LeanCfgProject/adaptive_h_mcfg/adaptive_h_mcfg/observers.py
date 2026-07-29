from __future__ import annotations

from abc import ABC, abstractmethod
from dataclasses import dataclass
from typing import Hashable, Iterable, Mapping, Sequence


class Observer(ABC):
    """A finite monoid observation h: Sigma* -> M.

    The prototype only needs equality and a stable printable name.  Each
    implementation is homomorphic by construction.
    """

    name: str

    @abstractmethod
    def value(self, word: str) -> Hashable:
        raise NotImplementedError

    def tuple_type(self, components: Sequence[str]) -> tuple[Hashable, ...]:
        return tuple(self.value(component) for component in components)


@dataclass(frozen=True)
class TrivialObserver(Observer):
    name: str = "trivial"

    def value(self, word: str) -> int:
        return 0


@dataclass(frozen=True)
class ModularCountObserver(Observer):
    symbols: tuple[str, ...]
    modulus: int
    name: str

    def __init__(self, symbols: Iterable[str], modulus: int, name: str | None = None):
        symbols_tuple = tuple(symbols)
        if modulus < 2:
            raise ValueError("modulus must be at least 2")
        object.__setattr__(self, "symbols", symbols_tuple)
        object.__setattr__(self, "modulus", modulus)
        object.__setattr__(
            self,
            "name",
            name or f"count_{{{''.join(symbols_tuple)}}}_mod_{modulus}",
        )

    def value(self, word: str) -> tuple[int, ...]:
        return tuple(word.count(symbol) % self.modulus for symbol in self.symbols)


@dataclass(frozen=True)
class ProductObserver(Observer):
    factors: tuple[Observer, ...]
    name: str

    def __init__(self, factors: Iterable[Observer]):
        factors_tuple = tuple(factors)
        object.__setattr__(self, "factors", factors_tuple)
        object.__setattr__(
            self,
            "name",
            "trivial" if not factors_tuple else " x ".join(f.name for f in factors_tuple),
        )

    def value(self, word: str) -> tuple[Hashable, ...]:
        return tuple(factor.value(word) for factor in self.factors)


@dataclass(frozen=True)
class DFATransitionObserver(Observer):
    """Transition-monoid observer induced by an explicit complete DFA.

    h(w) is the transformation q |-> delta*(q, w), represented as a tuple in
    the fixed state ordering.  Composition of transformations is the monoid
    operation, so this is an explicit finite-monoid homomorphism.
    """

    states: tuple[int, ...]
    alphabet: tuple[str, ...]
    transition: Mapping[tuple[int, str], int]
    name: str

    def value(self, word: str) -> tuple[int, ...]:
        result: list[int] = []
        for start in self.states:
            state = start
            for symbol in word:
                try:
                    state = self.transition[(state, symbol)]
                except KeyError as exc:
                    raise ValueError(f"symbol {symbol!r} is outside the DFA alphabet") from exc
            result.append(state)
        return tuple(result)


def parallel_envelope_observer() -> DFATransitionObserver:
    """Transition observer for the regular envelope a+#b+#c+#d+.

    State 8 is a dead state.  Acceptance is irrelevant here: the full transition
    action, not only the start-state result, is the observed monoid element.
    """

    alphabet = ("a", "b", "c", "d", "#")
    states = tuple(range(9))
    dead = 8
    transition: dict[tuple[int, str], int] = {}

    for q in states:
        for symbol in alphabet:
            transition[(q, symbol)] = dead
    for symbol in alphabet:
        transition[(dead, symbol)] = dead

    transition[(0, "a")] = 1
    transition[(1, "a")] = 1
    transition[(1, "#")] = 2
    transition[(2, "b")] = 3
    transition[(3, "b")] = 3
    transition[(3, "#")] = 4
    transition[(4, "c")] = 5
    transition[(5, "c")] = 5
    transition[(5, "#")] = 6
    transition[(6, "d")] = 7
    transition[(7, "d")] = 7

    return DFATransitionObserver(
        states=states,
        alphabet=alphabet,
        transition=transition,
        name="dfa[a+#b+#c+#d+]",
    )


def block_envelope_observer(
    block_alphabets: Sequence[Iterable[str]],
    separator: str = "#",
    allow_empty: bool = False,
    name: str | None = None,
) -> DFATransitionObserver:
    """Transition observer for A_1^+ # ... # A_k^+.

    Each ``A_i`` is the finite token set observed on one service lifeline.  The
    full transition action is used, so the result is a finite-monoid observer,
    not merely an acceptance predicate.
    """
    blocks = tuple(frozenset(alphabet) for alphabet in block_alphabets)
    if not blocks or any(not block for block in blocks):
        raise ValueError("every block alphabet must be nonempty")
    if any(separator in block for block in blocks):
        raise ValueError("separator cannot be a block token")
    alphabet = tuple(sorted(set().union(*blocks) | {separator}))

    # For block i, state 2i expects its first token and state 2i+1 is inside it.
    dead = 2 * len(blocks)
    states = tuple(range(dead + 1))
    transition: dict[tuple[int, str], int] = {
        (state, symbol): dead for state in states for symbol in alphabet
    }
    for symbol in alphabet:
        transition[(dead, symbol)] = dead

    for index, block in enumerate(blocks):
        expect = 2 * index
        inside = expect + 1
        for token in block:
            transition[(expect, token)] = inside
            transition[(inside, token)] = inside
        if index + 1 < len(blocks):
            next_expect = 2 * (index + 1)
            transition[(inside, separator)] = next_expect
            if allow_empty:
                transition[(expect, separator)] = next_expect

    label = name or "lifeline-envelope[" + ",".join(str(len(block)) for block in blocks) + "]"
    return DFATransitionObserver(states, alphabet, transition, label)


def alternating_phase_observer(
    start_tokens: Iterable[str],
    end_tokens: Iterable[str],
    alphabet: Iterable[str],
    name: str,
) -> DFATransitionObserver:
    """Observe whether selected START/END tokens alternate without nesting.

    Other alphabet symbols are ignored.  This is intentionally a small atomic
    observer; it is useful for sequential service-local spans and acts as a
    decoy or selected phase guard depending on the route.
    """
    starts = frozenset(start_tokens)
    ends = frozenset(end_tokens)
    alphabet_tuple = tuple(sorted(set(alphabet)))
    if starts & ends:
        raise ValueError("start and end token sets must be disjoint")
    states = (0, 1, 2)  # balanced, open, dead
    transition: dict[tuple[int, str], int] = {}
    for state in states:
        for symbol in alphabet_tuple:
            transition[(state, symbol)] = state if state != 2 else 2
    for token in starts:
        transition[(0, token)] = 1
        transition[(1, token)] = 2
    for token in ends:
        transition[(0, token)] = 2
        transition[(1, token)] = 0
    return DFATransitionObserver(states, alphabet_tuple, transition, name)
