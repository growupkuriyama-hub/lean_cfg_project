from __future__ import annotations

from dataclasses import dataclass
from itertools import combinations, permutations
from typing import Iterable, Iterator


@dataclass(frozen=True)
class Context:
    """Concrete sentence context with one or two named holes.

    tokens alternate between terminal strings and integer hole identifiers.
    Example: ("", 0, "#", 1, "") denotes hole_0 # hole_1.
    """

    tokens: tuple[str | int, ...]
    arity: int

    def fill(self, components: tuple[str, ...]) -> str:
        if len(components) != self.arity:
            raise ValueError("component arity does not match context")
        pieces: list[str] = []
        for token in self.tokens:
            pieces.append(components[token] if isinstance(token, int) else token)
        return "".join(pieces)


@dataclass(frozen=True)
class Occurrence:
    word: str
    components: tuple[str, ...]
    context: Context
    intervals: tuple[tuple[int, int], ...]


def _structural_intervals(word: str) -> list[tuple[int, int]]:
    """A small trace-like interval basis for the first synthetic stage.

    Separator boundaries model lifeline/block boundaries.  Single letters are
    retained for lexical grounding.  This is deliberately smaller than the full
    cut enumeration used by the theoretical learner.
    """
    n = len(word)
    boundaries = {0, n}
    for index, symbol in enumerate(word):
        if symbol == "#":
            boundaries.add(index)
            boundaries.add(index + 1)
    ordered = sorted(boundaries)
    intervals = {(i, j) for i in ordered for j in ordered if i < j and "#" in word[i:j]}
    intervals.update((i, i + 1) for i in range(n))
    intervals.add((0, n))
    return sorted(intervals)


def _arity_one_occurrences(word: str, include_empty: bool) -> Iterator[Occurrence]:
    intervals = _structural_intervals(word)
    if include_empty:
        intervals = [*intervals, *((i, i) for i in range(len(word) + 1))]
    for i, j in intervals:
        component = word[i:j]
        context = Context((word[:i], 0, word[j:]), arity=1)
        yield Occurrence(word, (component,), context, ((i, j),))


def _arity_two_occurrences(word: str) -> Iterator[Occurrence]:
    intervals = [interval for interval in _structural_intervals(word) if "#" in word[interval[0]:interval[1]]]
    for (i1, j1), (i2, j2) in combinations(intervals, 2):
        if not (j1 <= i2 or j2 <= i1):
            continue
        ordered = sorted(((i1, j1, 0), (i2, j2, 1)), key=lambda x: (x[0], x[1]))
        (a, b, original_first), (c, d, original_second) = ordered
        base_components = (word[i1:j1], word[i2:j2])
        # Preserve both named-hole orders.  Named contexts may expose components
        # in a different order from their left-to-right positions.
        for swap in (False, True):
            components = base_components if not swap else (base_components[1], base_components[0])
            left_label = original_first if not swap else 1 - original_first
            right_label = original_second if not swap else 1 - original_second
            context = Context((word[:a], left_label, word[b:c], right_label, word[d:]), arity=2)
            intervals_out = ((i1, j1), (i2, j2)) if not swap else ((i2, j2), (i1, j1))
            yield Occurrence(word, components, context, intervals_out)



def _block_intervals(word: str) -> list[tuple[int, int]]:
    """Maximal non-separator blocks used by the fan-out-three trace basis."""
    result: list[tuple[int, int]] = []
    start = 0
    for index, symbol in enumerate(word):
        if symbol == "#":
            if start < index:
                result.append((start, index))
            start = index + 1
    if start < len(word):
        result.append((start, len(word)))
    return result


def _block_tuple_occurrences(word: str, arity: int) -> Iterator[Occurrence]:
    blocks = _block_intervals(word)
    for chosen_intervals in combinations(blocks, arity):
        for order in permutations(range(arity)):
            components = tuple(word[chosen_intervals[i][0]:chosen_intervals[i][1]] for i in order)
            label_for_position = {original_index: label for label, original_index in enumerate(order)}
            tokens: list[str | int] = []
            cursor = 0
            for original_index, (start, end) in enumerate(chosen_intervals):
                tokens.append(word[cursor:start])
                tokens.append(label_for_position[original_index])
                cursor = end
            tokens.append(word[cursor:])
            ordered_intervals = tuple(chosen_intervals[i] for i in order)
            yield Occurrence(word, components, Context(tuple(tokens), arity), ordered_intervals)

def enumerate_occurrences(
    words: Iterable[str],
    fanout: int = 2,
    include_empty_unary: bool = True,
) -> list[Occurrence]:
    if fanout not in (1, 2, 3):
        raise ValueError("prototype currently supports fanout 1, 2, or 3")
    result: list[Occurrence] = []
    for word in words:
        result.extend(_arity_one_occurrences(word, include_empty=include_empty_unary))
        if fanout >= 2:
            result.extend(_arity_two_occurrences(word))
        if fanout >= 3:
            # Add whole-block tuples. This trace-oriented basis exposes the
            # synchronized service lifelines without enumerating every triple
            # of arbitrary substrings.
            result.extend(_block_tuple_occurrences(word, 2))
            result.extend(_block_tuple_occurrences(word, 3))
    return result
