#!/usr/bin/env python3
"""Generate odd and even graph certificates from the folded-NFA specification."""
from __future__ import annotations

from collections import deque
from functools import lru_cache
from pathlib import Path
import folded_nfa as nfa

TYPES = nfa.ODD_TYPES
MARKERS = (4, 3, 2, 1, 0)


def accepting_odd(tagged_state) -> bool:
    _, state = tagged_state
    prev, groups, lower_carry, upper_carry, middle_carry = state
    return (
        all(not prefix and not sequence for prefix, sequence in groups)
        and lower_carry == middle_carry
        and upper_carry + prev == 1
    )


def accepting_even_frame(tagged_state) -> bool:
    _, state = tagged_state
    prev, groups, lower_carry, upper_carry, middle_carry = state
    return (
        all(not prefix and not sequence for prefix, sequence in groups)
        and lower_carry == middle_carry
        and upper_carry + prev == 0
    )


def export(path: Path, header: str, accepting) -> None:
    initial = {
        (type_index, state)
        for type_index, counts in enumerate(TYPES)
        for state in nfa.initial_states(counts)
    }

    @lru_cache(maxsize=None)
    def transition(tagged_state, marker, symbol):
        type_index, state = tagged_state
        return tuple(
            (type_index, successor)
            for successor in nfa.step_state(
                state, TYPES[type_index], marker, symbol
            )
        )

    interior = set(initial)
    queue = deque(initial)
    while queue:
        state = queue.popleft()
        for symbol in range(4):
            for successor in transition(state, None, symbol):
                if successor not in interior:
                    interior.add(successor)
                    queue.append(successor)

    phases = [interior]
    for marker in MARKERS:
        next_phase = set()
        for state in phases[-1]:
            for symbol in range(4):
                next_phase.update(transition(state, marker, symbol))
        phases.append(next_phase)

    lists = [sorted(phase, key=repr) for phase in phases]
    indices = [
        {state: index for index, state in enumerate(states)}
        for states in lists
    ]

    with path.open('w', encoding='utf-8') as handle:
        handle.write(header + '\n')
        handle.write('SIZES ' + ' '.join(str(len(states)) for states in lists) + '\n')
        handle.write(
            'INITIAL '
            + ' '.join(str(indices[0][state]) for state in sorted(initial, key=repr))
            + '\n'
        )
        handle.write(
            'ACCEPT '
            + ' '.join(
                str(index)
                for index, state in enumerate(lists[-1])
                if accepting(state)
            )
            + '\n'
        )
        handle.write('TRANS INTERIOR\n')
        for state in lists[0]:
            fields = []
            for symbol in range(4):
                ids = sorted(
                    indices[0][successor]
                    for successor in transition(state, None, symbol)
                )
                fields.append(','.join(map(str, ids)) if ids else '-')
            handle.write('|'.join(fields) + '\n')

        for phase_index, marker in enumerate(MARKERS):
            handle.write(f'TRANS {marker}\n')
            for state in lists[phase_index]:
                fields = []
                for symbol in range(4):
                    ids = sorted(
                        indices[phase_index + 1][successor]
                        for successor in transition(state, marker, symbol)
                    )
                    fields.append(','.join(map(str, ids)) if ids else '-')
                handle.write('|'.join(fields) + '\n')

    print(
        f'{path.name}: sizes={[len(states) for states in lists]}, '
        f'initial={len(initial)}, '
        f'accept={sum(accepting(state) for state in lists[-1])}'
    )


def main() -> None:
    base = Path(__file__).resolve().parent
    export(base / 'odd_graph.txt', 'ODD_GENERALIZED_GRAPH_V1', accepting_odd)
    export(
        base / 'even_graph.txt',
        'EVEN_VIA_ODD_FRAME_GRAPH_V1',
        accepting_even_frame,
    )


if __name__ == '__main__':
    main()
