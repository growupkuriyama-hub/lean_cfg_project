from __future__ import annotations

from typing import Iterable


def parallel_word(n: int) -> str:
    if n < 1:
        raise ValueError("n must be positive")
    return "a" * n + "#" + "b" * n + "#" + "c" * n + "#" + "d" * n


def parallel_mutants(n: int) -> list[str]:
    """Count, order, and cross-block splice mutations.

    The splice family is important: a coarse untyped tuple substitution can
    preserve global length while moving a service-local fragment across a
    lifeline boundary.
    """
    if n < 2:
        n = 2
    variants = []
    blocks = ["a" * n, "b" * n, "c" * n, "d" * n]
    for index, symbol in enumerate("abcd"):
        longer = blocks.copy()
        longer[index] = symbol * (n + 1)
        variants.append("#".join(longer))
        shorter = blocks.copy()
        shorter[index] = symbol * (n - 1)
        variants.append("#".join(shorter))
    variants.append("a" * n + "#" + "c" * n + "#" + "b" * n + "#" + "d" * n)

    # Cross-block splice mutations inspired by the actual overgeneralizations
    # produced by the trivial observer in the restricted tuple learner.
    variants.extend(
        [
            "a" * n + "#" + "b" + "#" + "c" * n + "b" * (n - 1) + "#" + "d" * n,
            "a" * n + "#" + "b" * (n - 1) + "#" + "c" * n + "b" + "#" + "d" * n,
            "a" * n + "#" + "c" + "b" * n + "#" + "c" * (n - 1) + "#" + "d" * n,
            "a" * n + "#" + "c" * (n - 1) + "b" * n + "#" + "c" + "#" + "d" * n,
        ]
    )
    return variants


def unique(items: Iterable[str]) -> list[str]:
    return list(dict.fromkeys(items))


def transfer_mutant(n: int, source: int, target: int, position: str) -> str:
    """Move one service-local symbol from one lifeline block to another.

    ``source`` and ``target`` are block indices in ``a,b,c,d``.  The operation
    preserves total length and separator count, so simple global-count and
    route-length checks cannot detect it.
    """
    if n < 2:
        raise ValueError("n must be at least 2")
    if source not in range(4) or target not in range(4) or source == target:
        raise ValueError("source and target must be distinct block indices 0..3")
    if position not in {"prefix", "middle", "suffix"}:
        raise ValueError("position must be prefix, middle, or suffix")

    symbols = "abcd"
    blocks = [symbol * n for symbol in symbols]
    moved = symbols[source]
    blocks[source] = blocks[source][:-1]
    insertion = {
        "prefix": 0,
        "middle": len(blocks[target]) // 2,
        "suffix": len(blocks[target]),
    }[position]
    blocks[target] = blocks[target][:insertion] + moved + blocks[target][insertion:]
    return "#".join(blocks)


def parallel_selection_mutants(n: int) -> list[str]:
    """Mutants available to the outer observer-selection loop.

    The diagnostic cross-lifeline operator moves a ``b`` event to the suffix of
    the ``c`` lifeline.  The inverse transfer is deliberately withheld for the
    unseen-mutation test.
    """
    base = parallel_mutants(n)[:9]  # count changes and block-order violation
    base.append(transfer_mutant(n, source=1, target=2, position="suffix"))
    return unique(base)


def parallel_unseen_mutants(n: int) -> list[str]:
    """Held-out mutation family not used for observer selection.

    It reverses the diagnostic transfer: a ``c`` event is moved to the prefix
    of the ``b`` lifeline.  The event direction, target position, and test
    length are therefore all unseen during selection.
    """
    return [transfer_mutant(n, source=2, target=1, position="prefix")]


def _encoded_blocks(word: str, separator: str = "#") -> list[str]:
    blocks = word.split(separator)
    if len(blocks) < 2:
        raise ValueError("encoded lifeline word must contain at least two blocks")
    return blocks


def encoded_omission(word: str, block: int, position: int = -1, separator: str = "#") -> str:
    blocks = _encoded_blocks(word, separator)
    if block not in range(len(blocks)) or not blocks[block]:
        raise ValueError("invalid or empty source block")
    index = position if position >= 0 else len(blocks[block]) - 1
    if index not in range(len(blocks[block])):
        raise ValueError("position outside source block")
    blocks[block] = blocks[block][:index] + blocks[block][index + 1:]
    return separator.join(blocks)


def encoded_duplication(word: str, block: int, position: int = -1, separator: str = "#") -> str:
    blocks = _encoded_blocks(word, separator)
    if block not in range(len(blocks)) or not blocks[block]:
        raise ValueError("invalid or empty source block")
    index = position if position >= 0 else len(blocks[block]) - 1
    token = blocks[block][index]
    blocks[block] = blocks[block][:index + 1] + token + blocks[block][index + 1:]
    return separator.join(blocks)


def encoded_adjacent_swap(word: str, block: int, position: int = 0, separator: str = "#") -> str:
    blocks = _encoded_blocks(word, separator)
    if block not in range(len(blocks)) or len(blocks[block]) < 2:
        raise ValueError("source block needs at least two tokens")
    if position not in range(len(blocks[block]) - 1):
        raise ValueError("swap position outside source block")
    chars = list(blocks[block])
    chars[position], chars[position + 1] = chars[position + 1], chars[position]
    blocks[block] = "".join(chars)
    return separator.join(blocks)


def encoded_transfer(
    word: str,
    source: int,
    target: int,
    source_position: int = -1,
    target_position: str = "suffix",
    separator: str = "#",
) -> str:
    blocks = _encoded_blocks(word, separator)
    if source not in range(len(blocks)) or target not in range(len(blocks)) or source == target:
        raise ValueError("source and target must be distinct valid block indices")
    if not blocks[source]:
        raise ValueError("source block is empty")
    index = source_position if source_position >= 0 else len(blocks[source]) - 1
    token = blocks[source][index]
    blocks[source] = blocks[source][:index] + blocks[source][index + 1:]
    insertion = {
        "prefix": 0,
        "middle": len(blocks[target]) // 2,
        "suffix": len(blocks[target]),
    }.get(target_position)
    if insertion is None:
        raise ValueError("target_position must be prefix, middle, or suffix")
    blocks[target] = blocks[target][:insertion] + token + blocks[target][insertion:]
    return separator.join(blocks)


def encoded_selection_mutants(words: Iterable[str], separator: str = "#") -> list[str]:
    """Mutations exposed to observer selection.

    Uses local omission/duplication/order corruption plus one directed
    cross-lifeline transfer.  Duplicates and accidental identities are removed.
    """
    output: list[str] = []
    for word in words:
        blocks = _encoded_blocks(word, separator)
        for index, block in enumerate(blocks):
            if block:
                output.append(encoded_omission(word, index, separator=separator))
                output.append(encoded_duplication(word, index, separator=separator))
            if len(block) >= 2:
                output.append(encoded_adjacent_swap(word, index, 0, separator))
        if len(blocks) >= 2:
            source = max(0, len(blocks) // 2 - 1)
            target = min(len(blocks) - 1, source + 1)
            if blocks[source]:
                output.append(encoded_transfer(word, source, target, -1, "suffix", separator))
    return [mutant for mutant in unique(output) if mutant not in set(words)]


def encoded_unseen_mutants(words: Iterable[str], separator: str = "#") -> list[str]:
    """Held-out inverse transfers, unseen in the selection loop."""
    output: list[str] = []
    for word in words:
        blocks = _encoded_blocks(word, separator)
        if len(blocks) >= 2:
            target = max(0, len(blocks) // 2 - 1)
            source = min(len(blocks) - 1, target + 1)
            if blocks[source]:
                output.append(encoded_transfer(word, source, target, 0, "prefix", separator))
    return [mutant for mutant in unique(output) if mutant not in set(words)]
