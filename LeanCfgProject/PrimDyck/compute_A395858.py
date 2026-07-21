#!/usr/bin/env python3
"""Generate terms and a b-file for OEIS A395858.

A395858 is the sequence a(n)=r(2n), n>=1, where r(N) is the least
number of positive primitive Dyck numbers (OEIS A057547) whose sum is N.
Primitive Dyck words are enumerated directly, and r(N) is computed by
unbounded coin-change dynamic programming.

This program uses only the Python standard library.
"""

from __future__ import annotations

from argparse import ArgumentParser
from pathlib import Path


def dyck_words(n: int) -> list[str]:
    """Return all Dyck words with n opening and n closing symbols."""
    out: list[str] = []

    def rec(s: str, opens: int, closes: int) -> None:
        if len(s) == 2 * n:
            out.append(s)
            return
        if opens < n:
            rec(s + "1", opens + 1, closes)
        if closes < opens:
            rec(s + "0", opens, closes + 1)

    rec("", 0, 0)
    return out


def primitive_dyck_numbers_upto(bound: int) -> set[int]:
    """Return all positive primitive Dyck numbers not exceeding bound."""
    values: set[int] = set()
    inner_pairs = 0
    while (1 << (2 * inner_pairs + 1)) <= bound:
        for middle in dyck_words(inner_pairs):
            value = int("1" + middle + "0", 2)
            if value <= bound:
                values.add(value)
        inner_pairs += 1
    return values


def compute_r(bound: int) -> list[int]:
    """Compute r(N) for 0<=N<=bound by unbounded coin-change DP."""
    parts = sorted(primitive_dyck_numbers_upto(bound))
    infinity = bound + 1
    r = [infinity] * (bound + 1)
    r[0] = 0
    for n in range(1, bound + 1):
        r[n] = min((r[n - p] + 1 for p in parts if p <= n), default=infinity)
    return r


def main(num_terms: int, num_data: int, output: Path) -> None:
    if num_terms < 423:
        raise ValueError("--terms must be at least 423 to include all exceptional indices")
    if not 1 <= num_data <= num_terms:
        raise ValueError("--data must satisfy 1 <= --data <= --terms")

    r = compute_r(2 * num_terms)
    sequence = [r[2 * n] for n in range(1, num_terms + 1)]

    print("OEIS A395858")
    print("OFFSET 1")
    print("a(n)=r(2n), the least number of positive primitive Dyck numbers")
    print("(A057547) whose sum is 2n.")
    print(f"\nFirst {num_data} terms:")
    print(",".join(str(value) for value in sequence[:num_data]))

    output.write_text(
        "".join(f"{n} {value}\n" for n, value in enumerate(sequence, start=1)),
        encoding="ascii",
    )
    print(f"\nb-file written to: {output.resolve()}")

    expected = {
        17: 7, 22: 7, 23: 8, 49: 7, 77: 7,
        99: 7, 101: 7, 103: 7, 419: 7, 421: 7, 423: 7,
    }
    print("\nChecks at all indices corresponding to r(N)>=7:")
    for n, expected_value in expected.items():
        actual = sequence[n - 1]
        status = "OK" if actual == expected_value else "MISMATCH"
        print(f"  n={n:3d}, N={2*n:3d}, a(n)={actual}, expected={expected_value} [{status}]")
        if actual != expected_value:
            raise AssertionError(f"A395858 check failed at n={n}")

    print("\nAll checks passed.")


if __name__ == "__main__":
    parser = ArgumentParser(description=__doc__)
    parser.add_argument("--terms", type=int, default=500,
                        help="number of terms to generate (default: 500; minimum: 423)")
    parser.add_argument("--data", type=int, default=40,
                        help="number of terms printed as a DATA line (default: 40)")
    parser.add_argument("--output", type=Path, default=Path("b395858.txt"),
                        help="b-file path (default: ./b395858.txt)")
    args = parser.parse_args()
    main(args.terms, args.data, args.output)
