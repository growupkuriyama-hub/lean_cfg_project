#!/usr/bin/env python3
"""Reproduce the finite computations in

    Takayuki Kuriyama,
    "Additive Representations by Primitive Dyck Numbers".

The script checks the finite certificates used in the paper:

* the five interval inclusions in the finite interval certificate;
* the low-end checks for the five-summand proposition;
* the finite exceptional-set certificate on [0, 211]; and
* a direct dynamic-programming cross-check of r(N) on a finite range.

Conventions
-----------
For a finite set X of nonnegative integers,

    kX     = {x_1 + ... + x_k : x_i in X},
    F_k(X) = union_{j=0}^k jX,

where repetition is allowed and 0X = {0}.  Intervals [a,b] are integer
intervals.  All sumsets below are constructed exhaustively as finite sets.

This program uses only the Python standard library.
"""

from __future__ import annotations

from argparse import ArgumentParser
from typing import Iterable, Set


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


def kx(values: Iterable[int], k: int, cap: int) -> set[int]:
    """Return kX intersected with [0, cap], with repetition allowed."""
    current = {0}
    usable = sorted(x for x in values if 0 <= x <= cap)
    for _ in range(k):
        current = {
            subtotal + x
            for subtotal in current
            for x in usable
            if subtotal + x <= cap
        }
    return current


def fk(values: Iterable[int], k: int, cap: int) -> set[int]:
    """Return F_k(X) intersected with [0, cap]."""
    result = {0}
    current = {0}
    usable = sorted(x for x in values if 0 <= x <= cap)
    for _ in range(k):
        current = {
            subtotal + x
            for subtotal in current
            for x in usable
            if subtotal + x <= cap
        }
        result.update(current)
    return result


def sumset(left: Iterable[int], right: Iterable[int], cap: int) -> set[int]:
    """Return (left + right) intersected with [0, cap]."""
    return {a + b for a in left for b in right if a + b <= cap}


def interval(a: int, b: int) -> set[int]:
    return set(range(a, b + 1))


def check(name: str, condition: bool) -> None:
    """Print a concise certificate result and stop immediately on failure."""
    if condition:
        print(f"PASS: {name}")
        return
    print(f"FAIL: {name}")
    raise AssertionError(name)


def compute_r(bound: int, primitive_numbers: Iterable[int]) -> list[int]:
    """Compute r(N) for 0 <= N <= bound by unbounded coin-change DP."""
    parts = sorted(p for p in primitive_numbers if 0 < p <= bound)
    infinity = bound + 1
    r = [infinity] * (bound + 1)
    r[0] = 0
    for n in range(1, bound + 1):
        r[n] = min((r[n - p] + 1 for p in parts if p <= n), default=infinity)
    return r


def main(theorem_check_bound: int) -> None:
    if theorem_check_bound < 848:
        raise ValueError("--bound must be at least 848")

    # P = {v/4 : v is a primitive Dyck number and v >= 12}.
    # The finite sumset checks only use elements of P at most 1100, so
    # primitive Dyck numbers through 4400 suffice for this part.
    certificate_cap = 1100
    primitive_for_certificates = primitive_dyck_numbers_upto(4 * certificate_cap)
    p_set = {v // 4 for v in primitive_for_certificates if v >= 12}

    low = {3, 13, 14, 53, 54, 57, 58, 60}
    high = {213, 214, 217, 218, 220, 229, 230, 233, 234, 236,
            241, 242, 244, 248}
    check("L is contained in P", low <= p_set)
    check("H is contained in P", high <= p_set)
    check("P intersect [0,211] equals L", (p_set & interval(0, 211)) == low)
    five_low = kx(low, 5, certificate_cap)
    high_plus_4low = sumset(high, kx(low, 4, certificate_cap), certificate_cap)
    two_high_plus_3low = sumset(
        kx(high, 2, certificate_cap), kx(low, 3, certificate_cap), certificate_cap
    )
    three_high_plus_2low = sumset(
        kx(high, 3, certificate_cap), kx(low, 2, certificate_cap), certificate_cap
    )
    four_high_plus_low = sumset(kx(high, 4, certificate_cap), low, certificate_cap)

    check("[215,254] is contained in 5L", interval(215, 254) <= five_low)
    check("[245,486] is contained in H+4L", interval(245, 486) <= high_plus_4low)
    check("[439,674] is contained in 2H+3L", interval(439, 674) <= two_high_plus_3low)
    check("[645,862] is contained in 3H+2L", interval(645, 862) <= three_high_plus_2low)
    check("[855,1046] is contained in 4H+L", interval(855, 1046) <= four_high_plus_low)

    finite_union = (
        five_low
        | high_plus_4low
        | two_high_plus_3low
        | three_high_plus_2low
        | four_high_plus_low
    )
    check("[215,1046] is covered by the five finite sumsets",
          interval(215, 1046) <= finite_union)
    f5p_small = fk(p_set, 5, 300)
    check("212, 213, and 214 belong to F_5(P)", {212, 213, 214} <= f5p_small)
    check("209, 210, and 211 do not belong to F_5(P)",
          {209, 210, 211}.isdisjoint(f5p_small))
    f5_low = fk(low, 5, 211)
    paper_f5_low = (
        {0, 3, 6, 9}
        | interval(12, 17)
        | {19, 20, 22, 23}
        | interval(25, 37)
        | interval(39, 48)
        | interval(52, 208)
    )
    check("F_5(L) matches the interval certificate in the paper", f5_low == paper_f5_low)

    criterion = (
        fk(low, 5, 211)
        | {1 + x for x in fk(low, 3, 211) if 1 + x <= 211}
        | {2 + x for x in fk(low, 1, 211) if 2 + x <= 211}
    ) & interval(0, 211)

    paper_criterion = (
        interval(0, 7)
        | {9, 10}
        | interval(12, 23)
        | interval(25, 37)
        | interval(39, 48)
        | interval(52, 208)
    )
    check("the six-summand criterion matches the paper", criterion == paper_criterion)

    expected_complement = {8, 11, 24, 38, 49, 50, 51, 209, 210, 211}
    actual_complement = interval(0, 211) - criterion
    check("the complement is the stated ten-element set",
          actual_complement == expected_complement)
    print("PASS: exceptional m-values are")
    print(f"      {sorted(actual_complement)}")
    print("PASS: corresponding N=4m+2 values are")
    print(f"      {sorted(4 * m + 2 for m in actual_complement)}")
    primitive_for_r = primitive_dyck_numbers_upto(theorem_check_bound)
    r = compute_r(theorem_check_bound, primitive_for_r)

    expected_r7 = [34, 44, 98, 154, 198, 202, 206, 838, 842, 846]
    actual_r7 = [n for n in range(2, theorem_check_bound + 1, 2) if r[n] == 7]
    actual_r8 = [n for n in range(2, theorem_check_bound + 1, 2) if r[n] == 8]
    actual_over8 = [n for n in range(2, theorem_check_bound + 1, 2) if r[n] > 8]

    check("r(46)=8", r[46] == 8)
    check("the r=7 values in the checked range are exactly the stated ten",
          actual_r7 == expected_r7)
    check("46 is the only r=8 value in the checked range", actual_r8 == [46])
    check("no checked even N has r(N)>8", not actual_over8)
    check(f"every checked even N in [848,{theorem_check_bound}] has r(N)<=6",
          all(r[n] <= 6 for n in range(848, theorem_check_bound + 1, 2)))

    print("PASS: finite-range r(N) cross-check gives")
    print(f"      r(N)=7 at {actual_r7}")
    print(f"      r(N)=8 at {actual_r8}")
    print("PASS: all certificates verified")


if __name__ == "__main__":
    parser = ArgumentParser(description=__doc__)
    parser.add_argument(
        "--bound",
        type=int,
        default=2000,
        help="upper bound for the independent finite-range check of r(N) (default: 2000)",
    )
    args = parser.parse_args()
    main(args.bound)
