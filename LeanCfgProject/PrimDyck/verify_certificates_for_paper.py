#!/usr/bin/env python3
"""Verify the finite certificates and finite-range cross-checks used in

    Takayuki Kuriyama,
    "Additive Representations by Primitive Dyck Numbers" (v6).

The script checks the finite ingredients used in the paper while keeping all
infinite-range arguments separate.  In particular, it verifies:

* the base-4/Motzkin description of P on the finite ranges used below;
* the two finite certificates for the regular family E;
* the finite seed for the five-summand tail of P;
* the sharp low-end exclusions 209, 210, 211 not in F_5(P);
* the small-multiple certificate below 100;
* the complete exceptional-set certificate on [0, 211];
* finite instances of the recurrent obstructions;
* the first 50 terms of OEIS A395858; and
* an independent dynamic-programming computation of r(N).

Conventions
-----------
For a finite set X of nonnegative integers,

    kX     = {x_1 + ... + x_k : x_i in X},
    F_k(X) = union_{j=0}^k jX,

where repetition is allowed and 0X = {0}.  Intervals [a,b] are integer
intervals.  All certificate sumsets are constructed exhaustively as finite
sets using only exact integer arithmetic.

The infinite conclusions in the paper are *not* established by finite search:
they follow from the digit-lifting lemma, generation bounds, and recurrent
obstruction arguments in the text.  This program only reproduces the finite
certificates and provides independent finite-range cross-checks.

This program uses only the Python standard library.
"""

from __future__ import annotations

from argparse import ArgumentParser
from dataclasses import dataclass
import json
from pathlib import Path
from typing import Iterable, Sequence


# ---------------------------------------------------------------------------
# Basic combinatorial constructions
# ---------------------------------------------------------------------------


def dyck_words(n: int) -> list[str]:
    """Return all Dyck words with n opening and n closing symbols."""
    if n < 0:
        raise ValueError("n must be nonnegative")

    out: list[str] = []

    def rec(prefix: str, opens: int, closes: int) -> None:
        if len(prefix) == 2 * n:
            out.append(prefix)
            return
        if opens < n:
            rec(prefix + "1", opens + 1, closes)
        if closes < opens:
            rec(prefix + "0", opens, closes + 1)

    rec("", 0, 0)
    return out


def primitive_dyck_numbers_upto(bound: int) -> set[int]:
    """Return all positive primitive Dyck numbers not exceeding bound.

    Every primitive Dyck word is uniquely of the form 1u0, where u is a
    (possibly empty) Dyck word.
    """
    if bound < 0:
        raise ValueError("bound must be nonnegative")

    values: set[int] = set()
    inner_pairs = 0
    while (1 << (2 * inner_pairs + 1)) <= bound:
        for middle in dyck_words(inner_pairs):
            value = int("1" + middle + "0", 2)
            if value <= bound:
                values.add(value)
        inner_pairs += 1
    return values


def p_from_primitive_numbers(
    primitive_numbers: Iterable[int], cap: int
) -> set[int]:
    """Return P intersected with [0, cap] from primitive Dyck numbers."""
    return {
        value // 4
        for value in primitive_numbers
        if 12 <= value <= 4 * cap and value % 4 == 0
    }


def p_from_motzkin_upto(cap: int) -> set[int]:
    """Return P intersected with [0, cap] from the base-4 Motzkin model.

    P consists of base-4 words 3w, where w is a two-coloured Motzkin word
    with digit weights sigma(3)=1, sigma(0)=-1, sigma(1)=sigma(2)=0.
    """
    if cap < 0:
        raise ValueError("cap must be nonnegative")

    values: set[int] = set()
    suffix_length = 0
    while 3 * (4**suffix_length) <= cap:
        place_values = [4 ** (suffix_length - 1 - i) for i in range(suffix_length)]

        def rec(position: int, height: int, suffix_value: int) -> None:
            remaining = suffix_length - position
            if height > remaining:
                return  # not enough positions remain to return to height 0
            if position == suffix_length:
                if height == 0:
                    value = 3 * (4**suffix_length) + suffix_value
                    if value <= cap:
                        values.add(value)
                return

            place = place_values[position]
            # Deterministic digit order keeps witness/debug output stable.
            rec(position + 1, height + 1, suffix_value + 3 * place)
            rec(position + 1, height, suffix_value + place)
            rec(position + 1, height, suffix_value + 2 * place)
            if height > 0:
                rec(position + 1, height - 1, suffix_value)

        rec(0, 0, 0)
        suffix_length += 1

    return values


def regular_e_positive_upto(cap: int) -> set[int]:
    """Return E^+ intersected with [0, cap].

    E^+ is the regular base-4 family 3{1,2}^*.  It is generated from 3 by
    repeatedly applying x -> 4x+1 and x -> 4x+2.
    """
    if cap < 0:
        raise ValueError("cap must be nonnegative")

    values: set[int] = set()
    frontier = [3] if cap >= 3 else []
    while frontier:
        value = frontier.pop()
        if value in values or value > cap:
            continue
        values.add(value)
        for child in (4 * value + 1, 4 * value + 2):
            if child <= cap:
                frontier.append(child)
    return values


def interval(a: int, b: int) -> set[int]:
    """Return the integer interval [a,b], or the empty set when a>b."""
    return set(range(a, b + 1)) if a <= b else set()


def sumset(left: Iterable[int], right: Iterable[int], cap: int) -> set[int]:
    """Return (left + right) intersected with [0, cap]."""
    left_values = tuple(sorted(x for x in left if 0 <= x <= cap))
    right_values = tuple(sorted(x for x in right if 0 <= x <= cap))
    return {
        a + b
        for a in left_values
        for b in right_values
        if a + b <= cap
    }


def kx(values: Iterable[int], k: int, cap: int) -> set[int]:
    """Return kX intersected with [0, cap], with repetition allowed."""
    if k < 0:
        raise ValueError("k must be nonnegative")
    usable = tuple(sorted(x for x in values if 0 <= x <= cap))
    current = {0}
    for _ in range(k):
        current = sumset(current, usable, cap)
    return current


def fk(values: Iterable[int], k: int, cap: int) -> set[int]:
    """Return F_k(X) intersected with [0, cap]."""
    if k < 0:
        raise ValueError("k must be nonnegative")
    usable = tuple(sorted(x for x in values if 0 <= x <= cap))
    result = {0}
    current = {0}
    for _ in range(k):
        current = sumset(current, usable, cap)
        result.update(current)
    return result


def mixed_sumset(groups: Sequence[Iterable[int]], cap: int) -> set[int]:
    """Return the sumset obtained by choosing one element from each group."""
    current = {0}
    for group in groups:
        current = sumset(current, group, cap)
    return current


# ---------------------------------------------------------------------------
# Witness construction for optional machine-readable certificates
# ---------------------------------------------------------------------------


def mixed_sumset_witnesses(
    groups: Sequence[Iterable[int]], cap: int
) -> dict[int, tuple[int, ...]]:
    """Return one deterministic witness tuple for every attainable sum."""
    current: dict[int, tuple[int, ...]] = {0: ()}
    for group in groups:
        usable = tuple(sorted(x for x in group if 0 <= x <= cap))
        next_map: dict[int, tuple[int, ...]] = {}
        for subtotal in sorted(current):
            witness = current[subtotal]
            for value in usable:
                total = subtotal + value
                if total > cap:
                    break
                candidate = tuple(sorted(witness + (value,)))
                previous = next_map.get(total)
                if previous is None or candidate < previous:
                    next_map[total] = candidate
        current = next_map
    return current


def fk_witnesses(
    values: Iterable[int], k: int, cap: int
) -> dict[int, tuple[int, ...]]:
    """Return one witness using at most k terms for every sum in F_k(X)."""
    usable = tuple(sorted(x for x in values if 0 <= x <= cap))
    best: dict[int, tuple[int, ...]] = {0: ()}
    exact: dict[int, tuple[int, ...]] = {0: ()}
    for _ in range(k):
        next_exact: dict[int, tuple[int, ...]] = {}
        for subtotal in sorted(exact):
            witness = exact[subtotal]
            for value in usable:
                total = subtotal + value
                if total > cap:
                    break
                candidate = tuple(sorted(witness + (value,)))
                previous = next_exact.get(total)
                if previous is None or candidate < previous:
                    next_exact[total] = candidate
        exact = next_exact
        for total, candidate in exact.items():
            previous = best.get(total)
            if (
                previous is None
                or len(candidate) < len(previous)
                or (len(candidate) == len(previous) and candidate < previous)
            ):
                best[total] = candidate
    return best


# ---------------------------------------------------------------------------
# Checks and reporting
# ---------------------------------------------------------------------------


class CertificateError(AssertionError):
    """Raised when a finite certificate check fails."""


def pass_message(name: str) -> None:
    print(f"PASS: {name}")


def check_true(name: str, condition: bool, detail: str | None = None) -> None:
    if not condition:
        message = name if detail is None else f"{name}: {detail}"
        print(f"FAIL: {message}")
        raise CertificateError(message)
    pass_message(name)


def check_equal(name: str, actual: object, expected: object) -> None:
    if actual != expected:
        detail = f"expected {expected!r}, got {actual!r}"
        print(f"FAIL: {name}: {detail}")
        raise CertificateError(f"{name}: {detail}")
    pass_message(name)


def check_subset(name: str, required: set[int], actual: set[int]) -> None:
    missing = sorted(required - actual)
    if missing:
        preview = missing[:20]
        suffix = " ..." if len(missing) > len(preview) else ""
        detail = f"missing {preview}{suffix} ({len(missing)} total)"
        print(f"FAIL: {name}: {detail}")
        raise CertificateError(f"{name}: {detail}")
    pass_message(name)


def check_disjoint(name: str, left: set[int], right: set[int]) -> None:
    intersection = sorted(left & right)
    if intersection:
        detail = f"unexpected intersection {intersection[:20]}"
        print(f"FAIL: {name}: {detail}")
        raise CertificateError(f"{name}: {detail}")
    pass_message(name)


@dataclass(frozen=True)
class IntervalCertificate:
    """A finite interval inclusion and the groups forming its sumset."""

    name: str
    lower: int
    upper: int
    groups: tuple[frozenset[int], ...]

    def attainable(self, cap: int) -> set[int]:
        return mixed_sumset(self.groups, cap)

    def witnesses(self) -> dict[int, tuple[int, ...]]:
        return mixed_sumset_witnesses(self.groups, self.upper)

    def verify(self, cap: int) -> set[int]:
        attainable = self.attainable(cap)
        check_subset(
            f"[{self.lower},{self.upper}] is contained in {self.name}",
            interval(self.lower, self.upper),
            attainable,
        )
        return attainable


# ---------------------------------------------------------------------------
# Independent r(N) computation and criterion checks
# ---------------------------------------------------------------------------


def compute_r(bound: int, primitive_numbers: Iterable[int]) -> list[int]:
    """Compute r(N) for 0 <= N <= bound by exact unbounded coin-change DP.

    All positive primitive Dyck numbers are even, so the computation is scaled
    by a factor of 2.  Odd entries are left at infinity.
    """
    if bound < 0:
        raise ValueError("bound must be nonnegative")

    scaled_bound = bound // 2
    parts = sorted({p // 2 for p in primitive_numbers if 0 < p <= bound})
    infinity = bound + 1
    scaled_r = [infinity] * (scaled_bound + 1)
    scaled_r[0] = 0

    for n in range(1, scaled_bound + 1):
        best = infinity
        for part in parts:
            if part > n:
                break
            candidate = scaled_r[n - part] + 1
            if candidate < best:
                best = candidate
        scaled_r[n] = best

    r = [infinity] * (bound + 1)
    for n, value in enumerate(scaled_r):
        r[2 * n] = value
    return r


def mod4_criterion_values(
    p_values: Iterable[int], epsilon: int, h: int, m_cap: int
) -> set[int]:
    """Compute the m-values in the general mod-4 criterion up to m_cap."""
    if epsilon not in (0, 1):
        raise ValueError("epsilon must be 0 or 1")
    if h < 0 or m_cap < 0:
        raise ValueError("h and m_cap must be nonnegative")

    p_values = set(p_values)
    result: set[int] = set()
    for s in range(h + 1):
        if s % 2 != epsilon:
            continue
        shift = (s - epsilon) // 2
        if shift > m_cap:
            continue
        result.update(
            shift + value
            for value in fk(p_values, h - s, m_cap - shift)
            if shift + value <= m_cap
        )
    return result


# ---------------------------------------------------------------------------
# Main verification routine
# ---------------------------------------------------------------------------


def verify(
    theorem_check_bound: int,
    obstruction_k_max: int,
    witness_output: Path | None,
    skip_dp: bool,
) -> None:
    if theorem_check_bound < 848:
        raise ValueError("--bound must be at least 848")
    if obstruction_k_max < 2:
        raise ValueError("--obstruction-k-max must be at least 2")

    certificate_cap = 1100
    max_x = 10 * (4**obstruction_k_max) - 2
    primitive_bound = max(
        theorem_check_bound,
        4 * certificate_cap,
        4 * max_x,
    )

    print("Generating primitive Dyck numbers ...")
    primitive_numbers = primitive_dyck_numbers_upto(primitive_bound)
    p_values = p_from_primitive_numbers(
        primitive_numbers, max(certificate_cap, max_x, theorem_check_bound // 4)
    )

    # ------------------------------------------------------------------
    # Structural finite-range cross-checks
    # ------------------------------------------------------------------
    structural_cap = max(certificate_cap, max_x)
    p_motzkin = p_from_motzkin_upto(structural_cap)
    p_primitive_structural = {
        p for p in p_values if p <= structural_cap
    }
    check_equal(
        f"P from primitive Dyck words equals P from Motzkin words on [0,{structural_cap}]",
        p_primitive_structural,
        p_motzkin,
    )

    e_positive = regular_e_positive_upto(certificate_cap)
    check_subset("E^+ is contained in P on the certificate range", e_positive, p_values)
    check_true(
        "finite E^+ digit-closure check",
        all(
            4 * value + digit in e_positive
            for value in e_positive
            for digit in (1, 2)
            if 4 * value + digit <= certificate_cap
        ),
    )
    check_true(
        "finite P digit-closure check",
        all(
            4 * value + digit in p_motzkin
            for value in p_motzkin
            for digit in (1, 2)
            if 4 * value + digit <= structural_cap
        ),
    )

    max_generation = 0
    while 4 ** (max_generation + 1) - 2**max_generation <= structural_cap:
        max_generation += 1
    for d in range(1, max_generation + 1):
        generation = {
            p for p in p_motzkin if 4 ** (d - 1) <= p < 4**d
        }
        g_d = 3 * 4 ** (d - 1) + (4 ** (d - 1) - 1) // 3
        u_d = 4**d - 2 ** (d - 1)
        check_equal(f"generation {d} minimum", min(generation), g_d)
        check_equal(f"generation {d} maximum", max(generation), u_d)

    # ------------------------------------------------------------------
    # v6 regular-family certificates
    # ------------------------------------------------------------------
    a0 = frozenset({0, 3, 13, 14})
    b = frozenset({53, 54, 57, 58})
    a = frozenset({3, 13, 14, 53, 54, 57, 58})
    c = frozenset({213, 214, 217, 218, 229, 230, 233, 234})

    check_subset("A_0 is contained in E", set(a0), e_positive | {0})
    check_subset("A is contained in E^+", set(a), e_positive)
    check_subset("B is contained in E^+", set(b), e_positive)
    check_subset("C is contained in E^+", set(c), e_positive)

    e_small_certificates = (
        IntervalCertificate("6A_0", 25, 62, (a0,) * 6),
        IntervalCertificate("B+5A_0", 56, 128, (b,) + (a0,) * 5),
        IntervalCertificate("2B+4A_0", 106, 172, (b,) * 2 + (a0,) * 4),
        IntervalCertificate("3B+3A_0", 159, 216, (b,) * 3 + (a0,) * 3),
        IntervalCertificate("4B+2A_0", 212, 260, (b,) * 4 + (a0,) * 2),
    )
    e_tail_certificates = (
        IntervalCertificate("6A", 218, 260, (a,) * 6),
        IntervalCertificate("C+5A", 258, 524, (c,) + (a,) * 5),
        IntervalCertificate("2C+4A", 446, 700, (c,) * 2 + (a,) * 4),
        IntervalCertificate("3C+3A", 648, 876, (c,) * 3 + (a,) * 3),
        IntervalCertificate("4C+2A", 858, 1052, (c,) * 4 + (a,) * 2),
    )

    e_small_union: set[int] = set()
    for certificate in e_small_certificates:
        e_small_union.update(certificate.verify(certificate_cap))
    check_subset(
        "the regular-family small certificates cover [25,217]",
        interval(25, 217),
        e_small_union,
    )

    e_tail_union: set[int] = set()
    for certificate in e_tail_certificates:
        e_tail_union.update(certificate.verify(certificate_cap))
    check_subset(
        "the regular-family tail certificates cover [218,877]",
        interval(218, 877),
        e_tail_union,
    )

    e_all = e_positive | {0}
    check_subset(
        "direct check: [25,217] is contained in 6E",
        interval(25, 217),
        kx(e_all, 6, 217),
    )
    check_subset(
        "direct check: [218,877] is contained in 6E^+",
        interval(218, 877),
        kx(e_positive, 6, 877),
    )

    # ------------------------------------------------------------------
    # P certificates and sharp lower endpoint
    # ------------------------------------------------------------------
    low = frozenset({3, 13, 14, 53, 54, 57, 58, 60})
    high = frozenset(
        {213, 214, 217, 218, 220, 229, 230, 233, 234, 236, 241, 242, 244, 248}
    )
    check_subset("L is contained in P", set(low), p_values)
    check_subset("H is contained in P", set(high), p_values)
    check_equal("P intersect [0,211] equals L", p_values & interval(0, 211), set(low))

    p_certificates = (
        IntervalCertificate("5L", 215, 254, (low,) * 5),
        IntervalCertificate("H+4L", 245, 486, (high,) + (low,) * 4),
        IntervalCertificate("2H+3L", 439, 674, (high,) * 2 + (low,) * 3),
        IntervalCertificate("3H+2L", 645, 862, (high,) * 3 + (low,) * 2),
        IntervalCertificate("4H+L", 855, 1046, (high,) * 4 + (low,)),
    )

    p_seed_union: set[int] = set()
    for certificate in p_certificates:
        p_seed_union.update(certificate.verify(certificate_cap))
    check_subset(
        "the five P-certificates cover [215,1046]",
        interval(215, 1046),
        p_seed_union,
    )
    check_subset(
        "the finite seed required for tail propagation is [215,864]",
        interval(215, 864),
        p_seed_union,
    )

    f5_low = fk(low, 5, 211)
    check_disjoint(
        "209, 210, and 211 do not belong to F_5(L)",
        {209, 210, 211},
        f5_low,
    )
    f5_p_small = fk(p_values, 5, 300)
    check_subset(
        "212, 213, and 214 belong to F_5(P)",
        {212, 213, 214},
        f5_p_small,
    )
    check_true(
        "the displayed four-term representations of 212, 213, and 214 are valid",
        212 == 53 + 53 + 53 + 53
        and 213 == 53 + 53 + 53 + 54
        and 214 == 53 + 53 + 54 + 54,
    )

    # ------------------------------------------------------------------
    # Small multiples and complete exceptional-set certificate
    # ------------------------------------------------------------------
    primitive_below_100 = {p for p in primitive_numbers if 0 < p < 100}
    check_equal(
        "the positive primitive Dyck numbers below 100",
        primitive_below_100,
        {2, 12, 52, 56},
    )
    f6_small_primitive = fk(primitive_below_100, 6, 99)
    positive_multiples_of_four = set(range(4, 100, 4))
    missing_small_multiples = positive_multiples_of_four - f6_small_primitive
    check_equal(
        "44 is the only positive multiple of 4 below 100 outside F_6(N_pD)",
        missing_small_multiples,
        {44},
    )
    check_true(
        "the displayed seven-term representation of 44 is valid",
        44 == 12 + 12 + 12 + 2 + 2 + 2 + 2,
    )

    criterion = (
        fk(low, 5, 211)
        | {1 + x for x in fk(low, 3, 210)}
        | {2 + x for x in fk(low, 1, 209)}
    ) & interval(0, 211)
    expected_complement = {8, 11, 24, 38, 49, 50, 51, 209, 210, 211}
    actual_complement = interval(0, 211) - criterion
    check_equal(
        "the finite exceptional m-set is the stated ten-element set",
        actual_complement,
        expected_complement,
    )
    corresponding_n = {4 * m + 2 for m in actual_complement}
    check_equal(
        "the corresponding N=4m+2 values",
        corresponding_n,
        {34, 46, 98, 154, 198, 202, 206, 838, 842, 846},
    )

    # ------------------------------------------------------------------
    # Recurrent obstructions (finite instances)
    # ------------------------------------------------------------------
    p_for_obstructions = {p for p in p_values if p <= max_x}
    f2_obstruction = fk(p_for_obstructions, 2, max_x)
    f4_obstruction = fk(p_for_obstructions, 4, max_x)
    for k in range(2, obstruction_k_max + 1):
        x_k = 10 * (4**k) - 2
        check_true(
            f"obstruction k={k}: x_k is not in F_4(P)",
            x_k not in f4_obstruction,
        )
        check_true(
            f"obstruction k={k}: x_k-1 is not in F_2(P)",
            x_k - 1 not in f2_obstruction,
        )

    # ------------------------------------------------------------------
    # Optional witness certificate output
    # ------------------------------------------------------------------
    if witness_output is not None:
        witness_document: dict[str, object] = {
            "paper": "Additive Representations by Primitive Dyck Numbers",
            "version": "v6",
            "conventions": {
                "exact_sumset": "one element is chosen from each listed group",
                "intervals": "inclusive integer intervals",
            },
            "certificates": {},
        }
        output_certificates: dict[str, object] = {}
        for certificate in (
            *e_small_certificates,
            *e_tail_certificates,
            *p_certificates,
        ):
            witnesses = certificate.witnesses()
            required = interval(certificate.lower, certificate.upper)
            missing = required - witnesses.keys()
            if missing:
                raise CertificateError(
                    f"cannot write witnesses for {certificate.name}; missing {sorted(missing)[:10]}"
                )
            output_certificates[certificate.name] = {
                "interval": [certificate.lower, certificate.upper],
                "witnesses": {
                    str(total): list(witnesses[total])
                    for total in range(certificate.lower, certificate.upper + 1)
                },
            }
        witness_document["certificates"] = output_certificates

        f5_witness_map = fk_witnesses(low, 5, 211)
        witness_document["sharp_lower_endpoint"] = {
            "excluded": [209, 210, 211],
            "verified_absent_from_F5L": all(
                value not in f5_witness_map for value in (209, 210, 211)
            ),
        }
        witness_document["finite_exceptional_m_values"] = sorted(actual_complement)
        witness_document["finite_exceptional_N_values"] = sorted(corresponding_n)

        witness_output.parent.mkdir(parents=True, exist_ok=True)
        witness_output.write_text(
            json.dumps(witness_document, indent=2, sort_keys=True),
            encoding="utf-8",
        )
        pass_message(f"wrote witness certificate to {witness_output}")

    # ------------------------------------------------------------------
    # Independent dynamic-programming checks
    # ------------------------------------------------------------------
    if not skip_dp:
        print(f"Computing r(N) independently through N={theorem_check_bound} ...")
        primitive_for_r = {p for p in primitive_numbers if p <= theorem_check_bound}
        r = compute_r(theorem_check_bound, primitive_for_r)

        expected_first_50 = [
            1, 2, 3, 4, 5, 1, 2, 3, 4, 5,
            6, 2, 3, 4, 5, 6, 7, 3, 4, 5,
            6, 7, 8, 4, 5, 1, 2, 1, 2, 3,
            4, 2, 3, 2, 3, 4, 5, 3, 4, 3,
            4, 5, 6, 4, 5, 4, 5, 6, 7, 5,
        ]
        actual_first_50 = [r[2 * n] for n in range(1, 51)]
        check_equal("the first 50 terms of A395858", actual_first_50, expected_first_50)

        expected_r7_all = [34, 44, 98, 154, 198, 202, 206, 838, 842, 846]
        expected_r7 = [n for n in expected_r7_all if n <= theorem_check_bound]
        actual_r7 = [
            n for n in range(2, theorem_check_bound + 1, 2) if r[n] == 7
        ]
        actual_r8 = [
            n for n in range(2, theorem_check_bound + 1, 2) if r[n] == 8
        ]
        actual_over8 = [
            n for n in range(2, theorem_check_bound + 1, 2) if r[n] > 8
        ]

        check_equal("r(46)", r[46], 8)
        check_equal(
            "the r=7 values in the checked range",
            actual_r7,
            expected_r7,
        )
        check_equal("the r=8 values in the checked range", actual_r8, [46])
        check_equal("no checked even N has r(N)>8", actual_over8, [])
        check_true(
            f"every checked even N in [848,{theorem_check_bound}] has r(N)<=6",
            all(r[n] <= 6 for n in range(848, theorem_check_bound + 1, 2)),
        )

        # Cross-check the general mod-4 criterion for h=5 and h=6.
        m_cap = theorem_check_bound // 4
        p_for_criteria = {p for p in p_values if p <= m_cap}
        criterion_h6 = mod4_criterion_values(p_for_criteria, 1, 6, m_cap)
        criterion_h5 = mod4_criterion_values(p_for_criteria, 1, 5, m_cap)
        criterion_h4_even = mod4_criterion_values(p_for_criteria, 0, 4, m_cap)

        mismatches_h6: list[int] = []
        mismatches_h5: list[int] = []
        mismatches_h4_even: list[int] = []
        for n in range(2, theorem_check_bound + 1, 2):
            if n % 4 == 2:
                m = (n - 2) // 4
                if (r[n] <= 6) != (m in criterion_h6):
                    mismatches_h6.append(n)
                if m >= 3 and (r[n] <= 5) != (m in criterion_h5):
                    mismatches_h5.append(n)
            else:
                m = n // 4
                if (r[n] <= 4) != (m in criterion_h4_even):
                    mismatches_h4_even.append(n)

        check_equal("the h=6 mod-4 criterion mismatch set", mismatches_h6, [])
        check_equal("the h=5 mod-4 criterion mismatch set", mismatches_h5, [])
        check_equal(
            "the h=4 criterion mismatch set for multiples of 4",
            mismatches_h4_even,
            [],
        )
        pass_message(
            f"general mod-4 criteria agree with r(N) through {theorem_check_bound}"
        )

        for k in range(2, obstruction_k_max + 1):
            n6 = 10 * (4 ** (k + 1)) - 6
            if n6 <= theorem_check_bound:
                check_equal(f"r(10*4^({k}+1)-6)", r[n6], 6)
        for k in range(3, obstruction_k_max + 1):
            n5 = 10 * (4 ** (k + 1)) - 8
            if n5 <= theorem_check_bound:
                check_equal(f"r(10*4^({k}+1)-8)", r[n5], 5)

        print("PASS: finite-range r(N) cross-check gives")
        print(f"      r(N)=7 at {actual_r7}")
        print(f"      r(N)=8 at {actual_r8}")

    print("PASS: all v6 certificates verified")


def main() -> None:
    parser = ArgumentParser(description=__doc__)
    parser.add_argument(
        "--bound",
        type=int,
        default=50_000,
        help=(
            "upper bound for the independent finite-range check of r(N) "
            "(default: 50000)"
        ),
    )
    parser.add_argument(
        "--obstruction-k-max",
        type=int,
        default=5,
        help=(
            "largest k for the finite recurrent-obstruction and exact-order "
            "cross-checks (default: 5)"
        ),
    )
    parser.add_argument(
        "--write-witnesses",
        type=Path,
        default=None,
        metavar="PATH",
        help=(
            "optionally write one explicit summand witness for every integer "
            "in each finite interval certificate as JSON"
        ),
    )
    parser.add_argument(
        "--skip-dp",
        action="store_true",
        help="skip the independent dynamic-programming computation of r(N)",
    )
    args = parser.parse_args()

    verify(
        theorem_check_bound=args.bound,
        obstruction_k_max=args.obstruction_k_max,
        witness_output=args.write_witnesses,
        skip_dp=args.skip_dp,
    )


if __name__ == "__main__":
    main()
