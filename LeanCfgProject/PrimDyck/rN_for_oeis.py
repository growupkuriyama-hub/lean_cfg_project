#!/usr/bin/env python3
"""
Generate OEIS submission data for the sequence

    a(n) = r(2n),  n = 1, 2, 3, ...

where r(N) (N a positive even integer) is the least number of positive
primitive Dyck numbers (OEIS A057547) needed to sum to N, as studied in

    T. Kuriyama, "Additive Representations by Primitive Dyck Numbers",
    J. Integer Seq. (to appear).

This reuses the same first-principles construction as
verify_certificates.py: primitive Dyck words are enumerated directly
(no reliance on the paper's closed-form structural results), and r(N)
is computed by an unbounded "coin problem" dynamic program.

Output:
  * OEIS-style DATA line (first NUM_DATA terms, comma-separated).
  * A b-file (b0.txt) with one "n a(n)" pair per line, suitable for
    upload as the b-file of a new OEIS entry.
"""

# ---------------------------------------------------------------------
# 1. Primitive Dyck numbers (A057547), enumerated directly.
# ---------------------------------------------------------------------

def dyck_words(n):
    """All Dyck words with n opening and n closing symbols."""
    out = []
    def rec(s, opens, closes):
        if len(s) == 2 * n:
            out.append(s)
            return
        if opens < n:
            rec(s + '1', opens + 1, closes)
        if closes < opens:
            rec(s + '0', opens, closes + 1)
    rec('', 0, 0)
    return out

def primitive_dyck_numbers_upto(bound):
    """All primitive Dyck numbers <= bound (values of 1u0 in base 2)."""
    vals = set()
    inner = 0
    while True:
        # shortest primitive word with this many inner pairs has value
        # >= 2^(2*inner+1) (leading '1' at that many bits), so stop once
        # that minimum exceeds bound.
        if (1 << (2 * inner + 1)) > bound:
            break
        for u in dyck_words(inner):
            v = int('1' + u + '0', 2)
            if v <= bound:
                vals.add(v)
        inner += 1
    return vals

# ---------------------------------------------------------------------
# 2. r(N) via unbounded coin-problem dynamic programming.
# ---------------------------------------------------------------------

def compute_r(bound):
    """r[N] = min number of primitive Dyck numbers (with repetition)
       summing to N, for 0 <= N <= bound.  r[0] = 0 (empty sum)."""
    parts = sorted(primitive_dyck_numbers_upto(bound))
    INF = float('inf')
    r = [INF] * (bound + 1)
    r[0] = 0
    for n in range(1, bound + 1):
        best = INF
        for p in parts:
            if p > n:
                break
            if r[n - p] + 1 < best:
                best = r[n - p] + 1
        r[n] = best
    return r

# ---------------------------------------------------------------------
# 3. Produce OEIS DATA line and b-file for a(n) = r(2n).
# ---------------------------------------------------------------------

NUM_TERMS = 300          # terms in the b-file: a(1) .. a(NUM_TERMS)
NUM_DATA  = 40            # terms shown in the OEIS "DATA" field

BOUND = 2 * NUM_TERMS
r = compute_r(BOUND)

a = [r[2 * n] for n in range(1, NUM_TERMS + 1)]   # a(n) = r(2n)

print("OFFSET 1")
print("NAME: a(n) = r(2n), the least number of positive primitive Dyck")
print("      numbers (A057547) that sum to 2n.")
print()
print("DATA line (first {} terms):".format(NUM_DATA))
print(",".join(str(x) for x in a[:NUM_DATA]))
print()

with open("/home/claude/b_rN.txt", "w") as f:
    for n, val in enumerate(a, start=1):
        f.write(f"{n} {val}\n")
print(f"b-file written: b_rN.txt  (a(1) .. a({NUM_TERMS}))")

# Sanity spot-check against the paper's Theorem: a(23)=r(46)=8,
# a(17)=r(34)=7, a(22)=r(44)=7, a(423)=r(846)=7  (423 > NUM_TERMS, so
# only check the ones within range).
checks = {23: 8, 17: 7, 22: 7, 49: 7, 77: 7, 99: 7, 101: 7, 103: 7}
print("\nSpot checks against Theorem 1 (n : a(n) expected):")
for n, expected in checks.items():
    if n <= NUM_TERMS:
        got = a[n - 1]
        status = "OK" if got == expected else "MISMATCH"
        print(f"  n={n:4d}  N=2n={2*n:4d}  a(n)={got}  expected={expected}  [{status}]")
