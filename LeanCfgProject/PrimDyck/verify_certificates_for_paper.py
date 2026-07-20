#!/usr/bin/env python3
"""
Verification program for
    "Additive Representations by Primitive Dyck Numbers"
    (Takayuki Kuriyama)

This script independently checks every finite computation on which the
paper relies, in particular:

  * Lemma "finite-five"        (the five interval inclusions in 5P)
  * Lemma "finite-exception"   (F_5(L), 1+F_3(L), 2+F_1(L) and the
                                exceptional complement in [0,211])
  * Proposition "fiveP"        ([212,inf) subset F_5(P); 209,210,211 not)
  * Theorem "main"             (the full exceptional set and r(N))

CONVENTIONS (answering the referee's likely questions).

  * kX  = { x_1 + ... + x_k : x_i in X }  -- sums of EXACTLY k elements,
          WITH REPETITION allowed (x_i need not be distinct).
  * F_k(X) = union_{j=0}^{k} jX          -- sums of AT MOST k elements.
  * 0X = {0} (the empty sum).
  * An "interval [a,b]" always means the integer interval {a,a+1,...,b}.

All sumsets are computed exhaustively as finite integer sets (dynamic
programming), never from a closed-form interval guess; the interval
descriptions printed in the paper are then verified against these
exhaustively computed sets.
"""

from functools import lru_cache

# ---------------------------------------------------------------------------
# 1. Primitive Dyck numbers, computed from first principles.
#    A primitive Dyck word is 1 u 0 with u any Dyck word.  We enumerate them
#    by length and record their base-2 values, so that L, H, P etc. below are
#    checked against the actual set N_pD rather than assumed.
# ---------------------------------------------------------------------------

def dyck_words(n):
    """All Dyck words with n opening and n closing symbols (as '1'/'0' strings)."""
    out = []
    def rec(s, height, opens, closes):
        if len(s) == 2 * n:
            out.append(s)
            return
        if opens < n:                      # place a '1'
            rec(s + '1', height + 1, opens + 1, closes)
        if closes < opens:                 # place a '0'
            rec(s + '0', height - 1, opens, closes + 1)
    rec('', 0, 0, 0)
    return out

def primitive_dyck_numbers(max_pairs):
    """Set of integer values [w]_2 for primitive Dyck words 1u0 with
       |1u0| <= 2*max_pairs."""
    vals = set()
    for inner in range(0, max_pairs):      # u has 'inner' pairs; word length 2(inner+1)
        for u in dyck_words(inner):
            vals.add(int('1' + u + '0', 2))
    return vals

# Enumerate far past every constant used in the paper (max value here is huge).
NPD = primitive_dyck_numbers(12)           # includes all primitive Dyck numbers < 4*10^6
P   = {v // 4 for v in NPD if v >= 12}     # P = { v/4 : v in N_pD, v >= 12 }

# ---------------------------------------------------------------------------
# 2. Exact sumset machinery (exhaustive, repetition allowed).
# ---------------------------------------------------------------------------

def kX(X, k, cap):
    """{ sums of EXACTLY k elements of X (with repetition) } intersect [0,cap]."""
    cur = {0}
    Xc = sorted(x for x in X if x <= cap)
    for _ in range(k):
        nxt = set()
        for s in cur:
            for x in Xc:
                t = s + x
                if t <= cap:
                    nxt.add(t)
        cur = nxt
    return cur

def F(X, k, cap):
    """F_k(X) = sums of AT MOST k elements of X, intersect [0,cap]."""
    res = {0}
    cur = {0}
    Xc = sorted(x for x in X if x <= cap)
    for _ in range(k):
        nxt = set()
        for s in cur:
            for x in Xc:
                t = s + x
                if t <= cap:
                    nxt.add(t)
        cur = nxt
        res |= cur
    return res

def sumset(A, B, cap):
    """A + B intersect [0,cap]."""
    return {a + b for a in A for b in B if a + b <= cap}

def contains_interval(S, a, b):
    """True iff [a,b] subset S."""
    return all(x in S for x in range(a, b + 1))

def as_intervals(S):
    """Represent finite integer set S as a sorted list of maximal [a,b] blocks."""
    xs = sorted(S)
    if not xs:
        return []
    blocks, start, prev = [], xs[0], xs[0]
    for x in xs[1:]:
        if x == prev + 1:
            prev = x
        else:
            blocks.append((start, prev))
            start = prev = x
    blocks.append((start, prev))
    return blocks

# ---------------------------------------------------------------------------
# 3. The finite sets named in the paper.
# ---------------------------------------------------------------------------

L = {3, 13, 14, 53, 54, 57, 58, 60}
H = {213, 214, 217, 218, 220, 229, 230, 233, 234, 236, 241, 242, 244, 248}

def check(name, condition):
    print(f"[{'OK ' if condition else 'FAIL'}] {name}")
    assert condition, name

print("=== Membership: L, H really lie in P ===")
check("L subset P", L <= P)
check("H subset P", H <= P)

print("\n=== Lemma finite-five: five interval inclusions in 5P ===")
CAP = 1100
fiveL   = kX(L, 5, CAP)
H_4L    = sumset(H,        kX(L, 4, CAP), CAP)
H2_3L   = sumset(kX(H,2,CAP), kX(L, 3, CAP), CAP)
H3_2L   = sumset(kX(H,3,CAP), kX(L, 2, CAP), CAP)
H4_L    = sumset(kX(H,4,CAP), L, CAP)
check("[215,254]  subset 5L",     contains_interval(fiveL, 215, 254))
check("[245,486]  subset H+4L",   contains_interval(H_4L, 245, 486))
check("[439,674]  subset 2H+3L",  contains_interval(H2_3L, 439, 674))
check("[645,862]  subset 3H+2L",  contains_interval(H3_2L, 645, 862))
check("[855,1046] subset 4H+L",   contains_interval(H4_L, 855, 1046))
# Every listed sumset uses EXACTLY 5 elements of P (5=5, 1+4, 2+3, 3+2, 4+1),
# so their union lies in 5P; overlap gives the stated corollary.
union5P = fiveL | H_4L | H2_3L | H3_2L | H4_L
check("[215,1046] subset 5P (overlap of the five)",
      contains_interval(union5P, 215, 1046))

print("\n=== Proposition fiveP: [212,inf) subset F_5(P), and 209,210,211 excluded ===")
# Sharpness at the low end, checked exhaustively against F_5(P) up to 214.
F5P_small = F(P, 5, 300)
check("212 in F_5(P)", 212 in F5P_small)
check("213 in F_5(P)", 213 in F5P_small)
check("214 in F_5(P)", 214 in F5P_small)
check("209 not in F_5(P)", 209 not in F5P_small)
check("210 not in F_5(P)", 210 not in F5P_small)
check("211 not in F_5(P)", 211 not in F5P_small)

print("\n=== Lemma finite-exception: F_5(L), and the criterion complement in [0,211] ===")
F5L = F(L, 5, 211)
paper_F5L = (
    {0, 3, 6, 9}
    | set(range(12, 18)) | {19, 20} | {22, 23}
    | set(range(25, 38)) | set(range(39, 49)) | set(range(52, 209))
)
check("F_5(L) cap [0,211] matches the paper's interval list",
      F5L == paper_F5L)

criterion = F(L, 5, 211) \
          | {1 + x for x in F(L, 3, 211) if 1 + x <= 211} \
          | {2 + x for x in F(L, 1, 211) if 2 + x <= 211}
criterion &= set(range(0, 212))
paper_criterion = (
    set(range(0, 8)) | {9, 10} | set(range(12, 24))
    | set(range(25, 38)) | set(range(39, 49)) | set(range(52, 209))
)
check("[0,211] cap (F5L u (1+F3L) u (2+F1L)) matches paper",
      criterion == paper_criterion)

complement = sorted(set(range(0, 212)) - criterion)
check("complement in [0,211] = {8,11,24,38,49,50,51,209,210,211}",
      complement == [8, 11, 24, 38, 49, 50, 51, 209, 210, 211])
print("    complement =", complement)
print("    => N = 4m+2 for these m:", [4 * m + 2 for m in complement])

# ---------------------------------------------------------------------------
# 4. Independent brute force of r(N): the whole theorem, no structure assumed.
#    r(N) = fewest primitive Dyck numbers (with repetition) summing to N.
# ---------------------------------------------------------------------------
print("\n=== Theorem main: brute-force r(N) for even N (coin-problem DP) ===")
BOUND = 2000
parts = sorted(v for v in NPD if 0 < v <= BOUND)
INF = float('inf')
r = [INF] * (BOUND + 1)
r[0] = 0
for n in range(1, BOUND + 1):
    best = INF
    for p in parts:
        if p > n:
            break
        if r[n - p] + 1 < best:
            best = r[n - p] + 1
    r[n] = best

need7 = [n for n in range(2, BOUND + 1, 2) if r[n] == 7]
need8 = [n for n in range(2, BOUND + 1, 2) if r[n] == 8]
need_more = [n for n in range(2, BOUND + 1, 2) if r[n] > 8]
check("r(46) = 8", r[46] == 8)
check("exactly the ten N with r=7", need7 ==
      [34, 44, 98, 154, 198, 202, 206, 838, 842, 846])
check("no even N with r>8", need_more == [])
check("every even N in [848,2000] has r<=6",
      all(r[n] <= 6 for n in range(848, BOUND + 1, 2)))
print("    r=7 at:", need7)
print("    r=8 at:", need8)

print("\nAll checks passed.")
