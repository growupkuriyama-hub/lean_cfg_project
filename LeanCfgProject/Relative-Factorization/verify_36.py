#!/usr/bin/env python3
"""Reproducible verifier for the 36-element UF--FRP witness.

Standard-library only.  The construction and theorem-facing checks match
Appendix A of `Relative_Prime_Factorization_arXiv_v8`.

Usage:
    python3 verify_36.py --json certificate_36.json

The program reconstructs the 64-element transformation monoid M0, forms the
least monoid congruence identifying h0(ab) and h0(abaaab), verifies the 36-
element quotient claims, checks exact fiber-product factorization by regular-
language equivalence, constructs the prime-avoidance lasso, audits every
proper monoid-congruence quotient, and writes a deterministic JSON certificate.
"""

from __future__ import annotations

import argparse
import json
from collections import defaultdict, deque
from pathlib import Path

ALPHABET = ("a", "b")
Q0 = (0, 1, 2, 3)
IDENTITY_T = (0, 1, 2, 3)
TAU_A = (1, 2, 0, 0)
TAU_B = (1, 3, 1, 0)
EXPECTED_PRIME_WORDS = (
    "a", "b", "ab", "ba", "aba", "baa", "bab", "aaab", "abaa",
    "abab", "baaa", "baba", "aaaba", "babaa", "aaabaa",
)
EXPECTED_PROPER_QUOTIENT_SIZES = (
    11, 9, 8, 7, 7, 6, 6, 5, 5, 5, 4, 4, 4, 3, 3, 2, 2, 2, 1,
)


def compose(f, g):
    """Transformation product f*g: first apply f, then g.

    Thus h(uv)=h(u)*h(v) when words are scanned left-to-right.
    """
    return tuple(g[f[i]] for i in Q0)


def eval_word_transformation(word):
    x = IDENTITY_T
    for ch in word:
        x = compose(x, TAU_A if ch == "a" else TAU_B)
    return x


def generate_transformation_monoid():
    seen = {IDENTITY_T}
    queue = deque([IDENTITY_T])
    while queue:
        x = queue.popleft()
        for g in (TAU_A, TAU_B):
            y = compose(x, g)
            if y not in seen:
                seen.add(y)
                queue.append(y)
    return sorted(seen)


class UnionFind:
    def __init__(self, n):
        self.parent = list(range(n))
        self.rank = [0] * n

    def find(self, x):
        while self.parent[x] != x:
            self.parent[x] = self.parent[self.parent[x]]
            x = self.parent[x]
        return x

    def union(self, a, b):
        a, b = self.find(a), self.find(b)
        if a == b:
            return False
        if self.rank[a] < self.rank[b]:
            a, b = b, a
        self.parent[b] = a
        if self.rank[a] == self.rank[b]:
            self.rank[a] += 1
        return True


def normalize_partition_from_uf(uf, n):
    groups = defaultdict(list)
    for i in range(n):
        groups[uf.find(i)].append(i)
    blocks = sorted((sorted(v) for v in groups.values()), key=lambda b: b[0])
    labels = [None] * n
    for label, block in enumerate(blocks):
        for x in block:
            labels[x] = label
    return tuple(labels), tuple(tuple(b) for b in blocks)


def blocks_from_labels(labels):
    groups = defaultdict(list)
    for i, label in enumerate(labels):
        groups[label].append(i)
    return [groups[k] for k in sorted(groups)]


def congruence_closure(mul, initial_blocks=None, add_pair=None):
    n = len(mul)
    uf = UnionFind(n)
    if initial_blocks:
        for block in initial_blocks:
            if not block:
                continue
            b0 = block[0]
            for x in block[1:]:
                uf.union(b0, x)
    if add_pair is not None:
        uf.union(add_pair[0], add_pair[1])

    changed = True
    while changed:
        changed = False
        groups = defaultdict(list)
        for i in range(n):
            groups[uf.find(i)].append(i)
        for members in groups.values():
            if len(members) < 2:
                continue
            base = members[0]
            for x in members[1:]:
                for z in range(n):
                    if uf.union(mul[z][base], mul[z][x]):
                        changed = True
                    if uf.union(mul[base][z], mul[x][z]):
                        changed = True
    return normalize_partition_from_uf(uf, n)


def least_monoid_congruence(monoid, pair):
    index = {x: i for i, x in enumerate(monoid)}
    mul = [[index[compose(x, y)] for y in monoid] for x in monoid]
    labels, blocks = congruence_closure(
        mul, add_pair=(index[pair[0]], index[pair[1]])
    )
    return mul, labels, blocks


def quotient_from_partition(mul, labels, generator_indices, identity_index):
    # labels returned by our closure are already normalized, but normalize again
    # so this helper also works on enumerated congruences.
    old_labels = sorted(set(labels), key=lambda c: min(i for i, x in enumerate(labels) if x == c))
    remap = {old: new for new, old in enumerate(old_labels)}
    lab = [remap[x] for x in labels]
    n2 = len(old_labels)
    reps = [None] * n2
    for i, c in enumerate(lab):
        if reps[c] is None:
            reps[c] = i
    mul2 = [[lab[mul[reps[i]][reps[j]]] for j in range(n2)] for i in range(n2)]
    gens2 = [lab[g] for g in generator_indices]
    id2 = lab[identity_index]
    return mul2, gens2, id2, tuple(lab), tuple(reps)


def shortest_words(mul, gens, identity):
    """Shortest words from epsilon, with a<b tie-breaking."""
    n = len(mul)
    best = [None] * n
    best[identity] = ""
    queue = deque([identity])
    while queue:
        q = queue.popleft()
        for ch, g in zip(ALPHABET, gens):
            r = mul[q][g]
            if best[r] is None:
                best[r] = best[q] + ch
                queue.append(r)
    return best


def shortest_positive_words(mul, gens):
    """Shortest nonempty word in each observer fiber, if it exists."""
    n = len(mul)
    best = [None] * n
    queue = deque()
    for ch, g in zip(ALPHABET, gens):
        if best[g] is None:
            best[g] = ch
            queue.append(g)
    while queue:
        q = queue.popleft()
        for ch, g in zip(ALPHABET, gens):
            r = mul[q][g]
            if best[r] is None:
                best[r] = best[q] + ch
                queue.append(r)
    return best


def eval_word_quotient(word, mul, gens, identity):
    q = identity
    for ch in word:
        q = mul[q][gens[0] if ch == "a" else gens[1]]
    return q


def make_concat_language_checker(mul, gens, identity):
    """Return exact regular-language equality checker.

    For targets q1,...,qk, the left language is the concatenation of the
    *positive* fibers F_q1 ... F_qk.  The right language is the positive fiber
    F_target.  This positive-fiber convention is crucial for proper observer
    quotients where nonempty words may map to the observer identity while the
    syntactic unit {epsilon} remains a separate relative class.
    """

    alphabet = tuple(zip(ALPHABET, gens))

    def epsilon_closure(states, targets):
        states = set(states)
        changed = True
        while changed:
            changed = False
            for i, m, used in list(states):
                if i < len(targets) and used and m == targets[i]:
                    nxt = (i + 1, identity, False)
                    if nxt not in states:
                        states.add(nxt)
                        changed = True
        return frozenset(states)

    def nfa_start(targets):
        return epsilon_closure({(0, identity, False)}, targets)

    def nfa_step(state_set, g, targets):
        out = set()
        for i, m, used in state_set:
            if i < len(targets):
                out.add((i, mul[m][g], True))
        return epsilon_closure(out, targets)

    def nfa_accept(state_set, targets):
        return any(i == len(targets) for i, _m, _used in state_set)

    def equal(targets, target, witness=False):
        # The first component tracks the positive target fiber.
        start_nfa = nfa_start(targets)
        start = (identity, False, start_nfa)
        queue = deque([start])
        previous = {start: (None, None)}
        while queue:
            q, total_used, nfa_state = queue.popleft()
            in_target = total_used and q == target
            in_product = nfa_accept(nfa_state, targets)
            if in_target != in_product:
                if not witness:
                    return False
                chars = []
                cur = (q, total_used, nfa_state)
                while previous[cur][0] is not None:
                    prev, ch = previous[cur]
                    chars.append(ch)
                    cur = prev
                word = "".join(reversed(chars))
                return False, word, in_target, in_product
            for ch, g in alphabet:
                nxt = (mul[q][g], True, nfa_step(nfa_state, g, targets))
                if nxt not in previous:
                    previous[nxt] = ((q, total_used, nfa_state), ch)
                    queue.append(nxt)
        if witness:
            return True, None, None, None
        return True

    return equal


def compute_primes(mul, gens, identity):
    positive = shortest_positive_words(mul, gens)
    live = [q for q, w in enumerate(positive) if w is not None]
    equal = make_concat_language_checker(mul, gens, identity)
    composite = {}
    for p in live:
        witnesses = []
        for x in live:
            for y in live:
                if mul[x][y] == p and equal([x, y], p):
                    witnesses.append((x, y))
        if witnesses:
            composite[p] = witnesses
    primes = [p for p in live if p not in composite]
    return positive, live, primes, composite, equal


def prime_cut_candidates(word, prime_set, mul, gens, identity):
    if not word:
        return []
    n = len(word)
    out = []
    for mask in range(1 << (n - 1)):
        pieces = []
        last = 0
        for i in range(n - 1):
            if (mask >> i) & 1:
                pieces.append(word[last : i + 1])
                last = i + 1
        pieces.append(word[last:])
        classes = tuple(eval_word_quotient(p, mul, gens, identity) for p in pieces)
        if all(q in prime_set for q in classes):
            out.append((tuple(pieces), classes))
    return out


def prime_avoidance_automaton(mul, primes):
    """Finite automaton for prime-irreducible paths.

    State (t,U,long) stores whole-prefix product t, products of proper
    nonempty suffixes that start after the first symbol, and whether the prefix
    has length >=2.  Transitions that would create a proper prime-valued block
    are suppressed.  Accepting states have length >=2 and prime total product.
    """
    pset = set(primes)
    starts = {(p, frozenset(), False) for p in primes}
    queue = deque(starts)
    seen = set(starts)
    adjacency = defaultdict(list)
    accepts = set()

    while queue:
        t, suffixes, long = queue.popleft()
        state = (t, suffixes, long)
        if long and t in pset:
            accepts.add(state)
        for p in primes:
            # If an already-long whole prefix is prime, appending anything would
            # make it a proper prime-valued prefix block.
            if long and t in pset:
                continue
            extended_suffixes = {mul[u][p] for u in suffixes}
            if extended_suffixes & pset:
                continue
            nt = mul[t][p]
            n_suffixes = frozenset({p} | extended_suffixes)
            nxt = (nt, n_suffixes, True)
            adjacency[state].append((p, nxt))
            if nxt not in seen:
                seen.add(nxt)
                queue.append(nxt)

    reverse = defaultdict(list)
    for state, edges in adjacency.items():
        for _p, nxt in edges:
            reverse[nxt].append(state)
    productive = set(accepts)
    queue = deque(accepts)
    while queue:
        state = queue.popleft()
        for prev in reverse[state]:
            if prev not in productive:
                productive.add(prev)
                queue.append(prev)

    color = {}
    cycle_edge = None

    def dfs(state):
        nonlocal cycle_edge
        color[state] = 1
        for p, nxt in adjacency.get(state, ()):
            if nxt not in productive:
                continue
            c = color.get(nxt, 0)
            if c == 0:
                if dfs(nxt):
                    return True
            elif c == 1:
                cycle_edge = (state, p, nxt)
                return True
        color[state] = 2
        return False

    for state in sorted(productive, key=repr):
        if color.get(state, 0) == 0 and dfs(state):
            break

    return {
        "states": seen,
        "accepts": accepts,
        "productive": productive,
        "adjacency": adjacency,
        "has_productive_cycle": cycle_edge is not None,
        "cycle_edge": cycle_edge,
    }


def enumerate_all_monoid_congruences(mul):
    """Enumerate the complete congruence lattice by adjoining generator pairs."""
    n = len(mul)
    identity_partition = tuple(range(n))
    seen = {identity_partition}
    queue = deque([identity_partition])
    while queue:
        labels = queue.popleft()
        blocks = blocks_from_labels(labels)
        for i in range(n):
            for j in range(i + 1, n):
                if labels[i] == labels[j]:
                    continue
                new_labels, _ = congruence_closure(mul, blocks, (i, j))
                if new_labels not in seen:
                    seen.add(new_labels)
                    queue.append(new_labels)
    return sorted(seen, key=lambda x: (-len(set(x)), x))


def state_after_prime_word(seq, mul):
    t = seq[0]
    suffixes = frozenset()
    long = False
    for p in seq[1:]:
        suffixes = frozenset({p} | {mul[u][p] for u in suffixes})
        t = mul[t][p]
        long = True
    return (t, suffixes, long)


def main(output_json):
    # ------------------------------------------------------------------
    # 1. Transformation monoid and 36-element quotient
    # ------------------------------------------------------------------
    m0 = generate_transformation_monoid()
    assert len(m0) == 64, len(m0)
    index0 = {x: i for i, x in enumerate(m0)}

    h0_ab = eval_word_transformation("ab")
    h0_abaaab = eval_word_transformation("abaaab")
    mul0, labels0, blocks0 = least_monoid_congruence(m0, (h0_ab, h0_abaaab))
    gen0 = [index0[TAU_A], index0[TAU_B]]
    id0 = index0[IDENTITY_T]
    mul36, gens36, id36, m0_to_36, block_reps = quotient_from_partition(
        mul0, labels0, gen0, id0
    )
    assert len(mul36) == 36, len(mul36)

    shortest = shortest_words(mul36, gens36, id36)
    assert all(w is not None for w in shortest)
    assert max(map(len, shortest)) == 8
    positive = shortest_positive_words(mul36, gens36)
    assert positive[id36] is None, "a nonempty word maps to the quotient identity"
    assert sum(w is not None for w in positive) == 35

    def qw(word):
        return eval_word_quotient(word, mul36, gens36, id36)

    # Give the quotient elements stable certificate ids by shortlex representative.
    quotient_order = sorted(range(36), key=lambda q: (len(shortest[q]), shortest[q]))
    cert_id = {q: i for i, q in enumerate(quotient_order)}
    cert_rep = {cert_id[q]: shortest[q] for q in quotient_order}

    # ------------------------------------------------------------------
    # 2. Relative primes and all exact factorizations
    # ------------------------------------------------------------------
    positive36, live36, primes36, composite36, equal36 = compute_primes(
        mul36, gens36, id36
    )
    prime_words = sorted((positive36[p] for p in primes36), key=lambda w: (len(w), w))
    assert tuple(prime_words) == tuple(sorted(EXPECTED_PRIME_WORDS, key=lambda w: (len(w), w)))
    prime_set = set(primes36)
    prime_label = {p: positive36[p] for p in primes36}

    candidate_count = 0
    rejected = []
    unique_factorizations = []

    for target in sorted(live36, key=lambda q: (len(positive36[q]), positive36[q])):
        target_word = positive36[target]
        candidates = prime_cut_candidates(
            target_word, prime_set, mul36, gens36, id36
        )
        candidate_count += len(candidates)
        survivors = []
        for pieces, classes in candidates:
            ok, witness, in_target, in_product = equal36(classes, target, witness=True)
            labels = [prime_label[q] for q in classes]
            if ok:
                survivors.append((pieces, classes, labels))
            else:
                assert in_target is True and in_product is False
                rejected.append({
                    "target": target_word,
                    "cut_pieces": list(pieces),
                    "prime_labels": labels,
                    "counterexample": witness,
                })
        assert len(survivors) == 1, (target_word, survivors)
        pieces, classes, labels = survivors[0]
        unique_factorizations.append({
            "target": target_word,
            "cut_pieces": list(pieces),
            "prime_labels": labels,
        })

    assert candidate_count == 222, candidate_count
    assert len(rejected) == 187, len(rejected)
    assert len(unique_factorizations) == 35

    # ------------------------------------------------------------------
    # 3. Infinite valid family and under-saturation
    # ------------------------------------------------------------------
    qa = qw("a")
    qq = qw("baaa")
    qb = qw("b")
    qab = qw("ab")
    q2 = mul36[qq][qq]
    q3 = mul36[q2][qq]
    assert q2 == q3
    assert mul36[qa][qb] == qab
    assert mul36[mul36[qa][qq]][qb] == qab
    assert mul36[mul36[qa][q2]][qb] == qab

    composite_identities_spec = (
        ("abaaa", ("abaa", "a")),
        ("baaab", ("b", "aaab")),
        ("baaabaaa", ("baaabaa", "a")),
    )
    composite_certificates = []
    for target_word, factor_words in composite_identities_spec:
        target = qw(target_word)
        factors = [qw(w) for w in factor_words]
        ok, witness, _a, _b = equal36(factors, target, witness=True)
        assert ok, (target_word, factor_words, witness)
        composite_certificates.append({
            "target": target_word,
            "factors": list(factor_words),
            "exact_language_equality": True,
        })

    # Proper interval quotient classes over all m collapse to these three.
    interval_classes = {qw("abaaa"), qw("baaab"), qw("baaabaaa")}
    observed_intervals = set()
    # q^2=q^3 means m=0,1,2,3 suffices to expose every quotient block type.
    for m in range(0, 4):
        seq = [qa] + [qq] * m + [qb]
        for i in range(len(seq)):
            acc = seq[i]
            for j in range(i + 1, len(seq)):
                acc = mul36[acc][seq[j]]
                if i == 0 and j == len(seq) - 1:
                    continue
                observed_intervals.add(acc)
    assert observed_intervals == interval_classes, (
        [shortest[x] for x in observed_intervals],
        [shortest[x] for x in interval_classes],
    )

    H = qw("baaab")
    # Locate H's unique exact factorization in the global certificate.
    H_fact = next(x for x in unique_factorizations if x["target"] == positive36[H])
    assert H_fact["prime_labels"] == ["b", "aaab"]

    # Strict under-saturation for all m>=1.  q*b already has quotient H;
    # q^m*b has the same quotient for every m>=1 because q^2=q^3.
    # Two explicit regular-language witnesses cover all m:
    #   m=1:  baaabaab in H but not P_q P_b
    #   m>=2: baaab has length 5, smaller than the minimum 4m+1.
    tail_cases = []
    for m, witness in ((1, "baaabaab"), (2, "baaab")):
        targets = [qq] * m + [qb]
        assert qw(witness) == H
        ok, shortest_counterexample, in_target, in_product = equal36(
            targets, H, witness=True
        )
        assert not ok and in_target and not in_product
        # Our checker should find exactly the intended short witnesses.
        assert shortest_counterexample == witness
        tail_cases.append({
            "m_case": "m=1" if m == 1 else "m>=2",
            "counterexample": witness,
            "reason": (
                "regular-language equality witness"
                if m == 1
                else "the target word has length 5 < 4m+1, the minimum product length"
            ),
        })

    # ------------------------------------------------------------------
    # 4. Prime-avoidance lasso
    # ------------------------------------------------------------------
    avoid36 = prime_avoidance_automaton(mul36, primes36)
    assert avoid36["has_productive_cycle"]
    lasso_state = state_after_prime_word([qa, qq, qq], mul36)
    assert shortest[lasso_state[0]] == "abaaa"
    assert {shortest[x] for x in lasso_state[1]} == {"baaa", "baaabaaa"}
    lasso_state_loop = state_after_prime_word([qa, qq, qq, qq], mul36)
    assert lasso_state_loop == lasso_state
    assert lasso_state in avoid36["productive"]
    assert any(p == qq and nxt == lasso_state for p, nxt in avoid36["adjacency"][lasso_state])
    final_state = state_after_prime_word([qa, qq, qq, qb], mul36)
    assert final_state[0] == qab
    assert final_state in avoid36["accepts"]
    assert any(p == qb and nxt == final_state for p, nxt in avoid36["adjacency"][lasso_state])

    # ------------------------------------------------------------------
    # 5. Complete congruence lattice and proper-quotient FRP audit
    # ------------------------------------------------------------------
    all_congruences = enumerate_all_monoid_congruences(mul36)
    assert len(all_congruences) == 20, len(all_congruences)
    sizes = tuple(len(set(c)) for c in all_congruences)
    assert sizes[0] == 36
    assert tuple(sizes[1:]) == EXPECTED_PROPER_QUOTIENT_SIZES, sizes

    proper_audit = []
    for audit_index, labels in enumerate(all_congruences[1:], start=1):
        mulq, gensq, idq, main_to_q, qreps = quotient_from_partition(
            mul36, labels, gens36, id36
        )
        posq, liveq, primesq, compq, equalq = compute_primes(mulq, gensq, idq)
        avoidq = prime_avoidance_automaton(mulq, primesq)
        assert not avoidq["has_productive_cycle"]

        blocks = defaultdict(list)
        for main, qclass in enumerate(main_to_q):
            blocks[qclass].append(shortest[main])
        block_record = []
        for qclass in sorted(blocks):
            words = sorted(blocks[qclass], key=lambda w: (len(w), w))
            block_record.append(words)

        proper_audit.append({
            "audit_index": audit_index,
            "quotient_size": len(mulq),
            "observer_identity_has_positive_preimage": posq[idq] is not None,
            "live_positive_relative_classes": len(liveq),
            "relative_primes": len(primesq),
            "prime_labels": sorted(
                (posq[p] for p in primesq), key=lambda w: (len(w), w)
            ),
            "prime_avoidance_states": len(avoidq["states"]),
            "productive_states": len(avoidq["productive"]),
            "productive_cycle": False,
            "observer_blocks_by_M36_shortest_representative": block_record,
        })

    # ------------------------------------------------------------------
    # JSON certificate
    # ------------------------------------------------------------------
    # Quotient blocks of M0 expressed directly as transformations.
    m0_blocks_json = []
    for block in blocks0:
        m0_blocks_json.append([list(m0[i]) for i in block])

    # M36 multiplication table, relabeled by certificate ids.
    mult_cert = []
    for qi in quotient_order:
        row = []
        for qj in quotient_order:
            row.append(cert_id[mul36[qi][qj]])
        mult_cert.append(row)

    certificate = {
        "metadata": {
            "title": "36-element UF--FRP witness verification certificate",
            "verifier": "verify_36.py",
            "alphabet": list(ALPHABET),
            "transformation_product_convention": "f*g means first f, then g",
        },
        "construction": {
            "Q0": list(Q0),
            "tau_a": list(TAU_A),
            "tau_b": list(TAU_B),
            "M0_size": len(m0),
            "congruence_generator": ["h0(ab)", "h0(abaaab)"],
            "M36_size": len(mul36),
            "identity_has_nonempty_preimage": False,
            "max_shortest_representative_length": max(map(len, shortest)),
            "M0_congruence_blocks": m0_blocks_json,
        },
        "M36": {
            "certificate_id_to_shortest_representative": {
                str(i): cert_rep[i] for i in range(36)
            },
            "identity_certificate_id": cert_id[id36],
            "generator_certificate_ids": {
                "a": cert_id[gens36[0]],
                "b": cert_id[gens36[1]],
            },
            "multiplication_table_certificate_ids": mult_cert,
        },
        "prime_structure": {
            "relative_prime_count": len(primes36),
            "relative_prime_representatives": prime_words,
            "shortest_cut_candidate_count": candidate_count,
            "rejected_candidate_count": len(rejected),
            "unique_exact_factorizations": unique_factorizations,
            "rejected_shortest_cut_candidates": rejected,
        },
        "infinite_valid_family": {
            "rule_schema": "[ab] -> [a][baaa]^m[b] for m>=0",
            "q": "[baaa]",
            "quotient_identities": [
                "q^2=q^3",
                "h(a)h(b)=h(ab)",
                "h(a)q h(b)=h(ab)",
                "h(a)q^2 h(b)=h(ab)",
            ],
            "proper_interval_classes": [
                "[abaaa]", "[baaab]", "[baaabaaa]"
            ],
            "composite_interval_certificates": composite_certificates,
        },
        "under_saturation": {
            "tail_class": "[baaab]",
            "tail_unique_exact_factorization": ["[b]", "[aaab]"],
            "strict_subset_claim": "P_q^m P_b is a strict subset of [baaab] for all m>=1",
            "counterexample_cases": tail_cases,
        },
        "prime_avoidance_lasso": {
            "prefix": ["[a]", "[baaa]", "[baaa]"],
            "whole_prefix_class": "[abaaa]",
            "proper_suffix_classes": ["[baaa]", "[baaabaaa]"],
            "loop_symbol": "[baaa]",
            "final_symbol": "[b]",
            "final_prime": "[ab]",
            "productive_cycle_verified": True,
        },
        "quotient_minimality": {
            "monoid_congruence_count": len(all_congruences),
            "proper_quotient_sizes": list(sizes[1:]),
            "all_proper_quotients_have_FRP": True,
            "audit": proper_audit,
        },
    }

    output_json = Path(output_json)
    with output_json.open("w", encoding="utf-8") as f:
        json.dump(certificate, f, ensure_ascii=False, indent=2, sort_keys=True)
        f.write("\n")

    print("36-element UF--FRP witness: ALL CHECKS PASSED")
    print(f"  |M0| = {len(m0)}")
    print(f"  |M36| = {len(mul36)}")
    print(f"  live non-unit classes = {len(live36)}")
    print(f"  relative primes = {len(primes36)}")
    print(f"  shortest-cut candidates = {candidate_count}")
    print(f"  rejected candidates = {len(rejected)}")
    print(f"  unique surviving factorizations = {len(unique_factorizations)}")
    print(f"  monoid congruences on M36 = {len(all_congruences)}")
    print(f"  proper quotient sizes = {list(sizes[1:])}")
    print(f"  certificate written to {output_json}")


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--json",
        default="certificate_36.json",
        help="output path for the deterministic JSON certificate",
    )
    args = parser.parse_args()
    main(args.json)
