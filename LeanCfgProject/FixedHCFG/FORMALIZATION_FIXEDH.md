# Fixed-h TCS Lean formalization record

This directory formalizes theorem-facing parts of the manuscript
`fixed-h-CFG-arXiv-v4 = TCS-D-26-00494`.

Paper-side issues discovered by formalization are tracked separately in
[`LEAN_VERIFICATION_GAPS.md`](./LEAN_VERIFICATION_GAPS.md).

## Verified chain

The Lean development currently checks, without `sorry` or `admit`:

- the fixed finite-monoid observer and monoid-homomorphism laws;
- Lemma 4.4 (full typing derivability);
- Lemma 4.5(i) (yield-type invariant);
- Lemma 4.5(ii) (two-sided context-type invariant);
- Lemma 4.5(iii) (language preservation under reachable/productive trimming);
- Lemma 4.6 (types of canonical yield/context witnesses);
- shortlex canonical yield and context witnesses;
- Lemma 4.7 (characteristic-sample observation words are positive);
- Lemma 4.8 (anchor recovery from the paper characteristic sample);
- the finite reconstruction-basis bridge corresponding to Theorem 4.12;
- the learner rule kernel (paper Rules (1)--(5));
- Theorem 5.6 (soundness), via the stronger invariant
  `[x:u,v] =>* w -> u w v in L and h(w)=h(x)`;
- Lemmas 5.2--5.4 in the repaired terminal case described below;
- Theorem 5.5 (completeness);
- Theorem 5.7 (exact reconstruction);
- Corollary 5.8 (identification in the limit);
- an end-to-end bridge from a reduced SSBNF presentation, through the exact
  manuscript characteristic sample, to eventual exact hypotheses;
- the Section 6 combinatorial/arithmetic envelope underlying the manuscript's
  `O(||K||^5)` hypothesis-construction bound;
- Section 7 finite typed-state and typed-rule counting envelopes;
- strict-linear derivation and occurrence spines;
- cycle deletion and the derivation-level content of Lemmas 7.3--7.6;
- the manuscript-faithful lexicographic-shortlex proof of Lemma 7.6;
- the fixed-h typed linear refinement and its yield/context invariants;
- Proposition 7.7(i) and the corrected `(production,q,m,n)` proof of
  Proposition 7.7(ii), avoiding any cancellation assumption on the monoid;
- reachable/productive trimming for strict-linear grammars;
- the actual shortlex canonical `omega(X)` and `chi(X)` on the reduced
  strict-linear grammar, including the bounds of Lemmas 7.5--7.6;
- Lemma 7.8 exact reconstruction via learner Rules (1)--(5);
- a theorem-facing Theorem 7.9 package combining Lemma 7.8, a polynomial
  total-data envelope for `CS_lin`, and the Section-6 degree-five construction
  envelope.

The focused Section-7 CI run `34594044883` is green through the Theorem 7.9
time-and-data envelope and the proof-placeholder audit.

The aggregate core build target is:

```text
lake build LeanCfgProject.FixedHCFG.Summary
```

Section 7 also has a focused CI workflow.

## Important manuscript discrepancy found during formalization

The terminal case of manuscript Lemma 5.2 states, for an arbitrary realized
terminal rule `X -> a`, that `omega(X)=a`, and therefore that
`[omega(X):u_X,v_X] -> a` is directly a Rule-(4) production.

That equality is not valid in general when one typed nonterminal has more than
one terminal production.  For example, with the trivial observer, a state can
have both `X -> a` and `X -> b`; `omega(X)` is only the shortlex-minimal one of
those yields.

The reconstruction theorem is nevertheless repairable without strengthening
any hypothesis.  The Lean proof uses the following two-step terminal case:

1. the anchor observation gives `[omega(X):u_X,v_X]`;
2. the rule observation for `X -> a` gives `[a:u_X,v_X]` and Rule (4)
   `[a:u_X,v_X] -> a`;
3. Lemma 4.6 and the typed terminal rule give
   `h(omega(X)) = h(a)`;
4. Rule (3) transports
   `[omega(X):u_X,v_X] -> [a:u_X,v_X]`, followed by Rule (4).

Thus Theorem 5.5 remains valid, but the prose statement/proof of Lemma 5.2(i)
and the height-one case of Theorem 5.5 should be revised before the next
manuscript version.

## Current frontier: discharge the abstract Section-7 interface from the actual `H`

The Section-7 mathematical chain is now green at the theorem-facing interface,
including Lemma 7.8 and the time/data envelope for Theorem 7.9.  The remaining
high-value bridge is to construct that interface directly from the manuscript's
actual grammar

```text
H = trim(fullTypedLinearGrammar Obs G0)
```

and its exact `CS_lin(H)`.

The next layer therefore proves generic strict-linear language semantics and a
plugging lemma (`S =>* u X v` together with `X =>* w` gives `u w v`), then uses
the canonical `omega/chi` witnesses of the trimmed typed grammar to build the
`LinearReconstructionBasis` automatically.  This will remove the remaining
abstract assumptions `hCSrepr`, witness typing, and rule-observation membership
from the Section-7 end-to-end statement.

A separate remaining normalization target is Proposition 7.2: the present Lean
development starts from an indexed SSLNF presentation and does not yet verify a
concrete polynomial-time transformation from an arbitrary linear CFG to reduced
SSLNF.

See `LEAN_VERIFICATION_GAPS.md` for manuscript-side consequences and revision
notes.
