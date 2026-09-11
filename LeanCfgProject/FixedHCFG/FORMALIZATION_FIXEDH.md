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
  polynomial hypothesis-construction bound;
- Section 7 finite typed-state / typed-rule counting envelopes;
- strict-linear derivation and occurrence spines;
- cycle deletion and simple-spine bounds for the linear subclass;
- the derivation-level content of Lemmas 7.3--7.6 in a generic strict-linear
  grammar model.

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

## Current frontier: manuscript-faithful Section 7 shortlex bridge

The generic strict-linear spine development is green.  The remaining Section 7
work is to connect those generic bounds to the manuscript's exact canonical
choices and then to the retained typed linear grammar `H`.

A subtle proof obligation appears in Lemma 7.6: `chi(X)` is minimal in the
lexicographic extension of word-shortlex, not by total context length.  The
formalization therefore proves the stronger cycle-deletion fact that the
replacement context is strictly smaller in the *actual context shortlex order*.
This is implemented in `LinearShortlex.lean`; its CI is being stabilized before
we use it as the final bridge to Proposition 7.7 and Theorem 7.9.

See `LEAN_VERIFICATION_GAPS.md` for manuscript-side consequences and revision
notes.
