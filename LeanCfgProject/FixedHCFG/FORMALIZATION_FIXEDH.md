# Fixed-h TCS Lean formalization record

This directory formalizes theorem-facing parts of the manuscript
`fixed-h-CFG-arXiv-v4 = TCS-D-26-00494`.

## Verified chain

The Lean development currently checks, without `sorry` or `admit`:

- the fixed finite-monoid observer and monoid-homomorphism laws;
- Lemma 4.4 (full typing derivability);
- Lemma 4.5(i) (yield-type invariant);
- Lemma 4.5(ii) (two-sided context-type invariant);
- Lemma 4.5(iii) (language preservation under reachable/productive trimming);
- Lemma 4.6 (types of canonical yield/context witnesses);
- the learner rule kernel (paper Rules (1)--(5));
- Theorem 5.6 (soundness), via the stronger induction invariant
  `[x:u,v] =>* w -> u w v in L and h(w)=h(x)`;
- Lemmas 5.2--5.4 at the reconstruction-basis interface;
- Theorem 5.5 (completeness) at that interface;
- Theorem 5.7 (exact reconstruction) by combining 5.5 and 5.6;
- Corollary 5.8 in the paper's semantic identification sense: after a finite
  observation set has appeared in a positive text, every later hypothesis
  generates exactly the target language.

The aggregate build target is:

```text
lake build LeanCfgProject.FixedHCFG.Summary
```

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

## Remaining end-to-end gap

The current reconstruction theorem is proved against an abstract
`ReconstructionBasis` carrying exactly the finite typed local data used in
Section 5.  What is not yet connected end-to-end is the explicit construction
of that object from a raw reduced SSBNF grammar using the paper's shortlex
choices and characteristic sample:

- Lemma 4.7 (observation words are positive examples);
- Lemma 4.8 (anchor words occur in the characteristic sample);
- Theorem 4.9 (well-definedness/finiteness of `CS`);
- Definition 4.11 / Theorem 4.12 (finite typed reconstruction basis).

The next formalization phase should construct the shortlex witness layer and
then instantiate `ReconstructionBasis` from the trimmed typed grammar.  After
that bridge is checked, Sections 4--5 will form one end-to-end Lean chain from a
reduced SSBNF presentation to identification in the limit.

Computational Sections 6--7 and the separation examples are outside the current
Lean scope.
