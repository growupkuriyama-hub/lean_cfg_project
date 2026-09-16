# fixed-h CFG / TCS v62 Lean verification

Canonical manuscript for this branch: `TCS-D-26-00494_major_revision_working_v62`.

This branch was restarted from `tcs-fixed-h-v61-verification` because the
existing `V60*` layer already mirrors the mathematical architecture retained in
v62: nonempty observed factors, Rules R1--R5, yield-only typing `A_mu`, the
finite canonical witness set, exact batch reconstruction, and the conservative
Gold wrapper.

## v62 claims already represented in Lean

The manuscript-facing wrappers live in `V62ManuscriptAudit.lean`.  They connect
v62 directly to the already proved exact layer:

- Proposition `typed-core`: yield-type invariant and preservation of the
  underlying SSBNF language;
- Lemma `sample-consistency`;
- Theorem `soundness`, through the stronger invariant
  `[x:u,v] =>* w -> u w v in L /\ h(w)=h(x)` (with internal nonemptiness in the
  exact kernel);
- Theorem `complete`, from the finite canonical witness set;
- Theorem `reconstruction-fixed-h`, by soundness plus completeness;
- Corollary `ilt`: after the finite witness set is present, at most one later
  rebuild is possible, and every positive text eventually stabilizes exactly
  at the target language;
- concrete end-to-end SSBNF instances of exact reconstruction and Gold
  identification.

The old two-sided `TypedRefinement.lean` is retained only as legacy material.
The v62 manuscript uses the yield-only `V60TypedRefinement.lean` architecture.

## Fixed-window chain already represented

For Section `Fixed-Window Thick Data`, the current exact layer already contains:

- the displayed bound
  `B_{k,l}(G) = tau` for `k+l=0`, and
  `k+l + (2(k+l)-1) N tau` otherwise;
- the typed-yield lifting interface from untyped boundary-preserving
  compression;
- the finite typed dependency-path argument for reaching contexts;
- the canonical witness bound `(N_t+2) B_{k,l}(G)+1`;
- concrete derivation trees and one-hole contexts;
- repeated-label shortcutting;
- thickness-bounded replacement of off-path sibling subtrees;
- first-`k`/last-`l` Boolean leaf marks;
- construction of the marked support and the exact `2r-1` suppressed-block
  count;
- recursive pruning with the required quantitative length bound.

## Current mathematical frontier

The remaining positive-window obligation is to prove that the recursively
pruned tree used for the quantitative bound preserves the *same marked boundary
terminals and their order*.  The local repeated-label shortcut already has a
window-preservation theorem, but `V60MarkedPruningLength.lean` currently returns
only a same-root tree and a length bound.  The next proof layer must strengthen
that recursive construction with a boundary-preservation invariant and thereby
discharge `V60WindowUntypedCompression` without an abstract premise.

Once that is done, the existing `V60WindowYieldBridge` and
`V60WindowEnvelope` close Lemmas `window-typed-yield` and `window-context` and
the witness-length part of Theorem `window-thick`.

A second, independent v62 frontier is Proposition `thick-ssbnf-normal`: the
appendix gives a polynomial thickness-preserving conversion from an arbitrary
reduced CFG to reduced SSBNF.  The present Lean tree has not yet been audited as
an end-to-end formalization of that general normalization.  It should be taken
up after the boundary-preserving marked-pruning bridge, so the fixed-window
proof is first closed for reduced SSBNF exactly as stated in v62.

## CI

`.github/workflows/verify-fixed-h-tcs.yml` now runs on
`tcs-fixed-h-v62-verification` and builds `V62ManuscriptAudit` in addition to
the existing exact and legacy regression targets.  The fixed-h source audit
continues to reject `sorry` and `admit`.
