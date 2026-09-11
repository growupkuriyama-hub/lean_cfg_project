import LeanCfgProject.FixedHCFG.LinearDerivation

namespace LeanCfgProject
namespace FixedHCFG

/-!
Paper-facing aggregate import for the fixed-h TCS formalization.

Current verified chain:
* Section 4 typed refinement: Lemmas 4.4, 4.5(i)--(iii), and 4.6;
* manuscript-faithful shortlex witnesses `omega` and `chi`;
* the exact Section-4 characteristic sample `CS(G~)`, with no auxiliary anchor
  family, together with Lemmas 4.7 and 4.8 and the finite reconstruction-basis
  interface of Theorem 4.12;
* exact equality between the paper reconstruction-basis language and the
  original SSBNF presentation language;
* Section 5 learner soundness: Theorem 5.6;
* reconstruction: Lemmas 5.2--5.4 and Theorems 5.5 and 5.7;
* semantic identification in the limit: Corollary 5.8;
* end-to-end Corollary 5.8 from a concrete SSBNF presentation, using the exact
  manuscript characteristic sample;
* Section 6 combinatorial complexity envelope: quadratic factorization
  enumeration and the algebraic absorption of the displayed construction-cost
  expression into degree five;
* Section 7 finite envelopes underlying Proposition 7.7: typed-state and
  typed-rule `|M|^3` bounds, the `|W|+|R|+1` characteristic-sample bound,
  the `2|W|` witness-length arithmetic, and the induced total-data bound;
* strict-linear spine cycle deletion, together with derivation-level
  minimum-yield and minimum-context simplicity arguments giving the numerical
  conclusions of Lemmas 7.5 and 7.6.

The Section-6 file verifies the theorem-facing combinatorial/arithmetic bound,
not a low-level cost semantics for trie and radix-sort implementations.  The
remaining Section-7 bridge is to instantiate the strict-linear abstraction with
the concrete retained typed grammar `H`, connect its minimum-length witnesses
to the manuscript's shortlex `omega` and `chi`, and then formalize the linear
exact-reconstruction Lemma 7.8 and Theorem 7.9.  Sections 8--10 remain after
that.
-/

end FixedHCFG
end LeanCfgProject
