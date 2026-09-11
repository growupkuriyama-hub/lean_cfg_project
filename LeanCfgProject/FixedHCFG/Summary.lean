import LeanCfgProject.FixedHCFG.ComplexityBounds

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
  expression into degree five.

The Section-6 file verifies the theorem-facing combinatorial/arithmetic bound,
not a low-level cost semantics for trie and radix-sort implementations.  The
main remaining manuscript blocks are the linear polynomial-time-and-data result
of Section 7 and the separation/boundary results of Sections 8--10.
-/

end FixedHCFG
end LeanCfgProject
