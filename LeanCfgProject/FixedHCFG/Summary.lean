import LeanCfgProject.FixedHCFG.LinearSpine

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
* the relational spine core of Lemma 7.3: repeated-state cycle deletion,
  strict shortening, and the finite simple-spine cardinality bounds used by
  Lemmas 7.5 and 7.6.

The Section-6 file verifies the theorem-facing combinatorial/arithmetic bound,
not a low-level cost semantics for trie and radix-sort implementations.  For
Section 7, the next remaining proof-theoretic block is to connect the generic
cycle-deletion lemma to concrete strict-linear derivations and shortlex
minimality, yielding the full derivation-level Lemmas 7.5--7.6, followed by the
linear exact-reconstruction Lemma 7.8 and Theorem 7.9.  Sections 8--10 remain
after that.
-/

end FixedHCFG
end LeanCfgProject
