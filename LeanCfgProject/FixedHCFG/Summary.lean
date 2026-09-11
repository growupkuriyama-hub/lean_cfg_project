import LeanCfgProject.FixedHCFG.EndToEnd

namespace LeanCfgProject
namespace FixedHCFG

/-!
Paper-facing aggregate import for the fixed-h TCS formalization.

Current verified chain:
* Section 4 typed refinement: Lemmas 4.4, 4.5(i)--(iii), 4.6;
* finite retained-state extraction and finite enriched observation interface;
* Lemma 4.7-style positivity of all extracted observation words;
* exact equality between the extracted reconstruction-basis language and the
  original SSBNF presentation language;
* Section 5 learner soundness: Theorem 5.6;
* reconstruction-basis interface: Lemmas 5.2--5.4 and Theorems 5.5, 5.7;
* semantic identification from finite observations: Corollary 5.8;
* end-to-end Corollary 5.8 from a concrete SSBNF presentation through typed
  extraction to eventual learner-language stabilization.

The remaining manuscript-faithful refinement is to replace the enriched
observation interface by the exact shortlex-minimal `omega`, `chi`, and
`CS(G~)` of Sections 4.2--4.4.  The end-to-end learning argument itself no
longer depends on that normalization choice.
-/

end FixedHCFG
end LeanCfgProject
