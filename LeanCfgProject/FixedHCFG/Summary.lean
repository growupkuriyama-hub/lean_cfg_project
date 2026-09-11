import LeanCfgProject.FixedHCFG.TrimmedLanguage
import LeanCfgProject.FixedHCFG.Identification

namespace LeanCfgProject
namespace FixedHCFG

/-!
Paper-facing aggregate import for the fixed-h TCS formalization.

Current chain:
* Section 4 typed refinement: Lemmas 4.4, 4.5(i)--(iii), 4.6;
* Section 5 learner soundness: Theorem 5.6;
* reconstruction-basis interface: Lemmas 5.2--5.4 and Theorems 5.5, 5.7;
* semantic identification from finite observations: Corollary 5.8.

The remaining end-to-end bridge is the explicit shortlex/finite characteristic-
sample extraction of Lemmas 4.7--4.8 and Theorems 4.9/4.12 from a raw reduced
SSBNF grammar into `ReconstructionBasis`.
-/

end FixedHCFG
end LeanCfgProject
