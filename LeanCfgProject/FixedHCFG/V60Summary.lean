import LeanCfgProject.FixedHCFG.V60EndToEnd
import LeanCfgProject.FixedHCFG.V60WindowEnvelope
import LeanCfgProject.FixedHCFG.ComplexityBounds

namespace LeanCfgProject
namespace FixedHCFG

/-!
Aggregate build target for the manuscript-faithful v60 fixed-h development.

The imported exact-v60 chain contains:
* nonempty-factor batch kernel and soundness;
* yield-only typed refinement and successful-occurrence trim;
* manuscript canonical `omega` and total-length-first `chi`;
* the concrete finite characteristic witness set;
* exact finite-sample reconstruction;
* conservative Gold identification;
* canonical yield/context minimality and witness-length transfer lemmas;
* the exact arithmetic envelope of the fixed-window witness bound.

`ComplexityBounds` is imported only for the Section-6 arithmetic envelope; its
older learner-facing modules remain explicitly labelled legacy elsewhere.
-/

theorem v60_summary_marker : True := by
  trivial

end FixedHCFG
end LeanCfgProject
