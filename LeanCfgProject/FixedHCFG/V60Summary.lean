import LeanCfgProject.FixedHCFG.V60EndToEnd
import LeanCfgProject.FixedHCFG.V60WindowCompression
import LeanCfgProject.FixedHCFG.V60AlignedMarkedSupport
import LeanCfgProject.FixedHCFG.V60MarkedWordReplacement
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
* a finite dependency-spine proof of the fixed-window context bound;
* the positive/zero-window typed-yield bridge isolating marked-leaf compression;
* concrete SSBNF derivation trees and one-hole replacement contexts;
* the exact suppressed marked-skeleton count `(2r-1)N` once unary chains have
  been made label-simple by the manuscript's repeated-label shortcut;
* the compression-certificate bridge converting that count and the raw
  boundary-piece estimate into the displayed `r+(2r-1)N tau` yield bound and
  hence the exact `(N_t+2)B+1` canonical witness bound;
* an alignment-strengthened marked-support layer retaining the zero-mark
  sibling alignment needed for the remaining boundary-preservation proof;
* marked-word replacement semantics showing that preserving `true` leaves and
  changing only `false` material implies the exact first-`k`/last-`l` window
  equality and retains at least `k+l` terminals.

`ComplexityBounds` is imported only for the Section-6 arithmetic envelope; its
older learner-facing modules remain explicitly labelled legacy elsewhere.
-/

theorem v60_summary_marker : True := by
  trivial

end FixedHCFG
end LeanCfgProject
