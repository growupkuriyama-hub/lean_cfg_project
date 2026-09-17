import LeanCfgProject.FixedHCFG.V60EndToEnd
import LeanCfgProject.FixedHCFG.V60WindowCompression
import LeanCfgProject.FixedHCFG.V60AlignedMarkedSupport
import LeanCfgProject.FixedHCFG.V60MarkedWordReplacement
import LeanCfgProject.FixedHCFG.V60MarkedContext
import LeanCfgProject.FixedHCFG.V60MarkedShortcut
import LeanCfgProject.FixedHCFG.V60MarkedContextPruning
import LeanCfgProject.FixedHCFG.V60MarkedContextShortening
import LeanCfgProject.FixedHCFG.V60AlignedMarkedPruning
import LeanCfgProject.FixedHCFG.V60WindowCompressionConstructive
import LeanCfgProject.FixedHCFG.V62ThicknessNormalization
import LeanCfgProject.FixedHCFG.V62WindowSampleBounds
import LeanCfgProject.FixedHCFG.ComplexityBounds

namespace LeanCfgProject
namespace FixedHCFG

/-!
Aggregate build target for the manuscript-faithful v60 fixed-h development,
plus the v62 quantitative transfer audit layered on top of it.

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
  sibling alignment needed for the boundary-preservation proof;
* marked-word replacement semantics showing that preserving `true` leaves and
  changing only `false` material implies the exact first-`k`/last-`l` window
  equality and retains at least `k+l` terminals;
* marked one-hole context semantics proving that thickness-shortening every
  off-path sibling preserves the protected marked frontier;
* a marked repeated-label shortcut theorem showing that deleting a repeated
  context segment preserves every protected terminal and its order;
* root-oriented context splitting and target-label bookkeeping for iterating
  repeated-label deletion while retaining the same marked-frontier semantics;
* simultaneous chain normalization and sibling shortening, yielding a
  duplicate-free marked chain with the quantitative `|N|*tau` context charge;
* aligned recursive marked-support pruning carrying that semantics through the
  full suppressed support tree while proving the same quantitative length bound;
* constructive positive-window compression from base thickness alone, removing
  the former external structural-certificate premise from the witness bound;
* the v62 normalization-transfer arithmetic showing that the appendix's
  `1+|V_B| tau_B` estimate and the complete fixed-window witness envelope remain
  polynomial under polynomial SSBNF size/thickness bounds;
* the actual retained typed-state bound `N_t <= N |M|`, used to eliminate the
  last abstract typed-state-count premise from the normalization transfer.

`ComplexityBounds` is imported only for the Section-6 arithmetic envelope; its
older learner-facing modules remain explicitly labelled legacy elsewhere.
-/

theorem v60_summary_marker : True := by
  trivial

end FixedHCFG
end LeanCfgProject
