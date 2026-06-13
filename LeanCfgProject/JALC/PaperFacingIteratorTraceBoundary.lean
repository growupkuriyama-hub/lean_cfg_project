import LeanCfgProject.JALC.IteratorTraceBoundaryKernel
import LeanCfgProject.JALC.PaperFacingClosureTraceList

namespace LeanCfgProject
namespace JALC
namespace PaperFacingIteratorTraceBoundary

/-
Paper-facing target for the iterator trace boundary.

This target bundles rule-list data and closure-trace data into a single finite
payload and checks that this payload reaches FullKept decidability.
-/

open IteratorTraceBoundaryKernel
open FinalArtifactKernel


/-- The previous final artifact target remains available. -/
theorem checked_previous_final_artifact_from_iterator_trace :
    FinalArtifactChecked :=
  final_artifact_checked


/-- Paper-facing version of the iterator trace boundary via the trace-list path. -/
theorem checked_iteratorTraceBoundary_to_fullKept_decidable_via_trace
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    [DecidableEq (InverseKernel.TypedState V M)]
    (tau : Sigma → M)
    (G : RoundTripKernel.UntypedStructure V Sigma)
    (B : IteratorTraceBoundaryData tau G) :
    Nonempty (DecidablePred (FullKeptCorrectnessKernel.FullKept tau G)) :=
  iteratorTraceBoundary_to_fullKept_decidable_via_trace tau G B


/-- Paper-facing version of the iterator trace boundary via the rule-list path. -/
theorem checked_iteratorTraceBoundary_to_fullKept_decidable_via_rule_list
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    [DecidableEq (InverseKernel.TypedState V M)]
    (tau : Sigma → M)
    (G : RoundTripKernel.UntypedStructure V Sigma)
    (B : IteratorTraceBoundaryData tau G) :
    Nonempty (DecidablePred (FullKeptCorrectnessKernel.FullKept tau G)) :=
  iteratorTraceBoundary_to_fullKept_decidable_via_rule_list tau G B

end PaperFacingIteratorTraceBoundary
end JALC
end LeanCfgProject
