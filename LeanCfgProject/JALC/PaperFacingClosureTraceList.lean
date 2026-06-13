import LeanCfgProject.JALC.ClosureTraceListKernel
import LeanCfgProject.JALC.PaperFacingListCertificate

namespace LeanCfgProject
namespace JALC
namespace PaperFacingClosureTraceList

/-
Paper-facing target for closure trace list certificates.

This target records that finite lists representing the certified closure
iterates at the two Algorithm 1 heights are enough to reach FullKept
decidability.
-/

open ClosureTraceListKernel
open FinalArtifactKernel


/-- The previous final artifact target remains available. -/
theorem checked_previous_final_artifact_from_trace_list :
    FinalArtifactChecked :=
  final_artifact_checked


/--
Paper-facing version of the trace-list boundary to FullKept decidability
transfer.
-/
theorem checked_traceListBoundary_to_fullKept_decidable
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    [DecidableEq (InverseKernel.TypedState V M)]
    (tau : Sigma → M)
    (G : RoundTripKernel.UntypedStructure V Sigma)
    (T : StageTraceListBoundaryData tau G) :
    Nonempty (DecidablePred (FullKeptCorrectnessKernel.FullKept tau G)) :=
  traceListBoundary_to_fullKept_decidable tau G T


/-- Paper-facing productive-stage decidability from a trace-list boundary. -/
theorem checked_traceListBoundary_productive_decidable
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    [DecidableEq (InverseKernel.TypedState V M)]
    (tau : Sigma → M)
    (G : RoundTripKernel.UntypedStructure V Sigma)
    (T : StageTraceListBoundaryData tau G) :
    Nonempty (DecidablePred
      (AlgorithmicExtractionKernel.computedProductive T.extraction)) :=
  traceListBoundary_productive_decidable tau G T

end PaperFacingClosureTraceList
end JALC
end LeanCfgProject
