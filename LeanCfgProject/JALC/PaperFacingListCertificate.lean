import LeanCfgProject.JALC.ListCertificateKernel
import LeanCfgProject.JALC.PaperFacingRuleStageBoundary

namespace LeanCfgProject
namespace JALC
namespace PaperFacingListCertificate

/-
Paper-facing target for finite list certificates.

This target records that finite list certificates for the computed productivity
and reachability stages are enough to supply FullKept decidability.  It also
records a rule-list boundary for terminal, start, and binary rule predicates.
-/

open ListCertificateKernel
open FinalArtifactKernel


/-- The previous final artifact target remains available. -/
theorem checked_previous_final_artifact_from_list_certificate :
    FinalArtifactChecked :=
  final_artifact_checked


/-- Paper-facing version of the stage-list boundary to FullKept decidability transfer. -/
theorem checked_stageListBoundary_to_fullKept_decidable
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    [DecidableEq (InverseKernel.TypedState V M)]
    (tau : Sigma → M)
    (G : RoundTripKernel.UntypedStructure V Sigma)
    (B : StageListBoundaryData tau G) :
    Nonempty (DecidablePred (FullKeptCorrectnessKernel.FullKept tau G)) :=
  stageListBoundary_to_fullKept_decidable tau G B


/-- Paper-facing version of the rule-list boundary to FullKept decidability transfer. -/
theorem checked_ruleListBoundary_to_fullKept_decidable
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    [DecidableEq (InverseKernel.TypedState V M)]
    (tau : Sigma → M)
    (G : RoundTripKernel.UntypedStructure V Sigma)
    (B : RuleListBoundaryData tau G) :
    Nonempty (DecidablePred (FullKeptCorrectnessKernel.FullKept tau G)) :=
  ruleListBoundary_to_fullKept_decidable tau G B

end PaperFacingListCertificate
end JALC
end LeanCfgProject
