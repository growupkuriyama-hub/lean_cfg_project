import LeanCfgProject.JALC.RuleStageBoundaryKernel
import LeanCfgProject.JALC.PaperFacingStageDecidability

namespace LeanCfgProject
namespace JALC
namespace PaperFacingRuleStageBoundary

/-
Paper-facing target for the rule-stage boundary experiment.

This target is a small but useful continuation after StageDecidability:
stage-decidable certified runs now feed the executable payload boundary, and a
richer rule-stage payload records the concrete rule-predicate decisions that a
future finite enumerator should provide.
-/

open StagePayloadBridgeKernel
open RuleStageBoundaryKernel
open StageDecidabilityKernel
open FinalArtifactKernel


/-- The previous final artifact target remains available. -/
theorem checked_previous_final_artifact_again :
    FinalArtifactChecked :=
  final_artifact_checked


/-- Paper-facing version of the stage-run to FullKept decidability transfer. -/
theorem checked_stageDecidableRun_to_fullKept_decidable
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    (tau : Sigma → M)
    (G : RoundTripKernel.UntypedStructure V Sigma)
    (R : StageDecidableCertifiedRun tau G) :
    Nonempty (DecidablePred (FullKeptCorrectnessKernel.FullKept tau G)) :=
  stageDecidableRun_to_fullKept_decidable tau G R


/-- Paper-facing version of the rule-stage boundary to FullKept decidability transfer. -/
theorem checked_ruleStageBoundary_to_fullKept_decidable
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    (tau : Sigma → M)
    (G : RoundTripKernel.UntypedStructure V Sigma)
    (B : RuleStageBoundaryData tau G) :
    Nonempty (DecidablePred (FullKeptCorrectnessKernel.FullKept tau G)) :=
  ruleStageBoundary_to_fullKept_decidable tau G B

end PaperFacingRuleStageBoundary
end JALC
end LeanCfgProject
