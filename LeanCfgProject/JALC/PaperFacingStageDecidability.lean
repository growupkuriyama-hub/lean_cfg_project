import LeanCfgProject.JALC.StageDecidabilityKernel
import LeanCfgProject.JALC.PaperFacingExperimentClosure

namespace LeanCfgProject
namespace JALC
namespace PaperFacingStageDecidability

/-
Paper-facing target for the next JALC Lean experiment.

This target records that the FullKept decidability boundary can be reduced from
computedKept itself to the two stages computed by Algorithm 1.
-/

open StageDecidabilityKernel
open FinalArtifactKernel
open ContextClosureCoincidenceKernel
open ShortlexWitnessKernel


/-- The previous final artifact target remains included. -/
theorem checked_previous_final_artifact :
    FinalArtifactChecked :=
  final_artifact_checked


/--
The current target keeps the two larger future phases separated from this
stage-level decidability experiment.
-/
theorem checked_future_phase_markers_again :
    ContextClosureCoincidenceFuturePhase ∧ ShortlexWitnessFuturePhase := by
  exact ⟨
    context_closure_coincidence_boundary_recorded,
    shortlex_witness_boundary_recorded⟩


/--
Expose the stage-level decidability transfer under a paper-facing name.
-/
theorem checked_fullKept_decidable_of_stage_decidability
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    (tau : Sigma → M)
    (G : RoundTripKernel.UntypedStructure V Sigma)
    (E : AlgorithmicExtractionKernel.CertifiedExtraction
      (FullAlgorithmicAgreementKernel.fullExtractionRuleData tau G))
    (prodDec :
      DecidablePred (AlgorithmicExtractionKernel.computedProductive E))
    (reachDec :
      DecidablePred (AlgorithmicExtractionKernel.computedReachable E)) :
    Nonempty (DecidablePred
      (FullKeptCorrectnessKernel.FullKept tau G)) :=
  fullKept_decidable_of_stage_decidability tau G E prodDec reachDec

end PaperFacingStageDecidability
end JALC
end LeanCfgProject
