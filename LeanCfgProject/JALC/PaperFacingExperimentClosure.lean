import LeanCfgProject.JALC.ShortlexWitnessKernel
import LeanCfgProject.JALC.PaperFacingFinalArtifact

namespace LeanCfgProject
namespace JALC
namespace PaperFacingExperimentClosure

/-
Paper-facing closure target for the current Lean experiment sequence.

This target imports:

* the final artifact aggregation target;
* the decidability-transfer kernel;
* the algorithmic finite-main wrapper;
* the executable payload boundary;
* the descriptor reconstruction wrapper;
* the context-closure future-phase marker;
* the shortlex witness future-phase marker.

It is intended to close the current round of experiments without starting a new
large formalization phase.
-/

open FinalArtifactKernel
open ContextClosureCoincidenceKernel
open ShortlexWitnessKernel


/-- The final artifact target is still included. -/
theorem checked_final_artifact_again :
    FinalArtifactChecked :=
  final_artifact_checked


/-- The two larger remaining proof families are explicitly recorded as future phases. -/
theorem checked_remaining_future_phase_markers :
    ContextClosureCoincidenceFuturePhase ∧ ShortlexWitnessFuturePhase := by
  exact ⟨
    context_closure_coincidence_boundary_recorded,
    shortlex_witness_boundary_recorded⟩

end PaperFacingExperimentClosure
end JALC
end LeanCfgProject
