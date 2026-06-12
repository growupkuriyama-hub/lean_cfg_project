import LeanCfgProject.ObservedResidualConcept.ICFrozenArtifactIndex_v27_2
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace LeanCfgProject

/-
ICDependencyCertificate_v27_2.lean

Dependency certificate for the final-index layer.  This checks that the
observed-learning, point-frame, finite-basis, release, and metadata layers are
all available through the same import graph.
-/

theorem icDependencyCertificate_v27_2_observed_learning :
    True := by
  exact paperClaimIndex_v27_2_observed_learning

theorem icDependencyCertificate_v27_2_point_frame :
    True := by
  exact paperClaimIndex_v27_2_point_frame

theorem icDependencyCertificate_v27_2_finite_basis :
    True := by
  exact paperClaimIndex_v27_2_finite_basis

theorem icDependencyCertificate_v27_2_release :
    True := by
  exact paperClaimIndex_v27_2_release_certificate

theorem icDependencyCertificate_v27_2_metadata :
    icArtifactCIRun_ci180 = "Lean CI #180" := by
  exact icArtifactMetadata_ci180_ci_run

theorem icDependencyCertificate_v27_2_all :
    True ∧ True ∧ True ∧ True := by
  exact ⟨icDependencyCertificate_v27_2_observed_learning,
    icDependencyCertificate_v27_2_point_frame,
    icDependencyCertificate_v27_2_finite_basis,
    icDependencyCertificate_v27_2_release⟩

end LeanCfgProject
