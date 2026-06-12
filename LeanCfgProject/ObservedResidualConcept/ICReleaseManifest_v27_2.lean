import LeanCfgProject.ObservedResidualConcept.ObservedLearningReleaseRegression_v27_2
import LeanCfgProject.ObservedResidualConcept.PointFrameReleaseRegression_v27_2
import LeanCfgProject.ObservedResidualConcept.FiniteBasisReleaseRegression_v27_2
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace LeanCfgProject

/-
ICReleaseManifest_v27_2.lean

Manifest target for the paper-facing Lean release after CI #180.

This is a conservative aggregation target.  Its purpose is to keep the
observed-learning, point-frame, and finite-basis release-regression modules
under one explicit name for future FORMALIZATION.MD updates.
-/

theorem icReleaseManifest_v27_2_observedLearning :
    True := by
  exact observedLearningReleaseRegression_v27_2_summary

theorem icReleaseManifest_v27_2_pointFrame :
    True := by
  exact pointFrameReleaseRegression_v27_2_summary

theorem icReleaseManifest_v27_2_finiteBasis :
    True := by
  exact finiteBasisReleaseRegression_v27_2_summary

theorem icReleaseManifest_v27_2_all :
    True ∧ True ∧ True := by
  exact ⟨icReleaseManifest_v27_2_observedLearning,
    icReleaseManifest_v27_2_pointFrame,
    icReleaseManifest_v27_2_finiteBasis⟩

end LeanCfgProject
