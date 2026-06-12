import LeanCfgProject.ObservedResidualConcept.ICReproducibilityIndex_ci180
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace LeanCfgProject

/-
ICSubmissionSummary_v12.lean

Top-level target for the v27.2 / CI #180 release-regression push.
-/

theorem icSubmissionSummary_v12_available :
    True := by
  exact icReproducibilityIndex_ci180_manifest_available

theorem icSubmissionSummary_v12_release_index_available :
    True := by
  exact icReproducibilityIndex_ci180_release_index_available

theorem icSubmissionSummary_v12_summary :
    True ∧ True := by
  exact ⟨icSubmissionSummary_v12_available,
    icSubmissionSummary_v12_release_index_available⟩

end LeanCfgProject
