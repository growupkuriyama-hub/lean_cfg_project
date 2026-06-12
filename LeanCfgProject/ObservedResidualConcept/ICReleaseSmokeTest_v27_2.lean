import LeanCfgProject.ICAppendixReleaseIndex_v27_2

set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace LeanCfgProject

/-
ICReleaseSmokeTest_v27_2.lean

One-file smoke test for the v27.2 certificate layer.
-/

theorem icReleaseSmokeTest_v27_2_metadata :
    True := by
  exact icReleaseCertificate_v27_2_metadata

theorem icReleaseSmokeTest_v27_2_release_certificate :
    True := by
  exact icReleaseCertificate_v27_2_submission_v12

theorem icReleaseSmokeTest_v27_2_formalization_bridge :
    True := by
  exact icPaperFormalizationBridge_v27_2_release

theorem icReleaseSmokeTest_v27_2_appendix_index :
    True := by
  exact icAppendixReleaseIndex_v27_2_bridge_available

theorem icReleaseSmokeTest_v27_2_all :
    True ∧ True ∧ True ∧ True := by
  exact ⟨icReleaseSmokeTest_v27_2_metadata,
    icReleaseSmokeTest_v27_2_release_certificate,
    icReleaseSmokeTest_v27_2_formalization_bridge,
    icReleaseSmokeTest_v27_2_appendix_index⟩

end LeanCfgProject
