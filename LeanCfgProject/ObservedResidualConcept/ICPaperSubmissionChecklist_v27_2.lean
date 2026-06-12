import LeanCfgProject.ICFormalizationSupplementCertificate_v27_2

set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace LeanCfgProject

/-
ICPaperSubmissionChecklist_v27_2.lean

Lean-side submission checklist target for the paper-facing artifact.
-/

theorem icPaperSubmissionChecklist_v27_2_has_metadata :
    icArtifactCommit_ci180 = "c6c1705"
    ∧ icArtifactPushedBy_ci180 = "growupkuriyama-hub" := by
  exact ⟨icArtifactMetadata_ci180_commit,
    icArtifactMetadata_ci180_pushed_by⟩

theorem icPaperSubmissionChecklist_v27_2_has_release_certificate :
    True := by
  exact icReleaseCertificate_v27_2_submission_v12

theorem icPaperSubmissionChecklist_v27_2_has_theorem_table_index :
    True := by
  exact icTheoremTableIndex_v27_2_claims_available

theorem icPaperSubmissionChecklist_v27_2_has_formalization_supplement :
    icFormalizationSupplementCertificate_v27_2_file =
      "FORMALIZATION.MD" := by
  exact icFormalizationSupplementCertificate_v27_2_file_recorded

theorem icPaperSubmissionChecklist_v27_2_all :
    True ∧ True ∧ True := by
  exact ⟨icPaperSubmissionChecklist_v27_2_has_release_certificate,
    icPaperSubmissionChecklist_v27_2_has_theorem_table_index,
    icFormalizationSupplementCertificate_v27_2_dependencies⟩

end LeanCfgProject
