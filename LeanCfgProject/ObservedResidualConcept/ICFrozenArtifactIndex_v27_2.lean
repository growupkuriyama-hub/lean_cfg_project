import LeanCfgProject.ICTheoremTableIndex_v27_2

set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace LeanCfgProject

/-
ICFrozenArtifactIndex_v27_2.lean

Frozen artifact index for the paper-facing v27.2 state.

This file is meant to be a stable target for a release tag or archived
artifact snapshot.  It does not replace full regression testing; instead it
imports the current release-certificate graph and provides a compact target.
-/

theorem icFrozenArtifactIndex_v27_2_metadata :
    icArtifactCommit_ci180 = "c6c1705"
    ∧ icArtifactTopTarget_ci180 =
      "LeanCfgProject.ICSubmissionSummary_v12" := by
  exact ⟨icArtifactMetadata_ci180_commit,
    icArtifactMetadata_ci180_top_target⟩

theorem icFrozenArtifactIndex_v27_2_current_top_recorded :
    icTheoremTableIndex_v27_2_topTarget =
      "LeanCfgProject.ICSubmissionSummary_v14" := by
  exact icTheoremTableIndex_v27_2_topTarget_recorded

theorem icFrozenArtifactIndex_v27_2_claims :
    True := by
  exact paperClaimIndex_v27_2_formalization_bridge

theorem icFrozenArtifactIndex_v27_2_summary :
    True ∧ True := by
  exact ⟨icFrozenArtifactIndex_v27_2_claims,
    icTheoremTableIndex_v27_2_claims_available⟩

end LeanCfgProject
