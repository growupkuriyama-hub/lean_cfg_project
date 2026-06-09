import LeanCfgProject.ICSubmissionSummary_v12

set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace LeanCfgProject

/-
ICArtifactMetadata_ci180.lean

Machine-checkable metadata capsule for the paper-facing artifact state.

This file does not ask Lean to verify GitHub metadata.  Instead it records
the paper-facing release identifiers as ordinary Lean definitions and checks
that the intended strings are present at the current import target.
-/

def icArtifactCommit_ci180 : String := "c6c1705"

def icArtifactCIRun_ci180 : String := "Lean CI #180"

def icArtifactPushedBy_ci180 : String := "growupkuriyama-hub"

def icArtifactTopTarget_ci180 : String :=
  "LeanCfgProject.ICSubmissionSummary_v12"

def icArtifactPredecessorTopTarget_ci180 : String :=
  "LeanCfgProject.ICSubmissionSummary_v11"

theorem icArtifactMetadata_ci180_commit :
    icArtifactCommit_ci180 = "c6c1705" := by
  rfl

theorem icArtifactMetadata_ci180_ci_run :
    icArtifactCIRun_ci180 = "Lean CI #180" := by
  rfl

theorem icArtifactMetadata_ci180_pushed_by :
    icArtifactPushedBy_ci180 = "growupkuriyama-hub" := by
  rfl

theorem icArtifactMetadata_ci180_top_target :
    icArtifactTopTarget_ci180 =
      "LeanCfgProject.ICSubmissionSummary_v12" := by
  rfl

theorem icArtifactMetadata_ci180_predecessor_top_target :
    icArtifactPredecessorTopTarget_ci180 =
      "LeanCfgProject.ICSubmissionSummary_v11" := by
  rfl

theorem icArtifactMetadata_ci180_summary :
    icArtifactMetadata_ci180_commit = rfl
    ∧ icArtifactMetadata_ci180_ci_run = rfl
    ∧ icArtifactMetadata_ci180_pushed_by = rfl
    ∧ icArtifactMetadata_ci180_top_target = rfl
    ∧ icArtifactMetadata_ci180_predecessor_top_target = rfl := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

end LeanCfgProject
