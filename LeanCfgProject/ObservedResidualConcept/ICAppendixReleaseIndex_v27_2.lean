import LeanCfgProject.ObservedResidualConcept.ICPaperFormalizationBridge_v27_2
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace LeanCfgProject

/-
ICAppendixReleaseIndex_v27_2.lean

A stable appendix-index target for the formalization table in the paper.
-/

def icAppendixReleaseIndex_v27_2_target : String :=
  "LeanCfgProject.ICSubmissionSummary_v13"

def icAppendixReleaseIndex_v27_2_base : String :=
  "commit c6c1705 / Lean CI #180 / ICSubmissionSummary_v12"

theorem icAppendixReleaseIndex_v27_2_target_recorded :
    icAppendixReleaseIndex_v27_2_target =
      "LeanCfgProject.ICSubmissionSummary_v13" := by
  rfl

theorem icAppendixReleaseIndex_v27_2_base_recorded :
    icAppendixReleaseIndex_v27_2_base =
      "commit c6c1705 / Lean CI #180 / ICSubmissionSummary_v12" := by
  rfl

theorem icAppendixReleaseIndex_v27_2_bridge_available :
    True := by
  exact icPaperFormalizationBridge_v27_2_release

end LeanCfgProject
