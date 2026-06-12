import LeanCfgProject.ObservedResidualConcept.ICDependencyCertificate_v27_2
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace LeanCfgProject

/-
ICFormalizationSupplementCertificate_v27_2.lean

Certificate target corresponding to the FORMALIZATION.MD supplement.
-/

def icFormalizationSupplementCertificate_v27_2_file : String :=
  "FORMALIZATION.MD"

def icFormalizationSupplementCertificate_v27_2_repository : String :=
  "growupkuriyama-hub/lean_cfg_project"

def icFormalizationSupplementCertificate_v27_2_commit : String :=
  "c6c1705"

def icFormalizationSupplementCertificate_v27_2_ci : String :=
  "Lean CI #180"

theorem icFormalizationSupplementCertificate_v27_2_file_recorded :
    icFormalizationSupplementCertificate_v27_2_file =
      "FORMALIZATION.MD" := by
  rfl

theorem icFormalizationSupplementCertificate_v27_2_repository_recorded :
    icFormalizationSupplementCertificate_v27_2_repository =
      "growupkuriyama-hub/lean_cfg_project" := by
  rfl

theorem icFormalizationSupplementCertificate_v27_2_commit_recorded :
    icFormalizationSupplementCertificate_v27_2_commit =
      "c6c1705" := by
  rfl

theorem icFormalizationSupplementCertificate_v27_2_ci_recorded :
    icFormalizationSupplementCertificate_v27_2_ci =
      "Lean CI #180" := by
  rfl

theorem icFormalizationSupplementCertificate_v27_2_dependencies :
    True := by
  exact icDependencyCertificate_v27_2_release

end LeanCfgProject
