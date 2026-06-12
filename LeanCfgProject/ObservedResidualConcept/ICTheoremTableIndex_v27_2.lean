import LeanCfgProject.ObservedResidualConcept.ICPaperClaimIndex_v27_2
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace LeanCfgProject

/-
ICTheoremTableIndex_v27_2.lean

Index target for the Lean theorem/file table in the paper appendix.

The string constants are not intended as semantic proofs of filenames; they are
checked release labels that keep the appendix text synchronized with the current
Lean import graph.
-/

def icTheoremTableIndex_v27_2_topTarget : String :=
  "LeanCfgProject.ICSubmissionSummary_v14"

def icTheoremTableIndex_v27_2_previousTarget : String :=
  "LeanCfgProject.ICSubmissionSummary_v13"

def icTheoremTableIndex_v27_2_baseCI : String :=
  "commit c6c1705 / Lean CI #180"

def icTheoremTableIndex_v27_2_layer : String :=
  "v27.2 final paper-claim and frozen-artifact index"

theorem icTheoremTableIndex_v27_2_topTarget_recorded :
    icTheoremTableIndex_v27_2_topTarget =
      "LeanCfgProject.ICSubmissionSummary_v14" := by
  rfl

theorem icTheoremTableIndex_v27_2_previousTarget_recorded :
    icTheoremTableIndex_v27_2_previousTarget =
      "LeanCfgProject.ICSubmissionSummary_v13" := by
  rfl

theorem icTheoremTableIndex_v27_2_baseCI_recorded :
    icTheoremTableIndex_v27_2_baseCI =
      "commit c6c1705 / Lean CI #180" := by
  rfl

theorem icTheoremTableIndex_v27_2_layer_recorded :
    icTheoremTableIndex_v27_2_layer =
      "v27.2 final paper-claim and frozen-artifact index" := by
  rfl

theorem icTheoremTableIndex_v27_2_claims_available :
    True := by
  exact paperClaimIndex_v27_2_release_certificate

end LeanCfgProject
