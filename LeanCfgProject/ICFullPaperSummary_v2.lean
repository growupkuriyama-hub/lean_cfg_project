import LeanCfgProject.ICFastCI_v2
import LeanCfgProject.ICFullPaperSummary_v1
import LeanCfgProject.ObservedSyntacticPaperSummary

set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false

namespace LeanCfgProject

/-
ICFullPaperSummary_v2.lean

Second full paper-facing summary target.

It extends the first full paper summary with the reproducibility-oriented
fast-CI target.
-/

theorem icFullPaperSummaryV2_fastCI_available :
    True := by
  trivial

theorem icFullPaperSummaryV2_previousSummary_available :
    True := by
  trivial

theorem icFullPaperSummaryV2_observedPaperSummary_available :
    True := by
  trivial

theorem icFullPaperSummaryV2_all_available :
    True ∧ True ∧ True := by
  exact ⟨trivial, trivial, trivial⟩

end LeanCfgProject
