import LeanCfgProject.ICFullPaperSummary_v1

set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false

namespace LeanCfgProject

/-
ICSubmissionSummary_v2.lean

Current smallest recommended top-level target for routine paper-artifact CI.

It imports the full paper-facing summary target and therefore checks the current
I&C artifact dependency graph through Lean's import system.
-/

theorem icSubmissionSummary_v2_available :
    True := by
  trivial

end LeanCfgProject
