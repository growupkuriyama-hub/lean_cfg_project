import LeanCfgProject.ObservedResidualConcept.ICSubmissionSummary_v1
import LeanCfgProject.ObservedResidualConcept.ICArtifactReleaseSummary
import LeanCfgProject.ObservedResidualConcept.ICArtifactAppendixCoverage
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false

namespace LeanCfgProject

/-
ICFastCI.lean

One-file fast CI target.

For ordinary pushes, building this file checks the current paper-facing import
graph while avoiding many repeated explicit workflow steps.
-/

theorem icFastCI_submission_available :
    True := by
  trivial

theorem icFastCI_release_available :
    True := by
  trivial

theorem icFastCI_appendix_available :
    True := by
  trivial

theorem icFastCI_all_available :
    True ∧ True ∧ True := by
  exact ⟨trivial, trivial, trivial⟩

end LeanCfgProject
