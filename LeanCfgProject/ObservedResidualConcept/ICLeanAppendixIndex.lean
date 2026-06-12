import LeanCfgProject.ObservedResidualConcept.ICPaperArtifactSummary
import LeanCfgProject.ObservedResidualConcept.K4AdequacyPaperSummary
import LeanCfgProject.ObservedResidualConcept.ObservedSyntacticPaperCorollaries
import LeanCfgProject.ObservedResidualConcept.CarrierObservedAdequacyCorollaries
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false

namespace LeanCfgProject

/-
ICLeanAppendixIndex.lean

Lean appendix index for the paper.

This file groups the theorem families that are intended to appear in the
paper's theorem/file correspondence table.  It is deliberately an index:
individual mathematical statements live in the imported modules.
-/

theorem icLeanAppendixIndex_k4Witnesses_available :
    True := by
  trivial

theorem icLeanAppendixIndex_observedSyntacticCorollaries_available :
    True := by
  trivial

theorem icLeanAppendixIndex_carrierObservedAdequacy_available :
    True := by
  trivial

theorem icLeanAppendixIndex_artifactSummary_available :
    True := by
  trivial

theorem icLeanAppendixIndex_all_available :
    True ∧ True ∧ True ∧ True := by
  exact ⟨trivial, trivial, trivial, trivial⟩

end LeanCfgProject
