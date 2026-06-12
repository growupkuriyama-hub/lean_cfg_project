import LeanCfgProject.ObservedResidualConcept.ICLeanAppendixIndex
import LeanCfgProject.ObservedResidualConcept.K4AdequacyPaperSummary
import LeanCfgProject.ObservedResidualConcept.ObservedSyntacticPaperCorollaries
import LeanCfgProject.ObservedResidualConcept.CarrierObservedAdequacyCorollaries
import LeanCfgProject.ObservedResidualConcept.ObservedSyntacticResidualCorollaries
import LeanCfgProject.ObservedResidualConcept.ObservedSyntacticBlockAdequacyCorollaries
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false

namespace LeanCfgProject

/-
ICArtifactAppendixCoverage.lean

Appendix coverage target.

This module imports the file families that correspond to the theorem/file table
in the current I&C draft.  It is useful when updating the appendix and README.
-/

theorem icArtifactAppendixCoverage_index_available :
    True := by
  trivial

theorem icArtifactAppendixCoverage_k4_available :
    True := by
  trivial

theorem icArtifactAppendixCoverage_observedSyntactic_available :
    True := by
  trivial

theorem icArtifactAppendixCoverage_carrier_available :
    True := by
  trivial

theorem icArtifactAppendixCoverage_corollaries_available :
    True := by
  trivial

theorem icArtifactAppendixCoverage_all_available :
    True ∧ True ∧ True ∧ True ∧ True := by
  exact ⟨trivial, trivial, trivial, trivial, trivial⟩

end LeanCfgProject
