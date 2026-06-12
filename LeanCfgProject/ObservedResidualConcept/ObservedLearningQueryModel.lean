import LeanCfgProject.ObservedResidualConcept.ObservedLearningConstructibilitySummary
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false

namespace LeanCfgProject

universe u

/-
ObservedLearningQueryModel.lean

A small query-model wrapper for the finite observed-learning layer.
The model abstracts the paper's statement that identifying the finite observed
subset S is enough to construct the observed frame-concept object.
-/

variable {Q : Type u} [Mul Q]

/-- A transcript certifying that two observed subsets have the same answers. -/
structure ObservedMembershipTranscript (S T : Set Q) where
  same_answers : ∀ x : Q, x ∈ S ↔ x ∈ T

theorem transcript_identifies_observed_subset
    {S T : Set Q}
    (TST : ObservedMembershipTranscript (Q := Q) S T) :
    S = T := by
  exact finiteSet_eq_of_same_membership TST.same_answers

theorem transcript_identifies_frame_structure
    {S T : Set Q}
    (TST : ObservedMembershipTranscript (Q := Q) S T) :
    canonicalObservedFrameStructure (Q := Q) S =
      canonicalObservedFrameStructure (Q := Q) T := by
  exact observedFrameStructure_identified_from_membership
    (Q := Q) TST.same_answers

theorem transcript_identifies_residuals
    {S T : Set Q}
    (TST : ObservedMembershipTranscript (Q := Q) S T) :
    ∀ a b : Q, FrameResidual S a b = FrameResidual T a b := by
  exact identified_frameResidual_from_membership
    (Q := Q) TST.same_answers

theorem transcript_identifies_singleBlock
    {S T : Set Q}
    (TST : ObservedMembershipTranscript (Q := Q) S T) :
    ∀ a b : Q, SingleObservedBlock S a b ↔ SingleObservedBlock T a b := by
  exact identified_singleBlock_from_membership
    (Q := Q) TST.same_answers

theorem transcript_constructibility_package
    {S T : Set Q}
    (TST : ObservedMembershipTranscript (Q := Q) S T) :
    canonicalObservedFrameStructure (Q := Q) S =
      canonicalObservedFrameStructure (Q := Q) T
    ∧
    (∀ a b : Q, FrameResidual S a b = FrameResidual T a b)
    ∧
    (∀ a b : Q, SingleObservedBlock S a b ↔ SingleObservedBlock T a b) := by
  exact observedLearningConstructibility_from_membership
    (Q := Q) TST.same_answers

end LeanCfgProject
