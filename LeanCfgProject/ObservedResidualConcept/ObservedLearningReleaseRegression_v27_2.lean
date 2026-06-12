import LeanCfgProject.ObservedResidualConcept.ICSubmissionSummary_v11
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace LeanCfgProject

universe u

/-
ObservedLearningReleaseRegression_v27_2.lean

Regression target after Lean CI #180 / commit c6c1705.

This module re-exposes the observed-learning release theorems through a
single paper-facing regression layer.  It is intentionally conservative:
if this file builds, the v27.1 observed-learning release package is still
available through the current submission target.
-/

variable {Q : Type u} [Mul Q]

theorem observedLearningRegression_membership_to_structure
    {S T : Set Q}
    (h : ∀ x : Q, x ∈ S ↔ x ∈ T) :
    canonicalObservedFrameStructure (Q := Q) S =
      canonicalObservedFrameStructure (Q := Q) T
    ∧
    (∀ a b : Q, FrameResidual S a b = FrameResidual T a b)
    ∧
    (∀ a b : Q, SingleObservedBlock S a b ↔ SingleObservedBlock T a b)
    ∧
    (∀ x y : Q,
      (canonicalObservedFrameStructure (Q := Q) S).rel x y
        ↔
      (canonicalObservedFrameStructure (Q := Q) T).rel x y) := by
  exact observedLearning_release_membership_to_structure (Q := Q) h

theorem observedLearningRegression_transcript_transport
    {S T : Set Q}
    (Tr : ObservedMembershipTranscript (Q := Q) S T) :
    (∀ x y : Q, SameObservedSyntactic S x y ↔ SameObservedSyntactic T x y)
    ∧
    (∀ gamma : Q, CanonicalPoint S gamma = CanonicalPoint T gamma)
    ∧
    (∀ a b : Q, CanonicalFrame S a b = CanonicalFrame T a b)
    ∧
    (∀ a b : Q, FrameResidual S a b = FrameResidual T a b)
    ∧
    (∀ a b : Q, SingleObservedBlock S a b ↔ SingleObservedBlock T a b) := by
  exact observedLearning_release_transcript_to_transport (Q := Q) Tr

theorem observedLearningRegression_transcript_observed_structure
    {S T : Set Q}
    (Tr : ObservedMembershipTranscript (Q := Q) S T) :
    (∀ x y : Q,
      (canonicalObservedFrameStructure (Q := Q) S).rel x y
        ↔
      (canonicalObservedFrameStructure (Q := Q) T).rel x y)
    ∧
    (∀ a b : Q,
      (canonicalObservedFrameStructure (Q := Q) S).residual a b =
      (canonicalObservedFrameStructure (Q := Q) T).residual a b)
    ∧
    (∀ a b : Q,
      (canonicalObservedFrameStructure (Q := Q) S).singleBlock a b
        ↔
      (canonicalObservedFrameStructure (Q := Q) T).singleBlock a b) := by
  exact observedLearning_release_transcript_to_observed_structure (Q := Q) Tr

theorem observedLearningReleaseRegression_v27_2_summary :
    True := by
  trivial

end LeanCfgProject
