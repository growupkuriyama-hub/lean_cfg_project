import LeanCfgProject.ICReleaseCertificate_v27_2

set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace LeanCfgProject

universe u

/-
ObservedLearningCertificate_v27_2.lean

Paper-facing certificate for observed-learning release regression.
-/

variable {Q : Type u} [Mul Q]

theorem observedLearningCertificate_membership
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
  exact observedLearningRegression_membership_to_structure (Q := Q) h

theorem observedLearningCertificate_transcript
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
  exact observedLearningRegression_transcript_transport (Q := Q) Tr

theorem observedLearningCertificate_observed_structure
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
  exact observedLearningRegression_transcript_observed_structure (Q := Q) Tr

theorem observedLearningCertificate_v27_2_available :
    True := by
  exact icReleaseCertificate_v27_2_manifest

end LeanCfgProject
