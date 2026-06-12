import LeanCfgProject.ObservedSubsetTransportPackage_v27
import LeanCfgProject.ObservedLearningStablePackage_v27

set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace LeanCfgProject

universe u

/-
ObservedLearningReleaseTheorems_v27.lean

Release-facing theorem package for the observed-learning layer.
-/

variable {Q : Type u} [Mul Q]

theorem observedLearning_release_membership_to_structure
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
  exact membership_identifies_stable_observed_package (Q := Q) h

theorem observedLearning_release_transcript_to_transport
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
  exact transcript_transport_package (Q := Q) Tr

theorem observedLearning_release_transcript_to_observed_structure
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
  exact transcript_transport_observed_structure_package (Q := Q) Tr

theorem observedLearning_release_summary :
    True := by
  trivial

end LeanCfgProject
