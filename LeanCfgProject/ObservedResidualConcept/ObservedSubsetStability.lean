import LeanCfgProject.CanonicalFrameModelCorollaries
import LeanCfgProject.ObservedLearningQueryModel

set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace LeanCfgProject

universe u

/-
ObservedSubsetStability.lean

Safe stability lemmas for the canonical observed point/frame data under
equality of observed subsets.

This version avoids both:
1. structure-level equality between differently indexed frame models, and
2. name collisions with ObservedLearningQueryModel.
-/

variable {Q : Type u} [Mul Q]

theorem same_observed_subset_same_sameObservedSyntactic
    {S T : Set Q} (hST : S = T) (x y : Q) :
    SameObservedSyntactic S x y ↔ SameObservedSyntactic T x y := by
  cases hST
  exact Iff.rfl

theorem same_observed_subset_same_canonicalPoint
    {S T : Set Q} (hST : S = T) (gamma : Q) :
    CanonicalPoint S gamma = CanonicalPoint T gamma := by
  cases hST
  rfl

theorem same_observed_subset_same_canonicalFrame
    {S T : Set Q} (hST : S = T) (a b : Q) :
    CanonicalFrame S a b = CanonicalFrame T a b := by
  cases hST
  rfl

theorem same_observed_subset_same_frameResidual
    {S T : Set Q} (hST : S = T) (a b : Q) :
    FrameResidual S a b = FrameResidual T a b := by
  cases hST
  rfl

theorem same_observed_subset_same_singleBlock
    {S T : Set Q} (hST : S = T) (a b : Q) :
    SingleObservedBlock S a b ↔ SingleObservedBlock T a b := by
  cases hST
  exact Iff.rfl

theorem same_observed_subset_same_observed_structure_rel
    {S T : Set Q} (hST : S = T) (x y : Q) :
    (canonicalObservedFrameStructure (Q := Q) S).rel x y
      ↔
    (canonicalObservedFrameStructure (Q := Q) T).rel x y := by
  cases hST
  exact Iff.rfl

theorem same_observed_subset_same_observed_structure_residual
    {S T : Set Q} (hST : S = T) (a b : Q) :
    (canonicalObservedFrameStructure (Q := Q) S).residual a b =
      (canonicalObservedFrameStructure (Q := Q) T).residual a b := by
  cases hST
  rfl

theorem same_observed_subset_same_observed_structure_singleBlock
    {S T : Set Q} (hST : S = T) (a b : Q) :
    (canonicalObservedFrameStructure (Q := Q) S).singleBlock a b
      ↔
    (canonicalObservedFrameStructure (Q := Q) T).singleBlock a b := by
  cases hST
  exact Iff.rfl

theorem transcript_identifies_sameObservedSyntactic
    {S T : Set Q}
    (Tr : ObservedMembershipTranscript (Q := Q) S T) (x y : Q) :
    SameObservedSyntactic S x y ↔ SameObservedSyntactic T x y := by
  have hST : S = T := transcript_identifies_observed_subset (Q := Q) Tr
  exact same_observed_subset_same_sameObservedSyntactic (Q := Q) hST x y

theorem transcript_identifies_canonicalPoint
    {S T : Set Q}
    (Tr : ObservedMembershipTranscript (Q := Q) S T) (gamma : Q) :
    CanonicalPoint S gamma = CanonicalPoint T gamma := by
  have hST : S = T := transcript_identifies_observed_subset (Q := Q) Tr
  exact same_observed_subset_same_canonicalPoint (Q := Q) hST gamma

theorem transcript_identifies_canonicalFrame
    {S T : Set Q}
    (Tr : ObservedMembershipTranscript (Q := Q) S T) (a b : Q) :
    CanonicalFrame S a b = CanonicalFrame T a b := by
  have hST : S = T := transcript_identifies_observed_subset (Q := Q) Tr
  exact same_observed_subset_same_canonicalFrame (Q := Q) hST a b

theorem transcript_identifies_frameResidual
    {S T : Set Q}
    (Tr : ObservedMembershipTranscript (Q := Q) S T) (a b : Q) :
    FrameResidual S a b = FrameResidual T a b := by
  have hST : S = T := transcript_identifies_observed_subset (Q := Q) Tr
  exact same_observed_subset_same_frameResidual (Q := Q) hST a b

/-- Avoids collision with `ObservedLearningQueryModel.transcript_identifies_singleBlock`. -/
theorem transcript_identifies_singleBlock_subset_stability
    {S T : Set Q}
    (Tr : ObservedMembershipTranscript (Q := Q) S T) (a b : Q) :
    SingleObservedBlock S a b ↔ SingleObservedBlock T a b := by
  have hST : S = T := transcript_identifies_observed_subset (Q := Q) Tr
  exact same_observed_subset_same_singleBlock (Q := Q) hST a b

theorem transcript_identifies_observed_structure_rel
    {S T : Set Q}
    (Tr : ObservedMembershipTranscript (Q := Q) S T) (x y : Q) :
    (canonicalObservedFrameStructure (Q := Q) S).rel x y
      ↔
    (canonicalObservedFrameStructure (Q := Q) T).rel x y := by
  have hST : S = T := transcript_identifies_observed_subset (Q := Q) Tr
  exact same_observed_subset_same_observed_structure_rel (Q := Q) hST x y

theorem transcript_identifies_observed_structure_residual
    {S T : Set Q}
    (Tr : ObservedMembershipTranscript (Q := Q) S T) (a b : Q) :
    (canonicalObservedFrameStructure (Q := Q) S).residual a b =
      (canonicalObservedFrameStructure (Q := Q) T).residual a b := by
  have hST : S = T := transcript_identifies_observed_subset (Q := Q) Tr
  exact same_observed_subset_same_observed_structure_residual (Q := Q) hST a b

theorem transcript_identifies_observed_structure_singleBlock_subset_stability
    {S T : Set Q}
    (Tr : ObservedMembershipTranscript (Q := Q) S T) (a b : Q) :
    (canonicalObservedFrameStructure (Q := Q) S).singleBlock a b
      ↔
    (canonicalObservedFrameStructure (Q := Q) T).singleBlock a b := by
  have hST : S = T := transcript_identifies_observed_subset (Q := Q) Tr
  exact same_observed_subset_same_observed_structure_singleBlock
    (Q := Q) hST a b

theorem transcript_identifies_observed_subset_stability_package
    {S T : Set Q}
    (Tr : ObservedMembershipTranscript (Q := Q) S T) :
    (∀ x y : Q, SameObservedSyntactic S x y ↔ SameObservedSyntactic T x y)
    ∧
    (∀ gamma : Q, CanonicalPoint S gamma = CanonicalPoint T gamma)
    ∧
    (∀ a b : Q, CanonicalFrame S a b = CanonicalFrame T a b)
    ∧
    (∀ a b : Q, SingleObservedBlock S a b ↔ SingleObservedBlock T a b) := by
  constructor
  · intro x y
    exact transcript_identifies_sameObservedSyntactic (Q := Q) Tr x y
  constructor
  · intro gamma
    exact transcript_identifies_canonicalPoint (Q := Q) Tr gamma
  constructor
  · intro a b
    exact transcript_identifies_canonicalFrame (Q := Q) Tr a b
  · intro a b
    exact transcript_identifies_singleBlock_subset_stability (Q := Q) Tr a b

end LeanCfgProject
