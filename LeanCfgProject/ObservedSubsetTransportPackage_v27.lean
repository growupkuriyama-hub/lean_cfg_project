import LeanCfgProject.ObservedSubsetStability

set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace LeanCfgProject

universe u

/-
ObservedSubsetTransportPackage_v27.lean

Paper-facing package for transporting observed syntactic data along equality
of the observed subset.  This module avoids structure-level equality between
indexed frame models and records only the pointwise data used by the paper.
-/

variable {Q : Type u} [Mul Q]

theorem same_observed_subset_transport_package
    {S T : Set Q} (hST : S = T) :
    (∀ x y : Q, SameObservedSyntactic S x y ↔ SameObservedSyntactic T x y)
    ∧
    (∀ gamma : Q, CanonicalPoint S gamma = CanonicalPoint T gamma)
    ∧
    (∀ a b : Q, CanonicalFrame S a b = CanonicalFrame T a b)
    ∧
    (∀ a b : Q, FrameResidual S a b = FrameResidual T a b)
    ∧
    (∀ a b : Q, SingleObservedBlock S a b ↔ SingleObservedBlock T a b) := by
  constructor
  · intro x y
    exact same_observed_subset_same_sameObservedSyntactic (Q := Q) hST x y
  constructor
  · intro gamma
    exact same_observed_subset_same_canonicalPoint (Q := Q) hST gamma
  constructor
  · intro a b
    exact same_observed_subset_same_canonicalFrame (Q := Q) hST a b
  constructor
  · intro a b
    exact same_observed_subset_same_frameResidual (Q := Q) hST a b
  · intro a b
    exact same_observed_subset_same_singleBlock (Q := Q) hST a b

theorem transcript_transport_package
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
  have hST : S = T := transcript_identifies_observed_subset (Q := Q) Tr
  exact same_observed_subset_transport_package (Q := Q) hST

theorem transcript_transport_observed_structure_package
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
  constructor
  · intro x y
    exact transcript_identifies_observed_structure_rel (Q := Q) Tr x y
  constructor
  · intro a b
    exact transcript_identifies_observed_structure_residual (Q := Q) Tr a b
  · intro a b
    exact transcript_identifies_observed_structure_singleBlock (Q := Q) Tr a b

end LeanCfgProject
