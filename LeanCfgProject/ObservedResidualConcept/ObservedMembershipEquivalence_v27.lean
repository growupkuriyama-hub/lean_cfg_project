import LeanCfgProject.ObservedResidualConcept.ObservedLearningStablePackage_v27
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false

namespace LeanCfgProject

universe u

/-
ObservedMembershipEquivalence_v27.lean

A small equivalence wrapper for the observed-learning layer.
The relation records equality of all observed membership answers.
-/

variable {Q : Type u} [Mul Q]

def ObservedMembershipEquivalent (S T : Set Q) : Prop :=
  ∀ x : Q, x ∈ S ↔ x ∈ T

theorem observedMembershipEquivalent_refl
    (S : Set Q) :
    ObservedMembershipEquivalent (Q := Q) S S := by
  intro x
  exact Iff.rfl

theorem observedMembershipEquivalent_symm
    {S T : Set Q}
    (h : ObservedMembershipEquivalent (Q := Q) S T) :
    ObservedMembershipEquivalent (Q := Q) T S := by
  intro x
  exact (h x).symm

theorem observedMembershipEquivalent_trans
    {S T U : Set Q}
    (hST : ObservedMembershipEquivalent (Q := Q) S T)
    (hTU : ObservedMembershipEquivalent (Q := Q) T U) :
    ObservedMembershipEquivalent (Q := Q) S U := by
  intro x
  exact (hST x).trans (hTU x)

theorem observedMembershipEquivalent_iff_eq
    {S T : Set Q} :
    ObservedMembershipEquivalent (Q := Q) S T ↔ S = T := by
  constructor
  · intro h
    exact finiteSet_eq_of_same_membership h
  · intro h
    subst T
    exact observedMembershipEquivalent_refl (Q := Q) S

theorem observedMembershipEquivalent_identifies_structure
    {S T : Set Q}
    (h : ObservedMembershipEquivalent (Q := Q) S T) :
    canonicalObservedFrameStructure (Q := Q) S =
      canonicalObservedFrameStructure (Q := Q) T := by
  exact observedFrameStructure_identified_from_membership (Q := Q) h

theorem observedMembershipEquivalent_identifies_stable_package
    {S T : Set Q}
    (h : ObservedMembershipEquivalent (Q := Q) S T) :
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

end LeanCfgProject
