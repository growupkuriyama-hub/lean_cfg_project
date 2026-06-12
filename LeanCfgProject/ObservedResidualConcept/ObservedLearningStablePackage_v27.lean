import LeanCfgProject.ObservedLearningConstructibilitySummary

set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false

namespace LeanCfgProject

universe u

/-
ObservedLearningStablePackage_v27.lean

Stable paper-facing consequences of the observed-learning layer.
This file depends only on the CI #166 observed-learning core.
-/

variable {Q : Type u} [Mul Q]

theorem membership_identifies_observed_relation
    {S T : Set Q}
    (h : ∀ x : Q, x ∈ S ↔ x ∈ T) :
    ∀ x y : Q,
      (canonicalObservedFrameStructure (Q := Q) S).rel x y
        ↔
      (canonicalObservedFrameStructure (Q := Q) T).rel x y := by
  have hST : S = T := finiteSet_eq_of_same_membership h
  subst T
  intro x y
  exact Iff.rfl

theorem membership_identifies_observed_residual_map
    {S T : Set Q}
    (h : ∀ x : Q, x ∈ S ↔ x ∈ T) :
    ∀ a b : Q,
      (canonicalObservedFrameStructure (Q := Q) S).residual a b =
      (canonicalObservedFrameStructure (Q := Q) T).residual a b := by
  have hST : S = T := finiteSet_eq_of_same_membership h
  subst T
  intro a b
  rfl

theorem membership_identifies_observed_singleBlock_map
    {S T : Set Q}
    (h : ∀ x : Q, x ∈ S ↔ x ∈ T) :
    ∀ a b : Q,
      (canonicalObservedFrameStructure (Q := Q) S).singleBlock a b
        ↔
      (canonicalObservedFrameStructure (Q := Q) T).singleBlock a b := by
  have hST : S = T := finiteSet_eq_of_same_membership h
  subst T
  intro a b
  exact Iff.rfl

theorem membership_identifies_stable_observed_package
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
  have hpack :=
    observedLearningConstructibility_from_membership (Q := Q) h
  constructor
  · exact hpack.1
  constructor
  · exact hpack.2.1
  constructor
  · exact hpack.2.2
  · exact membership_identifies_observed_relation (Q := Q) h

end LeanCfgProject
