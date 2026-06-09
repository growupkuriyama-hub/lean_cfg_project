import LeanCfgProject.UniversalFrameModelCore

set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false

namespace LeanCfgProject

universe u

/-
CanonicalPointFrameStablePackage_v27.lean

Stable paper-facing consequences of the canonical point-frame incidence core.
This file depends only on the CI #166 point-frame core.
-/

variable {Q : Type u} [Mul Q]

theorem canonical_point_frame_incidence_checked
    (S : Set Q) (gamma a b : Q) :
    CanonicalPoint S gamma ⊆
        (canonicalObservedFrameStructure (Q := Q) S).residual a b
      ↔ a * gamma * b ∈ S := by
  exact canonicalObservedFrameStructure_represents_incidence S gamma a b

theorem canonical_point_collapse_checked
    (S : Set Q) (x y : Q) :
    CanonicalPoint S x = CanonicalPoint S y
      ↔ (canonicalObservedFrameStructure (Q := Q) S).rel x y := by
  exact canonicalObservedFrameStructure_pointCollapse S x y

theorem canonical_point_frame_core_checked
    (S : Set Q) :
    (∀ gamma a b : Q,
      CanonicalPoint S gamma ⊆
          (canonicalObservedFrameStructure (Q := Q) S).residual a b
        ↔ a * gamma * b ∈ S)
    ∧
    (∀ x y : Q,
      CanonicalPoint S x = CanonicalPoint S y
        ↔ (canonicalObservedFrameStructure (Q := Q) S).rel x y) := by
  exact universalFrameModelCore_summary (Q := Q) S

theorem canonical_point_frame_incidence_respects_membership_equality
    {S T : Set Q}
    (h : ∀ x : Q, x ∈ S ↔ x ∈ T)
    (gamma a b : Q) :
    (CanonicalPoint S gamma ⊆
        (canonicalObservedFrameStructure (Q := Q) S).residual a b)
      ↔
    (CanonicalPoint T gamma ⊆
        (canonicalObservedFrameStructure (Q := Q) T).residual a b) := by
  have hST : S = T := finiteSet_eq_of_same_membership h
  subst T
  exact Iff.rfl

theorem canonical_point_collapse_respects_membership_equality
    {S T : Set Q}
    (h : ∀ x : Q, x ∈ S ↔ x ∈ T)
    (x y : Q) :
    (CanonicalPoint S x = CanonicalPoint S y)
      ↔
    (CanonicalPoint T x = CanonicalPoint T y) := by
  have hST : S = T := finiteSet_eq_of_same_membership h
  subst T
  exact Iff.rfl

end LeanCfgProject
