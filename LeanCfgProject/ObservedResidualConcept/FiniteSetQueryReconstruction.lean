import LeanCfgProject.ObservedFrameStructureDecidable

set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false

namespace LeanCfgProject

universe u

/-
FiniteSetQueryReconstruction.lean

Finite-set reconstruction layer for the observed subset S.

The statements here say only that the observed subset S is determined by its
membership answers on Q.
-/

variable {Q : Type u}

/-- A hypothesis subset is correct exactly when it has the same memberships. -/
theorem finiteSet_eq_of_same_membership
    {S T : Set Q}
    (h : ∀ x : Q, x ∈ S ↔ x ∈ T) :
    S = T := by
  ext x
  exact h x

/-- If two subsets differ, some element separates their membership answers. -/
theorem finiteSet_counterexample_of_ne
    {S T : Set Q}
    (hneq : S ≠ T) :
    ∃ x : Q, ¬ (x ∈ S ↔ x ∈ T) := by
  classical
  by_contra hnone
  apply hneq
  ext x
  by_cases hx : x ∈ S ↔ x ∈ T
  · exact hx
  · exact False.elim (hnone ⟨x, hx⟩)

/--
A finite-set reconstruction package: once all membership bits on Q agree, the
observed subsets are equal.
-/
theorem finiteSet_reconstruction_package
    [Mul Q] {S T : Set Q}
    (h : ∀ x : Q, x ∈ S ↔ x ∈ T) :
    S = T ∧
    (canonicalObservedFrameStructure (Q := Q) S).rel =
      (canonicalObservedFrameStructure (Q := Q) T).rel := by
  have hST : S = T := finiteSet_eq_of_same_membership h
  constructor
  · exact hST
  · subst T
    rfl

end LeanCfgProject
