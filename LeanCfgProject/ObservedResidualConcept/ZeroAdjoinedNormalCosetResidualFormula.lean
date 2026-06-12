import LeanCfgProject.ObservedResidualConcept.ZeroAdjoinedNormalCosetCharacterization
import LeanCfgProject.ObservedResidualConcept.NormalCosetResidualFormula
import Mathlib.Tactic

set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace LeanCfgProject
namespace ZeroAdjoinedNormalCoset

open NormalCosetAdequacy
open NormalCosetResidualFormula

namespace ZeroAdjoin

/-
Zero-adjoined residual formula.

For the zero-adjoined monoid, every lifted normal-coset residual over nonzero
outer frames is exactly the lifted coset with shifted base:

  Res_{lift(sN)}(nz a, nz b) = lift((a^{-1} s b^{-1})N).

This is the non-group monoid version of the previous residual formula.
-/

universe u

variable {G : Type u} [Group G] {N : Set G}

/--
Membership formula for the zero-adjoined residual.
-/
theorem lifted_normalCoset_residual_mem_iff_shifted_liftedCoset
    (hN : NormalSubgroupSet G N) (s a b : G) (x : ZeroAdjoin G) :
    x ∈ TwoSidedResidual (LiftedCosetSet N s) (nz a) (nz b)
      ↔
    x ∈ LiftedCosetSet N (a⁻¹ * s * b⁻¹) := by
  cases x with
  | z =>
      change False ↔ False
      rfl
  | nz xg =>
      change
        (s⁻¹ * (a * xg * b) ∈ N
          ↔
        (a⁻¹ * s * b⁻¹)⁻¹ * xg ∈ N)
      exact normalCoset_residual_mem_iff_leftCoset hN s a b xg

/--
Set equality form for lifted residuals.
-/
theorem lifted_normalCoset_residual_eq_shifted_liftedCoset
    (hN : NormalSubgroupSet G N) (s a b : G) :
    TwoSidedResidual (LiftedCosetSet N s) (nz a) (nz b) =
      LiftedCosetSet N (a⁻¹ * s * b⁻¹) := by
  ext x
  exact lifted_normalCoset_residual_mem_iff_shifted_liftedCoset hN s a b x

/--
The canonical nonzero base point belongs to the lifted residual.
-/
theorem lifted_normalCoset_residual_base_mem
    (hN : NormalSubgroupSet G N) (s a b : G) :
    (nz (a⁻¹ * s * b⁻¹) : ZeroAdjoin G) ∈
      TwoSidedResidual (LiftedCosetSet N s) (nz a) (nz b) := by
  exact
    (lifted_normalCoset_residual_mem_iff_shifted_liftedCoset
      hN s a b (nz (a⁻¹ * s * b⁻¹))).2
      (by
        change (a⁻¹ * s * b⁻¹)⁻¹ * (a⁻¹ * s * b⁻¹) ∈ N
        have heq :
            (a⁻¹ * s * b⁻¹)⁻¹ * (a⁻¹ * s * b⁻¹) = (1 : G) := by
          group
        rw [heq]
        exact hN.one_mem)

/--
The lifted residual is nonempty.
-/
theorem lifted_normalCoset_residual_nonempty
    (hN : NormalSubgroupSet G N) (s a b : G) :
    ∃ x : ZeroAdjoin G,
      x ∈ TwoSidedResidual (LiftedCosetSet N s) (nz a) (nz b) := by
  exact ⟨nz (a⁻¹ * s * b⁻¹),
    lifted_normalCoset_residual_base_mem hN s a b⟩

/--
The canonical lifted base point generates the whole lifted residual by concept
closure.
-/
theorem lifted_normalCoset_base_singleton_generates_residual
    (hN : NormalSubgroupSet G N) (s a b : G) :
    ConceptClosure
      (LiftedCosetSet N s)
      ({nz (a⁻¹ * s * b⁻¹)} : Set (ZeroAdjoin G))
      =
    TwoSidedResidual (LiftedCosetSet N s) (nz a) (nz b) := by
  exact lifted_normalCoset_nonempty_subset_generates_residual
    hN s a b
    ({nz (a⁻¹ * s * b⁻¹)} : Set (ZeroAdjoin G))
    ⟨nz (a⁻¹ * s * b⁻¹), by simp⟩
    (by
      intro x hx
      have hx_eq : x = nz (a⁻¹ * s * b⁻¹) := by
        simpa using hx
      simpa [hx_eq] using lifted_normalCoset_residual_base_mem hN s a b)

/--
Paper-facing package theorem.
-/
theorem lifted_normalCoset_residual_formula_package
    (hN : NormalSubgroupSet G N) (s a b : G) :
    TwoSidedResidual (LiftedCosetSet N s) (nz a) (nz b) =
      LiftedCosetSet N (a⁻¹ * s * b⁻¹)
    ∧
    (∃ x : ZeroAdjoin G,
      x ∈ TwoSidedResidual (LiftedCosetSet N s) (nz a) (nz b))
    ∧
    ConceptClosure
      (LiftedCosetSet N s)
      ({nz (a⁻¹ * s * b⁻¹)} : Set (ZeroAdjoin G))
      =
    TwoSidedResidual (LiftedCosetSet N s) (nz a) (nz b) := by
  exact ⟨lifted_normalCoset_residual_eq_shifted_liftedCoset hN s a b,
    lifted_normalCoset_residual_nonempty hN s a b,
    lifted_normalCoset_base_singleton_generates_residual hN s a b⟩

end ZeroAdjoin
end ZeroAdjoinedNormalCoset
end LeanCfgProject
