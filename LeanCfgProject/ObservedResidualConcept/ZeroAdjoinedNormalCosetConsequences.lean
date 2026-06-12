import LeanCfgProject.ObservedResidualConcept.ZeroAdjoinedNormalCosetResidualFormula
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
Zero-adjoined consequence layer.

This is the zero-adjoined analogue of `NormalCosetConsequences`.
-/

universe u

variable {G : Type u} [Group G] {N : Set G}

/--
The shifted lifted coset is nonempty.
-/
theorem shifted_liftedCoset_nonempty
    (hN : NormalSubgroupSet G N) (s a b : G) :
    ∃ x : ZeroAdjoin G, x ∈ LiftedCosetSet N (a⁻¹ * s * b⁻¹) := by
  refine ⟨nz (a⁻¹ * s * b⁻¹), ?_⟩
  change (a⁻¹ * s * b⁻¹)⁻¹ * (a⁻¹ * s * b⁻¹) ∈ N
  have heq :
      (a⁻¹ * s * b⁻¹)⁻¹ * (a⁻¹ * s * b⁻¹) = (1 : G) := by
    group
  rw [heq]
  exact hN.one_mem

/--
If a nonempty observed state image is contained in the lifted residual, then it
generates the shifted lifted coset identified by the residual formula.
-/
theorem lifted_normalCoset_nonempty_subset_generates_shifted_liftedCoset
    (hN : NormalSubgroupSet G N) (s a b : G)
    (U : Set (ZeroAdjoin G))
    (hne : ∃ x : ZeroAdjoin G, x ∈ U)
    (hU : U ⊆ TwoSidedResidual (LiftedCosetSet N s) (nz a) (nz b)) :
    ConceptClosure (LiftedCosetSet N s) U =
      LiftedCosetSet N (a⁻¹ * s * b⁻¹) := by
  rw [lifted_normalCoset_nonempty_subset_generates_residual hN s a b U hne hU]
  exact lifted_normalCoset_residual_eq_shifted_liftedCoset hN s a b

/--
Shifted-lifted-coset input form.
-/
theorem lifted_normalCoset_nonempty_subset_of_shifted_liftedCoset_generates_shifted_liftedCoset
    (hN : NormalSubgroupSet G N) (s a b : G)
    (U : Set (ZeroAdjoin G))
    (hne : ∃ x : ZeroAdjoin G, x ∈ U)
    (hU : U ⊆ LiftedCosetSet N (a⁻¹ * s * b⁻¹)) :
    ConceptClosure (LiftedCosetSet N s) U =
      LiftedCosetSet N (a⁻¹ * s * b⁻¹) := by
  apply lifted_normalCoset_nonempty_subset_generates_shifted_liftedCoset
    hN s a b U hne
  intro x hx
  rw [lifted_normalCoset_residual_eq_shifted_liftedCoset hN s a b]
  exact hU hx

/--
The shifted lifted coset is closed by the residual concept closure induced by
the observed lifted coset.
-/
theorem lifted_normalCoset_shifted_liftedCoset_self_closure
    (hN : NormalSubgroupSet G N) (s a b : G) :
    ConceptClosure
      (LiftedCosetSet N s)
      (LiftedCosetSet N (a⁻¹ * s * b⁻¹))
      =
    LiftedCosetSet N (a⁻¹ * s * b⁻¹) := by
  exact
    lifted_normalCoset_nonempty_subset_of_shifted_liftedCoset_generates_shifted_liftedCoset
      hN s a b
      (LiftedCosetSet N (a⁻¹ * s * b⁻¹))
      (shifted_liftedCoset_nonempty hN s a b)
      (by
        intro x hx
        exact hx)

/--
Any singleton nonzero point lying in the shifted lifted coset generates that
whole shifted lifted coset.
-/
theorem lifted_normalCoset_singleton_in_shifted_liftedCoset_generates_shifted_liftedCoset
    (hN : NormalSubgroupSet G N) (s a b : G) (x : ZeroAdjoin G)
    (hx : x ∈ LiftedCosetSet N (a⁻¹ * s * b⁻¹)) :
    ConceptClosure (LiftedCosetSet N s) ({x} : Set (ZeroAdjoin G)) =
      LiftedCosetSet N (a⁻¹ * s * b⁻¹) := by
  apply lifted_normalCoset_nonempty_subset_of_shifted_liftedCoset_generates_shifted_liftedCoset
    hN s a b ({x} : Set (ZeroAdjoin G))
  · exact ⟨x, by rfl⟩
  · intro y hy
    have hy_eq : y = x := hy
    rw [hy_eq]
    exact hx

/--
Package theorem for paper use.
-/
theorem lifted_normalCoset_shifted_liftedCoset_consequence_package
    (hN : NormalSubgroupSet G N) (s a b : G) :
    (∃ x : ZeroAdjoin G, x ∈ LiftedCosetSet N (a⁻¹ * s * b⁻¹))
    ∧
    ConceptClosure
      (LiftedCosetSet N s)
      (LiftedCosetSet N (a⁻¹ * s * b⁻¹))
      =
    LiftedCosetSet N (a⁻¹ * s * b⁻¹)
    ∧
    (∀ x : ZeroAdjoin G,
      x ∈ LiftedCosetSet N (a⁻¹ * s * b⁻¹) →
      ConceptClosure (LiftedCosetSet N s) ({x} : Set (ZeroAdjoin G)) =
        LiftedCosetSet N (a⁻¹ * s * b⁻¹)) := by
  exact ⟨shifted_liftedCoset_nonempty hN s a b,
    lifted_normalCoset_shifted_liftedCoset_self_closure hN s a b,
    fun x hx =>
      lifted_normalCoset_singleton_in_shifted_liftedCoset_generates_shifted_liftedCoset
        hN s a b x hx⟩

end ZeroAdjoin
end ZeroAdjoinedNormalCoset
end LeanCfgProject
