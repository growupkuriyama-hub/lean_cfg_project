import LeanCfgProject.NormalCosetResidualFormula
import Mathlib.Tactic

set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace LeanCfgProject
namespace NormalCosetConsequences

open NormalCosetAdequacy
open NormalCosetAdequacyCorollaries
open NormalCosetResidualFormula

/-
Normal-coset consequence layer.

The previous module proved the exact residual formula

  Res_{sN}(a,b) = (a^{-1} s b^{-1})N.

This module states the adequacy consequences directly in shifted-coset form:
every nonempty subset of the shifted coset generates the shifted coset by
residual concept closure.
-/

variable {G : Type*} [Group G] {N : Set G}

/--
The shifted coset appearing in the residual formula is nonempty.
-/
theorem shifted_leftCoset_nonempty
    (hN : NormalSubgroupSet G N) (s a b : G) :
    ∃ x : G, x ∈ LeftCosetSet N (a⁻¹ * s * b⁻¹) := by
  refine ⟨a⁻¹ * s * b⁻¹, ?_⟩
  change (a⁻¹ * s * b⁻¹)⁻¹ * (a⁻¹ * s * b⁻¹) ∈ N
  have heq :
      (a⁻¹ * s * b⁻¹)⁻¹ * (a⁻¹ * s * b⁻¹) = (1 : G) := by
    group
  rw [heq]
  exact hN.one_mem

/--
If a nonempty observed state image is contained in the residual, then it
generates the shifted coset identified by the normal-coset residual formula.
-/
theorem normalCoset_nonempty_subset_generates_shifted_leftCoset
    (hN : NormalSubgroupSet G N) (s a b : G)
    (U : Set G)
    (hne : ∃ x : G, x ∈ U)
    (hU : U ⊆ TwoSidedResidual (LeftCosetSet N s) a b) :
    ConceptClosure (LeftCosetSet N s) U =
      LeftCosetSet N (a⁻¹ * s * b⁻¹) := by
  rw [normalCoset_nonempty_subset_generates_residual hN s a b U hne hU]
  exact normalCoset_residual_eq_leftCoset hN s a b

/--
Shifted-coset input form: if a nonempty state image is contained in the shifted
coset `(a^{-1} s b^{-1})N`, then its closure is that shifted coset.
-/
theorem normalCoset_nonempty_subset_of_shifted_leftCoset_generates_shifted_leftCoset
    (hN : NormalSubgroupSet G N) (s a b : G)
    (U : Set G)
    (hne : ∃ x : G, x ∈ U)
    (hU : U ⊆ LeftCosetSet N (a⁻¹ * s * b⁻¹)) :
    ConceptClosure (LeftCosetSet N s) U =
      LeftCosetSet N (a⁻¹ * s * b⁻¹) := by
  apply normalCoset_nonempty_subset_generates_shifted_leftCoset
    hN s a b U hne
  intro x hx
  rw [normalCoset_residual_eq_leftCoset hN s a b]
  exact hU hx

/--
The shifted coset itself is closed by the residual concept closure induced by
the observed coset `sN`.
-/
theorem normalCoset_shifted_leftCoset_self_closure
    (hN : NormalSubgroupSet G N) (s a b : G) :
    ConceptClosure
      (LeftCosetSet N s)
      (LeftCosetSet N (a⁻¹ * s * b⁻¹))
      =
    LeftCosetSet N (a⁻¹ * s * b⁻¹) := by
  exact
    normalCoset_nonempty_subset_of_shifted_leftCoset_generates_shifted_leftCoset
      hN s a b
      (LeftCosetSet N (a⁻¹ * s * b⁻¹))
      (shifted_leftCoset_nonempty hN s a b)
      (by
        intro x hx
        exact hx)

/--
Any singleton point lying in the shifted coset generates that whole shifted
coset.
-/
theorem normalCoset_singleton_in_shifted_leftCoset_generates_shifted_leftCoset
    (hN : NormalSubgroupSet G N) (s a b x : G)
    (hx : x ∈ LeftCosetSet N (a⁻¹ * s * b⁻¹)) :
    ConceptClosure (LeftCosetSet N s) ({x} : Set G) =
      LeftCosetSet N (a⁻¹ * s * b⁻¹) := by
  apply normalCoset_nonempty_subset_of_shifted_leftCoset_generates_shifted_leftCoset
    hN s a b ({x} : Set G)
  · exact ⟨x, by rfl⟩
  · intro y hy
    have hy_eq : y = x := hy
    rw [hy_eq]
    exact hx

/--
Package theorem for paper use.
-/
theorem normalCoset_shifted_coset_consequence_package
    (hN : NormalSubgroupSet G N) (s a b : G) :
    (∃ x : G, x ∈ LeftCosetSet N (a⁻¹ * s * b⁻¹))
    ∧
    ConceptClosure
      (LeftCosetSet N s)
      (LeftCosetSet N (a⁻¹ * s * b⁻¹))
      =
    LeftCosetSet N (a⁻¹ * s * b⁻¹)
    ∧
    (∀ x : G,
      x ∈ LeftCosetSet N (a⁻¹ * s * b⁻¹) →
      ConceptClosure (LeftCosetSet N s) ({x} : Set G) =
        LeftCosetSet N (a⁻¹ * s * b⁻¹)) := by
  exact ⟨shifted_leftCoset_nonempty hN s a b,
    normalCoset_shifted_leftCoset_self_closure hN s a b,
    fun x hx =>
      normalCoset_singleton_in_shifted_leftCoset_generates_shifted_leftCoset
        hN s a b x hx⟩

end NormalCosetConsequences
end LeanCfgProject
