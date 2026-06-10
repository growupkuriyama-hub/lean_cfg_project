import LeanCfgProject.NormalCosetSyntacticCharacterization
import LeanCfgProject.NormalCosetAdequacyCorollaries
import Mathlib.Tactic

set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace LeanCfgProject
namespace NormalCosetResidualFormula

open NormalCosetAdequacy
open NormalCosetAdequacyCorollaries
open NormalCosetSyntacticCharacterization

/-
Normal-coset residual formula.

For a group G, a set-level normal subgroup N, and S = sN, every two-sided
residual is exactly one left coset:

  Res_S(a,b) = (a^{-1} s b^{-1}) N.

This is a useful paper-facing sharpening of the normal-coset adequacy layer.
It also gives an explicit nonempty witness for every such residual.
-/

variable {G : Type*} [Group G] {N : Set G}

/--
Membership formula for normal-coset residuals.
-/
theorem normalCoset_residual_mem_iff_leftCoset
    (hN : NormalSubgroupSet G N) (s a b x : G) :
    x ∈ TwoSidedResidual (LeftCosetSet N s) a b
      ↔
    x ∈ LeftCosetSet N (a⁻¹ * s * b⁻¹) := by
  change
    (s⁻¹ * (a * x * b) ∈ N
      ↔
    (a⁻¹ * s * b⁻¹)⁻¹ * x ∈ N)
  constructor
  · intro hx
    have hc : b * (s⁻¹ * (a * x * b)) * b⁻¹ ∈ N :=
      hN.conj_mem b hx
    have heq :
        b * (s⁻¹ * (a * x * b)) * b⁻¹
          =
        (a⁻¹ * s * b⁻¹)⁻¹ * x := by
      group
    rwa [heq] at hc
  · intro hx
    have hc : b⁻¹ * ((a⁻¹ * s * b⁻¹)⁻¹ * x) * (b⁻¹)⁻¹ ∈ N :=
      hN.conj_mem b⁻¹ hx
    have heq :
        b⁻¹ * ((a⁻¹ * s * b⁻¹)⁻¹ * x) * (b⁻¹)⁻¹
          =
        s⁻¹ * (a * x * b) := by
      group
    rwa [heq] at hc

/--
Set equality form.
-/
theorem normalCoset_residual_eq_leftCoset
    (hN : NormalSubgroupSet G N) (s a b : G) :
    TwoSidedResidual (LeftCosetSet N s) a b =
      LeftCosetSet N (a⁻¹ * s * b⁻¹) := by
  ext x
  exact normalCoset_residual_mem_iff_leftCoset hN s a b x

/--
Every normal-coset residual is nonempty, with canonical witness
`a^{-1} s b^{-1}`.
-/
theorem normalCoset_residual_base_mem
    (hN : NormalSubgroupSet G N) (s a b : G) :
    a⁻¹ * s * b⁻¹ ∈
      TwoSidedResidual (LeftCosetSet N s) a b := by
  exact
    (normalCoset_residual_mem_iff_leftCoset
      hN s a b (a⁻¹ * s * b⁻¹)).2
      (by
        change (a⁻¹ * s * b⁻¹)⁻¹ * (a⁻¹ * s * b⁻¹) ∈ N
        have heq :
            (a⁻¹ * s * b⁻¹)⁻¹ * (a⁻¹ * s * b⁻¹) = (1 : G) := by
          group
        rw [heq]
        exact hN.one_mem)

/--
Explicit nonemptiness package.
-/
theorem normalCoset_residual_nonempty
    (hN : NormalSubgroupSet G N) (s a b : G) :
    ∃ x : G, x ∈ TwoSidedResidual (LeftCosetSet N s) a b := by
  exact ⟨a⁻¹ * s * b⁻¹, normalCoset_residual_base_mem hN s a b⟩

/--
The canonical base point of a normal-coset residual generates the whole residual
by concept closure.
-/
theorem normalCoset_base_singleton_generates_residual
    (hN : NormalSubgroupSet G N) (s a b : G) :
    ConceptClosure (LeftCosetSet N s) ({a⁻¹ * s * b⁻¹} : Set G) =
      TwoSidedResidual (LeftCosetSet N s) a b := by
  exact normalCoset_singleton_generates_residual
    hN s a b (a⁻¹ * s * b⁻¹)
    (normalCoset_residual_base_mem hN s a b)

/--
Paper-facing package theorem.
-/
theorem normalCoset_residual_formula_package
    (hN : NormalSubgroupSet G N) (s a b : G) :
    TwoSidedResidual (LeftCosetSet N s) a b =
      LeftCosetSet N (a⁻¹ * s * b⁻¹)
    ∧
    (∃ x : G, x ∈ TwoSidedResidual (LeftCosetSet N s) a b)
    ∧
    ConceptClosure (LeftCosetSet N s) ({a⁻¹ * s * b⁻¹} : Set G) =
      TwoSidedResidual (LeftCosetSet N s) a b := by
  exact ⟨normalCoset_residual_eq_leftCoset hN s a b,
    normalCoset_residual_nonempty hN s a b,
    normalCoset_base_singleton_generates_residual hN s a b⟩

end NormalCosetResidualFormula
end LeanCfgProject
