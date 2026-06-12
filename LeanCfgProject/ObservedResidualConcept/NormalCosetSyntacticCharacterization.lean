import LeanCfgProject.ObservedResidualConcept.NormalCosetAdequacyCorollaries
import Mathlib.Tactic

set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace LeanCfgProject
namespace NormalCosetSyntacticCharacterization

open NormalCosetAdequacy
open NormalCosetAdequacyCorollaries

/-
Normal-coset syntactic characterization.

For a group G, a set-level normal subgroup N, and the observed set S = sN,
the observed syntactic equivalence is exactly equality modulo N:

  SameObservedSyntactic (sN) x y  iff  x*y⁻¹ ∈ N.

This strengthens the previous normal-coset adequacy file from a one-way
single-block theorem to an exact block characterization.
-/

variable {G : Type*} [Group G] {N : Set G}

/--
Forward direction: if `x` and `y` have the same two-sided observed membership
tests for the coset `sN`, then `x*y⁻¹ ∈ N`.
-/
theorem pair_difference_mem_of_sameObservedSyntactic_normalCoset
    (hN : NormalSubgroupSet G N) (s x y : G)
    (hsame : SameObservedSyntactic (LeftCosetSet N s) x y) :
    x * y⁻¹ ∈ N := by
  have hctx := hsame s y⁻¹
  have hy : s * y * y⁻¹ ∈ LeftCosetSet N s := by
    change s⁻¹ * ((s * y) * y⁻¹) ∈ N
    have heq : s⁻¹ * ((s * y) * y⁻¹) = 1 := by
      group
    rw [heq]
    exact hN.one_mem
  have hx : s * x * y⁻¹ ∈ LeftCosetSet N s := hctx.mpr hy
  change s⁻¹ * ((s * x) * y⁻¹) ∈ N at hx
  have heq : s⁻¹ * ((s * x) * y⁻¹) = x * y⁻¹ := by
    group
  rwa [heq] at hx

/--
Exact block characterization for normal cosets.
-/
theorem sameObservedSyntactic_normalCoset_iff_pair_difference_mem
    (hN : NormalSubgroupSet G N) (s x y : G) :
    SameObservedSyntactic (LeftCosetSet N s) x y
      ↔
    x * y⁻¹ ∈ N := by
  constructor
  · intro hsame
    exact pair_difference_mem_of_sameObservedSyntactic_normalCoset
      hN s x y hsame
  · intro hxy
    exact sameObservedSyntactic_of_same_normal_coset hN s hxy

/--
The observed syntactic block of a point is exactly its normal-subgroup coset.
-/
theorem normalCoset_block_of_point_eq_pair_difference
    (hN : NormalSubgroupSet G N) (s x y : G) :
    SameObservedSyntactic (LeftCosetSet N s) x y
      ↔
    x * y⁻¹ ∈ N := by
  exact sameObservedSyntactic_normalCoset_iff_pair_difference_mem hN s x y

/--
If two elements are in the same residual of a normal coset, then they are in the
same normal-subgroup coset.  This exposes the algebraic content behind the
single-block residual theorem.
-/
theorem pair_difference_mem_of_both_mem_normalCoset_residual
    (hN : NormalSubgroupSet G N) (s a b x y : G)
    (hx : x ∈ TwoSidedResidual (LeftCosetSet N s) a b)
    (hy : y ∈ TwoSidedResidual (LeftCosetSet N s) a b) :
    x * y⁻¹ ∈ N := by
  exact residual_mem_pair_difference_mem hN s a b x y hx hy

/--
Residual single-block theorem, restated through the exact block
characterization.
-/
theorem normalCoset_residual_sameObservedSyntactic_iff
    (hN : NormalSubgroupSet G N) (s a b x y : G)
    (hx : x ∈ TwoSidedResidual (LeftCosetSet N s) a b)
    (hy : y ∈ TwoSidedResidual (LeftCosetSet N s) a b) :
    SameObservedSyntactic (LeftCosetSet N s) x y
      ∧
    x * y⁻¹ ∈ N := by
  have hxy : x * y⁻¹ ∈ N :=
    pair_difference_mem_of_both_mem_normalCoset_residual hN s a b x y hx hy
  exact ⟨(sameObservedSyntactic_normalCoset_iff_pair_difference_mem
    hN s x y).2 hxy, hxy⟩

/--
Package theorem for paper use.
-/
theorem normalCoset_syntactic_characterization_package
    (hN : NormalSubgroupSet G N) (s : G) :
    (∀ x y : G,
      SameObservedSyntactic (LeftCosetSet N s) x y ↔ x * y⁻¹ ∈ N)
    ∧
    (∀ a b x y : G,
      x ∈ TwoSidedResidual (LeftCosetSet N s) a b →
      y ∈ TwoSidedResidual (LeftCosetSet N s) a b →
      x * y⁻¹ ∈ N) := by
  constructor
  · intro x y
    exact sameObservedSyntactic_normalCoset_iff_pair_difference_mem hN s x y
  · intro a b x y hx hy
    exact residual_mem_pair_difference_mem hN s a b x y hx hy

end NormalCosetSyntacticCharacterization
end LeanCfgProject
