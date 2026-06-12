import LeanCfgProject.ObservedResidualConcept.ZeroAdjoinedNormalCosetAdequacy
import LeanCfgProject.ObservedResidualConcept.NormalCosetSyntacticCharacterization
import Mathlib.Tactic

set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace LeanCfgProject
namespace ZeroAdjoinedNormalCoset

open NormalCosetAdequacy
open NormalCosetSyntacticCharacterization

namespace ZeroAdjoin

/-
Zero-adjoined normal-coset syntactic characterization.

This is the nonzero-part analogue of the exact normal-coset characterization:

  SameObservedSyntactic (lift(sN)) (nz x) (nz y) iff x*y⁻¹ ∈ N.

It shows that adjoining an absorbing zero does not disturb the normal-coset
observed syntactic blocks on the nonzero component.
-/

universe u

variable {G : Type u} [Group G] {N : Set G}

/--
Forward direction on the nonzero part of the zero-adjoined monoid.
-/
theorem pair_difference_mem_of_sameObservedSyntactic_lifted_normalCoset
    (hN : NormalSubgroupSet G N) (s x y : G)
    (hsame : SameObservedSyntactic (LiftedCosetSet N s) (nz x) (nz y)) :
    x * y⁻¹ ∈ N := by
  have hctx := hsame (nz s) (nz y⁻¹)
  have hy :
      (nz s : ZeroAdjoin G) * nz y * nz y⁻¹ ∈
        LiftedCosetSet N s := by
    change s⁻¹ * ((s * y) * y⁻¹) ∈ N
    have heq : s⁻¹ * ((s * y) * y⁻¹) = 1 := by
      group
    rw [heq]
    exact hN.one_mem
  have hx :
      (nz s : ZeroAdjoin G) * nz x * nz y⁻¹ ∈
        LiftedCosetSet N s :=
    hctx.mpr hy
  change s⁻¹ * ((s * x) * y⁻¹) ∈ N at hx
  have heq : s⁻¹ * ((s * x) * y⁻¹) = x * y⁻¹ := by
    group
  rwa [heq] at hx

/--
Exact observed syntactic block characterization on the nonzero component.
-/
theorem sameObservedSyntactic_lifted_normalCoset_iff_pair_difference_mem
    (hN : NormalSubgroupSet G N) (s x y : G) :
    SameObservedSyntactic (LiftedCosetSet N s) (nz x) (nz y)
      ↔
    x * y⁻¹ ∈ N := by
  constructor
  · intro hsame
    exact pair_difference_mem_of_sameObservedSyntactic_lifted_normalCoset
      hN s x y hsame
  · intro hxy
    exact sameObservedSyntactic_of_same_lifted_normal_coset hN s hxy

/--
If two lifted nonzero elements lie in the same lifted residual over nonzero
outer frames, then their group components differ by an element of N.
-/
theorem pair_difference_mem_of_both_mem_lifted_normalCoset_residual
    (hN : NormalSubgroupSet G N) (s a b x y : G)
    (hx : (nz x : ZeroAdjoin G) ∈
      TwoSidedResidual (LiftedCosetSet N s) (nz a) (nz b))
    (hy : (nz y : ZeroAdjoin G) ∈
      TwoSidedResidual (LiftedCosetSet N s) (nz a) (nz b)) :
    x * y⁻¹ ∈ N := by
  have hxG : x ∈ TwoSidedResidual (LeftCosetSet N s) a b := by
    exact (lifted_residual_mem_iff s a b x).1 hx
  have hyG : y ∈ TwoSidedResidual (LeftCosetSet N s) a b := by
    exact (lifted_residual_mem_iff s a b y).1 hy
  exact residual_mem_pair_difference_mem hN s a b x y hxG hyG

/--
Package theorem for paper use.
-/
theorem lifted_normalCoset_syntactic_characterization_package
    (hN : NormalSubgroupSet G N) (s : G) :
    (∀ x y : G,
      SameObservedSyntactic (LiftedCosetSet N s) (nz x) (nz y)
        ↔
      x * y⁻¹ ∈ N)
    ∧
    (∀ a b x y : G,
      (nz x : ZeroAdjoin G) ∈
        TwoSidedResidual (LiftedCosetSet N s) (nz a) (nz b) →
      (nz y : ZeroAdjoin G) ∈
        TwoSidedResidual (LiftedCosetSet N s) (nz a) (nz b) →
      x * y⁻¹ ∈ N) := by
  constructor
  · intro x y
    exact sameObservedSyntactic_lifted_normalCoset_iff_pair_difference_mem
      hN s x y
  · intro a b x y hx hy
    exact pair_difference_mem_of_both_mem_lifted_normalCoset_residual
      hN s a b x y hx hy

end ZeroAdjoin
end ZeroAdjoinedNormalCoset
end LeanCfgProject
