import LeanCfgProject.ObservedResidualConcept.ObservedSyntacticConcept
import Mathlib.Tactic

set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace LeanCfgProject
namespace NormalCosetAdequacy

/-
Normal-coset adequacy core.

This module proves the group-theoretic single-block core behind the paper's
normal-coset adequacy corollary.

We avoid depending on Mathlib's subgroup-coset API and instead use a small
set-level normal-subgroup interface.  This keeps the theorem directly aligned
with the paper proof and with the existing `SameObservedSyntactic` /
`TwoSidedResidual` definitions.

No residual, closure, or observed-syntactic relation is redefined.
-/

/-- A set-level normal subgroup interface for a group. -/
structure NormalSubgroupSet (G : Type*) [Group G] (N : Set G) : Prop where
  one_mem : (1 : G) ∈ N
  mul_mem : ∀ {x y : G}, x ∈ N → y ∈ N → x * y ∈ N
  inv_mem : ∀ {x : G}, x ∈ N → x⁻¹ ∈ N
  conj_mem : ∀ (g : G) {x : G}, x ∈ N → g * x * g⁻¹ ∈ N

/-- The left coset `sN`, written without using Mathlib coset notation. -/
def LeftCosetSet {G : Type*} [Group G] (N : Set G) (s : G) : Set G :=
  fun x => s⁻¹ * x ∈ N

theorem mem_iff_of_mul_inv_mem
    {G : Type*} [Group G] {N : Set G}
    (hN : NormalSubgroupSet G N) {x y : G}
    (hxy : x * y⁻¹ ∈ N) :
    x ∈ N ↔ y ∈ N := by
  constructor
  · intro hx
    have hy_eq : y = (x * y⁻¹)⁻¹ * x := by
      group
    rw [hy_eq]
    exact hN.mul_mem (hN.inv_mem hxy) hx
  · intro hy
    have hx_eq : x = (x * y⁻¹) * y := by
      group
    rw [hx_eq]
    exact hN.mul_mem hxy hy

theorem normal_mem_of_conjugate_mem
    {G : Type*} [Group G] {N : Set G}
    (hN : NormalSubgroupSet G N) (g x : G)
    (h : g * x * g⁻¹ ∈ N) :
    x ∈ N := by
  have hback := hN.conj_mem g⁻¹ h
  have hback_eq : g⁻¹ * (g * x * g⁻¹) * (g⁻¹)⁻¹ = x := by
    group
  rw [hback_eq] at hback
  exact hback

theorem residual_mem_pair_difference_mem
    {G : Type*} [Group G] {N : Set G}
    (hN : NormalSubgroupSet G N) (s a b x y : G)
    (hx : x ∈ TwoSidedResidual (LeftCosetSet N s) a b)
    (hy : y ∈ TwoSidedResidual (LeftCosetSet N s) a b) :
    x * y⁻¹ ∈ N := by
  change s⁻¹ * (a * x * b) ∈ N at hx
  change s⁻¹ * (a * y * b) ∈ N at hy
  have hmul :
      (s⁻¹ * (a * x * b)) * (s⁻¹ * (a * y * b))⁻¹ ∈ N :=
    hN.mul_mem hx (hN.inv_mem hy)
  have hconj :
      (s⁻¹ * a) * (x * y⁻¹) * (s⁻¹ * a)⁻¹ ∈ N := by
    have heq :
        (s⁻¹ * (a * x * b)) * (s⁻¹ * (a * y * b))⁻¹
          =
        (s⁻¹ * a) * (x * y⁻¹) * (s⁻¹ * a)⁻¹ := by
      group
    rwa [← heq]
  exact normal_mem_of_conjugate_mem hN (s⁻¹ * a) (x * y⁻¹) hconj

theorem context_pair_difference_mem
    {G : Type*} [Group G] {N : Set G}
    (hN : NormalSubgroupSet G N) (s alpha beta x y : G)
    (hxy : x * y⁻¹ ∈ N) :
    (s⁻¹ * (alpha * x * beta)) *
      (s⁻¹ * (alpha * y * beta))⁻¹ ∈ N := by
  have hconj := hN.conj_mem (s⁻¹ * alpha) hxy
  have heq :
      (s⁻¹ * alpha) * (x * y⁻¹) * (s⁻¹ * alpha)⁻¹
        =
      (s⁻¹ * (alpha * x * beta)) *
        (s⁻¹ * (alpha * y * beta))⁻¹ := by
    group
  rwa [← heq]

theorem sameObservedSyntactic_of_same_normal_coset
    {G : Type*} [Group G] {N : Set G}
    (hN : NormalSubgroupSet G N) (s : G) {x y : G}
    (hxy : x * y⁻¹ ∈ N) :
    SameObservedSyntactic (LeftCosetSet N s) x y := by
  intro alpha beta
  change
    (s⁻¹ * (alpha * x * beta) ∈ N ↔
      s⁻¹ * (alpha * y * beta) ∈ N)
  have hdiff :
      (s⁻¹ * (alpha * x * beta)) *
        (s⁻¹ * (alpha * y * beta))⁻¹ ∈ N :=
    context_pair_difference_mem hN s alpha beta x y hxy
  exact mem_iff_of_mul_inv_mem hN hdiff

/--
Normal-coset residuals are single observed-syntactic blocks.

If `S = sN` and `N` is normal, then every residual `Res_S(a,b)` is contained
in one `SameObservedSyntactic S` block.
-/
theorem normalCoset_residual_single_observed_block
    {G : Type*} [Group G] {N : Set G}
    (hN : NormalSubgroupSet G N) (s a b : G) :
    ∀ x y : G,
      x ∈ TwoSidedResidual (LeftCosetSet N s) a b →
      y ∈ TwoSidedResidual (LeftCosetSet N s) a b →
      SameObservedSyntactic (LeftCosetSet N s) x y := by
  intro x y hx hy
  have hxy : x * y⁻¹ ∈ N :=
    residual_mem_pair_difference_mem hN s a b x y hx hy
  exact sameObservedSyntactic_of_same_normal_coset hN s hxy

/--
Paper-facing corollary form: every nonempty subset of a normal-coset residual
lies in one observed-syntactic block.

The final equality `cl_S(U)=Res_S(a,b)` is supplied by the already checked
uniform-adequacy theorem; this module isolates the group/coset hypothesis that
feeds that theorem.
-/
theorem normalCoset_subset_single_observed_block
    {G : Type*} [Group G] {N : Set G}
    (hN : NormalSubgroupSet G N) (s a b : G) :
    ∀ U : Set G,
      U ⊆ TwoSidedResidual (LeftCosetSet N s) a b →
      ∀ x y : G, x ∈ U → y ∈ U →
        SameObservedSyntactic (LeftCosetSet N s) x y := by
  intro U hU x y hx hy
  exact normalCoset_residual_single_observed_block hN s a b
    x y (hU hx) (hU hy)

end NormalCosetAdequacy
end LeanCfgProject
