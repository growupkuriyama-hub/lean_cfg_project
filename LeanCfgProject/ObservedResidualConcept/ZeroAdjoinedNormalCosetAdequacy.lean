import LeanCfgProject.ObservedResidualConcept.NormalCosetAdequacyCorollaries
import Mathlib.Tactic

set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace LeanCfgProject
namespace ZeroAdjoinedNormalCoset

open NormalCosetAdequacy
open NormalCosetAdequacyCorollaries

/-
Zero-adjoined normal-coset adequacy.

This module adds an absorbing zero to a group and lifts the normal-coset
adequacy theorem to the nonzero part of the resulting monoid.

This version avoids fragile `simp` calls in the monoid laws and zero-context
cases.  The zero cases are closed by definitional reduction (`rfl`) or by
explicit `change False ↔ False`.
-/

universe u

/-- A group with an absorbing zero adjoined. -/
inductive ZeroAdjoin (G : Type u) : Type u where
  | z : ZeroAdjoin G
  | nz : G → ZeroAdjoin G
  deriving DecidableEq, Repr

namespace ZeroAdjoin

variable {G : Type u}

def mul [Group G] : ZeroAdjoin G → ZeroAdjoin G → ZeroAdjoin G
  | z, _ => z
  | _, z => z
  | nz x, nz y => nz (x * y)

instance [Group G] : Monoid (ZeroAdjoin G) where
  mul := mul
  one := nz 1
  mul_assoc := by
    intro x y w
    change mul (mul x y) w = mul x (mul y w)
    cases x with
    | z =>
        cases y <;> cases w <;> rfl
    | nz xg =>
        cases y with
        | z =>
            cases w <;> rfl
        | nz yg =>
            cases w with
            | z => rfl
            | nz zg =>
                change nz ((xg * yg) * zg) = nz (xg * (yg * zg))
                rw [mul_assoc]
  one_mul := by
    intro x
    change mul (nz 1) x = x
    cases x with
    | z => rfl
    | nz xg =>
        change nz (1 * xg) = nz xg
        rw [one_mul]
  mul_one := by
    intro x
    change mul x (nz 1) = x
    cases x with
    | z => rfl
    | nz xg =>
        change nz (xg * 1) = nz xg
        rw [mul_one]

/--
The lifted nonzero coset `sN` inside the zero-adjoined monoid.
The absorbing zero is not in the observed set.
-/
def LiftedCosetSet {G : Type u} [Group G] (N : Set G) (s : G) :
    Set (ZeroAdjoin G)
  | z => False
  | nz x => s⁻¹ * x ∈ N

theorem zero_not_mem_liftedCoset
    {G : Type u} [Group G] (N : Set G) (s : G) :
    z ∉ LiftedCosetSet N s := by
  intro h
  exact h

theorem nz_mem_liftedCoset_iff
    {G : Type u} [Group G] (N : Set G) (s x : G) :
    nz x ∈ LiftedCosetSet N s ↔ x ∈ LeftCosetSet N s := by
  rfl

/--
If two group elements are in the same normal-subgroup coset, then their lifted
nonzero points are observed-syntactically equivalent in the zero-adjoined
monoid.
-/
theorem sameObservedSyntactic_of_same_lifted_normal_coset
    {G : Type u} [Group G] {N : Set G}
    (hN : NormalSubgroupSet G N) (s : G) {x y : G}
    (hxy : x * y⁻¹ ∈ N) :
    SameObservedSyntactic (LiftedCosetSet N s) (nz x) (nz y) := by
  intro alpha beta
  cases alpha with
  | z =>
      change False ↔ False
      rfl
  | nz alphaG =>
      cases beta with
      | z =>
          change False ↔ False
          rfl
      | nz betaG =>
          change
            (s⁻¹ * (alphaG * x * betaG) ∈ N ↔
              s⁻¹ * (alphaG * y * betaG) ∈ N)
          exact sameObservedSyntactic_of_same_normal_coset
            hN s hxy alphaG betaG

/--
For nonzero outer frames, lifted residual membership in the zero-adjoined
monoid is exactly ordinary residual membership in the group.
-/
theorem lifted_residual_mem_iff
    {G : Type u} [Group G] {N : Set G} (s a b x : G) :
    (nz x : ZeroAdjoin G) ∈
        TwoSidedResidual (LiftedCosetSet N s) (nz a) (nz b)
      ↔
    x ∈ TwoSidedResidual (LeftCosetSet N s) a b := by
  change
    (s⁻¹ * (a * x * b) ∈ N ↔
      s⁻¹ * (a * x * b) ∈ N)
  rfl

/--
A lifted normal-coset residual over nonzero frames is a single observed-syntactic
block on its nonzero elements.
-/
theorem lifted_normalCoset_residual_single_observed_block
    {G : Type u} [Group G] {N : Set G}
    (hN : NormalSubgroupSet G N) (s a b : G) :
    ∀ x y : G,
      (nz x : ZeroAdjoin G) ∈
        TwoSidedResidual (LiftedCosetSet N s) (nz a) (nz b) →
      (nz y : ZeroAdjoin G) ∈
        TwoSidedResidual (LiftedCosetSet N s) (nz a) (nz b) →
      SameObservedSyntactic (LiftedCosetSet N s) (nz x) (nz y) := by
  intro x y hx hy
  have hxG : x ∈ TwoSidedResidual (LeftCosetSet N s) a b := by
    exact (lifted_residual_mem_iff s a b x).1 hx
  have hyG : y ∈ TwoSidedResidual (LeftCosetSet N s) a b := by
    exact (lifted_residual_mem_iff s a b y).1 hy
  have hxy : x * y⁻¹ ∈ N :=
    residual_mem_pair_difference_mem hN s a b x y hxG hyG
  exact sameObservedSyntactic_of_same_lifted_normal_coset hN s hxy

/--
The zero element is not in any lifted normal-coset residual with nonzero
outer frames.
-/
theorem zero_not_mem_lifted_nonzero_residual
    {G : Type u} [Group G] {N : Set G} (s a b : G) :
    (z : ZeroAdjoin G) ∉
      TwoSidedResidual (LiftedCosetSet N s) (nz a) (nz b) := by
  intro h
  change False at h
  exact h

/--
The whole lifted residual over nonzero frames is a single observed-syntactic
block, stated as a subset of the zero-adjoined monoid.
-/
theorem lifted_normalCoset_residual_singleBlockOn
    {G : Type u} [Group G] {N : Set G}
    (hN : NormalSubgroupSet G N) (s a b : G) :
    SingleObservedSyntacticBlockOn
      (LiftedCosetSet N s)
      (TwoSidedResidual (LiftedCosetSet N s) (nz a) (nz b)) := by
  intro x hx y hy
  cases x with
  | z =>
      exact False.elim ((zero_not_mem_lifted_nonzero_residual s a b) hx)
  | nz xG =>
      cases y with
      | z =>
          exact False.elim ((zero_not_mem_lifted_nonzero_residual s a b) hy)
      | nz yG =>
          exact lifted_normalCoset_residual_single_observed_block
            hN s a b xG yG hx hy

/--
Zero-adjoined normal-coset residuals over nonzero frames satisfy uniform
adequacy.
-/
theorem lifted_normalCoset_uniformAdequacyOn_residual
    {G : Type u} [Group G] {N : Set G}
    (hN : NormalSubgroupSet G N) (s a b : G) :
    UniformAdequacyOn
      (LiftedCosetSet N s)
      (TwoSidedResidual (LiftedCosetSet N s) (nz a) (nz b)) := by
  exact
    (uniformAdequacyOn_iff_singleObservedSyntacticBlockOn_residual
      (LiftedCosetSet N s) (nz a) (nz b)).2
      (lifted_normalCoset_residual_singleBlockOn hN s a b)

/--
Concrete nonempty-subset form in the zero-adjoined monoid.
-/
theorem lifted_normalCoset_nonempty_subset_generates_residual
    {G : Type u} [Group G] {N : Set G}
    (hN : NormalSubgroupSet G N) (s a b : G)
    (U : Set (ZeroAdjoin G))
    (hne : ∃ x : ZeroAdjoin G, x ∈ U)
    (hU : U ⊆ TwoSidedResidual (LiftedCosetSet N s) (nz a) (nz b)) :
    ConceptClosure (LiftedCosetSet N s) U =
      TwoSidedResidual (LiftedCosetSet N s) (nz a) (nz b) := by
  exact lifted_normalCoset_uniformAdequacyOn_residual hN s a b U hne hU

/--
Package theorem for paper use.
-/
theorem lifted_normalCoset_adequacy_package
    {G : Type u} [Group G] {N : Set G}
    (hN : NormalSubgroupSet G N) (s a b : G) :
    SingleObservedSyntacticBlockOn
      (LiftedCosetSet N s)
      (TwoSidedResidual (LiftedCosetSet N s) (nz a) (nz b))
    ∧
    UniformAdequacyOn
      (LiftedCosetSet N s)
      (TwoSidedResidual (LiftedCosetSet N s) (nz a) (nz b)) := by
  exact ⟨lifted_normalCoset_residual_singleBlockOn hN s a b,
    lifted_normalCoset_uniformAdequacyOn_residual hN s a b⟩

end ZeroAdjoin
end ZeroAdjoinedNormalCoset
end LeanCfgProject
