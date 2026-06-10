import LeanCfgProject.NormalCosetAdequacyCorollaries
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

The point is paper-facing: normal-coset adequacy is not merely a statement
about groups as standalone monoids.  It survives inside a simple non-group
monoid obtained by adjoining a zero element.

No new residual/concept/syntactic definitions are introduced.
-/

/-- A group with an absorbing zero adjoined. -/
inductive ZeroAdjoin (G : Type*) : Type
  | zero
  | of (g : G)
  deriving DecidableEq, Repr

namespace ZeroAdjoin

variable {G : Type*}

def mul [Group G] : ZeroAdjoin G → ZeroAdjoin G → ZeroAdjoin G
  | zero, _ => zero
  | _, zero => zero
  | of x, of y => of (x * y)

instance [Group G] : Monoid (ZeroAdjoin G) where
  mul := mul
  one := of 1
  mul_assoc := by
    intro x y z
    cases x <;> cases y <;> cases z <;>
      simp [mul, mul_assoc]
  one_mul := by
    intro x
    cases x <;> simp [mul]
  mul_one := by
    intro x
    cases x <;> simp [mul]

/--
The lifted nonzero coset `sN` inside the zero-adjoined monoid.
Zero itself is not in the observed set.
-/
def LiftedCosetSet {G : Type*} [Group G] (N : Set G) (s : G) :
    Set (ZeroAdjoin G)
  | zero => False
  | of x => s⁻¹ * x ∈ N

theorem zero_not_mem_liftedCoset
    {G : Type*} [Group G] (N : Set G) (s : G) :
    zero ∉ LiftedCosetSet N s := by
  intro h
  exact h

theorem of_mem_liftedCoset_iff
    {G : Type*} [Group G] (N : Set G) (s x : G) :
    of x ∈ LiftedCosetSet N s ↔ x ∈ LeftCosetSet N s := by
  rfl

/--
If two group elements are in the same normal-subgroup coset, then their lifted
nonzero points are observed-syntactically equivalent in the zero-adjoined
monoid.
-/
theorem sameObservedSyntactic_of_same_lifted_normal_coset
    {G : Type*} [Group G] {N : Set G}
    (hN : NormalSubgroupSet G N) (s : G) {x y : G}
    (hxy : x * y⁻¹ ∈ N) :
    SameObservedSyntactic (LiftedCosetSet N s) (of x) (of y) := by
  intro alpha beta
  cases alpha with
  | zero =>
      simp [LiftedCosetSet, mul]
  | of alphaG =>
      cases beta with
      | zero =>
          simp [LiftedCosetSet, mul]
      | of betaG =>
          change
            (s⁻¹ * (alphaG * x * betaG) ∈ N ↔
              s⁻¹ * (alphaG * y * betaG) ∈ N)
          exact sameObservedSyntactic_of_same_normal_coset
            hN s hxy alphaG betaG

/--
For nonzero outer frames, lifted residual membership in the zero-adjoined monoid
is exactly ordinary residual membership in the group.
-/
theorem lifted_residual_mem_iff
    {G : Type*} [Group G] {N : Set G} (s a b x : G) :
    (of x : ZeroAdjoin G) ∈
        TwoSidedResidual (LiftedCosetSet N s) (of a) (of b)
      ↔
    x ∈ TwoSidedResidual (LeftCosetSet N s) a b := by
  rfl

/--
A lifted normal-coset residual over nonzero frames is a single observed-syntactic
block.
-/
theorem lifted_normalCoset_residual_single_observed_block
    {G : Type*} [Group G] {N : Set G}
    (hN : NormalSubgroupSet G N) (s a b : G) :
    ∀ x y : G,
      (of x : ZeroAdjoin G) ∈
        TwoSidedResidual (LiftedCosetSet N s) (of a) (of b) →
      (of y : ZeroAdjoin G) ∈
        TwoSidedResidual (LiftedCosetSet N s) (of a) (of b) →
      SameObservedSyntactic (LiftedCosetSet N s) (of x) (of y) := by
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
    {G : Type*} [Group G] {N : Set G} (s a b : G) :
    (zero : ZeroAdjoin G) ∉
      TwoSidedResidual (LiftedCosetSet N s) (of a) (of b) := by
  intro h
  change False at h
  exact h

/--
The whole lifted residual over nonzero frames is a single observed-syntactic
block, now stated as a subset of the zero-adjoined monoid.
-/
theorem lifted_normalCoset_residual_singleBlockOn
    {G : Type*} [Group G] {N : Set G}
    (hN : NormalSubgroupSet G N) (s a b : G) :
    SingleObservedSyntacticBlockOn
      (LiftedCosetSet N s)
      (TwoSidedResidual (LiftedCosetSet N s) (of a) (of b)) := by
  intro x hx y hy
  cases x with
  | zero =>
      exact False.elim ((zero_not_mem_lifted_nonzero_residual s a b) hx)
  | of xG =>
      cases y with
      | zero =>
          exact False.elim ((zero_not_mem_lifted_nonzero_residual s a b) hy)
      | of yG =>
          exact lifted_normalCoset_residual_single_observed_block
            hN s a b xG yG hx hy

/--
Zero-adjoined normal-coset residuals over nonzero frames satisfy uniform
adequacy.
-/
theorem lifted_normalCoset_uniformAdequacyOn_residual
    {G : Type*} [Group G] {N : Set G}
    (hN : NormalSubgroupSet G N) (s a b : G) :
    UniformAdequacyOn
      (LiftedCosetSet N s)
      (TwoSidedResidual (LiftedCosetSet N s) (of a) (of b)) := by
  exact
    (uniformAdequacyOn_iff_singleObservedSyntacticBlockOn_residual
      (LiftedCosetSet N s) (of a) (of b)).2
      (lifted_normalCoset_residual_singleBlockOn hN s a b)

/--
Concrete nonempty-subset form in the zero-adjoined monoid.
-/
theorem lifted_normalCoset_nonempty_subset_generates_residual
    {G : Type*} [Group G] {N : Set G}
    (hN : NormalSubgroupSet G N) (s a b : G)
    (U : Set (ZeroAdjoin G))
    (hne : ∃ x : ZeroAdjoin G, x ∈ U)
    (hU : U ⊆ TwoSidedResidual (LiftedCosetSet N s) (of a) (of b)) :
    ConceptClosure (LiftedCosetSet N s) U =
      TwoSidedResidual (LiftedCosetSet N s) (of a) (of b) := by
  exact lifted_normalCoset_uniformAdequacyOn_residual hN s a b U hne hU

/--
Package theorem for paper use.
-/
theorem lifted_normalCoset_adequacy_package
    {G : Type*} [Group G] {N : Set G}
    (hN : NormalSubgroupSet G N) (s a b : G) :
    SingleObservedSyntacticBlockOn
      (LiftedCosetSet N s)
      (TwoSidedResidual (LiftedCosetSet N s) (of a) (of b))
    ∧
    UniformAdequacyOn
      (LiftedCosetSet N s)
      (TwoSidedResidual (LiftedCosetSet N s) (of a) (of b)) := by
  exact ⟨lifted_normalCoset_residual_singleBlockOn hN s a b,
    lifted_normalCoset_uniformAdequacyOn_residual hN s a b⟩

end ZeroAdjoin
end ZeroAdjoinedNormalCoset
end LeanCfgProject
