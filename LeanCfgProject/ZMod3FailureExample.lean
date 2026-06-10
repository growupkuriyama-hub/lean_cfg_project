import LeanCfgProject.ObservedSyntacticConcept

set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace LeanCfgProject
namespace ZMod3FailureExample

/-
Finite example (2): the Z/3 failure example.

Representation choice:
  Instead of using `Multiplicative (ZMod 3)`, we use an explicit three-element
  inductive type with the addition-mod-3 multiplication table.  This is more
  robust for CI because all cases reduce by `cases`, `simp`, and `decide`.

This file uses the existing definitions from ObservedSyntacticConcept.lean /
ResidualConcept.lean:
  TwoSidedResidual, CommonContexts, ElementsOfContexts, ConceptClosure,
  SameObservedSyntactic.
No residual, closure, or syntactic relation is redefined.
-/

inductive Z3 : Type
  | C0
  | C1
  | C2
  deriving DecidableEq, Repr, Fintype

open Z3

def z0 : Z3 := C0
def z1 : Z3 := C1
def z2 : Z3 := C2

/-- Addition modulo 3, used as multiplication. -/
def addMod3 : Z3 → Z3 → Z3
  | C0, x => x
  | x, C0 => x
  | C1, C1 => C2
  | C1, C2 => C0
  | C2, C1 => C0
  | C2, C2 => C1

instance : Monoid Z3 where
  mul := addMod3
  one := C0
  mul_assoc := by
    intro x y z
    cases x <;> cases y <;> cases z <;> rfl
  one_mul := by
    intro x
    cases x <;> rfl
  mul_one := by
    intro x
    cases x <;> rfl

/-- The observed set S = {0,1}. -/
def S : Set Z3 := fun x => x = z0 ∨ x = z1

/-- The state image U = {0}. -/
def U : Set Z3 := fun x => x = z0

instance decidableMemS : DecidablePred S := by
  intro x
  unfold S
  infer_instance

instance decidableMemU : DecidablePred U := by
  intro x
  unfold U
  infer_instance

theorem z0_mem_S : z0 ∈ S := by
  simp [S, z0, z1]

theorem z1_mem_S : z1 ∈ S := by
  simp [S, z0, z1]

theorem z2_not_mem_S : z2 ∉ S := by
  simp [S, z0, z1, z2]

theorem z0_mem_U : z0 ∈ U := by
  simp [U, z0]

theorem z1_not_mem_U : z1 ∉ U := by
  simp [U, z0, z1]

theorem residual_zero_zero_mem :
    ∀ gamma : Z3,
      gamma ∈ TwoSidedResidual S z0 z0 ↔ gamma ∈ S := by
  intro gamma
  cases gamma <;>
    simp [TwoSidedResidual, S, z0, z1, z2, addMod3]

theorem residual_zero_zero_eq :
    TwoSidedResidual S z0 z0 = S := by
  ext gamma
  exact residual_zero_zero_mem gamma

theorem closure_singleton_zero_mem :
    ∀ gamma : Z3,
      gamma ∈ ConceptClosure S U ↔ gamma ∈ U := by
  intro gamma
  cases gamma <;>
    simp [ConceptClosure, ElementsOfContexts, CommonContexts,
      S, U, z0, z1, z2, addMod3] <;>
    decide

theorem closure_singleton_zero_eq :
    ConceptClosure S U = U := by
  ext gamma
  exact closure_singleton_zero_mem gamma

theorem closure_singleton_zero_ne_residual_zero_zero :
    ConceptClosure S U ≠ TwoSidedResidual S z0 z0 := by
  intro h
  have hz1_res : z1 ∈ TwoSidedResidual S z0 z0 := by
    rw [residual_zero_zero_eq]
    exact z1_mem_S
  have hz1_cl : z1 ∈ ConceptClosure S U := by
    rw [h]
    exact hz1_res
  have hz1_not_cl : z1 ∉ ConceptClosure S U := by
    rw [closure_singleton_zero_eq]
    exact z1_not_mem_U
  exact hz1_not_cl hz1_cl

/--
The context (1,0) accepts 0 but rejects 1:
  1 + 0 + 0 = 1 ∈ S, while 1 + 1 + 0 = 2 ∉ S.
-/
theorem not_sameObservedSyntactic_zero_one :
    ¬ SameObservedSyntactic S z0 z1 := by
  intro h
  have hctx := h z1 z0
  have hleft : z1 * z0 * z0 ∈ S := by
    simp [S, z0, z1, z2, addMod3]
  have hright : z1 * z1 * z0 ∉ S := by
    simp [S, z0, z1, z2, addMod3]
  exact hright (hctx.mp hleft)

/--
The finite failure witness:
  Res_S(0,0) = S = {0,1};
  cl_S({0}) = {0};
  cl_S({0}) is not Res_S(0,0);
  and 0 is not observed-syntactically equivalent to 1.
-/
theorem zmod3_failure_witness :
    TwoSidedResidual S z0 z0 = S
      ∧
    ConceptClosure S U = U
      ∧
    ConceptClosure S U ≠ TwoSidedResidual S z0 z0
      ∧
    ¬ SameObservedSyntactic S z0 z1 := by
  exact ⟨residual_zero_zero_eq,
    closure_singleton_zero_eq,
    closure_singleton_zero_ne_residual_zero_zero,
    not_sameObservedSyntactic_zero_one⟩

end ZMod3FailureExample
end LeanCfgProject
