import LeanCfgProject.ObservedResidualConcept.ObservedSyntacticConcept
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace LeanCfgProject
namespace ZMod3FailureExample

/-
Finite example (2): the Z/3 failure example.

Representation choice:
  We use an explicit three-element type with the addition-mod-3 multiplication
  table.  The observed sets are defined by Boolean membership functions, so
  membership goals reduce to equations of the form `inSBool x = true`.

This file uses the existing definitions:
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

abbrev z0 : Z3 := C0
abbrev z1 : Z3 := C1
abbrev z2 : Z3 := C2

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

/-- Boolean membership for S = {0,1}. -/
def inSBool : Z3 → Bool
  | C0 => true
  | C1 => true
  | C2 => false

/-- Boolean membership for U = {0}. -/
def inUBool : Z3 → Bool
  | C0 => true
  | C1 => false
  | C2 => false

/-- The observed set S = {0,1}. -/
abbrev S : Set Z3 := fun x => inSBool x = true

/-- The state image U = {0}. -/
abbrev U : Set Z3 := fun x => inUBool x = true

theorem z0_mem_S : z0 ∈ S := by
  change inSBool C0 = true
  rfl

theorem z1_mem_S : z1 ∈ S := by
  change inSBool C1 = true
  rfl

theorem z2_not_mem_S : z2 ∉ S := by
  change ¬ inSBool C2 = true
  decide

theorem z0_mem_U : z0 ∈ U := by
  change inUBool C0 = true
  rfl

theorem z1_not_mem_U : z1 ∉ U := by
  change ¬ inUBool C1 = true
  decide

theorem residual_zero_zero_mem :
    ∀ gamma : Z3,
      gamma ∈ TwoSidedResidual S z0 z0 ↔ gamma ∈ S := by
  intro gamma
  cases gamma
  · change (inSBool (C0 * C0 * C0) = true ↔ inSBool C0 = true)
    decide
  · change (inSBool (C0 * C1 * C0) = true ↔ inSBool C1 = true)
    decide
  · change (inSBool (C0 * C2 * C0) = true ↔ inSBool C2 = true)
    decide

theorem residual_zero_zero_eq :
    TwoSidedResidual S z0 z0 = S := by
  ext gamma
  exact residual_zero_zero_mem gamma

theorem closure_singleton_zero_mem :
    ∀ gamma : Z3,
      gamma ∈ ConceptClosure S U ↔ gamma ∈ U := by
  intro gamma
  cases gamma
  · change
      ((∀ ab : Z3 × Z3,
          (∀ delta : Z3,
            inUBool delta = true →
              inSBool (ab.1 * delta * ab.2) = true) →
          inSBool (ab.1 * C0 * ab.2) = true)
        ↔ inUBool C0 = true)
    decide
  · change
      ((∀ ab : Z3 × Z3,
          (∀ delta : Z3,
            inUBool delta = true →
              inSBool (ab.1 * delta * ab.2) = true) →
          inSBool (ab.1 * C1 * ab.2) = true)
        ↔ inUBool C1 = true)
    decide
  · change
      ((∀ ab : Z3 × Z3,
          (∀ delta : Z3,
            inUBool delta = true →
              inSBool (ab.1 * delta * ab.2) = true) →
          inSBool (ab.1 * C2 * ab.2) = true)
        ↔ inUBool C2 = true)
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
    change inSBool (C1 * C0 * C0) = true
    decide
  have hright : z1 * z1 * z0 ∉ S := by
    change ¬ inSBool (C1 * C1 * C0) = true
    decide
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
