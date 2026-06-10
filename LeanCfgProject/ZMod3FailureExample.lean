import LeanCfgProject.ObservedSyntacticConcept
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace LeanCfgProject
namespace ZMod3FailureExample

/-
Finite example (2): the Z/3 failure example.

Representation choice:
  We use `Multiplicative (ZMod 3)` so that the existing definitions
  `TwoSidedResidual`, `ConceptClosure`, and `SameObservedSyntactic`, which are
  written with `*`, interpret multiplication as addition in `ZMod 3`.

Important CI detail:
  The observed set S and U are written as explicit decidable predicates rather
  than set-builder abbreviations `{z0,z1}` and `{z0}`.  This lets `simp [S,U]`
  expose membership as equality/disjunctions before `decide` is called.
-/

abbrev Z3 : Type := Multiplicative (ZMod 3)

instance : DecidableEq Z3 := inferInstance
instance : Fintype Z3 := inferInstance
instance : Monoid Z3 := inferInstance

def z0 : Z3 := Multiplicative.ofAdd (0 : ZMod 3)
def z1 : Z3 := Multiplicative.ofAdd (1 : ZMod 3)
def z2 : Z3 := Multiplicative.ofAdd (2 : ZMod 3)

/-- The observed set S = {0,1}. -/
def S : Set Z3 := fun x => x = z0 ∨ x = z1

/-- The state image U = {0}. -/
def U : Set Z3 := fun x => x = z0

theorem z0_mem_S : z0 ∈ S := by
  simp [S]

theorem z1_mem_S : z1 ∈ S := by
  simp [S]

theorem z2_not_mem_S : z2 ∉ S := by
  simp [S, z0, z1, z2]
  decide

theorem z0_mem_U : z0 ∈ U := by
  simp [U]

theorem z1_not_mem_U : z1 ∉ U := by
  simp [U, z0, z1]
  decide

theorem residual_zero_zero_mem :
    ∀ gamma : Z3,
      gamma ∈ TwoSidedResidual S z0 z0 ↔ gamma ∈ S := by
  intro gamma
  fin_cases gamma <;>
    simp [TwoSidedResidual, S, z0, z1, z2] <;>
    decide

theorem residual_zero_zero_eq :
    TwoSidedResidual S z0 z0 = S := by
  ext gamma
  exact residual_zero_zero_mem gamma

theorem closure_singleton_zero_mem :
    ∀ gamma : Z3,
      gamma ∈ ConceptClosure S U ↔ gamma ∈ U := by
  intro gamma
  fin_cases gamma <;>
    simp [ConceptClosure, ElementsOfContexts, CommonContexts, S, U,
      z0, z1, z2] <;>
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
    simp [S, z0, z1, z2]
    decide
  have hright : z1 * z1 * z0 ∉ S := by
    simp [S, z0, z1, z2]
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
