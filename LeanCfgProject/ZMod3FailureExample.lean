import LeanCfgProject.ObservedSyntacticConcept
import Mathlib.Data.ZMod.Basic

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

The observed set is S = {0,1}; the state image is U = {0}.
The file checks that Res_S(0,0) = {0,1}, but cl_S({0}) = {0}, and that
0 and 1 are not observed-syntactically equivalent.
-/

abbrev Z3 : Type := Multiplicative (ZMod 3)

instance : DecidableEq Z3 := inferInstance
instance : Fintype Z3 := inferInstance
instance : Monoid Z3 := inferInstance

def z0 : Z3 := Multiplicative.ofAdd (0 : ZMod 3)
def z1 : Z3 := Multiplicative.ofAdd (1 : ZMod 3)
def z2 : Z3 := Multiplicative.ofAdd (2 : ZMod 3)

def S : Set Z3 := {z0, z1}
def U : Set Z3 := {z0}

theorem residual_zero_zero_mem :
    ∀ gamma : Z3,
      gamma ∈ TwoSidedResidual S z0 z0 ↔ gamma ∈ S := by
  decide

theorem residual_zero_zero_eq :
    TwoSidedResidual S z0 z0 = S := by
  ext gamma
  exact residual_zero_zero_mem gamma

theorem closure_singleton_zero_mem :
    ∀ gamma : Z3,
      gamma ∈ ConceptClosure S U ↔ gamma ∈ U := by
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
    decide
  have hz1_cl : z1 ∈ ConceptClosure S U := by
    rw [h]
    exact hz1_res
  have hz1_not_cl : z1 ∉ ConceptClosure S U := by
    rw [closure_singleton_zero_eq]
    decide
  exact hz1_not_cl hz1_cl

theorem not_sameObservedSyntactic_zero_one :
    ¬ SameObservedSyntactic S z0 z1 := by
  decide

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
