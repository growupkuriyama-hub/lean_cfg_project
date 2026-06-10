import LeanCfgProject.ResidualConcept

set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace LeanCfgProject
namespace DiamondSemilatticeExample

/-
Finite example (1): the diamond meet-semilattice monoid.

Representation choice:
  Q is represented as `Fin 2 → Bool`, i.e. literally the powerset of a
  two-element set.  Multiplication is pointwise Boolean conjunction, which is
  set intersection; the unit is the full set.

This file proves the finite witness propositions using the existing
definitions from ResidualConcept.lean:
  TwoSidedResidual, CommonContexts, ConceptClosure.
-/

abbrev Diamond : Type := Fin 2 → Bool

instance : DecidableEq Diamond := inferInstance
instance : Fintype Diamond := inferInstance

def O : Diamond := fun _ => false
def E : Diamond := fun _ => true
def A : Diamond := fun i => decide (i = (0 : Fin 2))
def B : Diamond := fun i => decide (i = (1 : Fin 2))

def meet (x y : Diamond) : Diamond :=
  fun i => x i && y i

instance : Mul Diamond where
  mul := meet

instance : One Diamond where
  one := E

instance : Monoid Diamond where
  mul := meet
  one := E
  mul_assoc := by
    intro x y z
    funext i
    unfold meet
    cases x i <;> cases y i <;> cases z i <;> rfl
  one_mul := by
    intro x
    funext i
    unfold meet E
    cases x i <;> rfl
  mul_one := by
    intro x
    funext i
    unfold meet E
    cases x i <;> rfl

def S : Set Diamond := {A}

def R_A_E : Set Diamond := {E, A}

theorem residual_A_E_mem :
    ∀ gamma : Diamond,
      gamma ∈ TwoSidedResidual S A E ↔ gamma ∈ R_A_E := by
  decide

theorem residual_A_E_eq :
    TwoSidedResidual S A E = R_A_E := by
  ext gamma
  exact residual_A_E_mem gamma

theorem closure_singleton_E_mem :
    ∀ gamma : Diamond,
      gamma ∈ ConceptClosure S ({E} : Set Diamond) ↔ gamma ∈ R_A_E := by
  decide

theorem closure_singleton_E_eq :
    ConceptClosure S ({E} : Set Diamond) = R_A_E := by
  ext gamma
  exact closure_singleton_E_mem gamma

theorem closure_singleton_A_mem :
    ∀ gamma : Diamond,
      gamma ∈ ConceptClosure S ({A} : Set Diamond) ↔ gamma ∈ ({A} : Set Diamond) := by
  decide

theorem closure_singleton_A_eq :
    ConceptClosure S ({A} : Set Diamond) = ({A} : Set Diamond) := by
  ext gamma
  exact closure_singleton_A_mem gamma

theorem E_ne_A : E ≠ A := by
  decide

theorem closure_singleton_A_ne_residual_A_E :
    ConceptClosure S ({A} : Set Diamond) ≠ TwoSidedResidual S A E := by
  intro h
  have hE_res : E ∈ TwoSidedResidual S A E := by
    rw [residual_A_E_eq]
    decide
  have hE_cl : E ∈ ConceptClosure S ({A} : Set Diamond) := by
    rw [h]
    exact hE_res
  have hE_not_cl : E ∉ ConceptClosure S ({A} : Set Diamond) := by
    rw [closure_singleton_A_eq]
    decide
  exact hE_not_cl hE_cl

theorem two_block_pointwise_adequacy :
    ConceptClosure S ({E} : Set Diamond) = TwoSidedResidual S A E
      ∧
    ConceptClosure S ({A} : Set Diamond) ≠ TwoSidedResidual S A E := by
  constructor
  · rw [closure_singleton_E_eq, residual_A_E_eq]
  · exact closure_singleton_A_ne_residual_A_E

/--
The finite witness as a single proposition:
  Res_S(A,E) = {E,A},
  cl_S({E}) = {E,A},
  cl_S({A}) = {A},
  and cl_S({A}) is not the residual.
-/
theorem diamond_two_block_pointwise_adequacy_witness :
    TwoSidedResidual S A E = R_A_E
      ∧
    ConceptClosure S ({E} : Set Diamond) = R_A_E
      ∧
    ConceptClosure S ({A} : Set Diamond) = ({A} : Set Diamond)
      ∧
    ConceptClosure S ({E} : Set Diamond) = TwoSidedResidual S A E
      ∧
    ConceptClosure S ({A} : Set Diamond) ≠ TwoSidedResidual S A E := by
  exact ⟨residual_A_E_eq,
    closure_singleton_E_eq,
    closure_singleton_A_eq,
    two_block_pointwise_adequacy.1,
    two_block_pointwise_adequacy.2⟩

end DiamondSemilatticeExample
end LeanCfgProject
