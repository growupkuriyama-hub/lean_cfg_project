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
  We now use an explicit four-element inductive type `{O,A,B,E}`.
  This is less elegant than `Fin 2 → Bool`, but it is much better for CI:
  the multiplication table, monoid laws, and finite closure facts reduce by
  `cases` and `decide` without fragile function extensionality or instance
  search for decidability of function-valued sets.

This file uses the existing definitions from ResidualConcept.lean:
  TwoSidedResidual, CommonContexts, ConceptClosure.
No closure/residual/syntactic notion is redefined.
-/

inductive Diamond : Type
  | O
  | A
  | B
  | E
  deriving DecidableEq, Repr, Fintype

open Diamond

/-- Meet in the diamond semilattice.  `E` is top/unit, `O` is bottom. -/
def meet : Diamond → Diamond → Diamond
  | O, _ => O
  | _, O => O
  | E, x => x
  | x, E => x
  | A, A => A
  | B, B => B
  | A, B => O
  | B, A => O

instance : Monoid Diamond where
  mul := meet
  one := E
  mul_assoc := by
    intro x y z
    cases x <;> cases y <;> cases z <;> rfl
  one_mul := by
    intro x
    cases x <;> rfl
  mul_one := by
    intro x
    cases x <;> rfl

/-- The observed set S = {A}. -/
def S : Set Diamond := {A}

/-- The residual expected for Res_S(A,E): {E,A}. -/
def R_A_E : Set Diamond := {E, A}

theorem residual_A_E_mem :
    ∀ gamma : Diamond,
      gamma ∈ TwoSidedResidual S A E ↔ gamma ∈ R_A_E := by
  intro gamma
  cases gamma <;> decide

theorem residual_A_E_eq :
    TwoSidedResidual S A E = R_A_E := by
  ext gamma
  exact residual_A_E_mem gamma

theorem closure_singleton_E_mem :
    ∀ gamma : Diamond,
      gamma ∈ ConceptClosure S ({E} : Set Diamond) ↔ gamma ∈ R_A_E := by
  intro gamma
  cases gamma <;> decide

theorem closure_singleton_E_eq :
    ConceptClosure S ({E} : Set Diamond) = R_A_E := by
  ext gamma
  exact closure_singleton_E_mem gamma

theorem closure_singleton_A_mem :
    ∀ gamma : Diamond,
      gamma ∈ ConceptClosure S ({A} : Set Diamond) ↔ gamma ∈ ({A} : Set Diamond) := by
  intro gamma
  cases gamma <;> decide

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
