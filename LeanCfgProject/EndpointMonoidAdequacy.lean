import LeanCfgProject.ObservedSyntacticConcept

set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace LeanCfgProject
namespace EndpointMonoidExample

/-
Finite example (3): the endpoint monoid.

Carrier:
  E = {1} ∪ ({a,b} × {a,b}), represented as five constructors:
    I, AA, AB, BA, BB.

Multiplication:
  I is the unit; for non-units, (f,l)(f',l') = (f,l').
  We encode this by an explicit multiplication table.

Observed set:
  S = {AA, AB}, i.e. the non-unit elements whose first endpoint is a.

State image:
  U = {AB}.

This file checks:
  * Res_S(1,BB) = S,
  * all elements of S lie in one SameObservedSyntactic block,
  * ConceptClosure S {AB} = S.

Existing definitions used:
  TwoSidedResidual, CommonContexts, ElementsOfContexts, ConceptClosure,
  SameObservedSyntactic.
-/

inductive Endpoint : Type
  | I
  | AA
  | AB
  | BA
  | BB
  deriving DecidableEq, Repr, Fintype

open Endpoint

abbrev e1 : Endpoint := I
abbrev eAA : Endpoint := AA
abbrev eAB : Endpoint := AB
abbrev eBA : Endpoint := BA
abbrev eBB : Endpoint := BB

/-- Endpoint multiplication. -/
def endpointMul : Endpoint → Endpoint → Endpoint
  | I, x => x
  | x, I => x
  | AA, AA => AA
  | AA, AB => AB
  | AA, BA => AA
  | AA, BB => AB
  | AB, AA => AA
  | AB, AB => AB
  | AB, BA => AA
  | AB, BB => AB
  | BA, AA => BA
  | BA, AB => BB
  | BA, BA => BA
  | BA, BB => BB
  | BB, AA => BA
  | BB, AB => BB
  | BB, BA => BA
  | BB, BB => BB

instance : Monoid Endpoint where
  mul := endpointMul
  one := I
  mul_assoc := by
    intro x y z
    cases x <;> cases y <;> cases z <;> rfl
  one_mul := by
    intro x
    cases x <;> rfl
  mul_one := by
    intro x
    cases x <;> rfl

/-- Boolean membership for S = {AA, AB}. -/
def inSBool : Endpoint → Bool
  | AA => true
  | AB => true
  | _ => false

/-- Boolean membership for U = {AB}. -/
def inUBool : Endpoint → Bool
  | AB => true
  | _ => false

/-- The observed set S = {(a,a),(a,b)}. -/
abbrev S : Set Endpoint := fun x => inSBool x = true

/-- The singleton state image U = {(a,b)}. -/
abbrev U : Set Endpoint := fun x => inUBool x = true

theorem mem_S_iff (x : Endpoint) :
    x ∈ S ↔ x = eAA ∨ x = eAB := by
  cases x <;> change (inSBool x = true ↔ x = eAA ∨ x = eAB) <;> decide

theorem eAA_mem_S : eAA ∈ S := by
  change inSBool AA = true
  rfl

theorem eAB_mem_S : eAB ∈ S := by
  change inSBool AB = true
  rfl

theorem eBB_not_mem_S : eBB ∉ S := by
  change ¬ inSBool BB = true
  decide

theorem eAB_mem_U : eAB ∈ U := by
  change inUBool AB = true
  rfl

theorem eAA_not_mem_U : eAA ∉ U := by
  change ¬ inUBool AA = true
  decide

/--
Res_S(1,BB) = S.
-/
theorem residual_one_BB_mem :
    ∀ gamma : Endpoint,
      gamma ∈ TwoSidedResidual S e1 eBB ↔ gamma ∈ S := by
  intro gamma
  cases gamma
  · change (inSBool (I * I * BB) = true ↔ inSBool I = true)
    decide
  · change (inSBool (I * AA * BB) = true ↔ inSBool AA = true)
    decide
  · change (inSBool (I * AB * BB) = true ↔ inSBool AB = true)
    decide
  · change (inSBool (I * BA * BB) = true ↔ inSBool BA = true)
    decide
  · change (inSBool (I * BB * BB) = true ↔ inSBool BB = true)
    decide

theorem residual_one_BB_eq :
    TwoSidedResidual S e1 eBB = S := by
  ext gamma
  exact residual_one_BB_mem gamma

/--
AA and AB have the same two-sided S-membership tests.
-/
theorem sameObservedSyntactic_AA_AB :
    SameObservedSyntactic S eAA eAB := by
  intro alpha beta
  cases alpha <;> cases beta
  all_goals
    change (inSBool (alpha * AA * beta) = true ↔
      inSBool (alpha * AB * beta) = true)
    decide

theorem sameObservedSyntactic_AB_AA :
    SameObservedSyntactic S eAB eAA := by
  intro alpha beta
  exact (sameObservedSyntactic_AA_AB alpha beta).symm

theorem sameObservedSyntactic_AA_AA :
    SameObservedSyntactic S eAA eAA := by
  intro alpha beta
  rfl

theorem sameObservedSyntactic_AB_AB :
    SameObservedSyntactic S eAB eAB := by
  intro alpha beta
  rfl

/--
S is a single observed-syntactic block.
-/
theorem S_single_observed_syntactic_block :
    ∀ x y : Endpoint, x ∈ S → y ∈ S → SameObservedSyntactic S x y := by
  intro x y hx hy
  have hx' : x = eAA ∨ x = eAB := (mem_S_iff x).mp hx
  have hy' : y = eAA ∨ y = eAB := (mem_S_iff y).mp hy
  rcases hx' with rfl | rfl <;> rcases hy' with rfl | rfl
  · exact sameObservedSyntactic_AA_AA
  · exact sameObservedSyntactic_AA_AB
  · exact sameObservedSyntactic_AB_AA
  · exact sameObservedSyntactic_AB_AB

/--
cl_S({AB}) = S.
-/
theorem closure_singleton_AB_mem :
    ∀ gamma : Endpoint,
      gamma ∈ ConceptClosure S U ↔ gamma ∈ S := by
  intro gamma
  cases gamma
  · change
      ((∀ ab : Endpoint × Endpoint,
          (∀ delta : Endpoint,
            inUBool delta = true →
              inSBool (ab.1 * delta * ab.2) = true) →
          inSBool (ab.1 * I * ab.2) = true)
        ↔ inSBool I = true)
    decide
  · change
      ((∀ ab : Endpoint × Endpoint,
          (∀ delta : Endpoint,
            inUBool delta = true →
              inSBool (ab.1 * delta * ab.2) = true) →
          inSBool (ab.1 * AA * ab.2) = true)
        ↔ inSBool AA = true)
    decide
  · change
      ((∀ ab : Endpoint × Endpoint,
          (∀ delta : Endpoint,
            inUBool delta = true →
              inSBool (ab.1 * delta * ab.2) = true) →
          inSBool (ab.1 * AB * ab.2) = true)
        ↔ inSBool AB = true)
    decide
  · change
      ((∀ ab : Endpoint × Endpoint,
          (∀ delta : Endpoint,
            inUBool delta = true →
              inSBool (ab.1 * delta * ab.2) = true) →
          inSBool (ab.1 * BA * ab.2) = true)
        ↔ inSBool BA = true)
    decide
  · change
      ((∀ ab : Endpoint × Endpoint,
          (∀ delta : Endpoint,
            inUBool delta = true →
              inSBool (ab.1 * delta * ab.2) = true) →
          inSBool (ab.1 * BB * ab.2) = true)
        ↔ inSBool BB = true)
    decide

theorem closure_singleton_AB_eq :
    ConceptClosure S U = S := by
  ext gamma
  exact closure_singleton_AB_mem gamma

/--
The endpoint-monoid aperiodic adequacy witness:
  Res_S(1,BB) = S,
  S is a single SameObservedSyntactic block,
  and cl_S({AB}) = S.
-/
theorem endpoint_monoid_aperiodic_adequacy_witness :
    TwoSidedResidual S e1 eBB = S
      ∧
    (∀ x y : Endpoint, x ∈ S → y ∈ S → SameObservedSyntactic S x y)
      ∧
    ConceptClosure S U = S := by
  exact ⟨residual_one_BB_eq,
    S_single_observed_syntactic_block,
    closure_singleton_AB_eq⟩

end EndpointMonoidExample
end LeanCfgProject
