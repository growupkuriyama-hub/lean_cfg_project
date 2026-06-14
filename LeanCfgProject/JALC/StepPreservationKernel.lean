import LeanCfgProject.JALC.ProductiveReachableStepDecidabilityKernel

namespace LeanCfgProject
namespace JALC
namespace StepPreservationKernel

/-
Decidability preservation for the two closure steps.

This module removes one abstract boundary from PaperFacingStepDecidability:
ProductiveStep and ReachableStep preserve decidability when their rule
predicates are decidable over a finite universe list.
-/

universe u v w

open InverseKernel RoundTripKernel
open FiniteClosureKernel
open ProductiveReachableClosureKernel
open AlgorithmicExtractionKernel
open FullAlgorithmicAgreementKernel
open ListCertificateKernel
open FiniteUniverseListEnumerationKernel
open IterDecidabilityKernel
open ProductiveReachableStepDecidabilityKernel


/-- Decide existence of a witness in a finite list. -/
def decidableExistsInList
    {α : Type u}
    (xs : List α)
    (Q : α → Prop)
    (decQ : DecidablePred Q) :
    Decidable (∃ x, x ∈ xs ∧ Q x) :=
  match xs with
  | [] =>
      isFalse (by
        intro h
        rcases h with ⟨x, hx, _⟩
        cases hx)
  | a :: rest =>
      match decQ a with
      | isTrue ha =>
          isTrue ⟨a, List.mem_cons_self a rest, ha⟩
      | isFalse hna =>
          match decidableExistsInList rest Q decQ with
          | isTrue hrest =>
              isTrue (by
                rcases hrest with ⟨x, hx, hq⟩
                exact ⟨x, List.mem_cons_of_mem a hx, hq⟩)
          | isFalse hnrest =>
              isFalse (by
                intro h
                rcases h with ⟨x, hx, hq⟩
                have hx' : x = a ∨ x ∈ rest := List.mem_cons.mp hx
                cases hx' with
                | inl heq =>
                    subst x
                    exact hna hq
                | inr hmem =>
                    exact hnrest ⟨x, hmem, hq⟩)


/-- Decide existence of a witness in a complete finite universe list. -/
def decidableExistsInUniverse
    {α : Type u}
    (U : UniverseList α)
    (Q : α → Prop)
    (decQ : DecidablePred Q) :
    Decidable (∃ x, Q x) :=
  match decidableExistsInList U.support Q decQ with
  | isTrue h =>
      isTrue (by
        rcases h with ⟨x, _hx, hq⟩
        exact ⟨x, hq⟩)
  | isFalse hn =>
      isFalse (by
        intro h
        rcases h with ⟨x, hq⟩
        exact hn ⟨x, U.complete x, hq⟩)


/-- Decide the binary productivity witness used by ProductiveStep. -/
def productiveWitnessDecidable
    {α : Type u}
    (U : UniverseList α)
    {binary : α → α → α → Prop}
    (binaryDec : ∀ x y z : α, Decidable (binary x y z))
    {P : α → Prop}
    (Pdec : DecidablePred P)
    (x : α) :
    Decidable (∃ y, ∃ z, binary x y z ∧ P y ∧ P z) :=
  decidableExistsInUniverse U
    (fun y => ∃ z, binary x y z ∧ P y ∧ P z)
    (fun y =>
      decidableExistsInUniverse U
        (fun z => binary x y z ∧ P y ∧ P z)
        (fun z =>
          letI : Decidable (binary x y z) := binaryDec x y z
          letI : Decidable (P y) := Pdec y
          letI : Decidable (P z) := Pdec z
          inferInstance))


/--
Productivity step preserves decidability over a complete finite universe list.
-/
def productiveStep_preserves_decidable_of_universe
    {α : Type u}
    (U : UniverseList α)
    (terminal : α → Prop)
    (binary : α → α → α → Prop)
    (terminalDec : DecidablePred terminal)
    (binaryDec : ∀ x y z : α, Decidable (binary x y z)) :
    PreservesDecidablePred (ProductiveStep terminal binary) := by
  intro P Pdec x
  change Decidable
    (P x ∨ terminal x ∨ ∃ y, ∃ z, binary x y z ∧ P y ∧ P z)
  letI : Decidable (P x) := Pdec x
  letI : Decidable (terminal x) := terminalDec x
  letI :
      Decidable (∃ y, ∃ z, binary x y z ∧ P y ∧ P z) :=
    productiveWitnessDecidable U binaryDec Pdec x
  exact inferInstance


/-- Decide the left-child reachability witness used by ReachableStep. -/
def reachableLeftWitnessDecidable
    {α : Type u}
    (U : UniverseList α)
    {binary : α → α → α → Prop}
    (binaryDec : ∀ x y z : α, Decidable (binary x y z))
    {productive : α → Prop}
    (productiveDec : DecidablePred productive)
    {R : α → Prop}
    (Rdec : DecidablePred R)
    (x : α) :
    Decidable
      (∃ p, ∃ y, ∃ z, R p ∧ binary p x z ∧ productive z) :=
  decidableExistsInUniverse U
    (fun p => ∃ y, ∃ z, R p ∧ binary p x z ∧ productive z)
    (fun p =>
      decidableExistsInUniverse U
        (fun y => ∃ z, R p ∧ binary p x z ∧ productive z)
        (fun y =>
          decidableExistsInUniverse U
            (fun z => R p ∧ binary p x z ∧ productive z)
            (fun z =>
              letI : Decidable (R p) := Rdec p
              letI : Decidable (binary p x z) := binaryDec p x z
              letI : Decidable (productive z) := productiveDec z
              inferInstance)))


/-- Decide the right-child reachability witness used by ReachableStep. -/
def reachableRightWitnessDecidable
    {α : Type u}
    (U : UniverseList α)
    {binary : α → α → α → Prop}
    (binaryDec : ∀ x y z : α, Decidable (binary x y z))
    {productive : α → Prop}
    (productiveDec : DecidablePred productive)
    {R : α → Prop}
    (Rdec : DecidablePred R)
    (x : α) :
    Decidable
      (∃ p, ∃ y, ∃ z, R p ∧ binary p y x ∧ productive y) :=
  decidableExistsInUniverse U
    (fun p => ∃ y, ∃ z, R p ∧ binary p y x ∧ productive y)
    (fun p =>
      decidableExistsInUniverse U
        (fun y => ∃ z, R p ∧ binary p y x ∧ productive y)
        (fun y =>
          decidableExistsInUniverse U
            (fun z => R p ∧ binary p y x ∧ productive y)
            (fun z =>
              letI : Decidable (R p) := Rdec p
              letI : Decidable (binary p y x) := binaryDec p y x
              letI : Decidable (productive y) := productiveDec y
              inferInstance)))


/--
Reachability step preserves decidability over a complete finite universe list.
-/
def reachableStep_preserves_decidable_of_universe
    {α : Type u}
    (U : UniverseList α)
    (start : α → Prop)
    (binary : α → α → α → Prop)
    (productive : α → Prop)
    (startDec : DecidablePred start)
    (binaryDec : ∀ x y z : α, Decidable (binary x y z))
    (productiveDec : DecidablePred productive) :
    PreservesDecidablePred (ReachableStep start binary productive) := by
  intro R Rdec x
  change Decidable
    (R x ∨
      (productive x ∧ start x) ∨
      (productive x ∧
        ∃ p, ∃ y, ∃ z, R p ∧ binary p x z ∧ productive z) ∨
      (productive x ∧
        ∃ p, ∃ y, ∃ z, R p ∧ binary p y x ∧ productive y))
  letI : Decidable (R x) := Rdec x
  letI : Decidable (productive x) := productiveDec x
  letI : Decidable (start x) := startDec x
  letI :
      Decidable
        (∃ p, ∃ y, ∃ z, R p ∧ binary p x z ∧ productive z) :=
    reachableLeftWitnessDecidable U binaryDec productiveDec Rdec x
  letI :
      Decidable
        (∃ p, ∃ y, ∃ z, R p ∧ binary p y x ∧ productive y) :=
    reachableRightWitnessDecidable U binaryDec productiveDec Rdec x
  exact inferInstance

end StepPreservationKernel
end JALC
end LeanCfgProject
