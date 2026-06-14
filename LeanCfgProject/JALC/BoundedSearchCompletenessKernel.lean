import LeanCfgProject.JALC.BoundedListStabilitySearchKernel

namespace LeanCfgProject
namespace JALC
namespace BoundedSearchCompletenessKernel

/-
Weak completeness for the generic bounded list-stability search.

The previous bounded-search kernel defines a search procedure and shows that
any returned witness can be used as a closure certificate.  This file proves the
first completeness direction needed for later finite-stabilization work:

if stability holds at the current fuel height, then the bounded search up to
that fuel returns some witness.

This is deliberately weaker than a global finite-bound theorem.  It is the
local search-correctness layer that will later combine with a finite
stabilization theorem.
-/

universe u

open FiniteClosureKernel
open FiniteUniverseListEnumerationKernel
open ListStabilityKernel
open BoundedListStabilitySearchKernel


/--
If list-stability holds at the exact fuel height, then bounded search up to that
fuel returns a witness.
-/
theorem findListStabilityWitness_exists_of_stable_at_fuel
    {α : Type u}
    (U : UniverseList α)
    (F : (α → Prop) → α → Prop)
    (dec :
      ∀ n : Nat,
        Decidable
          (AgreeOnList U.support
            (F (Iter F n))
            (Iter F n))) :
    ∀ fuel : Nat,
      AgreeOnList U.support
        (F (Iter F fuel))
        (Iter F fuel) →
      ∃ W : ListStabilityWitness U F,
        findListStabilityWitness U F dec fuel = some W
  | 0, hstable =>
      by
        unfold findListStabilityWitness
        cases dec 0 with
        | isTrue hdec =>
            exact ⟨{ height := 0, stable_on_list := hdec }, rfl⟩
        | isFalse hbad =>
            exact False.elim (hbad hstable)
  | Nat.succ fuel, hstable =>
      by
        unfold findListStabilityWitness
        cases hprev :
          findListStabilityWitness U F dec fuel with
        | some W =>
            exact ⟨W, rfl⟩
        | none =>
            cases dec (Nat.succ fuel) with
            | isTrue hdec =>
                exact
                  ⟨{ height := Nat.succ fuel,
                     stable_on_list := hdec },
                   rfl⟩
            | isFalse hbad =>
                exact False.elim (hbad hstable)


/--
Global `StableAt` at the fuel height implies search success up to that fuel.
-/
theorem findListStabilityWitness_exists_of_global_stable_at_fuel
    {α : Type u}
    (U : UniverseList α)
    (F : (α → Prop) → α → Prop)
    (dec :
      ∀ n : Nat,
        Decidable
          (AgreeOnList U.support
            (F (Iter F n))
            (Iter F n)))
    (fuel : Nat)
    (hstable : StableAt F fuel) :
    ∃ W : ListStabilityWitness U F,
      findListStabilityWitness U F dec fuel = some W :=
  findListStabilityWitness_exists_of_stable_at_fuel
    U F dec fuel
    (by
      intro x _hx
      exact hstable x)


/--
A fuel-height list-stability proof yields a successful bounded-search witness
and hence a closure certificate.
-/
theorem closureCertificate_exists_of_stable_at_fuel
    {α : Type u}
    (U : UniverseList α)
    (F : (α → Prop) → α → Prop)
    (dec :
      ∀ n : Nat,
        Decidable
          (AgreeOnList U.support
            (F (Iter F n))
            (Iter F n)))
    (fuel : Nat)
    (hstable :
      AgreeOnList U.support
        (F (Iter F fuel))
        (Iter F fuel)) :
    ∃ W : ListStabilityWitness U F,
      findListStabilityWitness U F dec fuel = some W ∧
      StableAt F W.height :=
  by
    rcases
      findListStabilityWitness_exists_of_stable_at_fuel
        U F dec fuel hstable with ⟨W, hW⟩
    exact
      ⟨W, hW, stableAt_of_listStabilityWitness W⟩


/--
A global fuel-height stability proof yields a successful bounded-search witness
and a closure certificate.
-/
theorem closureCertificate_exists_of_global_stable_at_fuel
    {α : Type u}
    (U : UniverseList α)
    (F : (α → Prop) → α → Prop)
    (dec :
      ∀ n : Nat,
        Decidable
          (AgreeOnList U.support
            (F (Iter F n))
            (Iter F n)))
    (fuel : Nat)
    (hstable : StableAt F fuel) :
    ∃ W : ListStabilityWitness U F,
      findListStabilityWitness U F dec fuel = some W ∧
      StableAt F W.height :=
  closureCertificate_exists_of_stable_at_fuel
    U F dec fuel
    (by
      intro x _hx
      exact hstable x)

end BoundedSearchCompletenessKernel
end JALC
end LeanCfgProject
