import LeanCfgProject.JALC.BoundedSearchOffsetCompletenessKernel

namespace LeanCfgProject
namespace JALC
namespace BoundedSearchWithinBoundKernel

/-
Within-bound completeness for the generic bounded list-stability search.

The previous offset target proves:

  stability at height n
  => search succeeds at n + k.

This file repackages that result in the form needed for the future finite
stabilization theorem:

  if some stable height n is at most the fuel,
  then bounded search at that fuel succeeds.
-/

universe u

open FiniteClosureKernel
open FiniteUniverseListEnumerationKernel
open ListStabilityKernel
open BoundedListStabilitySearchKernel
open BoundedSearchOffsetCompletenessKernel


/--
A certificate that a list-stability height occurs within a given fuel bound.
-/
structure StableWithinBound
    {α : Type u}
    (U : UniverseList α)
    (F : (α → Prop) → α → Prop)
    (fuel : Nat) : Type (u + 1) where
  height :
    Nat
  height_le_fuel :
    height ≤ fuel
  stable_on_list :
    AgreeOnList U.support
      (F (Iter F height))
      (Iter F height)


/--
A `StableWithinBound` certificate can be converted to a successful bounded
search at the recorded fuel.
-/
theorem findListStabilityWitness_exists_of_stableWithinBound
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
    (H : StableWithinBound U F fuel) :
    ∃ W : ListStabilityWitness U F,
      findListStabilityWitness U F dec fuel = some W :=
  by
    rcases Nat.exists_eq_add_of_le H.height_le_fuel with ⟨k, hk⟩
    rw [hk]
    exact
      findListStabilityWitness_exists_of_stable_at_offset
        U F dec H.height k H.stable_on_list


/--
Existential within-bound list-stability implies bounded-search success.
-/
theorem findListStabilityWitness_exists_of_exists_stable_le_fuel
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
    (h :
      ∃ n : Nat,
        n ≤ fuel ∧
        AgreeOnList U.support
          (F (Iter F n))
          (Iter F n)) :
    ∃ W : ListStabilityWitness U F,
      findListStabilityWitness U F dec fuel = some W :=
  by
    rcases h with ⟨n, hnle, hstable⟩
    exact
      findListStabilityWitness_exists_of_stableWithinBound
        U F dec fuel
        { height := n,
          height_le_fuel := hnle,
          stable_on_list := hstable }


/--
Global stability at some height within the fuel implies bounded-search success.
-/
theorem findListStabilityWitness_exists_of_exists_global_stable_le_fuel
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
    (h :
      ∃ n : Nat,
        n ≤ fuel ∧ StableAt F n) :
    ∃ W : ListStabilityWitness U F,
      findListStabilityWitness U F dec fuel = some W :=
  by
    rcases h with ⟨n, hnle, hstable⟩
    exact
      findListStabilityWitness_exists_of_exists_stable_le_fuel
        U F dec fuel
        ⟨n, hnle, by
          intro x _hx
          exact hstable x⟩


/--
A within-bound list-stability certificate also yields a closure certificate.
-/
theorem closureCertificate_exists_of_stableWithinBound
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
    (H : StableWithinBound U F fuel) :
    ∃ W : ListStabilityWitness U F,
      findListStabilityWitness U F dec fuel = some W ∧
      StableAt F W.height :=
  by
    rcases
      findListStabilityWitness_exists_of_stableWithinBound
        U F dec fuel H with ⟨W, hW⟩
    exact ⟨W, hW, stableAt_of_listStabilityWitness W⟩


/--
Existential within-bound list-stability gives a successful bounded search and a
closure certificate.
-/
theorem closureCertificate_exists_of_exists_stable_le_fuel
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
    (h :
      ∃ n : Nat,
        n ≤ fuel ∧
        AgreeOnList U.support
          (F (Iter F n))
          (Iter F n)) :
    ∃ W : ListStabilityWitness U F,
      findListStabilityWitness U F dec fuel = some W ∧
      StableAt F W.height :=
  by
    rcases
      findListStabilityWitness_exists_of_exists_stable_le_fuel
        U F dec fuel h with ⟨W, hW⟩
    exact ⟨W, hW, stableAt_of_listStabilityWitness W⟩


/--
This is the exact bridge expected from the future finite-stabilization theorem:
if the finite-stabilization theorem supplies a stable height below a fuel bound,
then the bounded search at that fuel succeeds.
-/
abbrev FiniteStabilizationOutput
    {α : Type u}
    (U : UniverseList α)
    (F : (α → Prop) → α → Prop)
    (fuel : Nat) :=
  StableWithinBound U F fuel


/--
A finite-stabilization output is accepted by bounded search.
-/
theorem boundedSearch_accepts_finiteStabilizationOutput
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
    (H : FiniteStabilizationOutput U F fuel) :
    ∃ W : ListStabilityWitness U F,
      findListStabilityWitness U F dec fuel = some W :=
  findListStabilityWitness_exists_of_stableWithinBound
    U F dec fuel H

end BoundedSearchWithinBoundKernel
end JALC
end LeanCfgProject
