import LeanCfgProject.JALC.BoundedSearchCompletenessKernel

namespace LeanCfgProject
namespace JALC
namespace BoundedSearchOffsetCompletenessKernel

/-
Offset completeness for the generic bounded list-stability search.

The previous weak-completeness target says: if stability holds exactly at the
fuel height, then bounded search up to that fuel succeeds.

This file proves the more useful bridge for finite stabilization:

if stability holds at height n, then bounded search up to n + k succeeds for
any extra fuel k.
-/

universe u

open FiniteClosureKernel
open FiniteUniverseListEnumerationKernel
open ListStabilityKernel
open BoundedListStabilitySearchKernel
open BoundedSearchCompletenessKernel


/--
Once bounded search has found a witness by a given fuel, it still returns some
witness at the successor fuel.
-/
theorem findListStabilityWitness_some_monotone_succ
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
    {W : ListStabilityWitness U F}
    (h :
      findListStabilityWitness U F dec fuel = some W) :
    ∃ W' : ListStabilityWitness U F,
      findListStabilityWitness U F dec (Nat.succ fuel) = some W' :=
  by
    unfold findListStabilityWitness
    rw [h]
    exact ⟨W, rfl⟩


/--
Once bounded search has found a witness by height n, it still returns some
witness at height n + k.
-/
theorem findListStabilityWitness_some_monotone_add
    {α : Type u}
    (U : UniverseList α)
    (F : (α → Prop) → α → Prop)
    (dec :
      ∀ n : Nat,
        Decidable
          (AgreeOnList U.support
            (F (Iter F n))
            (Iter F n)))
    (n : Nat)
    {W : ListStabilityWitness U F}
    (h :
      findListStabilityWitness U F dec n = some W) :
    ∀ k : Nat,
      ∃ W' : ListStabilityWitness U F,
        findListStabilityWitness U F dec (n + k) = some W'
  | 0 =>
      by
        exact ⟨W, by
          rw [Nat.add_zero]
          exact h⟩
  | Nat.succ k =>
      by
        rcases
          findListStabilityWitness_some_monotone_add
            U F dec n h k with ⟨Wk, hWk⟩
        rcases
          findListStabilityWitness_some_monotone_succ
            U F dec (n + k) hWk with ⟨Wnext, hnext⟩
        exact ⟨Wnext, by
          rw [Nat.add_succ]
          exact hnext⟩


/--
If list-stability holds at height n, then bounded search up to n + k succeeds.
-/
theorem findListStabilityWitness_exists_of_stable_at_offset
    {α : Type u}
    (U : UniverseList α)
    (F : (α → Prop) → α → Prop)
    (dec :
      ∀ n : Nat,
        Decidable
          (AgreeOnList U.support
            (F (Iter F n))
            (Iter F n)))
    (n k : Nat)
    (hstable :
      AgreeOnList U.support
        (F (Iter F n))
        (Iter F n)) :
    ∃ W : ListStabilityWitness U F,
      findListStabilityWitness U F dec (n + k) = some W :=
  by
    rcases
      findListStabilityWitness_exists_of_stable_at_fuel
        U F dec n hstable with ⟨W, hW⟩
    exact
      findListStabilityWitness_some_monotone_add
        U F dec n hW k


/--
Global stability at height n also gives bounded-search success up to n + k.
-/
theorem findListStabilityWitness_exists_of_global_stable_at_offset
    {α : Type u}
    (U : UniverseList α)
    (F : (α → Prop) → α → Prop)
    (dec :
      ∀ n : Nat,
        Decidable
          (AgreeOnList U.support
            (F (Iter F n))
            (Iter F n)))
    (n k : Nat)
    (hstable : StableAt F n) :
    ∃ W : ListStabilityWitness U F,
      findListStabilityWitness U F dec (n + k) = some W :=
  findListStabilityWitness_exists_of_stable_at_offset
    U F dec n k
    (by
      intro x _hx
      exact hstable x)


/--
A stability proof at height n yields a successful search at n + k and a closure
certificate.
-/
theorem closureCertificate_exists_of_stable_at_offset
    {α : Type u}
    (U : UniverseList α)
    (F : (α → Prop) → α → Prop)
    (dec :
      ∀ n : Nat,
        Decidable
          (AgreeOnList U.support
            (F (Iter F n))
            (Iter F n)))
    (n k : Nat)
    (hstable :
      AgreeOnList U.support
        (F (Iter F n))
        (Iter F n)) :
    ∃ W : ListStabilityWitness U F,
      findListStabilityWitness U F dec (n + k) = some W ∧
      StableAt F W.height :=
  by
    rcases
      findListStabilityWitness_exists_of_stable_at_offset
        U F dec n k hstable with ⟨W, hW⟩
    exact
      ⟨W, hW, stableAt_of_listStabilityWitness W⟩


/--
A global stability proof at height n yields a successful search at n + k and a
closure certificate.
-/
theorem closureCertificate_exists_of_global_stable_at_offset
    {α : Type u}
    (U : UniverseList α)
    (F : (α → Prop) → α → Prop)
    (dec :
      ∀ n : Nat,
        Decidable
          (AgreeOnList U.support
            (F (Iter F n))
            (Iter F n)))
    (n k : Nat)
    (hstable : StableAt F n) :
    ∃ W : ListStabilityWitness U F,
      findListStabilityWitness U F dec (n + k) = some W ∧
      StableAt F W.height :=
  closureCertificate_exists_of_stable_at_offset
    U F dec n k
    (by
      intro x _hx
      exact hstable x)


/--
A small package for the later finite-stabilization theorem: it records a
stability height together with extra fuel.
-/
structure StableWithinOffset
    {α : Type u}
    (U : UniverseList α)
    (F : (α → Prop) → α → Prop) : Type (u + 1) where
  height :
    Nat
  extra_fuel :
    Nat
  stable_on_list :
    AgreeOnList U.support
      (F (Iter F height))
      (Iter F height)


/-- The actual fuel determined by a `StableWithinOffset` certificate. -/
def StableWithinOffset.fuel
    {α : Type u}
    {U : UniverseList α}
    {F : (α → Prop) → α → Prop}
    (H : StableWithinOffset U F) :
    Nat :=
  H.height + H.extra_fuel


/--
A `StableWithinOffset` certificate makes the bounded search succeed at its
recorded fuel.
-/
theorem findListStabilityWitness_exists_of_stableWithinOffset
    {α : Type u}
    (U : UniverseList α)
    (F : (α → Prop) → α → Prop)
    (dec :
      ∀ n : Nat,
        Decidable
          (AgreeOnList U.support
            (F (Iter F n))
            (Iter F n)))
    (H : StableWithinOffset U F) :
    ∃ W : ListStabilityWitness U F,
      findListStabilityWitness U F dec H.fuel = some W :=
  findListStabilityWitness_exists_of_stable_at_offset
    U F dec H.height H.extra_fuel H.stable_on_list

end BoundedSearchOffsetCompletenessKernel
end JALC
end LeanCfgProject
