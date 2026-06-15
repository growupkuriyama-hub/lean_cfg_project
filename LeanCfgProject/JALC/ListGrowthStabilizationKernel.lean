import LeanCfgProject.JALC.BoundedSearchWithinBoundKernel

namespace LeanCfgProject
namespace JALC
namespace ListGrowthStabilizationKernel

/-
List-growth stabilization interface.

This file is the next step toward finite stabilization.  It isolates the local
growth principle needed for a future pigeonhole/counting argument:

for a monotone iteration, if no new element appears on the finite support at
height n, then the iteration is list-stable at height n.

The remaining future theorem should show that, over a finite support list,
strict growth cannot happen forever.
-/

universe u

open FiniteClosureKernel
open FiniteUniverseListEnumerationKernel
open ListStabilityKernel
open BoundedListStabilitySearchKernel
open BoundedSearchWithinBoundKernel


/-- Predicate inclusion restricted to a finite list. -/
def ListPredSubset
    {α : Type u}
    (xs : List α)
    (P Q : α → Prop) : Prop :=
  ∀ x : α, x ∈ xs → P x → Q x


/-- Strict growth from `P` to `Q` on a finite list. -/
def ListStrictGrowth
    {α : Type u}
    (xs : List α)
    (P Q : α → Prop) : Prop :=
  ListPredSubset xs P Q ∧
    ∃ x : α, x ∈ xs ∧ Q x ∧ ¬ P x


/-- Global predicate inclusion restricts to list inclusion. -/
theorem listPredSubset_of_predSubset
    {α : Type u}
    (xs : List α)
    {P Q : α → Prop}
    (h : PredSubset P Q) :
    ListPredSubset xs P Q :=
  by
    intro x _hx hp
    exact h x hp


/--
A strict list growth step prevents list agreement.
-/
theorem not_agreeOnList_of_listStrictGrowth
    {α : Type u}
    {xs : List α}
    {P Q : α → Prop}
    (h : ListStrictGrowth xs P Q) :
    ¬ AgreeOnList xs Q P :=
  by
    intro hagree
    rcases h with ⟨_hsub, x, hx, hq, hnotp⟩
    exact hnotp ((hagree x hx).1 hq)


/--
If `P` is included in `Q` on the list and there is no strict growth, then
`P` and `Q` agree on the list.
-/
theorem agreeOnList_of_subset_and_no_strictGrowth
    {α : Type u}
    {xs : List α}
    {P Q : α → Prop}
    (hsub : ListPredSubset xs P Q)
    (hno : ¬ ListStrictGrowth xs P Q) :
    AgreeOnList xs Q P :=
  by
    intro x hx
    constructor
    · intro hq
      by_contra hnotp
      exact hno ⟨hsub, x, hx, hq, hnotp⟩
    · intro hp
      exact hsub x hx hp


/--
For a monotone predicate transformer, the finite iterates are increasing.
-/
theorem iter_subset_succ_of_monotone
    {α : Type u}
    {F : (α → Prop) → α → Prop}
    (mono : PredMonotone F) :
    ∀ n : Nat,
      PredSubset (Iter F n) (F (Iter F n)) :=
  by
    intro n
    induction n with
    | zero =>
        intro x hx
        cases hx
    | succ n ih =>
        exact mono ih


/--
For a monotone predicate transformer, the finite iterates are increasing on any
support list.
-/
theorem iter_listSubset_succ_of_monotone
    {α : Type u}
    (xs : List α)
    {F : (α → Prop) → α → Prop}
    (mono : PredMonotone F)
    (n : Nat) :
    ListPredSubset xs (Iter F n) (F (Iter F n)) :=
  listPredSubset_of_predSubset
    xs
    (iter_subset_succ_of_monotone mono n)


/--
If no strict growth occurs at height `n` on the support list, then the monotone
iteration is list-stable at height `n`.
-/
theorem agreeOnList_of_no_strictGrowth_at_iter
    {α : Type u}
    (xs : List α)
    {F : (α → Prop) → α → Prop}
    (mono : PredMonotone F)
    (n : Nat)
    (hno :
      ¬ ListStrictGrowth xs
        (Iter F n)
        (F (Iter F n))) :
    AgreeOnList xs
      (F (Iter F n))
      (Iter F n) :=
  agreeOnList_of_subset_and_no_strictGrowth
    (iter_listSubset_succ_of_monotone xs mono n)
    hno


/--
No strict growth at a height within a fuel bound gives the `StableWithinBound`
certificate expected by the bounded-search bridge.
-/
def stableWithinBound_of_no_strictGrowth
    {α : Type u}
    (U : UniverseList α)
    {F : (α → Prop) → α → Prop}
    (mono : PredMonotone F)
    (fuel n : Nat)
    (hle : n ≤ fuel)
    (hno :
      ¬ ListStrictGrowth U.support
        (Iter F n)
        (F (Iter F n))) :
    StableWithinBound U F fuel :=
  { height := n,
    height_le_fuel := hle,
    stable_on_list :=
      agreeOnList_of_no_strictGrowth_at_iter
        U.support mono n hno }


/--
If a monotone iteration has no strict growth at some height within the fuel
bound, then bounded search at that fuel succeeds.
-/
theorem findListStabilityWitness_exists_of_no_strictGrowth_le_fuel
    {α : Type u}
    (U : UniverseList α)
    (F : (α → Prop) → α → Prop)
    (mono : PredMonotone F)
    (dec :
      ∀ k : Nat,
        Decidable
          (AgreeOnList U.support
            (F (Iter F k))
            (Iter F k)))
    (fuel n : Nat)
    (hle : n ≤ fuel)
    (hno :
      ¬ ListStrictGrowth U.support
        (Iter F n)
        (F (Iter F n))) :
    ∃ W : ListStabilityWitness U F,
      findListStabilityWitness U F dec fuel = some W :=
  findListStabilityWitness_exists_of_stableWithinBound
    U F dec fuel
    (stableWithinBound_of_no_strictGrowth
      U mono fuel n hle hno)


/--
The same hypothesis gives both bounded-search success and a closure certificate.
-/
theorem closureCertificate_exists_of_no_strictGrowth_le_fuel
    {α : Type u}
    (U : UniverseList α)
    (F : (α → Prop) → α → Prop)
    (mono : PredMonotone F)
    (dec :
      ∀ k : Nat,
        Decidable
          (AgreeOnList U.support
            (F (Iter F k))
            (Iter F k)))
    (fuel n : Nat)
    (hle : n ≤ fuel)
    (hno :
      ¬ ListStrictGrowth U.support
        (Iter F n)
        (F (Iter F n))) :
    ∃ W : ListStabilityWitness U F,
      findListStabilityWitness U F dec fuel = some W ∧
      StableAt F W.height :=
  closureCertificate_exists_of_stableWithinBound
    U F dec fuel
    (stableWithinBound_of_no_strictGrowth
      U mono fuel n hle hno)


/--
This is the exact remaining local goal for finite support stabilization:
produce a height below the fuel at which no strict growth occurs.
-/
structure NoStrictGrowthWithinBound
    {α : Type u}
    (U : UniverseList α)
    (F : (α → Prop) → α → Prop)
    (fuel : Nat) : Type (u + 1) where
  height :
    Nat
  height_le_fuel :
    height ≤ fuel
  no_strict_growth :
    ¬ ListStrictGrowth U.support
      (Iter F height)
      (F (Iter F height))


/--
A no-strict-growth certificate for a monotone iteration is accepted by bounded
search.
-/
theorem boundedSearch_accepts_noStrictGrowthWithinBound
    {α : Type u}
    (U : UniverseList α)
    (F : (α → Prop) → α → Prop)
    (mono : PredMonotone F)
    (dec :
      ∀ k : Nat,
        Decidable
          (AgreeOnList U.support
            (F (Iter F k))
            (Iter F k)))
    (fuel : Nat)
    (H : NoStrictGrowthWithinBound U F fuel) :
    ∃ W : ListStabilityWitness U F,
      findListStabilityWitness U F dec fuel = some W :=
  findListStabilityWitness_exists_of_no_strictGrowth_le_fuel
    U F mono dec fuel H.height H.height_le_fuel H.no_strict_growth

end ListGrowthStabilizationKernel
end JALC
end LeanCfgProject
