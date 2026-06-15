import LeanCfgProject.JALC.ListGrowthStabilizationKernel

namespace LeanCfgProject
namespace JALC
namespace PaperFacingListGrowthStabilization

/-
Paper-facing target for the list-growth stabilization interface.
-/

universe u

open FiniteClosureKernel
open FiniteUniverseListEnumerationKernel
open ListStabilityKernel
open BoundedListStabilitySearchKernel
open BoundedSearchWithinBoundKernel
open ListGrowthStabilizationKernel


/-- Paper-facing monotone iterates are increasing. -/
theorem checked_iter_subset_succ_of_monotone
    {α : Type u}
    {F : (α → Prop) → α → Prop}
    (mono : PredMonotone F) :
    ∀ n : Nat,
      PredSubset (Iter F n) (F (Iter F n)) :=
  iter_subset_succ_of_monotone mono


/-- Paper-facing no-strict-growth gives list stability. -/
theorem checked_agreeOnList_of_no_strictGrowth_at_iter
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
  agreeOnList_of_no_strictGrowth_at_iter
    xs mono n hno


/-- Paper-facing no-strict-growth within fuel gives bounded-search success. -/
theorem checked_findListStabilityWitness_exists_of_no_strictGrowth_le_fuel
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
  findListStabilityWitness_exists_of_no_strictGrowth_le_fuel
    U F mono dec fuel n hle hno


/-- Paper-facing no-strict-growth within fuel gives a closure certificate. -/
theorem checked_closureCertificate_exists_of_no_strictGrowth_le_fuel
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
  closureCertificate_exists_of_no_strictGrowth_le_fuel
    U F mono dec fuel n hle hno


/-- Paper-facing no-strict-growth certificate is accepted by bounded search. -/
theorem checked_boundedSearch_accepts_noStrictGrowthWithinBound
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
  boundedSearch_accepts_noStrictGrowthWithinBound
    U F mono dec fuel H

end PaperFacingListGrowthStabilization
end JALC
end LeanCfgProject
