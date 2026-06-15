import LeanCfgProject.JALC.StrictGrowthCountingInterfaceKernel

namespace LeanCfgProject
namespace JALC
namespace PaperFacingStrictGrowthCountingInterface

/-
Paper-facing target for the strict-growth counting interface.
-/

universe u

open FiniteClosureKernel
open FiniteUniverseListEnumerationKernel
open ListStabilityKernel
open BoundedListStabilitySearchKernel
open ListGrowthStabilizationKernel
open StrictGrowthWitnessFreshnessKernel
open StrictGrowthCountingInterfaceKernel


/-- Paper-facing strict-growth run to fresh family. -/
theorem checked_freshFamily_exists_of_strictGrowthRun
    {α : Type u}
    {xs : List α}
    {F : (α → Prop) → α → Prop}
    {fuel : Nat}
    (mono : PredMonotone F)
    (run : StrictGrowthRun xs F fuel) :
    Nonempty (FreshStrictGrowthFamily xs F fuel) :=
  freshFamily_exists_of_strictGrowthRun mono run


/-- Paper-facing fresh-family obstruction rules out full strict-growth runs. -/
theorem checked_not_strictGrowthRun_of_freshFamilyImpossible
    {α : Type u}
    {xs : List α}
    {F : (α → Prop) → α → Prop}
    {fuel : Nat}
    (mono : PredMonotone F)
    (himp : FreshFamilyImpossible xs F fuel) :
    ¬ StrictGrowthRun xs F fuel :=
  not_strictGrowthRun_of_freshFamilyImpossible mono himp


/-- Paper-facing failed strict-growth run gives a no-strict-growth height. -/
theorem checked_exists_noStrictGrowth_height_of_not_strictGrowthRun
    {α : Type u}
    {xs : List α}
    {F : (α → Prop) → α → Prop}
    {fuel : Nat}
    (hnot : ¬ StrictGrowthRun xs F fuel) :
    ∃ n : Nat,
      n ≤ fuel ∧
      ¬ StrictGrowthAt xs F n :=
  exists_noStrictGrowth_height_of_not_strictGrowthRun hnot


/-- Paper-facing failed strict-growth run gives bounded-search success. -/
theorem checked_boundedSearch_of_not_strictGrowthRun
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
    (hnot : ¬ StrictGrowthRun U.support F fuel) :
    ∃ W : ListStabilityWitness U F,
      findListStabilityWitness U F dec fuel = some W :=
  boundedSearch_of_not_strictGrowthRun
    U F mono dec fuel hnot


/-- Paper-facing fresh-family obstruction gives bounded-search success. -/
theorem checked_boundedSearch_of_freshFamilyImpossible
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
    (himp : FreshFamilyImpossible U.support F fuel) :
    ∃ W : ListStabilityWitness U F,
      findListStabilityWitness U F dec fuel = some W :=
  boundedSearch_of_freshFamilyImpossible
    U F mono dec fuel himp


/-- Paper-facing fresh-family obstruction gives a closure certificate. -/
theorem checked_closureCertificate_of_freshFamilyImpossible
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
    (himp : FreshFamilyImpossible U.support F fuel) :
    ∃ W : ListStabilityWitness U F,
      findListStabilityWitness U F dec fuel = some W ∧
      StableAt F W.height :=
  closureCertificate_of_freshFamilyImpossible
    U F mono dec fuel himp

end PaperFacingStrictGrowthCountingInterface
end JALC
end LeanCfgProject
