import LeanCfgProject.JALC.BoundedSearchCompletenessKernel

namespace LeanCfgProject
namespace JALC
namespace PaperFacingBoundedSearchCompleteness

/-
Paper-facing target for weak completeness of the bounded list-stability search.
-/

universe u

open FiniteClosureKernel
open FiniteUniverseListEnumerationKernel
open ListStabilityKernel
open BoundedListStabilitySearchKernel
open BoundedSearchCompletenessKernel


/-- Paper-facing search success from list-stability at the fuel height. -/
theorem checked_findListStabilityWitness_exists_of_stable_at_fuel
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
      findListStabilityWitness U F dec fuel = some W :=
  findListStabilityWitness_exists_of_stable_at_fuel
    U F dec fuel hstable


/-- Paper-facing search success from global stability at the fuel height. -/
theorem checked_findListStabilityWitness_exists_of_global_stable_at_fuel
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
  findListStabilityWitness_exists_of_global_stable_at_fuel
    U F dec fuel hstable


/-- Paper-facing closure certificate consequence from list-stability at fuel. -/
theorem checked_closureCertificate_exists_of_stable_at_fuel
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
  closureCertificate_exists_of_stable_at_fuel
    U F dec fuel hstable


/-- Paper-facing closure certificate consequence from global stability at fuel. -/
theorem checked_closureCertificate_exists_of_global_stable_at_fuel
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
  closureCertificate_exists_of_global_stable_at_fuel
    U F dec fuel hstable

end PaperFacingBoundedSearchCompleteness
end JALC
end LeanCfgProject
