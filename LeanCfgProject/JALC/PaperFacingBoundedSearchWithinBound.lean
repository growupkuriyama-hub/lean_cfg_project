import LeanCfgProject.JALC.BoundedSearchWithinBoundKernel

namespace LeanCfgProject
namespace JALC
namespace PaperFacingBoundedSearchWithinBound

/-
Paper-facing target for within-bound completeness of bounded list-stability
search.
-/

universe u

open FiniteClosureKernel
open FiniteUniverseListEnumerationKernel
open ListStabilityKernel
open BoundedListStabilitySearchKernel
open BoundedSearchWithinBoundKernel


/-- Paper-facing within-bound certificate to bounded-search success. -/
theorem checked_findListStabilityWitness_exists_of_stableWithinBound
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
  findListStabilityWitness_exists_of_stableWithinBound
    U F dec fuel H


/-- Paper-facing existential stable height below fuel to bounded-search success. -/
theorem checked_findListStabilityWitness_exists_of_exists_stable_le_fuel
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
  findListStabilityWitness_exists_of_exists_stable_le_fuel
    U F dec fuel h


/-- Paper-facing global stable height below fuel to bounded-search success. -/
theorem checked_findListStabilityWitness_exists_of_exists_global_stable_le_fuel
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
  findListStabilityWitness_exists_of_exists_global_stable_le_fuel
    U F dec fuel h


/-- Paper-facing within-bound certificate to closure certificate. -/
theorem checked_closureCertificate_exists_of_stableWithinBound
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
  closureCertificate_exists_of_stableWithinBound
    U F dec fuel H


/-- Paper-facing finite-stabilization output accepted by bounded search. -/
theorem checked_boundedSearch_accepts_finiteStabilizationOutput
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
  boundedSearch_accepts_finiteStabilizationOutput
    U F dec fuel H

end PaperFacingBoundedSearchWithinBound
end JALC
end LeanCfgProject
