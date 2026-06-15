import LeanCfgProject.JALC.ConcreteNoStrictGrowthSearchSuccessKernel

namespace LeanCfgProject
namespace JALC
namespace PaperFacingConcreteNoStrictGrowthSearchSuccess

/-
Paper-facing target for the concrete no-strict-growth search-success bridge.
-/

universe u v w

open FiniteClosureKernel
open FiniteUniverseListEnumerationKernel
open ListStabilityKernel
open BoundedListStabilitySearchKernel
open ConcreteBoundedWitnessBridgeKernel
open ConcreteTwoStageBoundedSearchKernel
open ConcreteNoStrictGrowthSearchSuccessKernel


/-- Paper-facing productive no-strict-growth to productive search success. -/
theorem checked_findProductiveBoundedWitness_exists_of_noStrictGrowth
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    (tau : Sigma → M)
    (G : RoundTripKernel.UntypedStructure V Sigma)
    (I : ConcreteTwoStageBoundedSearchInput tau G)
    (productive_fuel : Nat)
    (productive_mono :
      PredMonotone (ProductiveConcreteStep tau G))
    (H :
      NoStrictGrowthWithinBound
        I.rule_universes.states
        (ProductiveConcreteStep tau G)
        productive_fuel) :
    ∃ PW :
      ListStabilityWitness
        I.rule_universes.states
        (ProductiveConcreteStep tau G),
      findProductiveBoundedWitness
        tau G I productive_fuel = some PW :=
  findProductiveBoundedWitness_exists_of_noStrictGrowth
    tau G I productive_fuel productive_mono H


/-- Paper-facing reachable no-strict-growth to reachable search success. -/
theorem checked_findReachableBoundedWitness_exists_of_noStrictGrowth
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    (tau : Sigma → M)
    (G : RoundTripKernel.UntypedStructure V Sigma)
    (I : ConcreteTwoStageBoundedSearchInput tau G)
    (reachable_fuel : Nat)
    (PW :
      ListStabilityWitness
        I.rule_universes.states
        (ProductiveConcreteStep tau G))
    (reachable_mono :
      PredMonotone (ReachableConcreteStepAt tau G PW.height))
    (H :
      NoStrictGrowthWithinBound
        I.rule_universes.states
        (ReachableConcreteStepAt tau G PW.height)
        reachable_fuel) :
    ∃ RW :
      ListStabilityWitness
        I.rule_universes.states
        (ReachableConcreteStepAt tau G PW.height),
      findReachableBoundedWitness
        tau G I PW reachable_fuel = some RW :=
  findReachableBoundedWitness_exists_of_noStrictGrowth
    tau G I reachable_fuel PW reachable_mono H


/-- Paper-facing no-strict-growth component certificates to combined search success. -/
theorem checked_findConcreteBoundedWitnessData_exists_of_noStrictGrowth_components
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    (tau : Sigma → M)
    (G : RoundTripKernel.UntypedStructure V Sigma)
    (I : ConcreteTwoStageBoundedSearchInput tau G)
    (productive_fuel reachable_fuel : Nat)
    (productive_mono :
      PredMonotone (ProductiveConcreteStep tau G))
    (reachable_mono :
      ∀ h : Nat,
        PredMonotone (ReachableConcreteStepAt tau G h))
    (Hprod :
      NoStrictGrowthWithinBound
        I.rule_universes.states
        (ProductiveConcreteStep tau G)
        productive_fuel)
    (Hreach :
      ∀ PW :
        ListStabilityWitness
          I.rule_universes.states
          (ProductiveConcreteStep tau G),
        findProductiveBoundedWitness
          tau G I productive_fuel = some PW →
        NoStrictGrowthWithinBound
          I.rule_universes.states
          (ReachableConcreteStepAt tau G PW.height)
          reachable_fuel) :
    ∃ B : ConcreteBoundedWitnessData tau G,
      findConcreteBoundedWitnessData
        tau G I productive_fuel reachable_fuel = some B :=
  findConcreteBoundedWitnessData_exists_of_noStrictGrowth_components
    tau G I productive_fuel reachable_fuel
    productive_mono reachable_mono Hprod Hreach


/-- Paper-facing no-strict-growth components to FullKept decidability. -/
theorem checked_noStrictGrowth_components_to_fullKept_decidable
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    [DecidableEq (InverseKernel.TypedState V M)]
    (tau : Sigma → M)
    (G : RoundTripKernel.UntypedStructure V Sigma)
    (I : ConcreteTwoStageBoundedSearchInput tau G)
    (productive_fuel reachable_fuel : Nat)
    (productive_mono :
      PredMonotone (ProductiveConcreteStep tau G))
    (reachable_mono :
      ∀ h : Nat,
        PredMonotone (ReachableConcreteStepAt tau G h))
    (Hprod :
      NoStrictGrowthWithinBound
        I.rule_universes.states
        (ProductiveConcreteStep tau G)
        productive_fuel)
    (Hreach :
      ∀ PW :
        ListStabilityWitness
          I.rule_universes.states
          (ProductiveConcreteStep tau G),
        findProductiveBoundedWitness
          tau G I productive_fuel = some PW →
        NoStrictGrowthWithinBound
          I.rule_universes.states
          (ReachableConcreteStepAt tau G PW.height)
          reachable_fuel) :
    Nonempty (DecidablePred (FullKeptCorrectnessKernel.FullKept tau G)) :=
  noStrictGrowth_components_to_fullKept_decidable
    tau G I productive_fuel reachable_fuel
    productive_mono reachable_mono Hprod Hreach


/-- Paper-facing bundled no-strict-growth certificate to search success. -/
theorem checked_concreteNoStrictGrowthSuccessData_to_search_success
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    (tau : Sigma → M)
    (G : RoundTripKernel.UntypedStructure V Sigma)
    (I : ConcreteTwoStageBoundedSearchInput tau G)
    (productive_fuel reachable_fuel : Nat)
    (D :
      ConcreteNoStrictGrowthSuccessData
        tau G I productive_fuel reachable_fuel) :
    ∃ B : ConcreteBoundedWitnessData tau G,
      findConcreteBoundedWitnessData
        tau G I productive_fuel reachable_fuel = some B :=
  concreteNoStrictGrowthSuccessData_to_search_success
    tau G I productive_fuel reachable_fuel D


/-- Paper-facing bundled no-strict-growth certificate to FullKept decidability. -/
theorem checked_concreteNoStrictGrowthSuccessData_to_fullKept_decidable
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    [DecidableEq (InverseKernel.TypedState V M)]
    (tau : Sigma → M)
    (G : RoundTripKernel.UntypedStructure V Sigma)
    (I : ConcreteTwoStageBoundedSearchInput tau G)
    (productive_fuel reachable_fuel : Nat)
    (D :
      ConcreteNoStrictGrowthSuccessData
        tau G I productive_fuel reachable_fuel) :
    Nonempty (DecidablePred (FullKeptCorrectnessKernel.FullKept tau G)) :=
  concreteNoStrictGrowthSuccessData_to_fullKept_decidable
    tau G I productive_fuel reachable_fuel D

end PaperFacingConcreteNoStrictGrowthSearchSuccess
end JALC
end LeanCfgProject
