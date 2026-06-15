import LeanCfgProject.JALC.ConcreteTwoStageSearchSuccessKernel
import LeanCfgProject.JALC.ListGrowthStabilizationKernel

namespace LeanCfgProject
namespace JALC
namespace ConcreteNoStrictGrowthSearchSuccessKernel

/-
Concrete no-strict-growth bridge.

The generic list-growth interface proves:

  monotone step + no strict growth within fuel
  => bounded list-stability search succeeds.

This file plugs that interface into the concrete two-stage extraction pipeline.
Once later finite-support counting supplies no-strict-growth certificates for
the productive and reachable steps, the concrete two-stage search succeeds and
routes to the certified extraction / FullKept decidability chain.
-/

universe u v w

open FiniteClosureKernel
open FiniteUniverseListEnumerationKernel
open ListStabilityKernel
open BoundedListStabilitySearchKernel
open ConcreteBoundedWitnessBridgeKernel
open ConcreteTwoStageBoundedSearchKernel
open ConcreteTwoStageSearchSuccessKernel
open ListGrowthStabilizationKernel


/--
No-strict-growth within the productive fuel makes the productive component
bounded search return a witness.
-/
theorem findProductiveBoundedWitness_exists_of_noStrictGrowth
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
  by
    rcases
      boundedSearch_accepts_noStrictGrowthWithinBound
        I.rule_universes.states
        (ProductiveConcreteStep tau G)
        productive_mono
        I.productive_dec
        productive_fuel
        H with ⟨PW, hPW⟩
    exact
      ⟨PW, by
        unfold findProductiveBoundedWitness
        exact hPW⟩


/--
No-strict-growth within the reachable fuel makes the reachable component
bounded search return a witness at a fixed productive witness.
-/
theorem findReachableBoundedWitness_exists_of_noStrictGrowth
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
  by
    rcases
      boundedSearch_accepts_noStrictGrowthWithinBound
        I.rule_universes.states
        (ReachableConcreteStepAt tau G PW.height)
        reachable_mono
        (I.reachable_dec PW.height)
        reachable_fuel
        H with ⟨RW, hRW⟩
    exact
      ⟨RW, by
        unfold findReachableBoundedWitness
        exact hRW⟩


/--
If the productive search has a no-strict-growth certificate, and every returned
productive witness supplies a reachable no-strict-growth certificate, then the
combined concrete two-stage bounded search succeeds.
-/
theorem findConcreteBoundedWitnessData_exists_of_noStrictGrowth_components
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
  by
    rcases
      findProductiveBoundedWitness_exists_of_noStrictGrowth
        tau G I productive_fuel productive_mono Hprod with ⟨PW, hP⟩
    rcases
      findReachableBoundedWitness_exists_of_noStrictGrowth
        tau G I reachable_fuel PW
        (reachable_mono PW.height)
        (Hreach PW hP) with ⟨RW, hR⟩
    exact
      ⟨boundedWitnessData_of_componentWitnesses
          tau G I PW RW,
       findConcreteBoundedWitnessData_some_of_component_success
          tau G I productive_fuel reachable_fuel hP hR⟩


/--
The same no-strict-growth component data routes to FullKept decidability.
-/
theorem noStrictGrowth_components_to_fullKept_decidable
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
  by
    rcases
      findProductiveBoundedWitness_exists_of_noStrictGrowth
        tau G I productive_fuel productive_mono Hprod with ⟨PW, hP⟩
    rcases
      findReachableBoundedWitness_exists_of_noStrictGrowth
        tau G I reachable_fuel PW
        (reachable_mono PW.height)
        (Hreach PW hP) with ⟨RW, hR⟩
    exact
      component_success_to_fullKept_decidable
        tau G I productive_fuel reachable_fuel hP hR


/--
A compact certificate bundle for no-strict-growth success of the concrete
two-stage search.
-/
structure ConcreteNoStrictGrowthSuccessData
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    (tau : Sigma → M)
    (G : RoundTripKernel.UntypedStructure V Sigma)
    (I : ConcreteTwoStageBoundedSearchInput tau G)
    (productive_fuel reachable_fuel : Nat) :
    Type (max (u + 1) (max (v + 1) (w + 1))) where
  productive_mono :
    PredMonotone (ProductiveConcreteStep tau G)
  reachable_mono :
    ∀ h : Nat,
      PredMonotone (ReachableConcreteStepAt tau G h)
  productive_no_strict_growth :
    NoStrictGrowthWithinBound
      I.rule_universes.states
      (ProductiveConcreteStep tau G)
      productive_fuel
  reachable_no_strict_growth :
    ∀ PW :
      ListStabilityWitness
        I.rule_universes.states
        (ProductiveConcreteStep tau G),
      findProductiveBoundedWitness
        tau G I productive_fuel = some PW →
      NoStrictGrowthWithinBound
        I.rule_universes.states
        (ReachableConcreteStepAt tau G PW.height)
        reachable_fuel


/--
A bundled no-strict-growth success certificate makes the combined search
succeed.
-/
theorem concreteNoStrictGrowthSuccessData_to_search_success
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
  findConcreteBoundedWitnessData_exists_of_noStrictGrowth_components
    tau G I productive_fuel reachable_fuel
    D.productive_mono
    D.reachable_mono
    D.productive_no_strict_growth
    D.reachable_no_strict_growth


/--
A bundled no-strict-growth success certificate routes to FullKept decidability.
-/
theorem concreteNoStrictGrowthSuccessData_to_fullKept_decidable
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
  noStrictGrowth_components_to_fullKept_decidable
    tau G I productive_fuel reachable_fuel
    D.productive_mono
    D.reachable_mono
    D.productive_no_strict_growth
    D.reachable_no_strict_growth

end ConcreteNoStrictGrowthSearchSuccessKernel
end JALC
end LeanCfgProject
