import LeanCfgProject.JALC.ConcreteTwoStageSearchConsistencyKernel
import LeanCfgProject.JALC.BoundedSearchCompletenessKernel

namespace LeanCfgProject
namespace JALC
namespace ConcreteTwoStageSearchSuccessKernel

/-
Success bridge for the concrete two-stage bounded search.

This file connects component-level bounded-search success to success of the
combined two-stage search.  It is the bridge needed before a later finite
stabilization theorem can be plugged into the concrete pipeline.
-/

universe u v w

open FiniteClosureKernel
open FiniteUniverseListEnumerationKernel
open ListStabilityKernel
open BoundedListStabilitySearchKernel
open BoundedSearchCompletenessKernel
open ConcreteBoundedWitnessBridgeKernel
open ConcreteTwoStageBoundedSearchKernel
open ConcreteTwoStageSearchCertificateKernel
open ConcreteTwoStageSearchConsistencyKernel


/-- The concrete bounded-witness data assembled from component witnesses. -/
def boundedWitnessData_of_componentWitnesses
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    (tau : Sigma → M)
    (G : RoundTripKernel.UntypedStructure V Sigma)
    (I : ConcreteTwoStageBoundedSearchInput tau G)
    (PW :
      ListStabilityWitness
        I.rule_universes.states
        (ProductiveConcreteStep tau G))
    (RW :
      ListStabilityWitness
        I.rule_universes.states
        (ReachableConcreteStepAt tau G PW.height)) :
    ConcreteBoundedWitnessData tau G :=
  { rule_universes := I.rule_universes,
    rule_decisions := I.rule_decisions,
    productive_witness := PW,
    reachable_witness := RW }


/--
If the productive component search and the reachable component search both
succeed, then the combined two-stage search succeeds.
-/
theorem findConcreteBoundedWitnessData_some_of_component_success
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    (tau : Sigma → M)
    (G : RoundTripKernel.UntypedStructure V Sigma)
    (I : ConcreteTwoStageBoundedSearchInput tau G)
    (productive_fuel reachable_fuel : Nat)
    {PW :
      ListStabilityWitness
        I.rule_universes.states
        (ProductiveConcreteStep tau G)}
    (hP :
      findProductiveBoundedWitness
        tau G I productive_fuel = some PW)
    {RW :
      ListStabilityWitness
        I.rule_universes.states
        (ReachableConcreteStepAt tau G PW.height)}
    (hR :
      findReachableBoundedWitness
        tau G I PW reachable_fuel = some RW) :
    findConcreteBoundedWitnessData
      tau G I productive_fuel reachable_fuel =
        some
          (boundedWitnessData_of_componentWitnesses
            tau G I PW RW) :=
  by
    unfold findConcreteBoundedWitnessData
    rw [hP]
    rw [hR]
    rfl


/--
Component-search success gives an explicit successful-run certificate for the
combined two-stage search.
-/
theorem component_success_to_searchCertificate_exists
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    (tau : Sigma → M)
    (G : RoundTripKernel.UntypedStructure V Sigma)
    (I : ConcreteTwoStageBoundedSearchInput tau G)
    (productive_fuel reachable_fuel : Nat)
    {PW :
      ListStabilityWitness
        I.rule_universes.states
        (ProductiveConcreteStep tau G)}
    (hP :
      findProductiveBoundedWitness
        tau G I productive_fuel = some PW)
    {RW :
      ListStabilityWitness
        I.rule_universes.states
        (ReachableConcreteStepAt tau G PW.height)}
    (hR :
      findReachableBoundedWitness
        tau G I PW reachable_fuel = some RW) :
    ∃ C : ConcreteTwoStageSearchCertificate tau G,
      C.result =
        boundedWitnessData_of_componentWitnesses
          tau G I PW RW :=
  by
    let B :=
      boundedWitnessData_of_componentWitnesses
        tau G I PW RW
    have hmain :
      findConcreteBoundedWitnessData
        tau G I productive_fuel reachable_fuel = some B :=
      findConcreteBoundedWitnessData_some_of_component_success
        tau G I productive_fuel reachable_fuel hP hR
    let C :=
      certificate_of_search_eq
        tau G I productive_fuel reachable_fuel hmain
    exact ⟨C, rfl⟩


/--
Component-search success routes to the FullKept-decidability chain.
-/
theorem component_success_to_fullKept_decidable
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    [DecidableEq (InverseKernel.TypedState V M)]
    (tau : Sigma → M)
    (G : RoundTripKernel.UntypedStructure V Sigma)
    (I : ConcreteTwoStageBoundedSearchInput tau G)
    (productive_fuel reachable_fuel : Nat)
    {PW :
      ListStabilityWitness
        I.rule_universes.states
        (ProductiveConcreteStep tau G)}
    (hP :
      findProductiveBoundedWitness
        tau G I productive_fuel = some PW)
    {RW :
      ListStabilityWitness
        I.rule_universes.states
        (ReachableConcreteStepAt tau G PW.height)}
    (hR :
      findReachableBoundedWitness
        tau G I PW reachable_fuel = some RW) :
    Nonempty (DecidablePred (FullKeptCorrectnessKernel.FullKept tau G)) :=
  by
    let B :=
      boundedWitnessData_of_componentWitnesses
        tau G I PW RW
    have hmain :
      findConcreteBoundedWitnessData
        tau G I productive_fuel reachable_fuel = some B :=
      findConcreteBoundedWitnessData_some_of_component_success
        tau G I productive_fuel reachable_fuel hP hR
    exact
      search_some_to_certificate_fullKept_decidable
        tau G I productive_fuel reachable_fuel hmain


/--
If productivity is stable at the productive fuel, and reachability is stable at
the reachable fuel for the productive witness that the first search returns,
then the two-stage search returns some concrete bounded-witness data.
-/
theorem findConcreteBoundedWitnessData_exists_of_component_stability
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    (tau : Sigma → M)
    (G : RoundTripKernel.UntypedStructure V Sigma)
    (I : ConcreteTwoStageBoundedSearchInput tau G)
    (productive_fuel reachable_fuel : Nat)
    (hPstable :
      AgreeOnList I.rule_universes.states.support
        (ProductiveConcreteStep tau G
          (Iter (ProductiveConcreteStep tau G) productive_fuel))
        (Iter (ProductiveConcreteStep tau G) productive_fuel))
    (hRstable :
      ∀ PW :
        ListStabilityWitness
          I.rule_universes.states
          (ProductiveConcreteStep tau G),
        findProductiveBoundedWitness
          tau G I productive_fuel = some PW →
        AgreeOnList I.rule_universes.states.support
          (ReachableConcreteStepAt tau G PW.height
            (Iter
              (ReachableConcreteStepAt tau G PW.height)
              reachable_fuel))
          (Iter
            (ReachableConcreteStepAt tau G PW.height)
            reachable_fuel)) :
    ∃ B : ConcreteBoundedWitnessData tau G,
      findConcreteBoundedWitnessData
        tau G I productive_fuel reachable_fuel = some B :=
  by
    rcases
      findListStabilityWitness_exists_of_stable_at_fuel
        I.rule_universes.states
        (ProductiveConcreteStep tau G)
        I.productive_dec
        productive_fuel
        hPstable with ⟨PW, hPWraw⟩
    have hP :
      findProductiveBoundedWitness
        tau G I productive_fuel = some PW := by
      unfold findProductiveBoundedWitness
      exact hPWraw
    rcases
      findListStabilityWitness_exists_of_stable_at_fuel
        I.rule_universes.states
        (ReachableConcreteStepAt tau G PW.height)
        (I.reachable_dec PW.height)
        reachable_fuel
        (hRstable PW hP) with ⟨RW, hRWraw⟩
    have hR :
      findReachableBoundedWitness
        tau G I PW reachable_fuel = some RW := by
      unfold findReachableBoundedWitness
      exact hRWraw
    exact
      ⟨boundedWitnessData_of_componentWitnesses
          tau G I PW RW,
       findConcreteBoundedWitnessData_some_of_component_success
          tau G I productive_fuel reachable_fuel hP hR⟩

end ConcreteTwoStageSearchSuccessKernel
end JALC
end LeanCfgProject
