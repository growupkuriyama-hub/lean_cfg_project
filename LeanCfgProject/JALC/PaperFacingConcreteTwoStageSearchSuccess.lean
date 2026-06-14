import LeanCfgProject.JALC.ConcreteTwoStageSearchSuccessKernel

namespace LeanCfgProject
namespace JALC
namespace PaperFacingConcreteTwoStageSearchSuccess

/-
Paper-facing target for the concrete two-stage search success bridge.
-/

universe u v w

open FiniteClosureKernel
open FiniteUniverseListEnumerationKernel
open ListStabilityKernel
open BoundedListStabilitySearchKernel
open ConcreteBoundedWitnessBridgeKernel
open ConcreteTwoStageBoundedSearchKernel
open ConcreteTwoStageSearchSuccessKernel


/-- Paper-facing component-success to combined-search success. -/
theorem checked_findConcreteBoundedWitnessData_some_of_component_success
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
  findConcreteBoundedWitnessData_some_of_component_success
    tau G I productive_fuel reachable_fuel hP hR


/-- Paper-facing component-success to successful-run certificate. -/
theorem checked_component_success_to_searchCertificate_exists
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
    ∃ C : ConcreteTwoStageSearchCertificateKernel.ConcreteTwoStageSearchCertificate
      tau G,
      C.result =
        boundedWitnessData_of_componentWitnesses
          tau G I PW RW :=
  component_success_to_searchCertificate_exists
    tau G I productive_fuel reachable_fuel hP hR


/-- Paper-facing component-success to FullKept decidability. -/
theorem checked_component_success_to_fullKept_decidable
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
  component_success_to_fullKept_decidable
    tau G I productive_fuel reachable_fuel hP hR


/-- Paper-facing component-stability to combined-search success. -/
theorem checked_findConcreteBoundedWitnessData_exists_of_component_stability
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
  findConcreteBoundedWitnessData_exists_of_component_stability
    tau G I productive_fuel reachable_fuel hPstable hRstable

end PaperFacingConcreteTwoStageSearchSuccess
end JALC
end LeanCfgProject
