import LeanCfgProject.JALC.ConcreteTwoStageBoundedSearchKernel

namespace LeanCfgProject
namespace JALC
namespace PaperFacingConcreteTwoStageBoundedSearch

/-
Paper-facing target for option-valued two-stage bounded search.
-/

universe u v w

open ConcreteTwoStageBoundedSearchKernel


/-- Paper-facing productive bounded search. -/
def checked_findProductiveBoundedWitness
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    (tau : Sigma → M)
    (G : RoundTripKernel.UntypedStructure V Sigma)
    (I : ConcreteTwoStageBoundedSearchInput tau G)
    (productive_fuel : Nat) :
    Option
      (BoundedListStabilitySearchKernel.ListStabilityWitness
        I.rule_universes.states
        (ConcreteBoundedWitnessBridgeKernel.ProductiveConcreteStep tau G)) :=
  findProductiveBoundedWitness tau G I productive_fuel


/-- Paper-facing reachable bounded search after productivity is fixed. -/
def checked_findReachableBoundedWitness
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    (tau : Sigma → M)
    (G : RoundTripKernel.UntypedStructure V Sigma)
    (I : ConcreteTwoStageBoundedSearchInput tau G)
    (PW :
      BoundedListStabilitySearchKernel.ListStabilityWitness
        I.rule_universes.states
        (ConcreteBoundedWitnessBridgeKernel.ProductiveConcreteStep tau G))
    (reachable_fuel : Nat) :
    Option
      (BoundedListStabilitySearchKernel.ListStabilityWitness
        I.rule_universes.states
        (ConcreteBoundedWitnessBridgeKernel.ReachableConcreteStepAt
          tau G PW.height)) :=
  findReachableBoundedWitness tau G I PW reachable_fuel


/-- Paper-facing option-valued two-stage concrete bounded search. -/
def checked_findConcreteBoundedWitnessData
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    (tau : Sigma → M)
    (G : RoundTripKernel.UntypedStructure V Sigma)
    (I : ConcreteTwoStageBoundedSearchInput tau G)
    (productive_fuel reachable_fuel : Nat) :
    Option (ConcreteBoundedWitnessBridgeKernel.ConcreteBoundedWitnessData tau G) :=
  findConcreteBoundedWitnessData
    tau G I productive_fuel reachable_fuel


/-- Paper-facing successful-search to FullKept decidability theorem. -/
theorem checked_findConcreteBoundedWitnessData_some_to_fullKept_decidable
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    [DecidableEq (InverseKernel.TypedState V M)]
    (tau : Sigma → M)
    (G : RoundTripKernel.UntypedStructure V Sigma)
    (I : ConcreteTwoStageBoundedSearchInput tau G)
    (productive_fuel reachable_fuel : Nat)
    {B : ConcreteBoundedWitnessBridgeKernel.ConcreteBoundedWitnessData tau G}
    (_h :
      findConcreteBoundedWitnessData
        tau G I productive_fuel reachable_fuel = some B) :
    Nonempty (DecidablePred (FullKeptCorrectnessKernel.FullKept tau G)) :=
  findConcreteBoundedWitnessData_some_to_fullKept_decidable
    tau G I productive_fuel reachable_fuel _h


/-- Paper-facing option-valued FullKept-decidability certificate. -/
def checked_fullKeptDecidableOption_of_search
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    [DecidableEq (InverseKernel.TypedState V M)]
    (tau : Sigma → M)
    (G : RoundTripKernel.UntypedStructure V Sigma)
    (I : ConcreteTwoStageBoundedSearchInput tau G)
    (productive_fuel reachable_fuel : Nat) :
    Option (Nonempty (DecidablePred (FullKeptCorrectnessKernel.FullKept tau G))) :=
  fullKeptDecidableOption_of_search
    tau G I productive_fuel reachable_fuel


/-- Paper-facing option-valued certified extraction result. -/
def checked_certifiedExtractionOption_of_search
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    (tau : Sigma → M)
    (G : RoundTripKernel.UntypedStructure V Sigma)
    (I : ConcreteTwoStageBoundedSearchInput tau G)
    (productive_fuel reachable_fuel : Nat) :
    Option
      (AlgorithmicExtractionKernel.CertifiedExtraction
        (FullAlgorithmicAgreementKernel.fullExtractionRuleData tau G)) :=
  certifiedExtractionOption_of_search
    tau G I productive_fuel reachable_fuel

end PaperFacingConcreteTwoStageBoundedSearch
end JALC
end LeanCfgProject
