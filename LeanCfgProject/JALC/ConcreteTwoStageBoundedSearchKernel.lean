import LeanCfgProject.JALC.ConcreteBoundedWitnessBridgeKernel

namespace LeanCfgProject
namespace JALC
namespace ConcreteTwoStageBoundedSearchKernel

/-
Option-valued two-stage bounded search.

The previous bounded-search kernel is generic: it searches for a
`ListStabilityWitness` for one monotone stage operator.  The previous concrete
bridge says that productive and reachable witnesses, once supplied, feed the
concrete certified-extraction interface.

This file connects the two layers.  It packages the finite list-stability
decision procedures for the productive and reachable stages, runs the
productive search first, and then uses the discovered productive height to run
the reachable search.
-/

universe u v w

open InverseKernel RoundTripKernel
open FiniteClosureKernel
open ListStabilityKernel
open BoundedListStabilitySearchKernel
open ConcreteBoundedWitnessBridgeKernel
open FullAlgorithmicAgreementKernel
open FiniteUniverseListEnumerationKernel
open RulePredicateListCertificateKernel


/--
Input data for the option-valued two-stage bounded search.

The fields `productive_dec` and `reachable_dec` are the finite list-stability
decision procedures used by the generic bounded-search kernel.
-/
structure ConcreteTwoStageBoundedSearchInput
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    (tau : Sigma → M)
    (G : UntypedStructure V Sigma) :
    Type (max (u + 1) (max (v + 1) (w + 1))) where
  rule_universes :
    FullRuleUniverseLists V M
  rule_decisions :
    FullRulePredicateDecisions tau G
  productive_dec :
    ∀ n : Nat,
      Decidable
        (AgreeOnList rule_universes.states.support
          (ProductiveConcreteStep tau G
            (Iter (ProductiveConcreteStep tau G) n))
          (Iter (ProductiveConcreteStep tau G) n))
  reachable_dec :
    ∀ productive_height n : Nat,
      Decidable
        (AgreeOnList rule_universes.states.support
          (ReachableConcreteStepAt tau G productive_height
            (Iter (ReachableConcreteStepAt tau G productive_height) n))
          (Iter (ReachableConcreteStepAt tau G productive_height) n))


/-- Run the productive bounded search from concrete two-stage input data. -/
def findProductiveBoundedWitness
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    (tau : Sigma → M)
    (G : UntypedStructure V Sigma)
    (I : ConcreteTwoStageBoundedSearchInput tau G)
    (productive_fuel : Nat) :
    Option
      (ListStabilityWitness
        I.rule_universes.states
        (ProductiveConcreteStep tau G)) :=
  findListStabilityWitness
    I.rule_universes.states
    (ProductiveConcreteStep tau G)
    I.productive_dec
    productive_fuel


/-- Run the reachable bounded search after a productive witness is known. -/
def findReachableBoundedWitness
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    (tau : Sigma → M)
    (G : UntypedStructure V Sigma)
    (I : ConcreteTwoStageBoundedSearchInput tau G)
    (PW :
      ListStabilityWitness
        I.rule_universes.states
        (ProductiveConcreteStep tau G))
    (reachable_fuel : Nat) :
    Option
      (ListStabilityWitness
        I.rule_universes.states
        (ReachableConcreteStepAt tau G PW.height)) :=
  findListStabilityWitness
    I.rule_universes.states
    (ReachableConcreteStepAt tau G PW.height)
    (I.reachable_dec PW.height)
    reachable_fuel


/--
Run the two-stage concrete bounded search.

If the productive search succeeds, its height is used to instantiate the
reachable stage operator.  If both searches succeed, the result is exactly the
concrete bounded-witness data expected by the bridge kernel.
-/
def findConcreteBoundedWitnessData
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    (tau : Sigma → M)
    (G : UntypedStructure V Sigma)
    (I : ConcreteTwoStageBoundedSearchInput tau G)
    (productive_fuel reachable_fuel : Nat) :
    Option (ConcreteBoundedWitnessData tau G) :=
  match findProductiveBoundedWitness tau G I productive_fuel with
  | none =>
      none
  | some PW =>
      match findReachableBoundedWitness tau G I PW reachable_fuel with
      | none =>
          none
      | some RW =>
          some
            { rule_universes := I.rule_universes,
              rule_decisions := I.rule_decisions,
              productive_witness := PW,
              reachable_witness := RW }


/--
A successful two-stage bounded search result supplies FullKept decidability.
-/
theorem findConcreteBoundedWitnessData_some_to_fullKept_decidable
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    [DecidableEq (InverseKernel.TypedState V M)]
    (tau : Sigma → M)
    (G : UntypedStructure V Sigma)
    (I : ConcreteTwoStageBoundedSearchInput tau G)
    (productive_fuel reachable_fuel : Nat)
    {B : ConcreteBoundedWitnessData tau G}
    (_h :
      findConcreteBoundedWitnessData
        tau G I productive_fuel reachable_fuel = some B) :
    Nonempty (DecidablePred (FullKeptCorrectnessKernel.FullKept tau G)) :=
  boundedWitnessData_to_fullKept_decidable tau G B


/--
Map the successful branch of the option-valued search directly to the
FullKept-decidability certificate.
-/
def fullKeptDecidableOption_of_search
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    [DecidableEq (InverseKernel.TypedState V M)]
    (tau : Sigma → M)
    (G : UntypedStructure V Sigma)
    (I : ConcreteTwoStageBoundedSearchInput tau G)
    (productive_fuel reachable_fuel : Nat) :
    Option (PLift (Nonempty (DecidablePred (FullKeptCorrectnessKernel.FullKept tau G)))) :=
  match findConcreteBoundedWitnessData tau G I productive_fuel reachable_fuel with
  | none =>
      none
  | some B =>
      some (PLift.up (boundedWitnessData_to_fullKept_decidable tau G B))


/--
The option-valued search is conservative: whenever it returns concrete
bounded-witness data, that data is accepted by the concrete bridge.
-/
def certifiedExtractionOption_of_search
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    (tau : Sigma → M)
    (G : UntypedStructure V Sigma)
    (I : ConcreteTwoStageBoundedSearchInput tau G)
    (productive_fuel reachable_fuel : Nat) :
    Option
      (AlgorithmicExtractionKernel.CertifiedExtraction
        (fullExtractionRuleData tau G)) :=
  match findConcreteBoundedWitnessData tau G I productive_fuel reachable_fuel with
  | none =>
      none
  | some B =>
      some (certifiedExtraction_of_boundedWitnessData tau G B)

end ConcreteTwoStageBoundedSearchKernel
end JALC
end LeanCfgProject
