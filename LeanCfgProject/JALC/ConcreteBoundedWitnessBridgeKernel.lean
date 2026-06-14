import LeanCfgProject.JALC.BoundedListStabilitySearchKernel
import LeanCfgProject.JALC.ConcreteListStabilityKernel

namespace LeanCfgProject
namespace JALC
namespace ConcreteBoundedWitnessBridgeKernel

/-
Concrete bridge from generic bounded-search witnesses to the already checked
concrete list-stability interface.

The generic bounded-search kernel knows how to produce witnesses of list
stability for an arbitrary monotone-stage operator.  This file reconnects such
witnesses to the full all-copy extraction data, but only as a thin bridge:
two witnesses are converted into `ConcreteListStabilityData`.
-/

universe u v w

open InverseKernel RoundTripKernel
open FiniteClosureKernel
open ProductiveReachableClosureKernel
open FullAlgorithmicAgreementKernel
open FiniteUniverseListEnumerationKernel
open RulePredicateListCertificateKernel
open ListStabilityKernel
open ConcreteListStabilityKernel
open BoundedListStabilitySearchKernel


/-- The productive stage operator for the concrete full all-copy rule data. -/
abbrev ProductiveConcreteStep
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    (tau : Sigma → M)
    (G : UntypedStructure V Sigma) :
    (InverseKernel.TypedState V M → Prop) →
      InverseKernel.TypedState V M → Prop :=
  ProductiveStep
    (fullExtractionRuleData tau G).terminal
    (fullExtractionRuleData tau G).binary


/-- The reachable stage operator after a concrete productive height is fixed. -/
abbrev ReachableConcreteStepAt
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    (tau : Sigma → M)
    (G : UntypedStructure V Sigma)
    (productive_height : Nat) :
    (InverseKernel.TypedState V M → Prop) →
      InverseKernel.TypedState V M → Prop :=
  ReachableStep
    (fullExtractionRuleData tau G).start
    (fullExtractionRuleData tau G).binary
    (Iter (ProductiveConcreteStep tau G) productive_height)


/--
Concrete data obtained after successful bounded searches for both stages.

This is not yet an automatic search procedure.  It is the checked bridge saying
that, if the generic search has supplied the two stage witnesses, then they
fit the concrete full-rule extraction interface.
-/
structure ConcreteBoundedWitnessData
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    (tau : Sigma → M)
    (G : UntypedStructure V Sigma) :
    Type (max (u + 1) (max v w)) where
  rule_universes :
    FullRuleUniverseLists V M
  rule_decisions :
    FullRulePredicateDecisions tau G
  productive_witness :
    ListStabilityWitness
      rule_universes.states
      (ProductiveConcreteStep tau G)
  reachable_witness :
    ListStabilityWitness
      rule_universes.states
      (ReachableConcreteStepAt tau G productive_witness.height)


/-- Convert bounded-search witness data into concrete list-stability data. -/
def concreteListStabilityData_of_boundedWitnessData
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    (tau : Sigma → M)
    (G : UntypedStructure V Sigma)
    (B : ConcreteBoundedWitnessData tau G) :
    ConcreteListStabilityData tau G :=
  { rule_universes := B.rule_universes,
    rule_decisions := B.rule_decisions,
    productive_height := B.productive_witness.height,
    productive_stable_on_list := B.productive_witness.stable_on_list,
    reachable_height := B.reachable_witness.height,
    reachable_stable_on_list := B.reachable_witness.stable_on_list }


/-- Bounded witness data gives the already checked concrete certified extraction. -/
def certifiedExtraction_of_boundedWitnessData
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    (tau : Sigma → M)
    (G : UntypedStructure V Sigma)
    (B : ConcreteBoundedWitnessData tau G) :
    AlgorithmicExtractionKernel.CertifiedExtraction
      (fullExtractionRuleData tau G) :=
  certifiedExtraction_of_concreteListStability
    tau G
    (concreteListStabilityData_of_boundedWitnessData tau G B)


/-- Bounded witness data exposes the concrete certified extraction kernel. -/
theorem boundedWitnessData_certifiedExtractionKernel
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    (tau : Sigma → M)
    (G : UntypedStructure V Sigma)
    (B : ConcreteBoundedWitnessData tau G) :
    AlgorithmicExtractionKernel.CertifiedExtractionKernel
      (certifiedExtraction_of_boundedWitnessData tau G B) :=
  concreteListStability_certifiedExtractionKernel
    tau G
    (concreteListStabilityData_of_boundedWitnessData tau G B)


/-- Bounded witness data supplies FullKept decidability via the existing chain. -/
theorem boundedWitnessData_to_fullKept_decidable
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    [DecidableEq (InverseKernel.TypedState V M)]
    (tau : Sigma → M)
    (G : UntypedStructure V Sigma)
    (B : ConcreteBoundedWitnessData tau G) :
    Nonempty (DecidablePred (FullKeptCorrectnessKernel.FullKept tau G)) :=
  concreteListStability_to_fullKept_decidable
    tau G
    (concreteListStabilityData_of_boundedWitnessData tau G B)

end ConcreteBoundedWitnessBridgeKernel
end JALC
end LeanCfgProject
