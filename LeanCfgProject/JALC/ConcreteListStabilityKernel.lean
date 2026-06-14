import LeanCfgProject.JALC.ListStabilityKernel
import LeanCfgProject.JALC.PaperFacingExecutableLimit

namespace LeanCfgProject
namespace JALC
namespace ConcreteListStabilityKernel

/-
Concrete list-stability boundary for the full all-copy rule data.

This module packages finite support stability checks for the two extraction
stages and turns them into the certified extraction object used downstream.
-/

universe u v w

open InverseKernel RoundTripKernel
open FiniteClosureKernel
open ProductiveReachableClosureKernel
open AlgorithmicExtractionKernel
open FullAlgorithmicAgreementKernel
open FiniteUniverseListEnumerationKernel
open RulePredicateListCertificateKernel
open ConcreteStepPreservationKernel
open ListStabilityKernel


/--
Concrete list-stability data for the full rule data.
-/
structure ConcreteListStabilityData
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    (tau : Sigma → M)
    (G : UntypedStructure V Sigma) :
    Type (max u v w) where
  rule_universes :
    FullRuleUniverseLists V M
  rule_decisions :
    FullRulePredicateDecisions tau G
  productive_height :
    Nat
  productive_stable_on_list :
    AgreeOnList rule_universes.states.support
      (ProductiveStep
        (fullExtractionRuleData tau G).terminal
        (fullExtractionRuleData tau G).binary
        (Iter
          (ProductiveStep
            (fullExtractionRuleData tau G).terminal
            (fullExtractionRuleData tau G).binary)
          productive_height))
      (Iter
        (ProductiveStep
          (fullExtractionRuleData tau G).terminal
          (fullExtractionRuleData tau G).binary)
        productive_height)
  reachable_height :
    Nat
  reachable_stable_on_list :
    AgreeOnList rule_universes.states.support
      (ReachableStep
        (fullExtractionRuleData tau G).start
        (fullExtractionRuleData tau G).binary
        (Iter
          (ProductiveStep
            (fullExtractionRuleData tau G).terminal
            (fullExtractionRuleData tau G).binary)
          productive_height)
        (Iter
          (ReachableStep
            (fullExtractionRuleData tau G).start
            (fullExtractionRuleData tau G).binary
            (Iter
              (ProductiveStep
                (fullExtractionRuleData tau G).terminal
                (fullExtractionRuleData tau G).binary)
              productive_height))
          reachable_height))
      (Iter
        (ReachableStep
          (fullExtractionRuleData tau G).start
          (fullExtractionRuleData tau G).binary
          (Iter
            (ProductiveStep
              (fullExtractionRuleData tau G).terminal
              (fullExtractionRuleData tau G).binary)
            productive_height))
        reachable_height)


/-- Convert concrete list-stability data to the generic list-stability package. -/
def listStableHeightData_of_concrete
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    (tau : Sigma → M)
    (G : UntypedStructure V Sigma)
    (H : ConcreteListStabilityData tau G) :
    ListStableHeightData (fullExtractionRuleData tau G) :=
  { state_universe := H.rule_universes.states,
    productive_height := H.productive_height,
    productive_stable_on_list := H.productive_stable_on_list,
    reachable_height := H.reachable_height,
    reachable_stable_on_list := H.reachable_stable_on_list }


/-- Build the certified extraction from concrete list-stability data. -/
def certifiedExtraction_of_concreteListStability
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    (tau : Sigma → M)
    (G : UntypedStructure V Sigma)
    (H : ConcreteListStabilityData tau G) :
    CertifiedExtraction (fullExtractionRuleData tau G) :=
  certifiedExtraction_of_listStability
    (listStableHeightData_of_concrete tau G H)


/-- The concrete step-preservation data induced by concrete list-stability. -/
def concreteStepData_of_concreteListStability
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    (tau : Sigma → M)
    (G : UntypedStructure V Sigma)
    (H : ConcreteListStabilityData tau G) :
    ConcreteStepPreservationData tau G
      (certifiedExtraction_of_concreteListStability tau G H) :=
  { rule_universes := H.rule_universes,
    rule_decisions := H.rule_decisions }


/-- Concrete list-stability data supplies FullKept decidability. -/
theorem concreteListStability_to_fullKept_decidable
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    [DecidableEq (InverseKernel.TypedState V M)]
    (tau : Sigma → M)
    (G : UntypedStructure V Sigma)
    (H : ConcreteListStabilityData tau G) :
    Nonempty (DecidablePred (FullKeptCorrectnessKernel.FullKept tau G)) :=
  ConcreteStepPreservationKernel.concreteStepPreservationData_to_fullKept_decidable
    tau G
    (certifiedExtraction_of_concreteListStability tau G H)
    (concreteStepData_of_concreteListStability tau G H)


/-- Concrete list-stability data exposes the certified extraction kernel. -/
theorem concreteListStability_certifiedExtractionKernel
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    (tau : Sigma → M)
    (G : UntypedStructure V Sigma)
    (H : ConcreteListStabilityData tau G) :
    CertifiedExtractionKernel
      (certifiedExtraction_of_concreteListStability tau G H) :=
  listStability_certifiedExtractionKernel
    (listStableHeightData_of_concrete tau G H)

end ConcreteListStabilityKernel
end JALC
end LeanCfgProject
