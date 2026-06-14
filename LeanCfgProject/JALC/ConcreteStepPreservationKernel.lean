import LeanCfgProject.JALC.StepPreservationKernel

namespace LeanCfgProject
namespace JALC
namespace ConcreteStepPreservationKernel

/-
Concrete step preservation for the full all-copy rule data.

This module instantiates the generic step-preservation lemmas for
fullExtractionRuleData tau G.
-/

universe u v w

open InverseKernel RoundTripKernel
open FiniteClosureKernel
open ProductiveReachableClosureKernel
open AlgorithmicExtractionKernel
open FullAlgorithmicAgreementKernel
open ListCertificateKernel
open FiniteUniverseListEnumerationKernel
open RulePredicateListCertificateKernel
open IterDecidabilityKernel
open ProductiveReachableStepDecidabilityKernel
open StepPreservationKernel


/-- Convert a binary-triple decider into the curried binary-rule decider. -/
def curriedBinaryDecidable_of_triple
    {V : Type u} {M : Type v}
    (D : ExtractionRuleData (TypedState V M))
    (dec : DecidablePred (binaryTriplePred D)) :
    ∀ x y z : TypedState V M, Decidable (D.binary x y z) :=
  fun x y z => dec (x, y, z)


/--
Concrete finite data sufficient to prove decidability preservation of the two
Algorithm 1 steps for the full rule data.
-/
structure ConcreteStepPreservationData
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    (tau : Sigma → M)
    (G : UntypedStructure V Sigma)
    (E : CertifiedExtraction (fullExtractionRuleData tau G)) :
    Type (max u v w) where
  rule_universes :
    FullRuleUniverseLists V M
  rule_decisions :
    FullRulePredicateDecisions tau G


/-- Rule-list certificates induced by the concrete finite rule-universe data. -/
def concreteRuleLists
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    (tau : Sigma → M)
    (G : UntypedStructure V Sigma)
    {E : CertifiedExtraction (fullExtractionRuleData tau G)}
    (D : ConcreteStepPreservationData tau G E) :
    FullRuleListCertificates tau G :=
  fullRuleListCertificates_of_universes tau G
    D.rule_universes D.rule_decisions


/-- ProductiveStep preserves decidability for the concrete full rule data. -/
def concrete_productive_preserves_decidable
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    (tau : Sigma → M)
    (G : UntypedStructure V Sigma)
    {E : CertifiedExtraction (fullExtractionRuleData tau G)}
    (D : ConcreteStepPreservationData tau G E) :
    PreservesDecidablePred
      (ProductiveStep
        (fullExtractionRuleData tau G).terminal
        (fullExtractionRuleData tau G).binary) :=
  productiveStep_preserves_decidable_of_universe
    D.rule_universes.states
    (fullExtractionRuleData tau G).terminal
    (fullExtractionRuleData tau G).binary
    D.rule_decisions.terminal_decidable
    (curriedBinaryDecidable_of_triple
      (fullExtractionRuleData tau G)
      D.rule_decisions.binary_decidable)


/-- The concrete computed productive predicate is decidable. -/
def concrete_computedProductive_decidable
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    (tau : Sigma → M)
    (G : UntypedStructure V Sigma)
    (E : CertifiedExtraction (fullExtractionRuleData tau G))
    (D : ConcreteStepPreservationData tau G E) :
    DecidablePred (computedProductive E) :=
  decidablePred_iter
    (ProductiveStep
      (fullExtractionRuleData tau G).terminal
      (fullExtractionRuleData tau G).binary)
    (concrete_productive_preserves_decidable tau G D)
    E.productiveCert.height


/-- ReachableStep preserves decidability for the concrete full rule data. -/
def concrete_reachable_preserves_decidable
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    (tau : Sigma → M)
    (G : UntypedStructure V Sigma)
    (E : CertifiedExtraction (fullExtractionRuleData tau G))
    (D : ConcreteStepPreservationData tau G E) :
    PreservesDecidablePred
      (ReachableStep
        (fullExtractionRuleData tau G).start
        (fullExtractionRuleData tau G).binary
        (computedProductive E)) :=
  reachableStep_preserves_decidable_of_universe
    D.rule_universes.states
    (fullExtractionRuleData tau G).start
    (fullExtractionRuleData tau G).binary
    (computedProductive E)
    D.rule_decisions.start_decidable
    (curriedBinaryDecidable_of_triple
      (fullExtractionRuleData tau G)
      D.rule_decisions.binary_decidable)
    (concrete_computedProductive_decidable tau G E D)


/-- Convert concrete finite rule data to the previous step-decidability payload. -/
def stepDecidabilityData_of_concrete
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    (tau : Sigma → M)
    (G : UntypedStructure V Sigma)
    (E : CertifiedExtraction (fullExtractionRuleData tau G))
    (D : ConcreteStepPreservationData tau G E) :
    ProductiveReachableStepDecidabilityData tau G E :=
  { state_universe := D.rule_universes.states,
    rule_lists := concreteRuleLists tau G D,
    productive_preserves :=
      concrete_productive_preserves_decidable tau G D,
    reachable_preserves :=
      concrete_reachable_preserves_decidable tau G E D }


/-- Concrete step-preservation data supplies FullKept decidability. -/
theorem concreteStepPreservationData_to_fullKept_decidable
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    [DecidableEq (TypedState V M)]
    (tau : Sigma → M)
    (G : UntypedStructure V Sigma)
    (E : CertifiedExtraction (fullExtractionRuleData tau G))
    (D : ConcreteStepPreservationData tau G E) :
    Nonempty (DecidablePred (FullKeptCorrectnessKernel.FullKept tau G)) :=
  stepDecidabilityData_to_fullKept_decidable tau G E
    (stepDecidabilityData_of_concrete tau G E D)

end ConcreteStepPreservationKernel
end JALC
end LeanCfgProject
