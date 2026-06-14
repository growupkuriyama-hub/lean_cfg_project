import LeanCfgProject.JALC.IterDecidabilityKernel

namespace LeanCfgProject
namespace JALC
namespace ProductiveReachableStepDecidabilityKernel

/-
Stage-step decidability boundary.

This module specializes the generic iterate-decidability recursion to the two
steps used by the certified productive and reachable closures.
-/

universe u v w

open InverseKernel RoundTripKernel
open FiniteClosureKernel
open ProductiveReachableClosureKernel
open AlgorithmicExtractionKernel
open FullAlgorithmicAgreementKernel
open FiniteUniverseListEnumerationKernel
open MonotoneListIteratorKernel
open RulePredicateListCertificateKernel
open ProductiveReachableIteratorCertificateKernel
open IteratorFromDecidableIteratesKernel
open IterDecidabilityKernel


/--
Decidability-preservation data for the productive and reachable steps of a
certified extraction.
-/
structure ProductiveReachableStepDecidabilityData
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    (tau : Sigma → M)
    (G : UntypedStructure V Sigma)
    (E : CertifiedExtraction (fullExtractionRuleData tau G)) : Type (max u v w) where
  state_universe :
    TypedStateUniverseList V M
  rule_lists :
    FullRuleListCertificates tau G
  productive_preserves :
    PreservesDecidablePred
      (ProductiveStep
        (fullExtractionRuleData tau G).terminal
        (fullExtractionRuleData tau G).binary)
  reachable_preserves :
    PreservesDecidablePred
      (ReachableStep
        (fullExtractionRuleData tau G).start
        (fullExtractionRuleData tau G).binary
        (computedProductive E))


/--
The productive iterate at the certified height is decidable from
decidability-preservation of the productive step.
-/
def productive_iterate_decidable_of_stepData
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    (tau : Sigma → M)
    (G : UntypedStructure V Sigma)
    (E : CertifiedExtraction (fullExtractionRuleData tau G))
    (D : ProductiveReachableStepDecidabilityData tau G E) :
    DecidablePred
      (Iter
        (ProductiveStep
          (fullExtractionRuleData tau G).terminal
          (fullExtractionRuleData tau G).binary)
        E.productiveCert.height) :=
  decidablePred_iter
    (ProductiveStep
      (fullExtractionRuleData tau G).terminal
      (fullExtractionRuleData tau G).binary)
    D.productive_preserves
    E.productiveCert.height


/--
The reachable iterate at the certified height is decidable from
decidability-preservation of the reachable step.
-/
def reachable_iterate_decidable_of_stepData
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    (tau : Sigma → M)
    (G : UntypedStructure V Sigma)
    (E : CertifiedExtraction (fullExtractionRuleData tau G))
    (D : ProductiveReachableStepDecidabilityData tau G E) :
    DecidablePred
      (Iter
        (ReachableStep
          (fullExtractionRuleData tau G).start
          (fullExtractionRuleData tau G).binary
          (computedProductive E))
        E.reachableCert.height) :=
  decidablePred_iter
    (ReachableStep
      (fullExtractionRuleData tau G).start
      (fullExtractionRuleData tau G).binary
      (computedProductive E))
    D.reachable_preserves
    E.reachableCert.height


/--
Convert step-decidability data into the previous iterate-decision data.
-/
def iterateDecisionData_of_stepDecidabilityData
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    (tau : Sigma → M)
    (G : UntypedStructure V Sigma)
    (E : CertifiedExtraction (fullExtractionRuleData tau G))
    (D : ProductiveReachableStepDecidabilityData tau G E) :
    ProductiveReachableIterateDecisionData tau G :=
  { extraction := E,
    state_universe := D.state_universe,
    rule_lists := D.rule_lists,
    productive_iterate_decidable :=
      productive_iterate_decidable_of_stepData tau G E D,
    reachable_iterate_decidable :=
      reachable_iterate_decidable_of_stepData tau G E D }


/--
Step-decidability data supplies FullKept decidability through the previous
iterate-decision boundary.
-/
theorem stepDecidabilityData_to_fullKept_decidable
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    [DecidableEq (TypedState V M)]
    (tau : Sigma → M)
    (G : UntypedStructure V Sigma)
    (E : CertifiedExtraction (fullExtractionRuleData tau G))
    (D : ProductiveReachableStepDecidabilityData tau G E) :
    Nonempty (DecidablePred (FullKeptCorrectnessKernel.FullKept tau G)) :=
  iterateDecisionData_to_fullKept_decidable tau G
    (iterateDecisionData_of_stepDecidabilityData tau G E D)


/--
Step-decidability data exposes the two iterator outputs at the certified
closure heights.
-/
theorem stepDecidabilityData_outputs_available
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    (tau : Sigma → M)
    (G : UntypedStructure V Sigma)
    (E : CertifiedExtraction (fullExtractionRuleData tau G))
    (D : ProductiveReachableStepDecidabilityData tau G E) :
    Nonempty (ProductiveIteratorOutput E) ∧
      Nonempty (ReachableIteratorOutput E) :=
  iterateDecisionData_outputs_available tau G
    (iterateDecisionData_of_stepDecidabilityData tau G E D)

end ProductiveReachableStepDecidabilityKernel
end JALC
end LeanCfgProject
