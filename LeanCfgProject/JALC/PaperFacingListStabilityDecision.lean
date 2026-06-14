import LeanCfgProject.JALC.ListStabilityDecisionKernel

namespace LeanCfgProject
namespace JALC
namespace PaperFacingListStabilityDecision

/-
Paper-facing target for decidable list-stability checks.

This target verifies that the finite support-stability checks used by the
previous list-stability extraction target are themselves decidable from concrete
finite rule data and chosen heights.
-/

universe u v w

open ListStabilityDecisionKernel
open FinalArtifactKernel


/-- The previous final artifact target remains available. -/
theorem checked_previous_final_artifact_from_list_stability_decision :
    FinalArtifactChecked :=
  final_artifact_checked


/-- Paper-facing productive stability decidability. -/
def checked_productiveListStabilityDecidable
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    (tau : Sigma → M)
    (G : RoundTripKernel.UntypedStructure V Sigma)
    (D : ConcreteListStabilityDecisionData tau G) :
    Decidable
      (ListStabilityKernel.AgreeOnList D.rule_universes.states.support
        (ProductiveReachableClosureKernel.ProductiveStep
          (FullAlgorithmicAgreementKernel.fullExtractionRuleData tau G).terminal
          (FullAlgorithmicAgreementKernel.fullExtractionRuleData tau G).binary
          (FiniteClosureKernel.Iter
            (ProductiveReachableClosureKernel.ProductiveStep
              (FullAlgorithmicAgreementKernel.fullExtractionRuleData tau G).terminal
              (FullAlgorithmicAgreementKernel.fullExtractionRuleData tau G).binary)
            D.productive_height))
        (FiniteClosureKernel.Iter
          (ProductiveReachableClosureKernel.ProductiveStep
            (FullAlgorithmicAgreementKernel.fullExtractionRuleData tau G).terminal
            (FullAlgorithmicAgreementKernel.fullExtractionRuleData tau G).binary)
          D.productive_height)) :=
  productiveListStabilityDecidable tau G D


/-- Paper-facing reachable stability decidability. -/
def checked_reachableListStabilityDecidable
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    (tau : Sigma → M)
    (G : RoundTripKernel.UntypedStructure V Sigma)
    (D : ConcreteListStabilityDecisionData tau G) :
    Decidable
      (ListStabilityKernel.AgreeOnList D.rule_universes.states.support
        (ProductiveReachableClosureKernel.ReachableStep
          (FullAlgorithmicAgreementKernel.fullExtractionRuleData tau G).start
          (FullAlgorithmicAgreementKernel.fullExtractionRuleData tau G).binary
          (FiniteClosureKernel.Iter
            (ProductiveReachableClosureKernel.ProductiveStep
              (FullAlgorithmicAgreementKernel.fullExtractionRuleData tau G).terminal
              (FullAlgorithmicAgreementKernel.fullExtractionRuleData tau G).binary)
            D.productive_height)
          (FiniteClosureKernel.Iter
            (ProductiveReachableClosureKernel.ReachableStep
              (FullAlgorithmicAgreementKernel.fullExtractionRuleData tau G).start
              (FullAlgorithmicAgreementKernel.fullExtractionRuleData tau G).binary
              (FiniteClosureKernel.Iter
                (ProductiveReachableClosureKernel.ProductiveStep
                  (FullAlgorithmicAgreementKernel.fullExtractionRuleData tau G).terminal
                  (FullAlgorithmicAgreementKernel.fullExtractionRuleData tau G).binary)
                D.productive_height))
            D.reachable_height))
        (FiniteClosureKernel.Iter
          (ProductiveReachableClosureKernel.ReachableStep
            (FullAlgorithmicAgreementKernel.fullExtractionRuleData tau G).start
            (FullAlgorithmicAgreementKernel.fullExtractionRuleData tau G).binary
            (FiniteClosureKernel.Iter
              (ProductiveReachableClosureKernel.ProductiveStep
                (FullAlgorithmicAgreementKernel.fullExtractionRuleData tau G).terminal
                (FullAlgorithmicAgreementKernel.fullExtractionRuleData tau G).binary)
              D.productive_height))
          D.reachable_height)) :=
  reachableListStabilityDecidable tau G D


/-- Paper-facing checked stability data to FullKept decidability. -/
theorem checked_listStabilityDecision_to_fullKept_decidable
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    [DecidableEq (InverseKernel.TypedState V M)]
    (tau : Sigma → M)
    (G : RoundTripKernel.UntypedStructure V Sigma)
    (C : ConcreteListStabilityCheckedData tau G) :
    Nonempty (DecidablePred (FullKeptCorrectnessKernel.FullKept tau G)) :=
  checkedListStability_to_fullKept_decidable tau G C

end PaperFacingListStabilityDecision
end JALC
end LeanCfgProject
