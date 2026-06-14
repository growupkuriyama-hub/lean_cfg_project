import LeanCfgProject.JALC.ConcreteStepPreservationKernel
import LeanCfgProject.JALC.PaperFacingStepDecidability

namespace LeanCfgProject
namespace JALC
namespace PaperFacingFullIteratorCertificate

/-
Paper-facing target for the full iterator-certificate boundary.

This target closes the previous abstract step-preservation assumptions using
finite rule-universe lists and concrete rule-predicate decisions.
-/

universe u v w

open ConcreteStepPreservationKernel
open FinalArtifactKernel


/-- The previous final artifact target remains available. -/
theorem checked_previous_final_artifact_from_full_iterator_certificate :
    FinalArtifactChecked :=
  final_artifact_checked


/--
Paper-facing concrete productive-step decidability preservation.

This is a definition, not a theorem, because `PreservesDecidablePred` is
type-valued: it packages a decision procedure rather than stating a proposition.
-/
@[reducible]
def checked_concrete_productive_preserves_decidable
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    (tau : Sigma → M)
    (G : RoundTripKernel.UntypedStructure V Sigma)
    (E : AlgorithmicExtractionKernel.CertifiedExtraction
      (FullAlgorithmicAgreementKernel.fullExtractionRuleData tau G))
    (D : ConcreteStepPreservationData tau G E) :
    IterDecidabilityKernel.PreservesDecidablePred
      (ProductiveReachableClosureKernel.ProductiveStep
        (FullAlgorithmicAgreementKernel.fullExtractionRuleData tau G).terminal
        (FullAlgorithmicAgreementKernel.fullExtractionRuleData tau G).binary) :=
  concrete_productive_preserves_decidable tau G D


/-- Paper-facing concrete step data to FullKept decidability. -/
theorem checked_concreteStepPreservationData_to_fullKept_decidable
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    [DecidableEq (InverseKernel.TypedState V M)]
    (tau : Sigma → M)
    (G : RoundTripKernel.UntypedStructure V Sigma)
    (E : AlgorithmicExtractionKernel.CertifiedExtraction
      (FullAlgorithmicAgreementKernel.fullExtractionRuleData tau G))
    (D : ConcreteStepPreservationData tau G E) :
    Nonempty (DecidablePred (FullKeptCorrectnessKernel.FullKept tau G)) :=
  concreteStepPreservationData_to_fullKept_decidable tau G E D

end PaperFacingFullIteratorCertificate
end JALC
end LeanCfgProject
