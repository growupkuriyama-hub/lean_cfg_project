import LeanCfgProject.JALC.PaperFacingFullIteratorCertificate

namespace LeanCfgProject
namespace JALC
namespace ActualListIteratorKernel

/-
Actual list-iterator interface.

This module packages the currently checked executable-interface chain as a
single constructor of productive/reachable iterator certificates from concrete
finite rule data.
-/

universe u v w

open InverseKernel RoundTripKernel
open FullAlgorithmicAgreementKernel
open AlgorithmicExtractionKernel
open ProductiveReachableIteratorCertificateKernel
open ProductiveReachableStepDecidabilityKernel
open IteratorFromDecidableIteratesKernel
open ConcreteStepPreservationKernel


/-- Build the productive/reachable iterator certificate from concrete data. -/
def productiveReachableIteratorCertificate_of_concreteStepData
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    (tau : Sigma → M)
    (G : UntypedStructure V Sigma)
    (E : CertifiedExtraction (fullExtractionRuleData tau G))
    (D : ConcreteStepPreservationData tau G E) :
    ProductiveReachableIteratorCertificateData tau G :=
  IteratorFromDecidableIteratesKernel.productiveReachableIteratorCertificate_of_iterateDecisionData
    tau G
    (ProductiveReachableStepDecidabilityKernel.iterateDecisionData_of_stepDecidabilityData
      tau G E (stepDecidabilityData_of_concrete tau G E D))


/-- The concrete-data iterator certificate supplies FullKept decidability. -/
theorem concreteData_iteratorCertificate_to_fullKept_decidable
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    [DecidableEq (InverseKernel.TypedState V M)]
    (tau : Sigma → M)
    (G : UntypedStructure V Sigma)
    (E : CertifiedExtraction (fullExtractionRuleData tau G))
    (D : ConcreteStepPreservationData tau G E) :
    Nonempty (DecidablePred (FullKeptCorrectnessKernel.FullKept tau G)) :=
  ProductiveReachableIteratorCertificateKernel.productiveReachableIteratorCertificate_to_fullKept_decidable
    tau G
    (productiveReachableIteratorCertificate_of_concreteStepData tau G E D)

end ActualListIteratorKernel
end JALC
end LeanCfgProject
