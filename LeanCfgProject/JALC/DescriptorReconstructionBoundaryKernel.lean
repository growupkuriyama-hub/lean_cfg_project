import LeanCfgProject.JALC.FiniteStabilizationBoundaryKernel

namespace LeanCfgProject
namespace JALC
namespace DescriptorReconstructionBoundaryKernel

/-
Descriptor reconstruction boundary.

This module records the finite-output shape for a later descriptor
reconstruction theorem.  The actual reconstruction proof can use this boundary
as its output interface.
-/

universe u v w

open InverseKernel RoundTripKernel
open FullAlgorithmicAgreementKernel
open AlgorithmicExtractionKernel
open ConcreteStepPreservationKernel
open ActualListIteratorKernel


/-- Minimal finite descriptor-output interface for a computed kept universe. -/
structure FiniteDescriptorOutput
    (State : Type u)
    (Rule : Type v)
    (Start : Type w) : Type (max u v w) where
  states : List State
  rules : List Rule
  starts : List Start


/--
Boundary package connecting concrete iterator data with a finite descriptor
output supplied by a later reconstruction phase.
-/
structure DescriptorReconstructionBoundaryData
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    (tau : Sigma → M)
    (G : UntypedStructure V Sigma)
    (E : CertifiedExtraction (fullExtractionRuleData tau G)) :
    Type (max u v w) where
  concrete_data :
    ConcreteStepPreservationData tau G E
  descriptor :
    FiniteDescriptorOutput
      (TypedState V M)
      (TypedState V M × TypedState V M × TypedState V M)
      (TypedState V M)


/-- The descriptor boundary still carries the checked iterator certificate. -/
theorem descriptorBoundary_to_fullKept_decidable
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    [DecidableEq (TypedState V M)]
    (tau : Sigma → M)
    (G : UntypedStructure V Sigma)
    (E : CertifiedExtraction (fullExtractionRuleData tau G))
    (B : DescriptorReconstructionBoundaryData tau G E) :
    Nonempty (DecidablePred (FullKeptCorrectnessKernel.FullKept tau G)) :=
  concreteData_iteratorCertificate_to_fullKept_decidable
    tau G E B.concrete_data

end DescriptorReconstructionBoundaryKernel
end JALC
end LeanCfgProject
