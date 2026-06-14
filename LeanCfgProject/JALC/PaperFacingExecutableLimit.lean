import LeanCfgProject.JALC.DescriptorReconstructionBoundaryKernel
import LeanCfgProject.JALC.PaperFacingFullIteratorCertificate

namespace LeanCfgProject
namespace JALC
namespace PaperFacingExecutableLimit

/-
Paper-facing target for the current executable-interface limit.

This target imports the concrete step-preservation package, the actual
list-iterator certificate interface, the finite-stabilization boundary, and the
descriptor-reconstruction boundary.
-/

universe u v w

open DescriptorReconstructionBoundaryKernel
open ConcreteStepPreservationKernel
open FinalArtifactKernel


/-- The previous final artifact target remains available. -/
theorem checked_previous_final_artifact_from_executable_limit :
    FinalArtifactChecked :=
  final_artifact_checked


/-- Paper-facing full-kept decidability from concrete iterator data. -/
theorem checked_executable_limit_fullKept_decidable
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    [DecidableEq (InverseKernel.TypedState V M)]
    (tau : Sigma → M)
    (G : RoundTripKernel.UntypedStructure V Sigma)
    (E : AlgorithmicExtractionKernel.CertifiedExtraction
      (FullAlgorithmicAgreementKernel.fullExtractionRuleData tau G))
    (B : DescriptorReconstructionBoundaryData tau G E) :
    Nonempty (DecidablePred (FullKeptCorrectnessKernel.FullKept tau G)) :=
  descriptorBoundary_to_fullKept_decidable tau G E B

end PaperFacingExecutableLimit
end JALC
end LeanCfgProject
