import LeanCfgProject.JALC.ConcreteListStabilityKernel

namespace LeanCfgProject
namespace JALC
namespace PaperFacingListStabilityExtraction

/-
Paper-facing target for list-stability extraction.

This target verifies the next executable-interface step: a finite support
stability check at the productive and reachable heights yields a certified
extraction object and then FullKept decidability through the already checked
full iterator chain.
-/

universe u v w

open ConcreteListStabilityKernel
open FinalArtifactKernel


/-- The previous final artifact target remains available. -/
theorem checked_previous_final_artifact_from_list_stability :
    FinalArtifactChecked :=
  final_artifact_checked


/-- Paper-facing certified extraction from concrete list-stability data. -/
def checked_certifiedExtraction_of_concreteListStability
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    (tau : Sigma → M)
    (G : RoundTripKernel.UntypedStructure V Sigma)
    (H : ConcreteListStabilityData tau G) :
    AlgorithmicExtractionKernel.CertifiedExtraction
      (FullAlgorithmicAgreementKernel.fullExtractionRuleData tau G) :=
  certifiedExtraction_of_concreteListStability tau G H


/-- Paper-facing FullKept decidability from concrete list-stability data. -/
theorem checked_concreteListStability_to_fullKept_decidable
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    [DecidableEq (InverseKernel.TypedState V M)]
    (tau : Sigma → M)
    (G : RoundTripKernel.UntypedStructure V Sigma)
    (H : ConcreteListStabilityData tau G) :
    Nonempty (DecidablePred (FullKeptCorrectnessKernel.FullKept tau G)) :=
  concreteListStability_to_fullKept_decidable tau G H


/-- Paper-facing certified extraction kernel from list stability. -/
theorem checked_concreteListStability_certifiedExtractionKernel
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    (tau : Sigma → M)
    (G : RoundTripKernel.UntypedStructure V Sigma)
    (H : ConcreteListStabilityData tau G) :
    AlgorithmicExtractionKernel.CertifiedExtractionKernel
      (certifiedExtraction_of_concreteListStability tau G H) :=
  concreteListStability_certifiedExtractionKernel tau G H

end PaperFacingListStabilityExtraction
end JALC
end LeanCfgProject
