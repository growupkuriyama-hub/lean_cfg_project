import LeanCfgProject.JALC.ConcreteBoundedWitnessBridgeKernel

namespace LeanCfgProject
namespace JALC
namespace PaperFacingConcreteBoundedWitnessBridge

/-
Paper-facing target for the concrete bounded-witness bridge.
-/

universe u v w

open ConcreteBoundedWitnessBridgeKernel
open FinalArtifactKernel


/-- The previous final artifact target remains available. -/
theorem checked_previous_final_artifact_from_concrete_bounded_bridge :
    FinalArtifactChecked :=
  final_artifact_checked


/-- Paper-facing conversion from bounded witnesses to concrete list-stability data. -/
def checked_concreteListStabilityData_of_boundedWitnessData
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    (tau : Sigma → M)
    (G : RoundTripKernel.UntypedStructure V Sigma)
    (B : ConcreteBoundedWitnessData tau G) :
    ConcreteListStabilityKernel.ConcreteListStabilityData tau G :=
  concreteListStabilityData_of_boundedWitnessData tau G B


/-- Paper-facing certified extraction from bounded witnesses. -/
def checked_certifiedExtraction_of_boundedWitnessData
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    (tau : Sigma → M)
    (G : RoundTripKernel.UntypedStructure V Sigma)
    (B : ConcreteBoundedWitnessData tau G) :
    AlgorithmicExtractionKernel.CertifiedExtraction
      (FullAlgorithmicAgreementKernel.fullExtractionRuleData tau G) :=
  certifiedExtraction_of_boundedWitnessData tau G B


/-- Paper-facing FullKept decidability from concrete bounded witnesses. -/
theorem checked_boundedWitnessData_to_fullKept_decidable
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    [DecidableEq (InverseKernel.TypedState V M)]
    (tau : Sigma → M)
    (G : RoundTripKernel.UntypedStructure V Sigma)
    (B : ConcreteBoundedWitnessData tau G) :
    Nonempty (DecidablePred (FullKeptCorrectnessKernel.FullKept tau G)) :=
  boundedWitnessData_to_fullKept_decidable tau G B

end PaperFacingConcreteBoundedWitnessBridge
end JALC
end LeanCfgProject
