import LeanCfgProject.JALC.StageDecidabilityKernel
import LeanCfgProject.JALC.ExecutableFullKeptExtraction

namespace LeanCfgProject
namespace JALC
namespace StagePayloadBridgeKernel

/-
Bridge from stage-decidable certified runs to the executable payload boundary.

The previous experiment reduced FullKept decidability to decidability of the two
computed stages.  This module connects that result to the existing executable
payload record used by the experiment-closure layer.
-/

universe u v w

open InverseKernel RoundTripKernel
open FullRefinementKernel
open AlgorithmicExtractionKernel
open FullAlgorithmicAgreementKernel
open StageDecidabilityKernel
open ExecutableFullKeptExtraction
open AlgorithmicFiniteMainKernel


/--
A stage-decidable certified run supplies the executable payload boundary:
computedKept is decidable because it is the intersection of the two decidable
computed stages.
-/
def executablePayload_of_stageDecidableRun
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    (tau : Sigma → M)
    (G : UntypedStructure V Sigma)
    (R : StageDecidableCertifiedRun tau G) :
    ExecutableFullKeptExtractionData tau G :=
  { extraction := R.extraction,
    computed_decidable :=
      computedKeptDecidable_of_stages R.extraction
        R.productive_decidable R.reachable_decidable }


/--
A stage-decidable certified run reaches the algorithmic finite-main boundary.
-/
theorem stageDecidableRun_to_algorithmic_finite_boundary
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    (tau : Sigma → M)
    (G : UntypedStructure V Sigma)
    (R : StageDecidableCertifiedRun tau G) :
    AlgorithmicFiniteMainBoundary tau G R.extraction :=
  executable_payload_to_algorithmic_finite_boundary tau G
    (executablePayload_of_stageDecidableRun tau G R)


/--
A stage-decidable certified run supplies FullKept decidability.
-/
theorem stageDecidableRun_to_fullKept_decidable
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    (tau : Sigma → M)
    (G : UntypedStructure V Sigma)
    (R : StageDecidableCertifiedRun tau G) :
    Nonempty (DecidablePred (FullKeptCorrectnessKernel.FullKept tau G)) :=
  (stageDecidableRun_to_algorithmic_finite_boundary tau G R).fullkept_decidable


/--
The executable payload recovered from a stage-decidable run has the same
certified extraction.
-/
theorem executablePayload_of_stageDecidableRun_extraction
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    (tau : Sigma → M)
    (G : UntypedStructure V Sigma)
    (R : StageDecidableCertifiedRun tau G) :
    (executablePayload_of_stageDecidableRun tau G R).extraction = R.extraction :=
  rfl

end StagePayloadBridgeKernel
end JALC
end LeanCfgProject
