import LeanCfgProject.JALC.IteratorFromDecidableIteratesKernel
import LeanCfgProject.JALC.PaperFacingProductiveReachableIteratorCertificate

namespace LeanCfgProject
namespace JALC
namespace PaperFacingIteratorFromDecidableIterates

/-
Paper-facing target for building iterator outputs from decidable iterates.

This target records that complete finite state-universe lists and decisions for
the certified productive/reachable iterates are enough to produce the iterator
outputs used by the previous boundary.
-/

open IteratorFromDecidableIteratesKernel
open FinalArtifactKernel


/-- The previous final artifact target remains available. -/
theorem checked_previous_final_artifact_from_decidable_iterates :
    FinalArtifactChecked :=
  final_artifact_checked


/--
Paper-facing version of the iterate-decision data to FullKept decidability
transfer.
-/
theorem checked_iterateDecisionData_to_fullKept_decidable
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    [DecidableEq (InverseKernel.TypedState V M)]
    (tau : Sigma → M)
    (G : RoundTripKernel.UntypedStructure V Sigma)
    (D : ProductiveReachableIterateDecisionData tau G) :
    Nonempty (DecidablePred (FullKeptCorrectnessKernel.FullKept tau G)) :=
  iterateDecisionData_to_fullKept_decidable tau G D


/-- Paper-facing statement that the iterator outputs can be obtained. -/
theorem checked_iterateDecisionData_outputs_available
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    (tau : Sigma → M)
    (G : RoundTripKernel.UntypedStructure V Sigma)
    (D : ProductiveReachableIterateDecisionData tau G) :
    Nonempty (MonotoneListIteratorKernel.ProductiveIteratorOutput D.extraction) ∧
      Nonempty (MonotoneListIteratorKernel.ReachableIteratorOutput D.extraction) :=
  iterateDecisionData_outputs_available tau G D

end PaperFacingIteratorFromDecidableIterates
end JALC
end LeanCfgProject
