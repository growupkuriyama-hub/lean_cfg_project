import LeanCfgProject.JALC.ProductiveReachableIteratorCertificateKernel
import LeanCfgProject.JALC.PaperFacingIteratorTraceBoundary

namespace LeanCfgProject
namespace JALC
namespace PaperFacingProductiveReachableIteratorCertificate

/-
Paper-facing target for the productive/reachable iterator certificate boundary.

This target imports the five executable-interface experiments and exposes the
final pre-implementation payload that reaches FullKept decidability.
-/

open ProductiveReachableIteratorCertificateKernel
open FinalArtifactKernel


/-- The previous final artifact target remains available. -/
theorem checked_previous_final_artifact_from_pr_iterator :
    FinalArtifactChecked :=
  final_artifact_checked


/--
Paper-facing version of the final pre-implementation payload to FullKept
decidability transfer.
-/
theorem checked_productiveReachableIteratorCertificate_to_fullKept_decidable
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    [DecidableEq (InverseKernel.TypedState V M)]
    (tau : Sigma → M)
    (G : RoundTripKernel.UntypedStructure V Sigma)
    (B : ProductiveReachableIteratorCertificateData tau G) :
    Nonempty (DecidablePred (FullKeptCorrectnessKernel.FullKept tau G)) :=
  productiveReachableIteratorCertificate_to_fullKept_decidable tau G B


/--
Paper-facing version of the rule-list path for the same payload.
-/
theorem checked_productiveReachableIteratorCertificate_to_fullKept_decidable_via_rules
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    [DecidableEq (InverseKernel.TypedState V M)]
    (tau : Sigma → M)
    (G : RoundTripKernel.UntypedStructure V Sigma)
    (B : ProductiveReachableIteratorCertificateData tau G) :
    Nonempty (DecidablePred (FullKeptCorrectnessKernel.FullKept tau G)) :=
  productiveReachableIteratorCertificate_to_fullKept_decidable_via_rules tau G B

end PaperFacingProductiveReachableIteratorCertificate
end JALC
end LeanCfgProject
