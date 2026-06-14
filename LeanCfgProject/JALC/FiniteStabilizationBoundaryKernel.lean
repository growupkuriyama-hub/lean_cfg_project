import LeanCfgProject.JALC.ActualListIteratorKernel

namespace LeanCfgProject
namespace JALC
namespace FiniteStabilizationBoundaryKernel

/-
Finite stabilization boundary.

This module records the remaining stabilization interface: finite heights with
stability proofs produce the certified extraction object used by the checked
Algorithm 1 chain.
-/

universe u

open FiniteClosureKernel
open ProductiveReachableClosureKernel
open AlgorithmicExtractionKernel


/-- Stable heights for the two stages of a certified extraction. -/
structure StableHeightData
    {α : Type u}
    (D : ExtractionRuleData α) : Type u where
  productive_height : Nat
  productive_stable :
    StableAt (ProductiveStep D.terminal D.binary) productive_height
  reachable_height : Nat
  reachable_stable :
    StableAt
      (ReachableStep D.start D.binary
        (Iter (ProductiveStep D.terminal D.binary) productive_height))
      reachable_height


/-- Convert stable-height data into a certified extraction. -/
def certifiedExtraction_of_stableHeights
    {α : Type u}
    {D : ExtractionRuleData α}
    (H : StableHeightData D) :
    CertifiedExtraction D :=
  { productiveCert :=
      { height := H.productive_height,
        stable := H.productive_stable },
    reachableCert :=
      { height := H.reachable_height,
        stable := by
          simpa [ProductiveClosure, certifiedClosure]
            using H.reachable_stable } }


/-- Stable-height data exposes the certified extraction kernel. -/
theorem stableHeights_certifiedExtractionKernel
    {α : Type u}
    {D : ExtractionRuleData α}
    (H : StableHeightData D) :
    CertifiedExtractionKernel
      (certifiedExtraction_of_stableHeights H) :=
  certifiedExtractionKernel_holds
    (certifiedExtraction_of_stableHeights H)

end FiniteStabilizationBoundaryKernel
end JALC
end LeanCfgProject
