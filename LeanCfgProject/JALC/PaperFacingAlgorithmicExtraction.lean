import LeanCfgProject.JALC.AlgorithmicExtractionKernel

namespace LeanCfgProject
namespace JALC
namespace PaperFacingAlgorithmicExtraction

/-
Paper-facing names for the certified algorithmic extraction kernel.
-/

universe u

open FiniteClosureKernel
open ProductiveReachableClosureKernel
open AlgorithmicExtractionKernel


/-- Paper-facing check: certified extraction has fixed productivity. -/
theorem checked_algorithmic_productive_fixed
    {α : Type u}
    {D : ExtractionRuleData α}
    (E : CertifiedExtraction D) :
    PredFixed (ProductiveStep D.terminal D.binary)
      (computedProductive E) :=
  computedProductive_fixed E


/-- Paper-facing check: certified extraction has fixed productive-part reachability. -/
theorem checked_algorithmic_reachable_fixed
    {α : Type u}
    {D : ExtractionRuleData α}
    (E : CertifiedExtraction D) :
    PredFixed
      (ReachableStep D.start D.binary (computedProductive E))
      (computedReachable E) :=
  computedReachable_fixed E


/-- Paper-facing check: keptness is the intersection of the two certified stages. -/
theorem checked_algorithmic_kept_iff
    {α : Type u}
    {D : ExtractionRuleData α}
    (E : CertifiedExtraction D)
    (x : α) :
    computedKept E x ↔
      computedProductive E x ∧ computedReachable E x :=
  computedKept_iff E x


/-- Paper-facing check: bundled Algorithm 1 kernel. -/
theorem checked_algorithmic_extraction_kernel
    {α : Type u}
    {D : ExtractionRuleData α}
    (E : CertifiedExtraction D) :
    PredFixed (ProductiveStep D.terminal D.binary)
        (computedProductive E) ∧
      PredFixed
        (ReachableStep D.start D.binary (computedProductive E))
        (computedReachable E) ∧
      (∀ x : α,
        computedKept E x ↔
          computedProductive E x ∧ computedReachable E x) :=
  algorithmic_extraction_kernel E


/-- Paper-facing check: bundled certified extraction record. -/
theorem checked_certifiedExtractionKernel_holds
    {α : Type u}
    {D : ExtractionRuleData α}
    (E : CertifiedExtraction D) :
    CertifiedExtractionKernel E :=
  certifiedExtractionKernel_holds E

end PaperFacingAlgorithmicExtraction
end JALC
end LeanCfgProject
