import LeanCfgProject.JALC.FullAlgorithmicAgreementKernel

namespace LeanCfgProject
namespace JALC
namespace PaperFacingFullAlgorithmicAgreement

/-
Paper-facing names for the direct agreement between Algorithm 1 and FullKept.
-/

universe u v w

open InverseKernel RoundTripKernel
open ReachableProductiveKernel
open FullRefinementKernel
open FullYieldKernel
open FullFrameReachabilityKernel
open FullKeptCorrectnessKernel
open AlgorithmicExtractionKernel AlgorithmicFullBridgeKernel
open FullAlgorithmicAgreementKernel


/-- Paper-facing check: the concrete full rule data for Algorithm 1. -/
def checked_fullExtractionRuleData
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    (tau : Sigma → M)
    (G : UntypedStructure V Sigma) :
    ExtractionRuleData (TypedState V M) :=
  fullExtractionRuleData tau G


/-- Paper-facing check: computed productivity agrees with full typed productivity. -/
theorem checked_full_computedProductive_agrees
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    (tau : Sigma → M)
    (G : UntypedStructure V Sigma)
    (E : CertifiedExtraction (fullExtractionRuleData tau G)) :
    ∀ s : TypedState V M,
      computedProductive E s ↔
        TypedProductive (fullTypedStructure tau G) s :=
  full_computedProductive_agrees tau G E


/-- Paper-facing check: computed reachability implies full productive-part reachability. -/
theorem checked_full_computedReachable_to_productiveReachable
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    (tau : Sigma → M)
    (G : UntypedStructure V Sigma)
    (E : CertifiedExtraction (fullExtractionRuleData tau G)) :
    ∀ s : TypedState V M,
      computedReachable E s → ProductiveReachableFull tau G s :=
  full_computedReachable_to_productiveReachable tau G E


/-- Paper-facing check: Algorithm 1 over the full rule data computes FullKept. -/
theorem checked_fullAlgorithmicComputedKept_agrees
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    (tau : Sigma → M)
    (G : UntypedStructure V Sigma)
    (E : CertifiedExtraction (fullExtractionRuleData tau G)) :
    ComputedAgreesWithFullKept E tau G :=
  fullAlgorithmicComputedKept_agrees tau G E


/-- Paper-facing check: the conditional bridge is closed for the full rule data. -/
theorem checked_closed_algorithmic_full_bridge_kernel
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    (tau : Sigma → M)
    (G : UntypedStructure V Sigma)
    (E : CertifiedExtraction (fullExtractionRuleData tau G))
    (T : StateTyping V M)
    (comp : TypingCompatible tau T G)
    (sound : UntypedYieldSound tau T G)
    (red : UntypedReduced G) :
    AlgorithmicFullBridge E T tau G comp sound red
      (fullAlgorithmicComputedKept_agrees tau G E) :=
  closed_algorithmic_full_bridge_kernel tau G E T comp sound red

end PaperFacingFullAlgorithmicAgreement
end JALC
end LeanCfgProject
