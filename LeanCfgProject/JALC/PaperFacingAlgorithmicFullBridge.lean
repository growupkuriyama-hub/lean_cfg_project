import LeanCfgProject.JALC.AlgorithmicFullBridgeKernel

namespace LeanCfgProject
namespace JALC
namespace PaperFacingAlgorithmicFullBridge

/-
Paper-facing names for the bridge from certified algorithmic extraction to the
full-kept representation package.
-/

universe u v w

open InverseKernel RoundTripKernel
open FullRefinementKernel
open FullYieldKernel
open FullKeptCorrectnessKernel
open AlgorithmicExtractionKernel AlgorithmicFullBridgeKernel
open KeptStartLanguageKernel


/-- Paper-facing check: computed kept-correctness under agreement with FullKept. -/
theorem checked_computed_kept_correctness_kernel
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    {D : ExtractionRuleData (TypedState V M)}
    (E : CertifiedExtraction D)
    (T : StateTyping V M)
    (tau : Sigma → M)
    (G : UntypedStructure V Sigma)
    (comp : TypingCompatible tau T G)
    (sound : UntypedYieldSound tau T G)
    (red : UntypedReduced G)
    (agree : ComputedAgreesWithFullKept E tau G) :
    (∀ X : V, AlgorithmicExtractionKernel.computedKept E (intendedCopy T X)) ∧
      (∀ s : TypedState V M,
        AlgorithmicExtractionKernel.computedKept E s → IsIntended T s) :=
  computed_kept_correctness_kernel E T tau G comp sound red agree


/-- Paper-facing check: computed kept-state language equivalence. -/
theorem checked_computed_trimmed_language_kernel
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    {D : ExtractionRuleData (TypedState V M)}
    (E : CertifiedExtraction D)
    (T : StateTyping V M)
    (tau : Sigma → M)
    (G : UntypedStructure V Sigma)
    (comp : TypingCompatible tau T G)
    (red : UntypedReduced G)
    (agree : ComputedAgreesWithFullKept E tau G) :
    ∀ word : List Sigma,
      KeptStartLanguage
          (computedKeptStructure E T tau G comp red agree) word ↔
        StartLanguageKernel.UntypedStartLanguage G word :=
  computed_trimmed_language_kernel E T tau G comp red agree


/-- Paper-facing check: representation kernel for the computed kept predicate. -/
theorem checked_representation_from_computed_agreement
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    {D : ExtractionRuleData (TypedState V M)}
    (E : CertifiedExtraction D)
    (T : StateTyping V M)
    (tau : Sigma → M)
    (G : UntypedStructure V Sigma)
    (comp : TypingCompatible tau T G)
    (sound : UntypedYieldSound tau T G)
    (red : UntypedReduced G)
    (agree : ComputedAgreesWithFullKept E tau G) :
    RepresentationKernel.RepresentationKernel T G
      (AlgorithmicExtractionKernel.computedKept E) :=
  representation_from_computed_agreement E T tau G comp sound red agree


/-- Paper-facing check: bundled algorithmic/full bridge. -/
theorem checked_algorithmic_full_bridge_kernel
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    {D : ExtractionRuleData (TypedState V M)}
    (E : CertifiedExtraction D)
    (T : StateTyping V M)
    (tau : Sigma → M)
    (G : UntypedStructure V Sigma)
    (comp : TypingCompatible tau T G)
    (sound : UntypedYieldSound tau T G)
    (red : UntypedReduced G)
    (agree : ComputedAgreesWithFullKept E tau G) :
    AlgorithmicFullBridge E T tau G comp sound red agree :=
  algorithmic_full_bridge_kernel E T tau G comp sound red agree

end PaperFacingAlgorithmicFullBridge
end JALC
end LeanCfgProject
