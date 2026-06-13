import LeanCfgProject.JALC.PaperFacingAlgorithmicExtraction
import LeanCfgProject.JALC.FullKeptCorrectnessKernel
import LeanCfgProject.JALC.KeptRepresentationKernel

namespace LeanCfgProject
namespace JALC
namespace AlgorithmicFullBridgeKernel

/-
Bridge from certified algorithmic extraction to the full-kept theorem package.

The bridge isolates the remaining connection point.  If the predicate computed
by a certified run of Algorithm 1 agrees with the abstract FullKept predicate,
then all existing full-kept correctness, representation, and language kernels
can be transported to the computed predicate.
-/

universe u v w

open InverseKernel RoundTripKernel
open ReachableProductiveKernel
open FullRefinementKernel
open FullYieldKernel
open FullFrameReachabilityKernel FullKeptCorrectnessKernel
open AlgorithmicExtractionKernel
open KeptStructureKernel KeptStartLanguageKernel KeptRepresentationKernel


/--
Agreement between a certified algorithmic extraction run and the abstract
full-kept predicate.
-/
def ComputedAgreesWithFullKept
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    {D : ExtractionRuleData (TypedState V M)}
    (E : CertifiedExtraction D)
    (tau : Sigma → M)
    (G : UntypedStructure V Sigma) : Prop :=
  ∀ s : TypedState V M,
    AlgorithmicExtractionKernel.computedKept E s ↔ FullKept tau G s


/-- Intended copies are kept by the computed predicate under agreement. -/
theorem computed_intended_of_full_agreement
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
    ∀ X : V, AlgorithmicExtractionKernel.computedKept E (intendedCopy T X) := by
  intro X
  exact (agree (intendedCopy T X)).2
    (intendedCopy_fullKept_of_reduced T tau G comp red X)


/-- Computed kept states are intended under agreement. -/
theorem computed_isIntended_of_full_agreement
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    {D : ExtractionRuleData (TypedState V M)}
    (E : CertifiedExtraction D)
    (T : StateTyping V M)
    (tau : Sigma → M)
    (G : UntypedStructure V Sigma)
    (comp : TypingCompatible tau T G)
    (sound : UntypedYieldSound tau T G)
    (agree : ComputedAgreesWithFullKept E tau G)
    {s : TypedState V M}
    (h : AlgorithmicExtractionKernel.computedKept E s) :
    IsIntended T s :=
  fullKept_isIntended T tau G comp sound ((agree s).1 h)


/-- Computed kept-correctness transferred from full-kept correctness. -/
theorem computed_kept_correctness_kernel
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
        AlgorithmicExtractionKernel.computedKept E s → IsIntended T s) := by
  constructor
  · exact computed_intended_of_full_agreement E T tau G comp red agree
  · intro s h
    exact computed_isIntended_of_full_agreement E T tau G comp sound agree h


/-- Representation kernel for the computed predicate under agreement. -/
theorem representation_from_computed_agreement
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
      (AlgorithmicExtractionKernel.computedKept E) := by
  exact
    RepresentationKernel.representationKernel_from_kept_intended
      T G (AlgorithmicExtractionKernel.computedKept E)
      (computed_intended_of_full_agreement E T tau G comp red agree)
      (fun s h =>
        computed_isIntended_of_full_agreement E T tau G comp sound agree h)


/-- Intended-copy proof for the computed kept predicate. -/
def computedKeptIntendedProof
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
    ∀ X : V, AlgorithmicExtractionKernel.computedKept E (intendedCopy T X) :=
  computed_intended_of_full_agreement E T tau G comp red agree


/-- Kept-state structure induced by the computed kept predicate. -/
def computedKeptStructure
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
    KeptStructure (AlgorithmicExtractionKernel.computedKept E) Sigma :=
  liftToKeptStructure T G (AlgorithmicExtractionKernel.computedKept E)
    (computedKeptIntendedProof E T tau G comp red agree)


/--
The computed kept-state structure has exactly the original start language,
under agreement with the abstract full-kept predicate.
-/
theorem computed_trimmed_language_kernel
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
        StartLanguageKernel.UntypedStartLanguage G word := by
  intro word
  exact
    keptRepresentationKernel_language T G
      (AlgorithmicExtractionKernel.computedKept E)
      (computedKeptIntendedProof E T tau G comp red agree) word


/-- Bundled bridge theorem for Algorithm 1 and the full-kept package. -/
structure AlgorithmicFullBridge
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
    (agree : ComputedAgreesWithFullKept E tau G) : Prop where
  certified :
    CertifiedExtractionKernel E
  computed_correctness :
    (∀ X : V, AlgorithmicExtractionKernel.computedKept E (intendedCopy T X)) ∧
      (∀ s : TypedState V M,
        AlgorithmicExtractionKernel.computedKept E s → IsIntended T s)
  language :
    ∀ word : List Sigma,
      KeptStartLanguage
          (computedKeptStructure E T tau G comp red agree) word ↔
        StartLanguageKernel.UntypedStartLanguage G word
  representation :
    RepresentationKernel.RepresentationKernel T G
      (AlgorithmicExtractionKernel.computedKept E)


/-- The bundled bridge follows from agreement with FullKept. -/
theorem algorithmic_full_bridge_kernel
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
    AlgorithmicFullBridge E T tau G comp sound red agree := by
  exact
    { certified := certifiedExtractionKernel_holds E,
      computed_correctness :=
        computed_kept_correctness_kernel E T tau G comp sound red agree,
      language := computed_trimmed_language_kernel E T tau G comp red agree,
      representation :=
        representation_from_computed_agreement E T tau G comp sound red agree }

end AlgorithmicFullBridgeKernel
end JALC
end LeanCfgProject
