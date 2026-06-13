import LeanCfgProject.JALC.ExecutableFullKeptExtraction

namespace LeanCfgProject
namespace JALC
namespace DescriptorReconstructionKernel

/-
Descriptor reconstruction wrapper.

This module packages the full-kept structure as the descriptor-level output
available from the current theorem kernels.  It is intentionally conservative:
it does not introduce a new descriptor syntax beyond the kept-state structure
already checked in the representation kernels.
-/

universe u v w

open InverseKernel RoundTripKernel
open FullRefinementKernel
open FullYieldKernel
open FullKeptCorrectnessKernel
open FullTrimmedLanguageKernel FullMainTheoremKernel
open KeptStructureKernel KeptStartLanguageKernel
open FiniteRepresentationBundle
open AlgorithmicExtractionKernel
open FullAlgorithmicAgreementKernel
open FullKeptDecidabilityKernel


/-- Descriptor-level package induced by the full-kept construction. -/
structure DescriptorReconstructionPackage
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M] [Fintype V] [Fintype M] [Fintype Sigma]
    (T : StateTyping V M)
    (tau : Sigma → M)
    (G : UntypedStructure V Sigma)
    (comp : TypingCompatible tau T G)
    (sound : UntypedYieldSound tau T G)
    (red : UntypedReduced G)
    (E : CertifiedExtraction (fullExtractionRuleData tau G)) : Prop where
  kept_structure :
    KeptStructure (FullKept tau G) Sigma
  kept_finite :
    KeptFiniteBundle Sigma (FullKept tau G)
  language :
    ∀ word : List Sigma,
      KeptStartLanguage kept_structure word ↔
        StartLanguageKernel.UntypedStartLanguage G word
  representation :
    RepresentationKernel.RepresentationKernel T G (FullKept tau G)


/-- Construct the descriptor-level package from a decidable certified run. -/
theorem descriptor_reconstruction_package
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M] [Fintype V] [Fintype M] [Fintype Sigma]
    (T : StateTyping V M)
    (tau : Sigma → M)
    (G : UntypedStructure V Sigma)
    (comp : TypingCompatible tau T G)
    (sound : UntypedYieldSound tau T G)
    (red : UntypedReduced G)
    (E : CertifiedExtraction (fullExtractionRuleData tau G))
    [DecidablePred (computedKept E)] :
    DescriptorReconstructionPackage T tau G comp sound red E := by
  letI : DecidablePred (FullKept tau G) :=
    fullKeptDecidable_of_fullExtraction tau G E
  exact
    { kept_structure := fullKeptStructure T tau G comp red,
      kept_finite := keptFiniteBundle_of_finite Sigma (FullKept tau G),
      language := full_finite_main_language T tau G comp sound red,
      representation := full_refinement_main_representation T tau G comp sound red }

end DescriptorReconstructionKernel
end JALC
end LeanCfgProject
