import LeanCfgProject.JALC.FullTrimmedLanguageKernel

namespace LeanCfgProject
namespace JALC
namespace FullMainTheoremKernel

/-
Main full-refinement package.

This module collects the full-kept correctness statement, the induced
kept-state language equivalence, and the representation package into a single
paper-facing kernel.
-/

universe u v w

open InverseKernel RoundTripKernel
open ReachableProductiveKernel
open FullRefinementKernel
open FullYieldKernel
open FullFrameReachabilityKernel FullKeptCorrectnessKernel
open FullTrimmedLanguageKernel
open KeptStartLanguageKernel


/-- Packaged main full-refinement kernel. -/
structure FullRefinementMainKernel
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    (T : StateTyping V M)
    (tau : Sigma → M)
    (G : UntypedStructure V Sigma)
    (comp : TypingCompatible tau T G)
    (sound : UntypedYieldSound tau T G)
    (red : UntypedReduced G) : Prop where
  kept_correctness :
    (∀ X : V, FullKept tau G (intendedCopy T X)) ∧
      (∀ s : TypedState V M, FullKept tau G s → IsIntended T s)
  trimmed_language :
    ∀ word : List Sigma,
      KeptStartLanguage (fullKeptStructure T tau G comp red) word ↔
        StartLanguageKernel.UntypedStartLanguage G word
  representation :
    RepresentationKernel.RepresentationKernel T G (FullKept tau G)


/-- The full-refinement main package follows from the checked kernels. -/
theorem full_refinement_main_kernel
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    (T : StateTyping V M)
    (tau : Sigma → M)
    (G : UntypedStructure V Sigma)
    (comp : TypingCompatible tau T G)
    (sound : UntypedYieldSound tau T G)
    (red : UntypedReduced G) :
    FullRefinementMainKernel T tau G comp sound red := by
  refine ⟨?_, ?_, ?_⟩
  · exact fullKept_correctness_kernel T tau G comp sound red
  · exact fullKept_trimmed_language_kernel T tau G comp red
  · exact representation_from_fullKept_correctness T tau G comp sound red


/-- Language component of the main full-refinement package. -/
theorem full_refinement_main_language
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    (T : StateTyping V M)
    (tau : Sigma → M)
    (G : UntypedStructure V Sigma)
    (comp : TypingCompatible tau T G)
    (sound : UntypedYieldSound tau T G)
    (red : UntypedReduced G) :
    ∀ word : List Sigma,
      KeptStartLanguage (fullKeptStructure T tau G comp red) word ↔
        StartLanguageKernel.UntypedStartLanguage G word :=
  (full_refinement_main_kernel T tau G comp sound red).trimmed_language


/-- Representation component of the main full-refinement package. -/
theorem full_refinement_main_representation
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    (T : StateTyping V M)
    (tau : Sigma → M)
    (G : UntypedStructure V Sigma)
    (comp : TypingCompatible tau T G)
    (sound : UntypedYieldSound tau T G)
    (red : UntypedReduced G) :
    RepresentationKernel.RepresentationKernel T G (FullKept tau G) :=
  (full_refinement_main_kernel T tau G comp sound red).representation

end FullMainTheoremKernel
end JALC
end LeanCfgProject
