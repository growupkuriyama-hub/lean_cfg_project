import LeanCfgProject.JALC.FullMainTheoremKernel

namespace LeanCfgProject
namespace JALC
namespace PaperFacingFullMain

/-
Paper-facing full-refinement theorem names.
-/

universe u v w

open InverseKernel RoundTripKernel
open ReachableProductiveKernel
open FullRefinementKernel
open FullYieldKernel
open FullKeptCorrectnessKernel
open FullTrimmedLanguageKernel FullMainTheoremKernel
open KeptStartLanguageKernel


/-- Paper-facing check: full kept trimming preserves and reflects the start language. -/
theorem checked_fullKept_trimmed_language_kernel
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    (T : StateTyping V M)
    (tau : Sigma → M)
    (G : UntypedStructure V Sigma)
    (comp : TypingCompatible tau T G)
    (red : UntypedReduced G) :
    ∀ word : List Sigma,
      KeptStartLanguage (fullKeptStructure T tau G comp red) word ↔
        StartLanguageKernel.UntypedStartLanguage G word :=
  fullKept_trimmed_language_kernel T tau G comp red


/-- Paper-facing check: full-refinement main package. -/
theorem checked_full_refinement_main_kernel
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    (T : StateTyping V M)
    (tau : Sigma → M)
    (G : UntypedStructure V Sigma)
    (comp : TypingCompatible tau T G)
    (sound : UntypedYieldSound tau T G)
    (red : UntypedReduced G) :
    FullRefinementMainKernel T tau G comp sound red :=
  full_refinement_main_kernel T tau G comp sound red


/-- Paper-facing check: the full-kept representation component. -/
theorem checked_full_refinement_main_representation
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    (T : StateTyping V M)
    (tau : Sigma → M)
    (G : UntypedStructure V Sigma)
    (comp : TypingCompatible tau T G)
    (sound : UntypedYieldSound tau T G)
    (red : UntypedReduced G) :
    RepresentationKernel.RepresentationKernel T G (FullKept tau G) :=
  full_refinement_main_representation T tau G comp sound red

end PaperFacingFullMain
end JALC
end LeanCfgProject
