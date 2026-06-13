import LeanCfgProject.JALC.FullFiniteMainKernel

namespace LeanCfgProject
namespace JALC
namespace PaperFacingFullFiniteMain

/-
Paper-facing finite full-main theorem names.
-/

universe u v w

open InverseKernel RoundTripKernel
open ReachableProductiveKernel
open FullRefinementKernel
open FullYieldKernel
open FullKeptCorrectnessKernel
open FullTrimmedLanguageKernel
open FullMainTheoremKernel FullFiniteMainKernel
open KeptStartLanguageKernel
open FiniteRepresentationBundle


/-- Paper-facing check: finite full-main package. -/
theorem checked_full_finite_main_kernel
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M] [Fintype V] [Fintype M] [Fintype Sigma]
    (T : StateTyping V M)
    (tau : Sigma → M)
    (G : UntypedStructure V Sigma)
    (comp : TypingCompatible tau T G)
    (sound : UntypedYieldSound tau T G)
    (red : UntypedReduced G)
    [DecidablePred (FullKept tau G)] :
    FullFiniteMainKernel T tau G comp sound red :=
  full_finite_main_kernel T tau G comp sound red


/-- Paper-facing check: the full-kept trimmed language is finite-state represented. -/
theorem checked_full_finite_main_language
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M] [Fintype V] [Fintype M] [Fintype Sigma]
    (T : StateTyping V M)
    (tau : Sigma → M)
    (G : UntypedStructure V Sigma)
    (comp : TypingCompatible tau T G)
    (sound : UntypedYieldSound tau T G)
    (red : UntypedReduced G)
    [DecidablePred (FullKept tau G)] :
    ∀ word : List Sigma,
      KeptStartLanguage (fullKeptStructure T tau G comp red) word ↔
        StartLanguageKernel.UntypedStartLanguage G word :=
  full_finite_main_language T tau G comp sound red


/-- Paper-facing check: the kept universes of the full-kept construction are finite. -/
theorem checked_full_finite_main_kept_finite
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M] [Fintype V] [Fintype M] [Fintype Sigma]
    (T : StateTyping V M)
    (tau : Sigma → M)
    (G : UntypedStructure V Sigma)
    (comp : TypingCompatible tau T G)
    (sound : UntypedYieldSound tau T G)
    (red : UntypedReduced G)
    [DecidablePred (FullKept tau G)] :
    KeptFiniteBundle Sigma (FullKept tau G) :=
  full_finite_main_kept_finite T tau G comp sound red

end PaperFacingFullFiniteMain
end JALC
end LeanCfgProject
