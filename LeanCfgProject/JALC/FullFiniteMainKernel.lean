import LeanCfgProject.JALC.PaperFacingFullMain
import LeanCfgProject.JALC.FiniteRepresentationBundle

namespace LeanCfgProject
namespace JALC
namespace FullFiniteMainKernel

/-
Finite full-main theorem package.

This module connects the full-kept main theorem package to the finite
representation kernels.  Under finite input data and decidable keptness, the
full-kept trimmed structure has finite kept-state and kept-rule universes, while
retaining the full language and representation kernels.
-/

universe u v w

open InverseKernel RoundTripKernel
open ReachableProductiveKernel
open FullRefinementKernel
open FullYieldKernel
open FullKeptCorrectnessKernel
open FullTrimmedLanguageKernel FullMainTheoremKernel
open KeptStartLanguageKernel
open FiniteRepresentationBundle


/--
Finite full-refinement main package.

The decidability assumption is deliberately explicit: it is the computational
boundary between the mathematical kept predicate and an executable extraction.
-/
structure FullFiniteMainKernel
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M] [Fintype V] [Fintype M] [Fintype Sigma]
    (T : StateTyping V M)
    (tau : Sigma → M)
    (G : UntypedStructure V Sigma)
    (comp : TypingCompatible tau T G)
    (sound : UntypedYieldSound tau T G)
    (red : UntypedReduced G)
    [DecidablePred (FullKept tau G)] : Prop where
  main :
    FullRefinementMainKernel T tau G comp sound red
  typed_finite :
    TypedFiniteBundle V M Sigma
  kept_finite :
    KeptFiniteBundle Sigma (FullKept tau G)
  language :
    ∀ word : List Sigma,
      KeptStartLanguage (fullKeptStructure T tau G comp red) word ↔
        StartLanguageKernel.UntypedStartLanguage G word
  representation :
    RepresentationKernel.RepresentationKernel T G (FullKept tau G)


/-- The finite full-main package follows from the checked kernels. -/
theorem full_finite_main_kernel
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M] [Fintype V] [Fintype M] [Fintype Sigma]
    (T : StateTyping V M)
    (tau : Sigma → M)
    (G : UntypedStructure V Sigma)
    (comp : TypingCompatible tau T G)
    (sound : UntypedYieldSound tau T G)
    (red : UntypedReduced G)
    [DecidablePred (FullKept tau G)] :
    FullFiniteMainKernel T tau G comp sound red := by
  exact
    { main := full_refinement_main_kernel T tau G comp sound red,
      typed_finite := typedFiniteBundle_of_finite V M Sigma,
      kept_finite := keptFiniteBundle_of_finite Sigma (FullKept tau G),
      language := full_refinement_main_language T tau G comp sound red,
      representation := full_refinement_main_representation T tau G comp sound red }


/-- Language component of the finite full-main package. -/
theorem full_finite_main_language
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
  (full_finite_main_kernel T tau G comp sound red).language


/-- Finite kept-universe component of the finite full-main package. -/
theorem full_finite_main_kept_finite
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
  (full_finite_main_kernel T tau G comp sound red).kept_finite


/-- Finite typed-universe component of the finite full-main package. -/
theorem full_finite_main_typed_finite
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M] [Fintype V] [Fintype M] [Fintype Sigma]
    (T : StateTyping V M)
    (tau : Sigma → M)
    (G : UntypedStructure V Sigma)
    (comp : TypingCompatible tau T G)
    (sound : UntypedYieldSound tau T G)
    (red : UntypedReduced G)
    [DecidablePred (FullKept tau G)] :
    TypedFiniteBundle V M Sigma :=
  (full_finite_main_kernel T tau G comp sound red).typed_finite

end FullFiniteMainKernel
end JALC
end LeanCfgProject
