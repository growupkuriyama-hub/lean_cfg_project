import LeanCfgProject.JALC.FullKeptCorrectnessKernel
import LeanCfgProject.JALC.KeptRepresentationKernel

namespace LeanCfgProject
namespace JALC
namespace FullTrimmedLanguageKernel

/-
Full-trimmed language kernel.

This module packages the consequence of full kept-correctness for the kept-state
substructure obtained from the full productivity and productive-reachability
predicate.
-/

universe u v w

open InverseKernel RoundTripKernel
open ReachableProductiveKernel
open FullRefinementKernel
open FullYieldKernel
open FullFrameReachabilityKernel FullKeptCorrectnessKernel
open KeptStructureKernel KeptStartLanguageKernel KeptRepresentationKernel


/-- The kept proof for intended copies in the full kept predicate. -/
def fullKeptIntendedProof
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    (T : StateTyping V M)
    (tau : Sigma → M)
    (G : UntypedStructure V Sigma)
    (comp : TypingCompatible tau T G)
    (red : UntypedReduced G) :
    ∀ X : V, FullKept tau G (intendedCopy T X) :=
  intendedCopy_fullKept_of_reduced T tau G comp red


/-- The kept-state structure induced by the full kept predicate. -/
def fullKeptStructure
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    (T : StateTyping V M)
    (tau : Sigma → M)
    (G : UntypedStructure V Sigma)
    (comp : TypingCompatible tau T G)
    (red : UntypedReduced G) :
    KeptStructure (FullKept tau G) Sigma :=
  liftToKeptStructure T G (FullKept tau G)
    (fullKeptIntendedProof T tau G comp red)


/--
The full-kept trimmed structure has exactly the original start language.
-/
theorem fullKept_trimmed_language_iff
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    (T : StateTyping V M)
    (tau : Sigma → M)
    (G : UntypedStructure V Sigma)
    (comp : TypingCompatible tau T G)
    (red : UntypedReduced G)
    (word : List Sigma) :
    KeptStartLanguage (fullKeptStructure T tau G comp red) word ↔
      StartLanguageKernel.UntypedStartLanguage G word :=
  keptRepresentationKernel_language T G (FullKept tau G)
    (fullKeptIntendedProof T tau G comp red) word


/--
The full-kept trimmed language kernel as a quantified statement.
-/
theorem fullKept_trimmed_language_kernel
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    (T : StateTyping V M)
    (tau : Sigma → M)
    (G : UntypedStructure V Sigma)
    (comp : TypingCompatible tau T G)
    (red : UntypedReduced G) :
    ∀ word : List Sigma,
      KeptStartLanguage (fullKeptStructure T tau G comp red) word ↔
        StartLanguageKernel.UntypedStartLanguage G word := by
  intro word
  exact fullKept_trimmed_language_iff T tau G comp red word


/--
The full-kept trimmed structure satisfies the kept representation package.
-/
theorem fullKept_trimmed_representation_kernel
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    (T : StateTyping V M)
    (tau : Sigma → M)
    (G : UntypedStructure V Sigma)
    (comp : TypingCompatible tau T G)
    (red : UntypedReduced G) :
    KeptRepresentationKernel.KeptRepresentationKernel
      T G (FullKept tau G)
        (fullKeptIntendedProof T tau G comp red) :=
  keptRepresentationKernel_holds T G (FullKept tau G)
    (fullKeptIntendedProof T tau G comp red)

end FullTrimmedLanguageKernel
end JALC
end LeanCfgProject
