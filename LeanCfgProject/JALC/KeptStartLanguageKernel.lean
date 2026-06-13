import LeanCfgProject.JALC.KeptDerivationKernel

namespace LeanCfgProject
namespace JALC
namespace KeptStartLanguageKernel

/-
Start-language kernel over kept states.

This module proves that the kept-intended-copy structure generates the same
start language as the original structure.
-/

universe u v w

open InverseKernel RoundTripKernel
open KeptStateKernel KeptStructureKernel KeptDerivationKernel


/-- Start language of a kept-state rule structure. -/
def KeptStartLanguage {V : Type u} {M : Type v} {Sigma : Type w}
    {Kept : TypedState V M → Prop}
    (H : KeptStructure Kept Sigma) (word : List Sigma) : Prop :=
  ∃ s : KeptStartRule Kept, H.start s ∧ KeptDeriv H s.state word


/-- Start-language membership is preserved by kept intended-copy lifting. -/
theorem kept_start_language_preserved
    {V : Type u} {M : Type v} {Sigma : Type w}
    (T : StateTyping V M)
    (G : UntypedStructure V Sigma)
    (Kept : TypedState V M → Prop)
    (hKept : ∀ X : V, Kept (intendedCopy T X))
    {word : List Sigma}
    (h : StartLanguageKernel.UntypedStartLanguage G word) :
    KeptStartLanguage (liftToKeptStructure T G Kept hKept) word := by
  rcases h with ⟨s, hs, hd⟩
  exact ⟨liftStartKept T Kept hKept s,
    kept_start_preserved T G Kept hKept hs,
    kept_derivation_preserved T G Kept hKept hd⟩


/-- Start-language membership is reflected by kept intended-copy lifting. -/
theorem kept_start_language_reflected
    {V : Type u} {M : Type v} {Sigma : Type w}
    (T : StateTyping V M)
    (G : UntypedStructure V Sigma)
    (Kept : TypedState V M → Prop)
    (hKept : ∀ X : V, Kept (intendedCopy T X))
    {word : List Sigma}
    (h : KeptStartLanguage
      (liftToKeptStructure T G Kept hKept) word) :
    StartLanguageKernel.UntypedStartLanguage G word := by
  rcases h with ⟨s, hs, hd⟩
  rcases hs with ⟨s0, hs0, heq⟩
  cases heq
  exact ⟨s0, hs0, by
    simpa [liftStartKept, intendedCopyToKept, intendedCopy] using
      kept_derivation_reflected T G Kept hKept hd⟩


/-- Start-language equivalence for kept intended-copy lifting. -/
theorem kept_start_language_lift_iff
    {V : Type u} {M : Type v} {Sigma : Type w}
    (T : StateTyping V M)
    (G : UntypedStructure V Sigma)
    (Kept : TypedState V M → Prop)
    (hKept : ∀ X : V, Kept (intendedCopy T X))
    (word : List Sigma) :
    KeptStartLanguage (liftToKeptStructure T G Kept hKept) word ↔
      StartLanguageKernel.UntypedStartLanguage G word := by
  constructor
  · intro h
    exact kept_start_language_reflected T G Kept hKept h
  · intro h
    exact kept_start_language_preserved T G Kept hKept h


/-- Paper-facing kept start-language kernel. -/
theorem kept_start_language_kernel
    {V : Type u} {M : Type v} {Sigma : Type w}
    (T : StateTyping V M)
    (G : UntypedStructure V Sigma)
    (Kept : TypedState V M → Prop)
    (hKept : ∀ X : V, Kept (intendedCopy T X)) :
    ∀ word : List Sigma,
      KeptStartLanguage (liftToKeptStructure T G Kept hKept) word ↔
        StartLanguageKernel.UntypedStartLanguage G word := by
  intro word
  exact kept_start_language_lift_iff T G Kept hKept word

end KeptStartLanguageKernel
end JALC
end LeanCfgProject
