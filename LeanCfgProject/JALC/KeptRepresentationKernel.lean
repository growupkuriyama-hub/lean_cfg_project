import LeanCfgProject.JALC.KeptStartLanguageKernel

namespace LeanCfgProject
namespace JALC
namespace KeptRepresentationKernel

/-
Kept-state representation kernel.

This module packages the result that the kept-intended-copy structure has the
same start language as the original structure, and keeps the rule equivalences
available for terminal, binary, and start rules.
-/

universe u v w

open InverseKernel RoundTripKernel
open KeptStateKernel KeptStructureKernel KeptStartLanguageKernel


/-- Packaged kept-state representation kernel. -/
structure KeptRepresentationKernel {V : Type u} {M : Type v} {Sigma : Type w}
    (T : StateTyping V M)
    (G : UntypedStructure V Sigma)
    (Kept : TypedState V M → Prop)
    (hKept : ∀ X : V, Kept (intendedCopy T X)) : Prop where
  terminal :
    ∀ r : TerminalRule V Sigma,
      (liftToKeptStructure T G Kept hKept).terminal
        (liftTerminalKept T Kept hKept r) ↔ G.terminal r
  binary :
    ∀ r : BinaryRule V,
      (liftToKeptStructure T G Kept hKept).binary
        (liftBinaryKept T Kept hKept r) ↔ G.binary r
  start :
    ∀ r : StartRule V,
      (liftToKeptStructure T G Kept hKept).start
        (liftStartKept T Kept hKept r) ↔ G.start r
  language :
    ∀ word : List Sigma,
      KeptStartLanguage (liftToKeptStructure T G Kept hKept) word ↔
        StartLanguageKernel.UntypedStartLanguage G word


/-- The kept-intended-copy lift satisfies the packaged representation kernel. -/
theorem keptRepresentationKernel_holds
    {V : Type u} {M : Type v} {Sigma : Type w}
    (T : StateTyping V M)
    (G : UntypedStructure V Sigma)
    (Kept : TypedState V M → Prop)
    (hKept : ∀ X : V, Kept (intendedCopy T X)) :
    KeptRepresentationKernel T G Kept hKept := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro r
    exact kept_terminal_lift_iff T G Kept hKept r
  · intro r
    exact kept_binary_lift_iff T G Kept hKept r
  · intro r
    exact kept_start_lift_iff T G Kept hKept r
  · intro word
    exact kept_start_language_lift_iff T G Kept hKept word


/-- Paper-facing kept-state language consequence. -/
theorem keptRepresentationKernel_language
    {V : Type u} {M : Type v} {Sigma : Type w}
    (T : StateTyping V M)
    (G : UntypedStructure V Sigma)
    (Kept : TypedState V M → Prop)
    (hKept : ∀ X : V, Kept (intendedCopy T X))
    (word : List Sigma) :
    KeptStartLanguage (liftToKeptStructure T G Kept hKept) word ↔
      StartLanguageKernel.UntypedStartLanguage G word :=
  (keptRepresentationKernel_holds T G Kept hKept).language word

end KeptRepresentationKernel
end JALC
end LeanCfgProject
