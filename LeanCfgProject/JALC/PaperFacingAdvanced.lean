import LeanCfgProject.JALC.RepresentationKernel

namespace LeanCfgProject
namespace JALC
namespace PaperFacingAdvanced

/-
Advanced paper-facing Lean checks.

This module exposes the current strongest theorem-facing kernel: from the
kept-state statement, the intended-copy construction yields state equivalence,
rule preservation and reflection, and start-language preservation and
reflection.
-/

universe u v w

open InverseKernel RoundTripKernel KeptStateKernel RepresentationKernel


/-- Paper-facing advanced representation kernel. -/
theorem checked_representation_kernel_from_kept_intended
    {V : Type u} {M : Type v} {Sigma : Type w}
    (T : StateTyping V M)
    (G : UntypedStructure V Sigma)
    (Kept : TypedState V M → Prop)
    (hKept : ∀ X : V, Kept (intendedCopy T X))
    (hAll : ∀ s : TypedState V M, Kept s → IsIntended T s) :
    RepresentationKernel T G Kept :=
  representationKernel_from_kept_intended T G Kept hKept hAll


/-- Paper-facing state-equivalence consequence. -/
theorem checked_state_equiv_from_kept_intended
    {V : Type u} {M : Type v}
    (T : StateTyping V M)
    (Kept : TypedState V M → Prop)
    (hKept : ∀ X : V, Kept (intendedCopy T X))
    (hAll : ∀ s : TypedState V M, Kept s → IsIntended T s) :
    Nonempty (V ≃ KeptSubtype Kept) :=
  kept_state_equivalence_kernel T Kept hKept hAll


/-- Paper-facing language consequence. -/
theorem checked_language_equivalence_from_kept_intended
    {V : Type u} {M : Type v} {Sigma : Type w}
    (T : StateTyping V M)
    (G : UntypedStructure V Sigma)
    (Kept : TypedState V M → Prop)
    (hKept : ∀ X : V, Kept (intendedCopy T X))
    (hAll : ∀ s : TypedState V M, Kept s → IsIntended T s)
    (word : List Sigma) :
    StartLanguageKernel.TypedStartLanguage (liftStructure T G) word ↔
      StartLanguageKernel.UntypedStartLanguage G word :=
  representationKernel_language T G Kept hKept hAll word

end PaperFacingAdvanced
end JALC
end LeanCfgProject
