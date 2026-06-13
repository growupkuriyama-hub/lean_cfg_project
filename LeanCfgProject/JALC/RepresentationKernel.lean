import LeanCfgProject.JALC.KeptStateKernel

namespace LeanCfgProject
namespace JALC
namespace RepresentationKernel

/-
Representation kernel from the kept-state statement.

This module packages the exact consequence needed from the remaining hard part:
if the kept typed states are exactly the intended copies, then the intended-copy
construction gives a state equivalence, rule preservation and reflection, and
start-language preservation and reflection.
-/

universe u v w

open InverseKernel RoundTripKernel KeptStateKernel
open RuleLift StartLanguageKernel


/-- Packaged representation kernel for the intended-copy construction. -/
structure RepresentationKernel {V : Type u} {M : Type v} {Sigma : Type w}
    (T : StateTyping V M)
    (G : UntypedStructure V Sigma)
    (Kept : TypedState V M → Prop) : Prop where
  state_equiv :
    Nonempty (V ≃ KeptSubtype Kept)
  terminal :
    ∀ r : TerminalRule V Sigma,
      (liftStructure T G).terminal (liftTerminal T r) ↔ G.terminal r
  binary :
    ∀ r : BinaryRule V,
      (liftStructure T G).binary (liftBinary T r) ↔ G.binary r
  start :
    ∀ r : StartRule V,
      (liftStructure T G).start (liftStart T r) ↔ G.start r
  language :
    ∀ word : List Sigma,
      TypedStartLanguage (liftStructure T G) word ↔ UntypedStartLanguage G word


/--
If the kept typed states are exactly the intended copies, then the representation
kernel follows.
-/
theorem representationKernel_from_kept_intended
    {V : Type u} {M : Type v} {Sigma : Type w}
    (T : StateTyping V M)
    (G : UntypedStructure V Sigma)
    (Kept : TypedState V M → Prop)
    (hKept : ∀ X : V, Kept (intendedCopy T X))
    (hAll : ∀ s : TypedState V M, Kept s → IsIntended T s) :
    RepresentationKernel T G Kept := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact kept_state_equivalence_kernel T Kept hKept hAll
  · intro r
    exact terminal_lift_iff T G r
  · intro r
    exact binary_lift_iff T G r
  · intro r
    exact start_lift_iff T G r
  · intro word
    exact start_language_lift_iff T G word


/-- State-equivalence component of the representation kernel. -/
theorem representationKernel_state_equiv
    {V : Type u} {M : Type v} {Sigma : Type w}
    (T : StateTyping V M)
    (G : UntypedStructure V Sigma)
    (Kept : TypedState V M → Prop)
    (hKept : ∀ X : V, Kept (intendedCopy T X))
    (hAll : ∀ s : TypedState V M, Kept s → IsIntended T s) :
    Nonempty (V ≃ KeptSubtype Kept) :=
  (representationKernel_from_kept_intended T G Kept hKept hAll).state_equiv


/-- Language component of the representation kernel. -/
theorem representationKernel_language
    {V : Type u} {M : Type v} {Sigma : Type w}
    (T : StateTyping V M)
    (G : UntypedStructure V Sigma)
    (Kept : TypedState V M → Prop)
    (hKept : ∀ X : V, Kept (intendedCopy T X))
    (hAll : ∀ s : TypedState V M, Kept s → IsIntended T s)
    (word : List Sigma) :
    TypedStartLanguage (liftStructure T G) word ↔ UntypedStartLanguage G word :=
  (representationKernel_from_kept_intended T G Kept hKept hAll).language word

end RepresentationKernel
end JALC
end LeanCfgProject
