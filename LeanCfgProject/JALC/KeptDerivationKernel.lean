import LeanCfgProject.JALC.KeptStructureKernel

namespace LeanCfgProject
namespace JALC
namespace KeptDerivationKernel

/-
Derivation kernel over the kept-state substructure.

This module shows that derivations are preserved and reflected between an
original structure and its kept-intended-copy structure.
-/

universe u v w

open InverseKernel RoundTripKernel
open KeptStateKernel KeptStructureKernel
open DerivationLiftKernel


/-- Derivations in a kept-state rule structure. -/
inductive KeptDeriv {V : Type u} {M : Type v} {Sigma : Type w}
    {Kept : TypedState V M → Prop}
    (H : KeptStructure Kept Sigma) : KeptSubtype Kept → List Sigma → Prop
  | terminal {r : KeptTerminalRule Kept Sigma}
      (h : H.terminal r) :
      KeptDeriv H r.lhs [r.terminal]
  | binary {r : KeptBinaryRule Kept} {u v : List Sigma}
      (h : H.binary r)
      (left : KeptDeriv H r.left u)
      (right : KeptDeriv H r.right v) :
      KeptDeriv H r.parent (u ++ v)


/-- Original derivations are preserved by kept intended-copy lifting. -/
theorem kept_derivation_preserved
    {V : Type u} {M : Type v} {Sigma : Type w}
    (T : StateTyping V M)
    (G : UntypedStructure V Sigma)
    (Kept : TypedState V M → Prop)
    (hKept : ∀ X : V, Kept (intendedCopy T X))
    {X : V} {word : List Sigma}
    (d : UntypedDeriv G X word) :
    KeptDeriv (liftToKeptStructure T G Kept hKept)
      (intendedCopyToKept T Kept hKept X) word := by
  induction d with
  | terminal h =>
      exact KeptDeriv.terminal
        (kept_terminal_preserved T G Kept hKept h)
  | binary h left right ihLeft ihRight =>
      exact KeptDeriv.binary
        (kept_binary_preserved T G Kept hKept h) ihLeft ihRight


/-- Kept derivations are reflected back to original derivations by labels. -/
theorem kept_derivation_reflected
    {V : Type u} {M : Type v} {Sigma : Type w}
    (T : StateTyping V M)
    (G : UntypedStructure V Sigma)
    (Kept : TypedState V M → Prop)
    (hKept : ∀ X : V, Kept (intendedCopy T X))
    {s : KeptSubtype Kept} {word : List Sigma}
    (d : KeptDeriv (liftToKeptStructure T G Kept hKept) s word) :
    UntypedDeriv G s.val.label word := by
  induction d with
  | terminal h =>
      rcases h with ⟨r, hr, heq⟩
      cases heq
      simpa [liftTerminalKept, intendedCopyToKept, intendedCopy] using
        UntypedDeriv.terminal hr
  | binary h left right ihLeft ihRight =>
      rcases h with ⟨r, hr, heq⟩
      cases heq
      simpa [liftBinaryKept, intendedCopyToKept, intendedCopy] using
        UntypedDeriv.binary hr ihLeft ihRight


/-- Derivation equivalence for kept intended copies. -/
theorem kept_derivation_lift_iff
    {V : Type u} {M : Type v} {Sigma : Type w}
    (T : StateTyping V M)
    (G : UntypedStructure V Sigma)
    (Kept : TypedState V M → Prop)
    (hKept : ∀ X : V, Kept (intendedCopy T X))
    (X : V) (word : List Sigma) :
    KeptDeriv (liftToKeptStructure T G Kept hKept)
      (intendedCopyToKept T Kept hKept X) word ↔
        UntypedDeriv G X word := by
  constructor
  · intro h
    simpa [intendedCopyToKept, intendedCopy] using
      kept_derivation_reflected T G Kept hKept h
  · intro h
    exact kept_derivation_preserved T G Kept hKept h


/-- Paper-facing kept derivation kernel. -/
theorem kept_derivation_kernel
    {V : Type u} {M : Type v} {Sigma : Type w}
    (T : StateTyping V M)
    (G : UntypedStructure V Sigma)
    (Kept : TypedState V M → Prop)
    (hKept : ∀ X : V, Kept (intendedCopy T X)) :
    ∀ (X : V) (word : List Sigma),
      KeptDeriv (liftToKeptStructure T G Kept hKept)
        (intendedCopyToKept T Kept hKept X) word ↔
          UntypedDeriv G X word := by
  intro X word
  exact kept_derivation_lift_iff T G Kept hKept X word

end KeptDerivationKernel
end JALC
end LeanCfgProject
