import LeanCfgProject.JALC.StateRuleIsoKernel

namespace LeanCfgProject
namespace JALC
namespace DerivationLiftKernel

/-
Derivation-lift kernel for the intended-copy construction.

This module shows that derivation trees are preserved by intended-copy lifting,
and reflected back by reading the original label of a typed state.  It is a
formal core immediately below language preservation.
-/

universe u v w

open InverseKernel RoundTripKernel


/-- Derivations in an untyped rule structure. -/
inductive UntypedDeriv {V : Type u} {Sigma : Type w}
    (G : UntypedStructure V Sigma) : V → List Sigma → Prop
  | terminal {r : TerminalRule V Sigma}
      (h : G.terminal r) :
      UntypedDeriv G r.lhs [r.terminal]
  | binary {r : BinaryRule V} {u v : List Sigma}
      (h : G.binary r)
      (left : UntypedDeriv G r.left u)
      (right : UntypedDeriv G r.right v) :
      UntypedDeriv G r.parent (u ++ v)


/-- Derivations in a typed rule structure. -/
inductive TypedRuleDeriv {V : Type u} {M : Type v} {Sigma : Type w}
    (H : TypedStructure V M Sigma) : TypedState V M → List Sigma → Prop
  | terminal {r : TypedTerminalRule V M Sigma}
      (h : H.terminal r) :
      TypedRuleDeriv H r.lhs [r.terminal]
  | binary {r : TypedBinaryRule V M} {u v : List Sigma}
      (h : H.binary r)
      (left : TypedRuleDeriv H r.left u)
      (right : TypedRuleDeriv H r.right v) :
      TypedRuleDeriv H r.parent (u ++ v)


/-- Untyped derivations are preserved by intended-copy lifting. -/
theorem derivation_preserved
    {V : Type u} {M : Type v} {Sigma : Type w}
    (T : StateTyping V M) (G : UntypedStructure V Sigma)
    {X : V} {word : List Sigma}
    (d : UntypedDeriv G X word) :
    TypedRuleDeriv (liftStructure T G) (intendedCopy T X) word := by
  induction d with
  | terminal h =>
      exact TypedRuleDeriv.terminal (terminal_preserved T G h)
  | binary h left right ihLeft ihRight =>
      exact TypedRuleDeriv.binary (binary_preserved T G h) ihLeft ihRight


/--
Typed derivations in the lifted structure are reflected by reading the original
label of the typed state.
-/
theorem derivation_reflected
    {V : Type u} {M : Type v} {Sigma : Type w}
    (T : StateTyping V M) (G : UntypedStructure V Sigma)
    {s : TypedState V M} {word : List Sigma}
    (d : TypedRuleDeriv (liftStructure T G) s word) :
    UntypedDeriv G s.label word := by
  induction d with
  | terminal h =>
      rcases h with ⟨r, hr, heq⟩
      cases heq
      exact UntypedDeriv.terminal hr
  | binary h left right ihLeft ihRight =>
      rcases h with ⟨r, hr, heq⟩
      cases heq
      exact UntypedDeriv.binary hr ihLeft ihRight


/-- Derivation preservation and reflection for intended copies. -/
theorem intended_derivation_lift_iff
    {V : Type u} {M : Type v} {Sigma : Type w}
    (T : StateTyping V M) (G : UntypedStructure V Sigma)
    (X : V) (word : List Sigma) :
    TypedRuleDeriv (liftStructure T G) (intendedCopy T X) word ↔
      UntypedDeriv G X word := by
  constructor
  · intro h
    simpa [intendedCopy] using derivation_reflected T G h
  · intro h
    exact derivation_preserved T G h


/--
Combined derivation kernel.

For every original state and word, derivability from the intended typed copy
is equivalent to derivability from the original state.
-/
theorem derivation_lift_kernel
    {V : Type u} {M : Type v} {Sigma : Type w}
    (T : StateTyping V M) (G : UntypedStructure V Sigma) :
    ∀ (X : V) (word : List Sigma),
      TypedRuleDeriv (liftStructure T G) (intendedCopy T X) word ↔
        UntypedDeriv G X word := by
  intro X word
  exact intended_derivation_lift_iff T G X word

end DerivationLiftKernel
end JALC
end LeanCfgProject
