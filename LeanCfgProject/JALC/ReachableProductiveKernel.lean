import LeanCfgProject.JALC.KeptRepresentationKernel

namespace LeanCfgProject
namespace JALC
namespace ReachableProductiveKernel

/-
Reachability and productivity kernels for the intended-copy lift.

This module formalizes the productive/reachable predicates used by the
remaining correctness statement, and proves that in the intended-copy lift,
reachable or productive typed states are intended copies.
-/

universe u v w

open InverseKernel RoundTripKernel
open DerivationLiftKernel StartLanguageKernel


/-- Reachability in an untyped rule structure. -/
inductive UntypedReachable {V : Type u} {Sigma : Type w}
    (G : UntypedStructure V Sigma) : V → Prop
  | start {r : StartRule V}
      (h : G.start r) :
      UntypedReachable G r.state
  | left {r : BinaryRule V}
      (h : G.binary r)
      (parent : UntypedReachable G r.parent) :
      UntypedReachable G r.left
  | right {r : BinaryRule V}
      (h : G.binary r)
      (parent : UntypedReachable G r.parent) :
      UntypedReachable G r.right


/-- Reachability in a typed rule structure. -/
inductive TypedReachable {V : Type u} {M : Type v} {Sigma : Type w}
    (H : TypedStructure V M Sigma) : TypedState V M → Prop
  | start {r : TypedStartRule V M}
      (h : H.start r) :
      TypedReachable H r.state
  | left {r : TypedBinaryRule V M}
      (h : H.binary r)
      (parent : TypedReachable H r.parent) :
      TypedReachable H r.left
  | right {r : TypedBinaryRule V M}
      (h : H.binary r)
      (parent : TypedReachable H r.parent) :
      TypedReachable H r.right


/-- Productivity in an untyped rule structure. -/
def UntypedProductive {V : Type u} {Sigma : Type w}
    (G : UntypedStructure V Sigma) (X : V) : Prop :=
  ∃ word : List Sigma, UntypedDeriv G X word


/-- Productivity in a typed rule structure. -/
def TypedProductive {V : Type u} {M : Type v} {Sigma : Type w}
    (H : TypedStructure V M Sigma) (s : TypedState V M) : Prop :=
  ∃ word : List Sigma, TypedRuleDeriv H s word


/-- Untyped reachability is preserved by intended-copy lifting. -/
theorem reachable_preserved
    {V : Type u} {M : Type v} {Sigma : Type w}
    (T : StateTyping V M)
    (G : UntypedStructure V Sigma)
    {X : V}
    (h : UntypedReachable G X) :
    TypedReachable (liftStructure T G) (intendedCopy T X) := by
  induction h with
  | start hs =>
      exact TypedReachable.start (start_preserved T G hs)
  | left hb hp ih =>
      exact TypedReachable.left (binary_preserved T G hb) ih
  | right hb hp ih =>
      exact TypedReachable.right (binary_preserved T G hb) ih


/-- Typed reachability in the intended-copy lift reflects to untyped reachability. -/
theorem reachable_reflected
    {V : Type u} {M : Type v} {Sigma : Type w}
    (T : StateTyping V M)
    (G : UntypedStructure V Sigma)
    {s : TypedState V M}
    (h : TypedReachable (liftStructure T G) s) :
    UntypedReachable G s.label := by
  induction h with
  | start hs =>
      rcases hs with ⟨r, hr, heq⟩
      cases heq
      exact UntypedReachable.start hr
  | left hb hp ih =>
      rcases hb with ⟨r, hr, heq⟩
      cases heq
      exact UntypedReachable.left hr ih
  | right hb hp ih =>
      rcases hb with ⟨r, hr, heq⟩
      cases heq
      exact UntypedReachable.right hr ih


/-- Any reachable typed state in the intended-copy lift is intended. -/
theorem typed_reachable_lifted_is_intended
    {V : Type u} {M : Type v} {Sigma : Type w}
    (T : StateTyping V M)
    (G : UntypedStructure V Sigma)
    {s : TypedState V M}
    (h : TypedReachable (liftStructure T G) s) :
    IsIntended T s := by
  induction h with
  | start hs =>
      rcases hs with ⟨r, hr, heq⟩
      cases heq
      exact intendedCopy_isIntended T r.state
  | left hb hp ih =>
      rcases hb with ⟨r, hr, heq⟩
      cases heq
      exact intendedCopy_isIntended T r.left
  | right hb hp ih =>
      rcases hb with ⟨r, hr, heq⟩
      cases heq
      exact intendedCopy_isIntended T r.right


/-- Untyped productivity is preserved by intended-copy lifting. -/
theorem productive_preserved
    {V : Type u} {M : Type v} {Sigma : Type w}
    (T : StateTyping V M)
    (G : UntypedStructure V Sigma)
    {X : V}
    (h : UntypedProductive G X) :
    TypedProductive (liftStructure T G) (intendedCopy T X) := by
  rcases h with ⟨word, d⟩
  exact ⟨word, derivation_preserved T G d⟩


/-- Typed productivity in the intended-copy lift reflects to untyped productivity. -/
theorem productive_reflected
    {V : Type u} {M : Type v} {Sigma : Type w}
    (T : StateTyping V M)
    (G : UntypedStructure V Sigma)
    {s : TypedState V M}
    (h : TypedProductive (liftStructure T G) s) :
    UntypedProductive G s.label := by
  rcases h with ⟨word, d⟩
  exact ⟨word, derivation_reflected T G d⟩


/-- Any productive typed state in the intended-copy lift is intended. -/
theorem typed_productive_lifted_is_intended
    {V : Type u} {M : Type v} {Sigma : Type w}
    (T : StateTyping V M)
    (G : UntypedStructure V Sigma)
    {s : TypedState V M}
    (h : TypedProductive (liftStructure T G) s) :
    IsIntended T s := by
  rcases h with ⟨word, d⟩
  induction d with
  | terminal ht =>
      rcases ht with ⟨r, hr, heq⟩
      cases heq
      exact intendedCopy_isIntended T r.lhs
  | binary hb left right ihLeft ihRight =>
      rcases hb with ⟨r, hr, heq⟩
      cases heq
      exact intendedCopy_isIntended T r.parent


/-- A reduced untyped structure: every state is productive and reachable. -/
structure UntypedReduced {V : Type u} {Sigma : Type w}
    (G : UntypedStructure V Sigma) : Prop where
  productive : ∀ X : V, UntypedProductive G X
  reachable : ∀ X : V, UntypedReachable G X

end ReachableProductiveKernel
end JALC
end LeanCfgProject
