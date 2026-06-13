import LeanCfgProject.JALC.KeptRepresentationKernel

namespace LeanCfgProject
namespace JALC
namespace FiniteUniverseKernel

/-
Finite-universe kernels for the typed representation.

This module supplies equivalences from the typed-state and rule structures used
in the JALC development to finite products.  Consequently, when the original
state set, terminal alphabet, and monoid are finite, the corresponding typed
state and rule universes are finite.
-/

universe u v w

open InverseKernel RoundTripKernel
open KeptStateKernel KeptStructureKernel


/-- A typed state is equivalent to a fourfold product. -/
def typedStateEquivProduct {V : Type u} {M : Type v} :
    TypedState V M ≃ (((V × M) × M) × M) where
  toFun s := (((s.label, s.yt), s.lt), s.rt)
  invFun x :=
    { label := x.1.1.1,
      yt := x.1.1.2,
      lt := x.1.2,
      rt := x.2 }
  left_inv := by
    intro s
    cases s
    rfl
  right_inv := by
    intro x
    rcases x with ⟨⟨⟨label, yt⟩, lt⟩, rt⟩
    rfl


/-- Terminal rules are equivalent to state-terminal pairs. -/
def terminalRuleEquivProduct {V : Type u} {Sigma : Type w} :
    TerminalRule V Sigma ≃ V × Sigma where
  toFun r := (r.lhs, r.terminal)
  invFun x := { lhs := x.1, terminal := x.2 }
  left_inv := by
    intro r
    cases r
    rfl
  right_inv := by
    intro x
    cases x
    rfl


/-- Binary rules are equivalent to triples of states. -/
def binaryRuleEquivProduct {V : Type u} :
    BinaryRule V ≃ ((V × V) × V) where
  toFun r := ((r.parent, r.left), r.right)
  invFun x := { parent := x.1.1, left := x.1.2, right := x.2 }
  left_inv := by
    intro r
    cases r
    rfl
  right_inv := by
    intro x
    rcases x with ⟨⟨parent, left⟩, right⟩
    rfl


/-- Start rules are equivalent to states. -/
def startRuleEquivProduct {V : Type u} :
    StartRule V ≃ V where
  toFun r := r.state
  invFun x := { state := x }
  left_inv := by
    intro r
    cases r
    rfl
  right_inv := by
    intro x
    rfl


/-- Typed terminal rules are equivalent to typed-state-terminal pairs. -/
def typedTerminalRuleEquivProduct
    {V : Type u} {M : Type v} {Sigma : Type w} :
    TypedTerminalRule V M Sigma ≃ TypedState V M × Sigma where
  toFun r := (r.lhs, r.terminal)
  invFun x := { lhs := x.1, terminal := x.2 }
  left_inv := by
    intro r
    cases r
    rfl
  right_inv := by
    intro x
    cases x
    rfl


/-- Typed binary rules are equivalent to triples of typed states. -/
def typedBinaryRuleEquivProduct {V : Type u} {M : Type v} :
    TypedBinaryRule V M ≃ ((TypedState V M × TypedState V M) ×
      TypedState V M) where
  toFun r := ((r.parent, r.left), r.right)
  invFun x := { parent := x.1.1, left := x.1.2, right := x.2 }
  left_inv := by
    intro r
    cases r
    rfl
  right_inv := by
    intro x
    rcases x with ⟨⟨parent, left⟩, right⟩
    rfl


/-- Typed start rules are equivalent to typed states. -/
def typedStartRuleEquivProduct {V : Type u} {M : Type v} :
    TypedStartRule V M ≃ TypedState V M where
  toFun r := r.state
  invFun x := { state := x }
  left_inv := by
    intro r
    cases r
    rfl
  right_inv := by
    intro x
    rfl


/-- Kept terminal rules are equivalent to kept-state-terminal pairs. -/
def keptTerminalRuleEquivProduct
    {V : Type u} {M : Type v} {Sigma : Type w}
    {Kept : TypedState V M → Prop} :
    KeptTerminalRule Kept Sigma ≃ KeptSubtype Kept × Sigma where
  toFun r := (r.lhs, r.terminal)
  invFun x := { lhs := x.1, terminal := x.2 }
  left_inv := by
    intro r
    cases r
    rfl
  right_inv := by
    intro x
    cases x
    rfl


/-- Kept binary rules are equivalent to triples of kept states. -/
def keptBinaryRuleEquivProduct
    {V : Type u} {M : Type v}
    {Kept : TypedState V M → Prop} :
    KeptBinaryRule Kept ≃ ((KeptSubtype Kept × KeptSubtype Kept) ×
      KeptSubtype Kept) where
  toFun r := ((r.parent, r.left), r.right)
  invFun x := { parent := x.1.1, left := x.1.2, right := x.2 }
  left_inv := by
    intro r
    cases r
    rfl
  right_inv := by
    intro x
    rcases x with ⟨⟨parent, left⟩, right⟩
    rfl


/-- Kept start rules are equivalent to kept states. -/
def keptStartRuleEquivProduct
    {V : Type u} {M : Type v}
    {Kept : TypedState V M → Prop} :
    KeptStartRule Kept ≃ KeptSubtype Kept where
  toFun r := r.state
  invFun x := { state := x }
  left_inv := by
    intro r
    cases r
    rfl
  right_inv := by
    intro x
    rfl


noncomputable instance typedStateFintype
    {V : Type u} {M : Type v} [Fintype V] [Fintype M] :
    Fintype (TypedState V M) :=
  Fintype.ofEquiv (((V × M) × M) × M) typedStateEquivProduct.symm


noncomputable instance terminalRuleFintype
    {V : Type u} {Sigma : Type w} [Fintype V] [Fintype Sigma] :
    Fintype (TerminalRule V Sigma) :=
  Fintype.ofEquiv (V × Sigma) terminalRuleEquivProduct.symm


noncomputable instance binaryRuleFintype
    {V : Type u} [Fintype V] :
    Fintype (BinaryRule V) :=
  Fintype.ofEquiv ((V × V) × V) binaryRuleEquivProduct.symm


noncomputable instance startRuleFintype
    {V : Type u} [Fintype V] :
    Fintype (StartRule V) :=
  Fintype.ofEquiv V startRuleEquivProduct.symm


noncomputable instance typedTerminalRuleFintype
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Fintype V] [Fintype M] [Fintype Sigma] :
    Fintype (TypedTerminalRule V M Sigma) :=
  Fintype.ofEquiv (TypedState V M × Sigma)
    typedTerminalRuleEquivProduct.symm


noncomputable instance typedBinaryRuleFintype
    {V : Type u} {M : Type v} [Fintype V] [Fintype M] :
    Fintype (TypedBinaryRule V M) :=
  Fintype.ofEquiv ((TypedState V M × TypedState V M) × TypedState V M)
    typedBinaryRuleEquivProduct.symm


noncomputable instance typedStartRuleFintype
    {V : Type u} {M : Type v} [Fintype V] [Fintype M] :
    Fintype (TypedStartRule V M) :=
  Fintype.ofEquiv (TypedState V M) typedStartRuleEquivProduct.symm


/-- Finiteness witness for typed states. -/
theorem typedState_fintype_exists
    {V : Type u} {M : Type v} [Fintype V] [Fintype M] :
    Nonempty (Fintype (TypedState V M)) := by
  exact ⟨inferInstance⟩


/-- Finiteness witness for the basic typed rule universes. -/
theorem typedRuleUniverses_fintype_exist
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Fintype V] [Fintype M] [Fintype Sigma] :
    Nonempty (Fintype (TypedTerminalRule V M Sigma)) ∧
    Nonempty (Fintype (TypedBinaryRule V M)) ∧
    Nonempty (Fintype (TypedStartRule V M)) := by
  exact ⟨⟨inferInstance⟩, ⟨inferInstance⟩, ⟨inferInstance⟩⟩

end FiniteUniverseKernel
end JALC
end LeanCfgProject
