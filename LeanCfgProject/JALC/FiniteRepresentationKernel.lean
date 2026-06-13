import LeanCfgProject.JALC.FiniteUniverseKernel

namespace LeanCfgProject
namespace JALC
namespace FiniteRepresentationKernel

/-
Finite representation kernel.

This module packages the finite-universe part of the representation theorem:
when the original state set, terminal alphabet, and monoid are finite, the
typed state and typed rule universes used by the construction are finite.
-/

universe u v w

open InverseKernel RoundTripKernel
open KeptStateKernel KeptStructureKernel FiniteUniverseKernel


/-- Packaged finite-universe witnesses for the typed construction. -/
structure FiniteTypedUniverses
    (V : Type u) (M : Type v) (Sigma : Type w) : Prop where
  typed_states : Nonempty (Fintype (TypedState V M))
  terminal_rules : Nonempty (Fintype (TypedTerminalRule V M Sigma))
  binary_rules : Nonempty (Fintype (TypedBinaryRule V M))
  start_rules : Nonempty (Fintype (TypedStartRule V M))


/-- The typed state and rule universes are finite under finite input data. -/
theorem finiteTypedUniverses_of_finite
    (V : Type u) (M : Type v) (Sigma : Type w)
    [Fintype V] [Fintype M] [Fintype Sigma] :
    FiniteTypedUniverses V M Sigma := by
  exact
    { typed_states := ⟨inferInstance⟩,
      terminal_rules := ⟨inferInstance⟩,
      binary_rules := ⟨inferInstance⟩,
      start_rules := ⟨inferInstance⟩ }


/--
A kept subtype is finite when the ambient typed-state universe is finite and
membership in the kept predicate is decidable.
-/
noncomputable instance keptSubtypeFintype
    {V : Type u} {M : Type v}
    (Kept : TypedState V M → Prop)
    [Fintype V] [Fintype M] [DecidablePred Kept] :
    Fintype (KeptSubtype Kept) := by
  infer_instance


/-- Finiteness witness for kept typed states. -/
theorem keptSubtype_fintype_exists
    {V : Type u} {M : Type v}
    (Kept : TypedState V M → Prop)
    [Fintype V] [Fintype M] [DecidablePred Kept] :
    Nonempty (Fintype (KeptSubtype Kept)) := by
  exact ⟨inferInstance⟩


/-- Kept terminal rules are finite under finite input data. -/
noncomputable instance keptTerminalRuleFintype
    {V : Type u} {M : Type v} {Sigma : Type w}
    {Kept : TypedState V M → Prop}
    [Fintype V] [Fintype M] [Fintype Sigma] [DecidablePred Kept] :
    Fintype (KeptTerminalRule Kept Sigma) :=
  Fintype.ofEquiv (KeptSubtype Kept × Sigma)
    FiniteUniverseKernel.keptTerminalRuleEquivProduct.symm


/-- Kept binary rules are finite under finite input data. -/
noncomputable instance keptBinaryRuleFintype
    {V : Type u} {M : Type v}
    {Kept : TypedState V M → Prop}
    [Fintype V] [Fintype M] [DecidablePred Kept] :
    Fintype (KeptBinaryRule Kept) :=
  Fintype.ofEquiv ((KeptSubtype Kept × KeptSubtype Kept) ×
      KeptSubtype Kept)
    FiniteUniverseKernel.keptBinaryRuleEquivProduct.symm


/-- Kept start rules are finite under finite input data. -/
noncomputable instance keptStartRuleFintype
    {V : Type u} {M : Type v}
    {Kept : TypedState V M → Prop}
    [Fintype V] [Fintype M] [DecidablePred Kept] :
    Fintype (KeptStartRule Kept) :=
  Fintype.ofEquiv (KeptSubtype Kept)
    FiniteUniverseKernel.keptStartRuleEquivProduct.symm


/-- Packaged finite-universe witnesses for the kept-state construction. -/
structure FiniteKeptUniverses
    {V : Type u} {M : Type v} (Sigma : Type w)
    (Kept : TypedState V M → Prop) : Prop where
  kept_states : Nonempty (Fintype (KeptSubtype Kept))
  terminal_rules : Nonempty (Fintype (KeptTerminalRule Kept Sigma))
  binary_rules : Nonempty (Fintype (KeptBinaryRule Kept))
  start_rules : Nonempty (Fintype (KeptStartRule Kept))


/-- The kept-state universes are finite under finite input data. -/
theorem finiteKeptUniverses_of_finite
    {V : Type u} {M : Type v} (Sigma : Type w)
    (Kept : TypedState V M → Prop)
    [Fintype V] [Fintype M] [Fintype Sigma] [DecidablePred Kept] :
    FiniteKeptUniverses Sigma Kept := by
  exact
    { kept_states := ⟨inferInstance⟩,
      terminal_rules := ⟨inferInstance⟩,
      binary_rules := ⟨inferInstance⟩,
      start_rules := ⟨inferInstance⟩ }

end FiniteRepresentationKernel
end JALC
end LeanCfgProject
