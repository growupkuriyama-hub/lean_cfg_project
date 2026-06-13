import LeanCfgProject.JALC.PaperFacingFinite

namespace LeanCfgProject
namespace JALC
namespace FiniteCardinalityKernel

/-
Cardinality kernels for the finite typed universes.

This module records that the typed-state and rule universes are not merely
finite: they are equivalent to explicit finite product universes.
-/

universe u v w

open InverseKernel RoundTripKernel
open KeptStateKernel KeptStructureKernel
open FiniteUniverseKernel FiniteRepresentationKernel


/-- Cardinality of typed states, expressed by the explicit product universe. -/
theorem typedState_card_product
    {V : Type u} {M : Type v} [Fintype V] [Fintype M] :
    Fintype.card (TypedState V M) =
      Fintype.card (((V × M) × M) × M) :=
  Fintype.card_congr typedStateEquivProduct


/-- Cardinality of terminal rules, expressed by the explicit product universe. -/
theorem terminalRule_card_product
    {V : Type u} {Sigma : Type w} [Fintype V] [Fintype Sigma] :
    Fintype.card (TerminalRule V Sigma) =
      Fintype.card (V × Sigma) :=
  Fintype.card_congr terminalRuleEquivProduct


/-- Cardinality of binary rules, expressed by the explicit product universe. -/
theorem binaryRule_card_product
    {V : Type u} [Fintype V] :
    Fintype.card (BinaryRule V) =
      Fintype.card ((V × V) × V) :=
  Fintype.card_congr binaryRuleEquivProduct


/-- Cardinality of start declarations, expressed by the state universe. -/
theorem startRule_card_product
    {V : Type u} [Fintype V] :
    Fintype.card (StartRule V) =
      Fintype.card V :=
  Fintype.card_congr startRuleEquivProduct


/-- Cardinality of typed terminal rules. -/
theorem typedTerminalRule_card_product
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Fintype V] [Fintype M] [Fintype Sigma] :
    Fintype.card (TypedTerminalRule V M Sigma) =
      Fintype.card (TypedState V M × Sigma) :=
  Fintype.card_congr typedTerminalRuleEquivProduct


/-- Cardinality of typed binary rules. -/
theorem typedBinaryRule_card_product
    {V : Type u} {M : Type v} [Fintype V] [Fintype M] :
    Fintype.card (TypedBinaryRule V M) =
      Fintype.card ((TypedState V M × TypedState V M) ×
        TypedState V M) :=
  Fintype.card_congr typedBinaryRuleEquivProduct


/-- Cardinality of typed start declarations. -/
theorem typedStartRule_card_product
    {V : Type u} {M : Type v} [Fintype V] [Fintype M] :
    Fintype.card (TypedStartRule V M) =
      Fintype.card (TypedState V M) :=
  Fintype.card_congr typedStartRuleEquivProduct


/-- Cardinality of kept terminal rules. -/
theorem keptTerminalRule_card_product
    {V : Type u} {M : Type v} {Sigma : Type w}
    {Kept : TypedState V M → Prop}
    [Fintype V] [Fintype M] [Fintype Sigma] [DecidablePred Kept] :
    Fintype.card (KeptTerminalRule Kept Sigma) =
      Fintype.card (KeptSubtype Kept × Sigma) :=
  Fintype.card_congr keptTerminalRuleEquivProduct


/-- Cardinality of kept binary rules. -/
theorem keptBinaryRule_card_product
    {V : Type u} {M : Type v}
    {Kept : TypedState V M → Prop}
    [Fintype V] [Fintype M] [DecidablePred Kept] :
    Fintype.card (KeptBinaryRule Kept) =
      Fintype.card ((KeptSubtype Kept × KeptSubtype Kept) ×
        KeptSubtype Kept) :=
  Fintype.card_congr keptBinaryRuleEquivProduct


/-- Cardinality of kept start declarations. -/
theorem keptStartRule_card_product
    {V : Type u} {M : Type v}
    {Kept : TypedState V M → Prop}
    [Fintype V] [Fintype M] [DecidablePred Kept] :
    Fintype.card (KeptStartRule Kept) =
      Fintype.card (KeptSubtype Kept) :=
  Fintype.card_congr keptStartRuleEquivProduct


/--
Packaged finite-cardinality kernel for typed states and typed rules.
-/
theorem typed_cardinality_kernel
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Fintype V] [Fintype M] [Fintype Sigma] :
    Fintype.card (TypedState V M) =
      Fintype.card (((V × M) × M) × M) ∧
    Fintype.card (TypedTerminalRule V M Sigma) =
      Fintype.card (TypedState V M × Sigma) ∧
    Fintype.card (TypedBinaryRule V M) =
      Fintype.card ((TypedState V M × TypedState V M) ×
        TypedState V M) ∧
    Fintype.card (TypedStartRule V M) =
      Fintype.card (TypedState V M) := by
  exact ⟨typedState_card_product,
    typedTerminalRule_card_product,
    typedBinaryRule_card_product,
    typedStartRule_card_product⟩


/--
Packaged finite-cardinality kernel for kept states and kept rules.
-/
theorem kept_cardinality_kernel
    {V : Type u} {M : Type v} {Sigma : Type w}
    {Kept : TypedState V M → Prop}
    [Fintype V] [Fintype M] [Fintype Sigma] [DecidablePred Kept] :
    Fintype.card (KeptTerminalRule Kept Sigma) =
      Fintype.card (KeptSubtype Kept × Sigma) ∧
    Fintype.card (KeptBinaryRule Kept) =
      Fintype.card ((KeptSubtype Kept × KeptSubtype Kept) ×
        KeptSubtype Kept) ∧
    Fintype.card (KeptStartRule Kept) =
      Fintype.card (KeptSubtype Kept) := by
  exact ⟨keptTerminalRule_card_product,
    keptBinaryRule_card_product,
    keptStartRule_card_product⟩

end FiniteCardinalityKernel
end JALC
end LeanCfgProject
