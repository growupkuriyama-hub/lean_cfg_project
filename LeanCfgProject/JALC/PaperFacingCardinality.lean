import LeanCfgProject.JALC.FiniteCardinalityKernel

namespace LeanCfgProject
namespace JALC
namespace PaperFacingCardinality

/-
Paper-facing cardinality checks for finite representation.
-/

universe u v w

open InverseKernel RoundTripKernel
open KeptStateKernel KeptStructureKernel
open FiniteCardinalityKernel


/-- Paper-facing finite-cardinality kernel for typed universes. -/
theorem checked_typed_cardinality_kernel
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
      Fintype.card (TypedState V M) :=
  typed_cardinality_kernel


/-- Paper-facing finite-cardinality kernel for kept universes. -/
theorem checked_kept_cardinality_kernel
    {V : Type u} {M : Type v} {Sigma : Type w}
    {Kept : TypedState V M → Prop}
    [Fintype V] [Fintype M] [Fintype Sigma] [DecidablePred Kept] :
    Fintype.card (KeptTerminalRule Kept Sigma) =
      Fintype.card (KeptSubtype Kept × Sigma) ∧
    Fintype.card (KeptBinaryRule Kept) =
      Fintype.card ((KeptSubtype Kept × KeptSubtype Kept) ×
        KeptSubtype Kept) ∧
    Fintype.card (KeptStartRule Kept) =
      Fintype.card (KeptSubtype Kept) :=
  kept_cardinality_kernel

end PaperFacingCardinality
end JALC
end LeanCfgProject
