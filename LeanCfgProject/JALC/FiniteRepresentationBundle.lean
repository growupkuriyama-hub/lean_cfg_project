import LeanCfgProject.JALC.PaperFacingCardinality

namespace LeanCfgProject
namespace JALC
namespace FiniteRepresentationBundle

/-
A compact bundle collecting the finite representation checks.
-/

universe u v w

open InverseKernel RoundTripKernel
open KeptStateKernel KeptStructureKernel
open FiniteRepresentationKernel FiniteCardinalityKernel


/-- Bundle of finite representation data for typed universes. -/
structure TypedFiniteBundle
    (V : Type u) (M : Type v) (Sigma : Type w) : Prop where
  finite_universes :
    FiniteTypedUniverses V M Sigma
  card_kernel :
    Fintype.card (TypedState V M) =
      Fintype.card (((V × M) × M) × M) ∧
    Fintype.card (TypedTerminalRule V M Sigma) =
      Fintype.card (TypedState V M × Sigma) ∧
    Fintype.card (TypedBinaryRule V M) =
      Fintype.card ((TypedState V M × TypedState V M) ×
        TypedState V M) ∧
    Fintype.card (TypedStartRule V M) =
      Fintype.card (TypedState V M)


/-- Bundle of finite representation data for kept universes. -/
structure KeptFiniteBundle
    {V : Type u} {M : Type v} (Sigma : Type w)
    (Kept : TypedState V M → Prop) : Prop where
  finite_universes :
    FiniteKeptUniverses Sigma Kept
  card_kernel :
    Fintype.card (KeptTerminalRule Kept Sigma) =
      Fintype.card (KeptSubtype Kept × Sigma) ∧
    Fintype.card (KeptBinaryRule Kept) =
      Fintype.card ((KeptSubtype Kept × KeptSubtype Kept) ×
        KeptSubtype Kept) ∧
    Fintype.card (KeptStartRule Kept) =
      Fintype.card (KeptSubtype Kept)


/-- The typed finite bundle follows from finite input data. -/
theorem typedFiniteBundle_of_finite
    (V : Type u) (M : Type v) (Sigma : Type w)
    [Fintype V] [Fintype M] [Fintype Sigma] :
    TypedFiniteBundle V M Sigma := by
  exact
    { finite_universes := finiteTypedUniverses_of_finite V M Sigma,
      card_kernel := typed_cardinality_kernel }


/-- The kept finite bundle follows from finite input data and decidable keptness. -/
theorem keptFiniteBundle_of_finite
    {V : Type u} {M : Type v} (Sigma : Type w)
    (Kept : TypedState V M → Prop)
    [Fintype V] [Fintype M] [Fintype Sigma] [DecidablePred Kept] :
    KeptFiniteBundle Sigma Kept := by
  exact
    { finite_universes := finiteKeptUniverses_of_finite Sigma Kept,
      card_kernel := kept_cardinality_kernel }

end FiniteRepresentationBundle
end JALC
end LeanCfgProject
