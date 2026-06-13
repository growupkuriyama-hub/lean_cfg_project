import LeanCfgProject.JALC.FiniteRepresentationKernel

namespace LeanCfgProject
namespace JALC
namespace PaperFacingFinite

/-
Paper-facing finite representation checks.
-/

universe u v w

open InverseKernel RoundTripKernel
open FiniteRepresentationKernel


/-- Paper-facing finite-universe statement for typed states and typed rules. -/
theorem checked_finite_typed_universes
    (V : Type u) (M : Type v) (Sigma : Type w)
    [Fintype V] [Fintype M] [Fintype Sigma] :
    FiniteTypedUniverses V M Sigma :=
  finiteTypedUniverses_of_finite V M Sigma


/-- Paper-facing finite-universe statement for kept states and kept rules. -/
theorem checked_finite_kept_universes
    {V : Type u} {M : Type v} (Sigma : Type w)
    (Kept : TypedState V M → Prop)
    [Fintype V] [Fintype M] [Fintype Sigma] [DecidablePred Kept] :
    FiniteKeptUniverses Sigma Kept :=
  finiteKeptUniverses_of_finite Sigma Kept

end PaperFacingFinite
end JALC
end LeanCfgProject
