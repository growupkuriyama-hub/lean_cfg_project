import LeanCfgProject.JALC.DoubletonSupportObstructionKernel

namespace LeanCfgProject
namespace JALC
namespace PaperFacingDoubletonSupportObstruction

/-
Paper-facing target for doubleton support obstruction.
-/

universe u

open FiniteClosureKernel
open FiniteUniverseListEnumerationKernel
open ListStabilityKernel
open BoundedListStabilitySearchKernel
open ListGrowthStabilizationKernel
open FreshFamilyFinEmbeddingKernel
open SmallSupportObstructionKernel
open DoubletonSupportObstructionKernel


/-- Paper-facing doubleton support obstruction. -/
theorem checked_finEmbeddingImpossible_doubleton
    {α : Type u}
    (a b : α)
    {fuel : Nat}
    (hfuel : 2 ≤ fuel) :
    FinEmbeddingImpossible ([a, b] : List α) fuel :=
  finEmbeddingImpossible_doubleton a b hfuel


/-- Paper-facing bounded-search success from doubleton support. -/
theorem checked_boundedSearch_of_doubleton_support
    {α : Type u}
    (U : UniverseList α)
    (F : (α → Prop) → α → Prop)
    (mono : PredMonotone F)
    (dec :
      ∀ k : Nat,
        Decidable
          (AgreeOnList U.support
            (F (Iter F k))
            (Iter F k)))
    (fuel : Nat)
    (a b : α)
    (hsupport : U.support = [a, b])
    (hfuel : 2 ≤ fuel) :
    ∃ W : ListStabilityWitness U F,
      findListStabilityWitness U F dec fuel = some W :=
  boundedSearch_of_doubleton_support
    U F mono dec fuel a b hsupport hfuel


/-- Paper-facing small-support obstruction from doubleton support. -/
theorem checked_smallSupportObstruction_doubleton
    {α : Type u}
    (a b : α)
    {fuel : Nat}
    (hfuel : 2 ≤ fuel) :
    SmallSupportObstruction ([a, b] : List α) fuel :=
  smallSupportObstruction_doubleton a b hfuel

end PaperFacingDoubletonSupportObstruction
end JALC
end LeanCfgProject
