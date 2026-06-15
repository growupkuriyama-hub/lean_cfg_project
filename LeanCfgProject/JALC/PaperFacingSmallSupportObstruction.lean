import LeanCfgProject.JALC.SmallSupportObstructionKernel

namespace LeanCfgProject
namespace JALC
namespace PaperFacingSmallSupportObstruction

/-
Paper-facing target for small-support finite obstructions.
-/

universe u

open FiniteClosureKernel
open FiniteUniverseListEnumerationKernel
open ListStabilityKernel
open BoundedListStabilitySearchKernel
open ListGrowthStabilizationKernel
open FreshFamilyFinEmbeddingKernel
open SmallSupportObstructionKernel


/-- Paper-facing empty support obstruction. -/
theorem checked_finEmbeddingImpossible_nil
    {α : Type u}
    (fuel : Nat) :
    FinEmbeddingImpossible ([] : List α) fuel :=
  finEmbeddingImpossible_nil fuel


/-- Paper-facing singleton support obstruction. -/
theorem checked_finEmbeddingImpossible_singleton
    {α : Type u}
    (a : α)
    {fuel : Nat}
    (hfuel : 1 ≤ fuel) :
    FinEmbeddingImpossible ([a] : List α) fuel :=
  finEmbeddingImpossible_singleton a hfuel


/-- Paper-facing bounded-search success from empty support. -/
theorem checked_boundedSearch_of_empty_support
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
    (hsupport : U.support = []) :
    ∃ W : ListStabilityWitness U F,
      findListStabilityWitness U F dec fuel = some W :=
  boundedSearch_of_empty_support
    U F mono dec fuel hsupport


/-- Paper-facing bounded-search success from singleton support. -/
theorem checked_boundedSearch_of_singleton_support
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
    (a : α)
    (hsupport : U.support = [a])
    (hfuel : 1 ≤ fuel) :
    ∃ W : ListStabilityWitness U F,
      findListStabilityWitness U F dec fuel = some W :=
  boundedSearch_of_singleton_support
    U F mono dec fuel a hsupport hfuel


/-- Paper-facing small-support obstruction routes to bounded-search success. -/
theorem checked_boundedSearch_of_smallSupportObstruction
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
    (H : SmallSupportObstruction U.support fuel) :
    ∃ W : ListStabilityWitness U F,
      findListStabilityWitness U F dec fuel = some W :=
  boundedSearch_of_smallSupportObstruction
    U F mono dec fuel H

end PaperFacingSmallSupportObstruction
end JALC
end LeanCfgProject
