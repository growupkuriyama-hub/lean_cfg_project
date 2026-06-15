import LeanCfgProject.JALC.CollisionObstructionBridgeKernel

namespace LeanCfgProject
namespace JALC
namespace PaperFacingCollisionObstructionBridge

/-
Paper-facing target for the collision obstruction bridge.
-/

universe u

open FiniteClosureKernel
open FiniteUniverseListEnumerationKernel
open ListStabilityKernel
open BoundedListStabilitySearchKernel
open ListGrowthStabilizationKernel
open StrictGrowthCountingInterfaceKernel
open FreshFamilyFinEmbeddingKernel
open CollisionObstructionBridgeKernel


/-- Paper-facing collision property rules out finite-index embeddings. -/
theorem checked_finEmbeddingImpossible_of_collisionProperty
    {α : Type u}
    {xs : List α}
    {fuel : Nat}
    (hcoll : FinEmbeddingCollisionProperty xs fuel) :
    FinEmbeddingImpossible xs fuel :=
  finEmbeddingImpossible_of_collisionProperty hcoll


/-- Paper-facing collision property rules out fresh families. -/
theorem checked_freshFamilyImpossible_of_collisionProperty
    {α : Type u}
    {xs : List α}
    {F : (α → Prop) → α → Prop}
    {fuel : Nat}
    (hcoll : FinEmbeddingCollisionProperty xs fuel) :
    FreshFamilyImpossible xs F fuel :=
  freshFamilyImpossible_of_collisionProperty hcoll


/-- Paper-facing collision property yields no-strict-growth within fuel. -/
noncomputable def checked_noStrictGrowthWithinBound_of_collisionProperty
    {α : Type u}
    (U : UniverseList α)
    (F : (α → Prop) → α → Prop)
    (fuel : Nat)
    (mono : PredMonotone F)
    (hcoll : FinEmbeddingCollisionProperty U.support fuel) :
    NoStrictGrowthWithinBound U F fuel :=
  noStrictGrowthWithinBound_of_collisionProperty
    U F fuel mono hcoll


/-- Paper-facing collision property gives bounded-search success. -/
theorem checked_boundedSearch_of_collisionProperty
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
    (hcoll : FinEmbeddingCollisionProperty U.support fuel) :
    ∃ W : ListStabilityWitness U F,
      findListStabilityWitness U F dec fuel = some W :=
  boundedSearch_of_collisionProperty
    U F mono dec fuel hcoll


/-- Paper-facing collision property gives a closure certificate. -/
theorem checked_closureCertificate_of_collisionProperty
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
    (hcoll : FinEmbeddingCollisionProperty U.support fuel) :
    ∃ W : ListStabilityWitness U F,
      findListStabilityWitness U F dec fuel = some W ∧
      StableAt F W.height :=
  closureCertificate_of_collisionProperty
    U F mono dec fuel hcoll


/-- Paper-facing packaged collision obstruction gives bounded-search success. -/
theorem checked_boundedSearch_of_collisionObstruction
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
    (H : CollisionObstruction U.support fuel) :
    ∃ W : ListStabilityWitness U F,
      findListStabilityWitness U F dec fuel = some W :=
  boundedSearch_of_collisionObstruction
    U F mono dec fuel H

end PaperFacingCollisionObstructionBridge
end JALC
end LeanCfgProject
