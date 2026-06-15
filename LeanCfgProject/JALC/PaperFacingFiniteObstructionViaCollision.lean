import LeanCfgProject.JALC.FiniteObstructionViaCollisionKernel

namespace LeanCfgProject
namespace JALC
namespace PaperFacingFiniteObstructionViaCollision

/-
Paper-facing target for finite obstructions routed through collision.
-/

universe u

open FiniteClosureKernel
open FiniteUniverseListEnumerationKernel
open ListStabilityKernel
open BoundedListStabilitySearchKernel
open ListGrowthStabilizationKernel
open FreshFamilyFinEmbeddingKernel
open CollisionObstructionBridgeKernel
open FiniteObstructionViaCollisionKernel


/-- Paper-facing impossibility-to-collision bridge. -/
theorem checked_collisionObstruction_of_finEmbeddingImpossible
    {α : Type u}
    {xs : List α}
    {fuel : Nat}
    (himp : FinEmbeddingImpossible xs fuel) :
    CollisionObstruction xs fuel :=
  collisionObstruction_of_finEmbeddingImpossible himp


/-- Paper-facing support equality transports collision obstructions. -/
theorem checked_collisionObstruction_of_support_eq
    {α : Type u}
    {xs ys : List α}
    {fuel : Nat}
    (hxy : xs = ys)
    (H : CollisionObstruction ys fuel) :
    CollisionObstruction xs fuel :=
  collisionObstruction_of_support_eq hxy H


/-- Paper-facing bounded-search success via collision from embedding impossibility. -/
theorem checked_boundedSearch_of_finEmbeddingImpossible_via_collision
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
    (himp : FinEmbeddingImpossible U.support fuel) :
    ∃ W : ListStabilityWitness U F,
      findListStabilityWitness U F dec fuel = some W :=
  boundedSearch_of_finEmbeddingImpossible_via_collision
    U F mono dec fuel himp


/-- Paper-facing closure certificate via collision from embedding impossibility. -/
theorem checked_closureCertificate_of_finEmbeddingImpossible_via_collision
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
    (himp : FinEmbeddingImpossible U.support fuel) :
    ∃ W : ListStabilityWitness U F,
      findListStabilityWitness U F dec fuel = some W ∧
      StableAt F W.height :=
  closureCertificate_of_finEmbeddingImpossible_via_collision
    U F mono dec fuel himp


/-- Paper-facing empty support as a collision obstruction. -/
theorem checked_collisionObstruction_nil
    {α : Type u}
    (fuel : Nat) :
    CollisionObstruction ([] : List α) fuel :=
  collisionObstruction_nil fuel


/-- Paper-facing singleton support as a collision obstruction. -/
theorem checked_collisionObstruction_singleton
    {α : Type u}
    (a : α)
    {fuel : Nat}
    (hfuel : 1 ≤ fuel) :
    CollisionObstruction ([a] : List α) fuel :=
  collisionObstruction_singleton a hfuel


/-- Paper-facing doubleton support as a collision obstruction. -/
theorem checked_collisionObstruction_doubleton
    {α : Type u}
    (a b : α)
    {fuel : Nat}
    (hfuel : 2 ≤ fuel) :
    CollisionObstruction ([a, b] : List α) fuel :=
  collisionObstruction_doubleton a b hfuel


/-- Paper-facing doubleton bounded-search success through collision. -/
theorem checked_boundedSearch_doubleton_via_collision
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
  boundedSearch_doubleton_via_collision
    U F mono dec fuel a b hsupport hfuel

end PaperFacingFiniteObstructionViaCollision
end JALC
end LeanCfgProject
