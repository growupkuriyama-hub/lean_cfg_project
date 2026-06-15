import LeanCfgProject.JALC.CollisionObstructionBridgeKernel
import LeanCfgProject.JALC.DoubletonSupportObstructionKernel

namespace LeanCfgProject
namespace JALC
namespace FiniteObstructionViaCollisionKernel

/-
Finite obstruction via collision.

Earlier targets proved concrete finite-list obstructions directly as
`FinEmbeddingImpossible`.  The collision bridge introduced a uniform interface:
prove that every candidate finite-indexed map has a collision, and bounded
search follows.

This file connects the two interfaces:

  FinEmbeddingImpossible
  => CollisionObstruction
  => bounded search success
  => closure certificate.

It then packages the empty, singleton, and doubleton support cases in the new
collision-obstruction form.
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
open SmallSupportObstructionKernel
open DoubletonSupportObstructionKernel


/--
An outright finite-index embedding impossibility gives the collision property
vacuously.
-/
theorem collisionProperty_of_finEmbeddingImpossible
    {α : Type u}
    {xs : List α}
    {fuel : Nat}
    (himp : FinEmbeddingImpossible xs fuel) :
    FinEmbeddingCollisionProperty xs fuel :=
  by
    intro E
    exact False.elim (himp E)


/--
An outright finite-index embedding impossibility gives a packaged collision
obstruction.
-/
theorem collisionObstruction_of_finEmbeddingImpossible
    {α : Type u}
    {xs : List α}
    {fuel : Nat}
    (himp : FinEmbeddingImpossible xs fuel) :
    CollisionObstruction xs fuel :=
  ⟨collisionProperty_of_finEmbeddingImpossible himp⟩


/--
Any finite-index embedding impossibility routes through the collision bridge to
bounded-search success.
-/
theorem boundedSearch_of_finEmbeddingImpossible_via_collision
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
  boundedSearch_of_collisionObstruction
    U F mono dec fuel
    (collisionObstruction_of_finEmbeddingImpossible himp)


/--
Any finite-index embedding impossibility routes through the collision bridge to
a closure certificate.
-/
theorem closureCertificate_of_finEmbeddingImpossible_via_collision
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
  closureCertificate_of_collisionObstruction
    U F mono dec fuel
    (collisionObstruction_of_finEmbeddingImpossible himp)


/-- Empty support as a collision obstruction. -/
theorem collisionObstruction_nil
    {α : Type u}
    (fuel : Nat) :
    CollisionObstruction ([] : List α) fuel :=
  collisionObstruction_of_finEmbeddingImpossible
    (finEmbeddingImpossible_nil fuel)


/-- Singleton support as a collision obstruction for fuel at least one. -/
theorem collisionObstruction_singleton
    {α : Type u}
    (a : α)
    {fuel : Nat}
    (hfuel : 1 ≤ fuel) :
    CollisionObstruction ([a] : List α) fuel :=
  collisionObstruction_of_finEmbeddingImpossible
    (finEmbeddingImpossible_singleton a hfuel)


/-- Doubleton support as a collision obstruction for fuel at least two. -/
theorem collisionObstruction_doubleton
    {α : Type u}
    (a b : α)
    {fuel : Nat}
    (hfuel : 2 ≤ fuel) :
    CollisionObstruction ([a, b] : List α) fuel :=
  collisionObstruction_of_finEmbeddingImpossible
    (finEmbeddingImpossible_doubleton a b hfuel)


/--
Empty support gives bounded-search success through the collision interface.
-/
theorem boundedSearch_nil_via_collision
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
  boundedSearch_of_collisionObstruction
    U F mono dec fuel
    (by
      cases hsupport
      exact collisionObstruction_nil fuel)


/--
Singleton support gives bounded-search success through the collision interface.
-/
theorem boundedSearch_singleton_via_collision
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
  boundedSearch_of_collisionObstruction
    U F mono dec fuel
    (by
      cases hsupport
      exact collisionObstruction_singleton a hfuel)


/--
Doubleton support gives bounded-search success through the collision interface.
-/
theorem boundedSearch_doubleton_via_collision
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
  boundedSearch_of_collisionObstruction
    U F mono dec fuel
    (by
      cases hsupport
      exact collisionObstruction_doubleton a b hfuel)

end FiniteObstructionViaCollisionKernel
end JALC
end LeanCfgProject
