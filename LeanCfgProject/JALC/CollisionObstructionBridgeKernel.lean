import LeanCfgProject.JALC.FreshFamilyFinEmbeddingKernel

namespace LeanCfgProject
namespace JALC
namespace CollisionObstructionBridgeKernel

/-
Collision obstruction bridge.

Fresh-family Fin embeddings are injective maps from `Fin (fuel+1)` into the
support list.  This file isolates the next finite-combinatorial interface:

  if every such finite-indexed map into the support has a collision, then no
  fresh-family Fin embedding exists.

The result is then routed back to the bounded-search and closure-certificate
pipeline.
-/

universe u

open FiniteClosureKernel
open FiniteUniverseListEnumerationKernel
open ListStabilityKernel
open BoundedListStabilitySearchKernel
open ListGrowthStabilizationKernel
open StrictGrowthCountingInterfaceKernel
open FreshFamilyFinEmbeddingKernel


/--
Every candidate finite-index embedding into `xs` has a collision.
-/
def FinEmbeddingCollisionProperty
    {α : Type u}
    (xs : List α)
    (fuel : Nat) : Prop :=
  ∀ E : FreshFamilyFinEmbedding xs fuel,
    ∃ i j : Fin (Nat.succ fuel),
      i ≠ j ∧ E.elem i = E.elem j


/--
A collision property rules out injective finite-index embeddings.
-/
theorem finEmbeddingImpossible_of_collisionProperty
    {α : Type u}
    {xs : List α}
    {fuel : Nat}
    (hcoll : FinEmbeddingCollisionProperty xs fuel) :
    FinEmbeddingImpossible xs fuel :=
  by
    intro E
    rcases hcoll E with ⟨i, j, hij, heq⟩
    exact hij (E.elem_injective heq)


/--
A collision property rules out fresh strict-growth families.
-/
theorem freshFamilyImpossible_of_collisionProperty
    {α : Type u}
    {xs : List α}
    {F : (α → Prop) → α → Prop}
    {fuel : Nat}
    (hcoll : FinEmbeddingCollisionProperty xs fuel) :
    FreshFamilyImpossible xs F fuel :=
  freshFamilyImpossible_of_finEmbeddingImpossible
    (finEmbeddingImpossible_of_collisionProperty hcoll)


/--
A collision property rules out full strict-growth runs.
-/
theorem not_strictGrowthRun_of_collisionProperty
    {α : Type u}
    {xs : List α}
    {F : (α → Prop) → α → Prop}
    {fuel : Nat}
    (mono : PredMonotone F)
    (hcoll : FinEmbeddingCollisionProperty xs fuel) :
    ¬ StrictGrowthRun xs F fuel :=
  not_strictGrowthRun_of_finEmbeddingImpossible
    mono
    (finEmbeddingImpossible_of_collisionProperty hcoll)


/--
A collision property yields a no-strict-growth certificate within the fuel.
-/
noncomputable def noStrictGrowthWithinBound_of_collisionProperty
    {α : Type u}
    (U : UniverseList α)
    (F : (α → Prop) → α → Prop)
    (fuel : Nat)
    (mono : PredMonotone F)
    (hcoll : FinEmbeddingCollisionProperty U.support fuel) :
    NoStrictGrowthWithinBound U F fuel :=
  noStrictGrowthWithinBound_of_not_strictGrowthRun
    U F fuel
    (not_strictGrowthRun_of_collisionProperty mono hcoll)


/--
A collision property is enough for bounded-search success.
-/
theorem boundedSearch_of_collisionProperty
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
  boundedSearch_of_finEmbeddingImpossible
    U F mono dec fuel
    (finEmbeddingImpossible_of_collisionProperty hcoll)


/--
A collision property gives both bounded-search success and the resulting
stability certificate.
-/
theorem closureCertificate_of_collisionProperty
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
  closureCertificate_of_freshFamilyImpossible
    U F mono dec fuel
    (freshFamilyImpossible_of_collisionProperty hcoll)


/--
A reusable package for finite collision obstructions.
-/
structure CollisionObstruction
    {α : Type u}
    (xs : List α)
    (fuel : Nat) : Prop where
  collision :
    FinEmbeddingCollisionProperty xs fuel


/--
A packaged collision obstruction rules out finite-index embeddings.
-/
theorem finEmbeddingImpossible_of_collisionObstruction
    {α : Type u}
    {xs : List α}
    {fuel : Nat}
    (H : CollisionObstruction xs fuel) :
    FinEmbeddingImpossible xs fuel :=
  finEmbeddingImpossible_of_collisionProperty H.collision


/--
A packaged collision obstruction yields bounded-search success.
-/
theorem boundedSearch_of_collisionObstruction
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
  boundedSearch_of_collisionProperty
    U F mono dec fuel H.collision


/--
A packaged collision obstruction yields a closure certificate.
-/
theorem closureCertificate_of_collisionObstruction
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
      findListStabilityWitness U F dec fuel = some W ∧
      StableAt F W.height :=
  closureCertificate_of_collisionProperty
    U F mono dec fuel H.collision

end CollisionObstructionBridgeKernel
end JALC
end LeanCfgProject
