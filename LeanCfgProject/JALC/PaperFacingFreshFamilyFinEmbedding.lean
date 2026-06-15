import LeanCfgProject.JALC.FreshFamilyFinEmbeddingKernel

namespace LeanCfgProject
namespace JALC
namespace PaperFacingFreshFamilyFinEmbedding

/-
Paper-facing target for fresh-family finite-index embeddings.
-/

universe u

open FiniteClosureKernel
open ListGrowthStabilizationKernel
open StrictGrowthWitnessFreshnessKernel
open StrictGrowthCountingInterfaceKernel
open FreshFamilyFinEmbeddingKernel


/-- Paper-facing finite-index height is below the fuel. -/
theorem checked_fin_height_le_fuel
    (fuel : Nat)
    (i : Fin (Nat.succ fuel)) :
    i.val ≤ fuel :=
  fin_height_le_fuel fuel i


/-- Paper-facing finite-indexed witness membership. -/
theorem checked_freshFamilyFinElem_mem
    {α : Type u}
    {xs : List α}
    {F : (α → Prop) → α → Prop}
    {fuel : Nat}
    (Fam : FreshStrictGrowthFamily xs F fuel)
    (i : Fin (Nat.succ fuel)) :
    freshFamilyFinElem Fam i ∈ xs :=
  freshFamilyFinElem_mem Fam i


/-- Paper-facing different finite indices select different support elements. -/
theorem checked_freshFamilyFinElem_ne_of_ne
    {α : Type u}
    {xs : List α}
    {F : (α → Prop) → α → Prop}
    {fuel : Nat}
    (Fam : FreshStrictGrowthFamily xs F fuel)
    {i j : Fin (Nat.succ fuel)}
    (hij : i ≠ j) :
    freshFamilyFinElem Fam i ≠ freshFamilyFinElem Fam j :=
  freshFamilyFinElem_ne_of_ne Fam hij


/-- Paper-facing fresh family gives an injective finite-indexed map. -/
theorem checked_freshFamilyFinElem_injective
    {α : Type u}
    {xs : List α}
    {F : (α → Prop) → α → Prop}
    {fuel : Nat}
    (Fam : FreshStrictGrowthFamily xs F fuel) :
    Function.Injective (freshFamilyFinElem Fam) :=
  freshFamilyFinElem_injective Fam


/-- Paper-facing construction of a finite-index embedding from a fresh family. -/
def checked_finEmbedding_of_freshFamily
    {α : Type u}
    {xs : List α}
    {F : (α → Prop) → α → Prop}
    {fuel : Nat}
    (Fam : FreshStrictGrowthFamily xs F fuel) :
    FreshFamilyFinEmbedding xs fuel :=
  finEmbedding_of_freshFamily Fam


/-- Paper-facing finite-index embedding obstruction rules out fresh families. -/
theorem checked_freshFamilyImpossible_of_finEmbeddingImpossible
    {α : Type u}
    {xs : List α}
    {F : (α → Prop) → α → Prop}
    {fuel : Nat}
    (himp : FinEmbeddingImpossible xs fuel) :
    FreshFamilyImpossible xs F fuel :=
  freshFamilyImpossible_of_finEmbeddingImpossible himp


/-- Paper-facing finite-index embedding obstruction gives bounded-search success. -/
theorem checked_boundedSearch_of_finEmbeddingImpossible
    {α : Type u}
    (U : FiniteUniverseListEnumerationKernel.UniverseList α)
    (F : (α → Prop) → α → Prop)
    (mono : PredMonotone F)
    (dec :
      ∀ k : Nat,
        Decidable
          (ListStabilityKernel.AgreeOnList U.support
            (F (FiniteClosureKernel.Iter F k))
            (FiniteClosureKernel.Iter F k)))
    (fuel : Nat)
    (himp : FinEmbeddingImpossible U.support fuel) :
    ∃ W : ListStabilityKernel.ListStabilityWitness U F,
      BoundedListStabilitySearchKernel.findListStabilityWitness
        U F dec fuel = some W :=
  boundedSearch_of_finEmbeddingImpossible
    U F mono dec fuel himp

end PaperFacingFreshFamilyFinEmbedding
end JALC
end LeanCfgProject
