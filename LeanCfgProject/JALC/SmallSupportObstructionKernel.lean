import LeanCfgProject.JALC.FreshFamilyFinEmbeddingKernel

namespace LeanCfgProject
namespace JALC
namespace SmallSupportObstructionKernel

/-
Small-support finite obstructions.

The fresh-family Fin embedding bridge reduced the remaining finite-support
counting issue to impossibility of injections from `Fin (fuel+1)` into a short
support list.  This file proves the first concrete finite cases:

  support = []
  support = [a] and fuel >= 1

and routes them back to bounded-search success.
-/

universe u

open FiniteClosureKernel
open FiniteUniverseListEnumerationKernel
open ListStabilityKernel
open BoundedListStabilitySearchKernel
open ListGrowthStabilizationKernel
open StrictGrowthWitnessFreshnessKernel
open StrictGrowthCountingInterfaceKernel
open FreshFamilyFinEmbeddingKernel


/-- No finite-index embedding can land in the empty support list. -/
theorem finEmbeddingImpossible_nil
    {α : Type u}
    (fuel : Nat) :
    FinEmbeddingImpossible ([] : List α) fuel :=
  by
    intro E
    let i0 : Fin (Nat.succ fuel) := ⟨0, Nat.succ_pos fuel⟩
    have hmem : E.elem i0 ∈ ([] : List α) := E.elem_mem i0
    cases hmem


/--
If a universe list has empty support, the bounded search succeeds immediately
from the finite-index obstruction.
-/
theorem boundedSearch_of_empty_support
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
  boundedSearch_of_finEmbeddingImpossible
    U F mono dec fuel
    (by
      intro E
      let i0 : Fin (Nat.succ fuel) := ⟨0, Nat.succ_pos fuel⟩
      have hmem : E.elem i0 ∈ ([] : List α) := by
        simpa [hsupport] using E.elem_mem i0
      cases hmem)


/--
No embedding from a domain with at least two finite indices can land injectively
in a singleton support list.
-/
theorem finEmbeddingImpossible_singleton
    {α : Type u}
    (a : α)
    {fuel : Nat}
    (hfuel : 1 ≤ fuel) :
    FinEmbeddingImpossible ([a] : List α) fuel :=
  by
    intro E
    let i0 : Fin (Nat.succ fuel) := ⟨0, Nat.succ_pos fuel⟩
    let i1 : Fin (Nat.succ fuel) := ⟨1, Nat.lt_succ_of_le hfuel⟩
    have h0mem : E.elem i0 ∈ ([a] : List α) := E.elem_mem i0
    have h1mem : E.elem i1 ∈ ([a] : List α) := E.elem_mem i1
    have h0 : E.elem i0 = a := by
      simpa using h0mem
    have h1 : E.elem i1 = a := by
      simpa using h1mem
    have heq : E.elem i0 = E.elem i1 := by
      rw [h0, h1]
    have hidx : i0 = i1 := E.elem_injective heq
    have hval : (0 : Nat) = 1 := by
      exact congrArg Fin.val hidx
    cases hval


/--
If a universe list has singleton support and the fuel is at least one, bounded
search succeeds.
-/
theorem boundedSearch_of_singleton_support
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
  boundedSearch_of_finEmbeddingImpossible
    U F mono dec fuel
    (by
      intro E
      have himp : FinEmbeddingImpossible ([a] : List α) fuel :=
        finEmbeddingImpossible_singleton a hfuel
      exact
        himp
          { elem := E.elem,
            elem_mem :=
              by
                intro i
                simpa [hsupport] using E.elem_mem i,
            elem_injective := E.elem_injective })


/--
A reusable small-support obstruction package.
-/
structure SmallSupportObstruction
    {α : Type u}
    (xs : List α)
    (fuel : Nat) : Prop where
  impossible :
    FinEmbeddingImpossible xs fuel


/-- Empty support gives the small-support obstruction. -/
theorem smallSupportObstruction_nil
    {α : Type u}
    (fuel : Nat) :
    SmallSupportObstruction ([] : List α) fuel :=
  ⟨finEmbeddingImpossible_nil fuel⟩


/-- Singleton support gives the small-support obstruction for fuel at least one. -/
theorem smallSupportObstruction_singleton
    {α : Type u}
    (a : α)
    {fuel : Nat}
    (hfuel : 1 ≤ fuel) :
    SmallSupportObstruction ([a] : List α) fuel :=
  ⟨finEmbeddingImpossible_singleton a hfuel⟩


/--
Any small-support obstruction routes to bounded-search success.
-/
theorem boundedSearch_of_smallSupportObstruction
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
  boundedSearch_of_finEmbeddingImpossible
    U F mono dec fuel H.impossible

end SmallSupportObstructionKernel
end JALC
end LeanCfgProject
