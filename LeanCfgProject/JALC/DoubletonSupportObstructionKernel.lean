import LeanCfgProject.JALC.SmallSupportObstructionKernel

namespace LeanCfgProject
namespace JALC
namespace DoubletonSupportObstructionKernel

/-
Doubleton support obstruction.

The previous small-support target handled empty and singleton supports.  This
file adds the next concrete finite-list obstruction:

  support = [a, b] and fuel >= 2
  => no injective map Fin (fuel+1) into the support list
  => bounded search succeeds.
-/

universe u

open FiniteClosureKernel
open FiniteUniverseListEnumerationKernel
open ListStabilityKernel
open BoundedListStabilitySearchKernel
open ListGrowthStabilizationKernel
open FreshFamilyFinEmbeddingKernel
open SmallSupportObstructionKernel


/-- Two different finite indices 0 and 1 are distinct. -/
theorem fin_zero_ne_one_of_two_le
    {fuel : Nat}
    (hfuel : 1 ≤ fuel) :
    (⟨0, Nat.succ_pos fuel⟩ : Fin (Nat.succ fuel)) ≠
      (⟨1, Nat.lt_succ_of_le hfuel⟩ : Fin (Nat.succ fuel)) :=
  by
    intro h
    have hval : (0 : Nat) = 1 := congrArg Fin.val h
    cases hval


/-- Two different finite indices 0 and 2 are distinct. -/
theorem fin_zero_ne_two_of_three_le
    {fuel : Nat}
    (hfuel : 2 ≤ fuel) :
    (⟨0, Nat.succ_pos fuel⟩ : Fin (Nat.succ fuel)) ≠
      (⟨2, Nat.lt_succ_of_le hfuel⟩ : Fin (Nat.succ fuel)) :=
  by
    intro h
    have hval : (0 : Nat) = 2 := congrArg Fin.val h
    cases hval


/-- Two different finite indices 1 and 2 are distinct. -/
theorem fin_one_ne_two_of_three_le
    {fuel : Nat}
    (hfuel : 2 ≤ fuel) :
    (⟨1, Nat.lt_succ_of_le (Nat.le_trans (by decide : 1 ≤ 2) hfuel)⟩ :
        Fin (Nat.succ fuel)) ≠
      (⟨2, Nat.lt_succ_of_le hfuel⟩ : Fin (Nat.succ fuel)) :=
  by
    intro h
    have hval : (1 : Nat) = 2 := congrArg Fin.val h
    cases hval


/-- No embedding from at least three finite indices can land injectively in a doubleton list. -/
theorem finEmbeddingImpossible_doubleton
    {α : Type u}
    (a b : α)
    {fuel : Nat}
    (hfuel : 2 ≤ fuel) :
    FinEmbeddingImpossible ([a, b] : List α) fuel :=
  by
    intro E
    let i0 : Fin (Nat.succ fuel) := ⟨0, Nat.succ_pos fuel⟩
    let i1 : Fin (Nat.succ fuel) :=
      ⟨1, Nat.lt_succ_of_le (Nat.le_trans (by decide : 1 ≤ 2) hfuel)⟩
    let i2 : Fin (Nat.succ fuel) := ⟨2, Nat.lt_succ_of_le hfuel⟩
    have h01 : i0 ≠ i1 := by
      intro h
      have hval : (0 : Nat) = 1 := congrArg Fin.val h
      cases hval
    have h02 : i0 ≠ i2 := by
      intro h
      have hval : (0 : Nat) = 2 := congrArg Fin.val h
      cases hval
    have h12 : i1 ≠ i2 := by
      intro h
      have hval : (1 : Nat) = 2 := congrArg Fin.val h
      cases hval
    have h0mem : E.elem i0 ∈ ([a, b] : List α) := E.elem_mem i0
    have h1mem : E.elem i1 ∈ ([a, b] : List α) := E.elem_mem i1
    have h2mem : E.elem i2 ∈ ([a, b] : List α) := E.elem_mem i2
    have h0cases : E.elem i0 = a ∨ E.elem i0 = b := by
      simpa using h0mem
    have h1cases : E.elem i1 = a ∨ E.elem i1 = b := by
      simpa using h1mem
    have h2cases : E.elem i2 = a ∨ E.elem i2 = b := by
      simpa using h2mem
    rcases h0cases with h0a | h0b
    · rcases h1cases with h1a | h1b
      · have heq : E.elem i0 = E.elem i1 := by
          rw [h0a, h1a]
        exact h01 (E.elem_injective heq)
      · rcases h2cases with h2a | h2b
        · have heq : E.elem i0 = E.elem i2 := by
            rw [h0a, h2a]
          exact h02 (E.elem_injective heq)
        · have heq : E.elem i1 = E.elem i2 := by
            rw [h1b, h2b]
          exact h12 (E.elem_injective heq)
    · rcases h1cases with h1a | h1b
      · rcases h2cases with h2a | h2b
        · have heq : E.elem i1 = E.elem i2 := by
            rw [h1a, h2a]
          exact h12 (E.elem_injective heq)
        · have heq : E.elem i0 = E.elem i2 := by
            rw [h0b, h2b]
          exact h02 (E.elem_injective heq)
      · have heq : E.elem i0 = E.elem i1 := by
          rw [h0b, h1b]
        exact h01 (E.elem_injective heq)


/--
If a universe list has doubleton support and fuel is at least two, bounded
search succeeds.
-/
theorem boundedSearch_of_doubleton_support
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
  boundedSearch_of_finEmbeddingImpossible
    U F mono dec fuel
    (by
      intro E
      have himp : FinEmbeddingImpossible ([a, b] : List α) fuel :=
        finEmbeddingImpossible_doubleton a b hfuel
      exact
        himp
          { elem := E.elem,
            elem_mem :=
              by
                intro i
                simpa [hsupport] using E.elem_mem i,
            elem_injective := E.elem_injective })


/-- Doubleton support gives the small-support obstruction for fuel at least two. -/
theorem smallSupportObstruction_doubleton
    {α : Type u}
    (a b : α)
    {fuel : Nat}
    (hfuel : 2 ≤ fuel) :
    SmallSupportObstruction ([a, b] : List α) fuel :=
  ⟨finEmbeddingImpossible_doubleton a b hfuel⟩

end DoubletonSupportObstructionKernel
end JALC
end LeanCfgProject
