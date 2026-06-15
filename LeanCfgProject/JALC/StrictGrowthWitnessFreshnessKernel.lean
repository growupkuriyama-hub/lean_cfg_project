import LeanCfgProject.JALC.ListGrowthStabilizationKernel

namespace LeanCfgProject
namespace JALC
namespace StrictGrowthWitnessFreshnessKernel

/-
Strict-growth witness freshness.

The previous list-growth stabilization interface reduced bounded-search
success to finding a height with no strict growth.  This file proves the next
local finite-combinatorial fact:

in a monotone iteration, strict-growth witnesses obtained at different ordered
heights are fresh from each other.

The future counting theorem will use this to show that strict growth cannot
happen more often than there are elements in the finite support list.
-/

universe u

open FiniteClosureKernel
open FiniteUniverseListEnumerationKernel
open ListStabilityKernel
open BoundedListStabilitySearchKernel
open ListGrowthStabilizationKernel


/-- Iterates of a monotone operator are increasing over an additive offset. -/
theorem iter_subset_add_of_monotone
    {α : Type u}
    {F : (α → Prop) → α → Prop}
    (mono : PredMonotone F)
    (n k : Nat) :
    PredSubset (Iter F n) (Iter F (n + k)) :=
  by
    induction k with
    | zero =>
        rw [Nat.add_zero]
        intro x hx
        exact hx
    | succ k ih =>
        rw [Nat.add_succ]
        intro x hx
        exact
          iter_subset_succ_of_monotone mono (n + k) x
            (ih x hx)


/-- Iterates of a monotone operator are increasing along `≤`. -/
theorem iter_subset_of_le_of_monotone
    {α : Type u}
    {F : (α → Prop) → α → Prop}
    (mono : PredMonotone F)
    {i j : Nat}
    (hij : i ≤ j) :
    PredSubset (Iter F i) (Iter F j) :=
  by
    rcases Nat.exists_eq_add_of_le hij with ⟨k, hk⟩
    rw [hk]
    exact iter_subset_add_of_monotone mono i k


/-- Strict growth at a concrete height of an iteration. -/
def StrictGrowthAt
    {α : Type u}
    (xs : List α)
    (F : (α → Prop) → α → Prop)
    (n : Nat) : Prop :=
  ListStrictGrowth xs
    (Iter F n)
    (F (Iter F n))


/-- A named witness for strict growth at a concrete height. -/
structure StrictGrowthWitnessAt
    {α : Type u}
    (xs : List α)
    (F : (α → Prop) → α → Prop)
    (n : Nat) : Type (u + 1) where
  elem :
    α
  elem_mem :
    elem ∈ xs
  elem_next :
    F (Iter F n) elem
  elem_not_current :
    ¬ Iter F n elem


/-- Extract a named witness from strict growth at a height. -/
def strictGrowthWitnessAt_of_strictGrowthAt
    {α : Type u}
    {xs : List α}
    {F : (α → Prop) → α → Prop}
    {n : Nat}
    (h : StrictGrowthAt xs F n) :
    StrictGrowthWitnessAt xs F n :=
  let hw := h.2
  { elem := hw.choose,
    elem_mem := hw.choose_spec.1,
    elem_next := hw.choose_spec.2.1,
    elem_not_current := hw.choose_spec.2.2 }


/--
The element of a strict-growth witness belongs to the next iterate.
-/
theorem strictGrowthWitnessAt_elem_in_next_iter
    {α : Type u}
    {xs : List α}
    {F : (α → Prop) → α → Prop}
    {n : Nat}
    (W : StrictGrowthWitnessAt xs F n) :
    Iter F (Nat.succ n) W.elem :=
  W.elem_next


/--
A later strict-growth witness cannot be an element already added at an earlier
strict-growth height.
-/
theorem later_witness_not_equal_earlier_added
    {α : Type u}
    {xs : List α}
    {F : (α → Prop) → α → Prop}
    (mono : PredMonotone F)
    {i j : Nat}
    (hij : i < j)
    {x y : α}
    (hx_next : F (Iter F i) x)
    (hy_not_current : ¬ Iter F j y) :
    x ≠ y :=
  by
    intro hxy
    have hx_succ : Iter F (Nat.succ i) x := hx_next
    have hle : Nat.succ i ≤ j := Nat.succ_le_of_lt hij
    have hx_j : Iter F j x :=
      iter_subset_of_le_of_monotone mono hle x hx_succ
    cases hxy
    exact hy_not_current hx_j


/--
Strict-growth witnesses at ordered distinct heights are distinct.
-/
theorem strictGrowthWitnessAt_distinct_of_lt
    {α : Type u}
    {xs : List α}
    {F : (α → Prop) → α → Prop}
    (mono : PredMonotone F)
    {i j : Nat}
    (hij : i < j)
    (Wi : StrictGrowthWitnessAt xs F i)
    (Wj : StrictGrowthWitnessAt xs F j) :
    Wi.elem ≠ Wj.elem :=
  later_witness_not_equal_earlier_added
    mono hij Wi.elem_next Wj.elem_not_current


/--
A strict-growth witness extracted at an earlier height is distinct from one
extracted at a later height.
-/
theorem extracted_strictGrowthWitness_distinct_of_lt
    {α : Type u}
    {xs : List α}
    {F : (α → Prop) → α → Prop}
    (mono : PredMonotone F)
    {i j : Nat}
    (hij : i < j)
    (hi : StrictGrowthAt xs F i)
    (hj : StrictGrowthAt xs F j) :
    (strictGrowthWitnessAt_of_strictGrowthAt hi).elem ≠
      (strictGrowthWitnessAt_of_strictGrowthAt hj).elem :=
  strictGrowthWitnessAt_distinct_of_lt
    mono hij
    (strictGrowthWitnessAt_of_strictGrowthAt hi)
    (strictGrowthWitnessAt_of_strictGrowthAt hj)


/--
The later witness is not in the earlier successor iterate's propagated image.
This is a useful reformulation for counting arguments.
-/
theorem later_witness_not_in_earlier_successor_if_equal_element
    {α : Type u}
    {xs : List α}
    {F : (α → Prop) → α → Prop}
    (mono : PredMonotone F)
    {i j : Nat}
    (hij : i < j)
    (Wj : StrictGrowthWitnessAt xs F j)
    {x : α}
    (hx_succ : Iter F (Nat.succ i) x) :
    x ≠ Wj.elem :=
  by
    intro hxeq
    have hle : Nat.succ i ≤ j := Nat.succ_le_of_lt hij
    have hx_j : Iter F j x :=
      iter_subset_of_le_of_monotone mono hle x hx_succ
    cases hxeq
    exact Wj.elem_not_current hx_j


/--
If all heights below a later height had strict-growth witnesses, the later
witness is fresh against each earlier witness.
-/
theorem later_witness_fresh_against_all_earlier_witnesses
    {α : Type u}
    {xs : List α}
    {F : (α → Prop) → α → Prop}
    (mono : PredMonotone F)
    {j : Nat}
    (Wj : StrictGrowthWitnessAt xs F j)
    (Wi : ∀ i : Nat, i < j → StrictGrowthWitnessAt xs F i) :
    ∀ i : Nat,
      (hij : i < j) →
      (Wi i hij).elem ≠ Wj.elem :=
  by
    intro i hij
    exact strictGrowthWitnessAt_distinct_of_lt
      mono hij (Wi i hij) Wj


/--
This package records the finite-combinatorial output needed by the next
counting layer: a witness selector for every strict-growth height below a fuel
bound.
-/
structure StrictGrowthWitnessSelector
    {α : Type u}
    (xs : List α)
    (F : (α → Prop) → α → Prop)
    (fuel : Nat) : Type (u + 1) where
  witness_at :
    ∀ n : Nat,
      n ≤ fuel →
      StrictGrowthAt xs F n →
      StrictGrowthWitnessAt xs F n


/-- The canonical selector obtained by extracting witnesses from strict growth. -/
def canonicalStrictGrowthWitnessSelector
    {α : Type u}
    (xs : List α)
    (F : (α → Prop) → α → Prop)
    (fuel : Nat) :
    StrictGrowthWitnessSelector xs F fuel :=
  { witness_at :=
      fun _n _hle hgrowth =>
        strictGrowthWitnessAt_of_strictGrowthAt hgrowth }


/--
Canonical selected witnesses at ordered heights are distinct.
-/
theorem canonicalStrictGrowthWitnessSelector_distinct_of_lt
    {α : Type u}
    {xs : List α}
    {F : (α → Prop) → α → Prop}
    (mono : PredMonotone F)
    {fuel i j : Nat}
    (hi_le : i ≤ fuel)
    (hj_le : j ≤ fuel)
    (hij : i < j)
    (hi : StrictGrowthAt xs F i)
    (hj : StrictGrowthAt xs F j) :
    ((canonicalStrictGrowthWitnessSelector xs F fuel).witness_at
        i hi_le hi).elem ≠
      ((canonicalStrictGrowthWitnessSelector xs F fuel).witness_at
        j hj_le hj).elem :=
  extracted_strictGrowthWitness_distinct_of_lt
    mono hij hi hj

end StrictGrowthWitnessFreshnessKernel
end JALC
end LeanCfgProject
