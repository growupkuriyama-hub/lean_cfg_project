import LeanCfgProject.JALC.StrictGrowthCountingInterfaceKernel

namespace LeanCfgProject
namespace JALC
namespace FreshFamilyFinEmbeddingKernel

/-
Fresh-family Fin embedding.

The previous strict-growth counting interface packages a fresh witness family
indexed by natural heights `n <= fuel`.  This file repackages such a family as
an injection from `Fin (fuel + 1)` into the finite support list.

This is the exact shape needed for the next pigeonhole/cardinality layer.
-/

universe u

open FiniteClosureKernel
open ListGrowthStabilizationKernel
open StrictGrowthWitnessFreshnessKernel
open StrictGrowthCountingInterfaceKernel


/-- A finite index below `fuel + 1` determines a height at most `fuel`. -/
theorem fin_height_le_fuel
    (fuel : Nat)
    (i : Fin (Nat.succ fuel)) :
    i.val ≤ fuel :=
  Nat.lt_succ_iff.mp i.isLt


/-- The support element selected by a fresh family at a finite index. -/
def freshFamilyFinElem
    {α : Type u}
    {xs : List α}
    {F : (α → Prop) → α → Prop}
    {fuel : Nat}
    (Fam : FreshStrictGrowthFamily xs F fuel)
    (i : Fin (Nat.succ fuel)) :
    α :=
  (Fam.witness_at i.val (fin_height_le_fuel fuel i)).elem


/-- The finite-indexed selected element lies in the support list. -/
theorem freshFamilyFinElem_mem
    {α : Type u}
    {xs : List α}
    {F : (α → Prop) → α → Prop}
    {fuel : Nat}
    (Fam : FreshStrictGrowthFamily xs F fuel)
    (i : Fin (Nat.succ fuel)) :
    freshFamilyFinElem Fam i ∈ xs :=
  (Fam.witness_at i.val
    (fin_height_le_fuel fuel i)).elem_mem


/-- The finite-indexed selected element is present in the next iterate. -/
theorem freshFamilyFinElem_next
    {α : Type u}
    {xs : List α}
    {F : (α → Prop) → α → Prop}
    {fuel : Nat}
    (Fam : FreshStrictGrowthFamily xs F fuel)
    (i : Fin (Nat.succ fuel)) :
    F (Iter F i.val) (freshFamilyFinElem Fam i) :=
  (Fam.witness_at i.val
    (fin_height_le_fuel fuel i)).elem_next


/-- The finite-indexed selected element is absent from the current iterate. -/
theorem freshFamilyFinElem_not_current
    {α : Type u}
    {xs : List α}
    {F : (α → Prop) → α → Prop}
    {fuel : Nat}
    (Fam : FreshStrictGrowthFamily xs F fuel)
    (i : Fin (Nat.succ fuel)) :
    ¬ Iter F i.val (freshFamilyFinElem Fam i) :=
  (Fam.witness_at i.val
    (fin_height_le_fuel fuel i)).elem_not_current


/--
Different finite indices select different support elements.
-/
theorem freshFamilyFinElem_ne_of_ne
    {α : Type u}
    {xs : List α}
    {F : (α → Prop) → α → Prop}
    {fuel : Nat}
    (Fam : FreshStrictGrowthFamily xs F fuel)
    {i j : Fin (Nat.succ fuel)}
    (hij : i ≠ j) :
    freshFamilyFinElem Fam i ≠ freshFamilyFinElem Fam j :=
  by
    intro heq
    have hval_ne : i.val ≠ j.val := by
      intro hval
      exact hij (Fin.ext hval)
    cases Nat.lt_or_gt_of_ne hval_ne with
    | inl hlt =>
        exact
          (Fam.distinct_of_lt
            (fin_height_le_fuel fuel i)
            (fin_height_le_fuel fuel j)
            hlt) heq
    | inr hgt =>
        exact
          (Fam.distinct_of_lt
            (fin_height_le_fuel fuel j)
            (fin_height_le_fuel fuel i)
            hgt) heq.symm


/--
The finite-indexed element map of a fresh family is injective.
-/
theorem freshFamilyFinElem_injective
    {α : Type u}
    {xs : List α}
    {F : (α → Prop) → α → Prop}
    {fuel : Nat}
    (Fam : FreshStrictGrowthFamily xs F fuel) :
    Function.Injective (freshFamilyFinElem Fam) :=
  by
    intro i j h
    by_contra hij
    exact freshFamilyFinElem_ne_of_ne Fam hij h


/--
A fresh family gives an explicit injection from `Fin (fuel+1)` into support
elements, together with membership in the support list.
-/
structure FreshFamilyFinEmbedding
    {α : Type u}
    (xs : List α)
    (fuel : Nat) : Type (u + 1) where
  elem :
    Fin (Nat.succ fuel) → α
  elem_mem :
    ∀ i : Fin (Nat.succ fuel), elem i ∈ xs
  elem_injective :
    Function.Injective elem


/-- Build the finite-index embedding from a fresh strict-growth family. -/
def finEmbedding_of_freshFamily
    {α : Type u}
    {xs : List α}
    {F : (α → Prop) → α → Prop}
    {fuel : Nat}
    (Fam : FreshStrictGrowthFamily xs F fuel) :
    FreshFamilyFinEmbedding xs fuel :=
  { elem := freshFamilyFinElem Fam,
    elem_mem := freshFamilyFinElem_mem Fam,
    elem_injective := freshFamilyFinElem_injective Fam }


/--
A strict-growth run yields an explicit finite-index injection into the support
list.
-/
noncomputable def finEmbedding_of_strictGrowthRun
    {α : Type u}
    {xs : List α}
    {F : (α → Prop) → α → Prop}
    {fuel : Nat}
    (mono : PredMonotone F)
    (run : StrictGrowthRun xs F fuel) :
    FreshFamilyFinEmbedding xs fuel :=
  finEmbedding_of_freshFamily
    (freshFamily_of_strictGrowthRun mono run)


/--
If no finite-index injection of the required shape exists, then no fresh family
exists.
-/
def FinEmbeddingImpossible
    {α : Type u}
    (xs : List α)
    (fuel : Nat) : Prop :=
  ∀ E : FreshFamilyFinEmbedding xs fuel, False


/--
The absence of a finite-index embedding rules out fresh families.
-/
theorem freshFamilyImpossible_of_finEmbeddingImpossible
    {α : Type u}
    {xs : List α}
    {F : (α → Prop) → α → Prop}
    {fuel : Nat}
    (himp : FinEmbeddingImpossible xs fuel) :
    FreshFamilyImpossible xs F fuel :=
  by
    intro Fam
    exact himp (finEmbedding_of_freshFamily Fam)


/--
The absence of a finite-index embedding rules out full strict-growth runs.
-/
theorem not_strictGrowthRun_of_finEmbeddingImpossible
    {α : Type u}
    {xs : List α}
    {F : (α → Prop) → α → Prop}
    {fuel : Nat}
    (mono : PredMonotone F)
    (himp : FinEmbeddingImpossible xs fuel) :
    ¬ StrictGrowthRun xs F fuel :=
  not_strictGrowthRun_of_freshFamilyImpossible
    mono
    (freshFamilyImpossible_of_finEmbeddingImpossible himp)


/--
If no finite-index embedding into the support exists, bounded search succeeds.
-/
theorem boundedSearch_of_finEmbeddingImpossible
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
  StrictGrowthCountingInterfaceKernel.boundedSearch_of_freshFamilyImpossible
    U F mono dec fuel
    (freshFamilyImpossible_of_finEmbeddingImpossible himp)

end FreshFamilyFinEmbeddingKernel
end JALC
end LeanCfgProject
