import LeanCfgProject.JALC.StrictGrowthWitnessFreshnessKernel

namespace LeanCfgProject
namespace JALC
namespace PaperFacingStrictGrowthWitnessFreshness

/-
Paper-facing target for strict-growth witness freshness.
-/

universe u

open FiniteClosureKernel
open ListGrowthStabilizationKernel
open StrictGrowthWitnessFreshnessKernel


/-- Paper-facing monotone iterate inclusion over additive offsets. -/
theorem checked_iter_subset_add_of_monotone
    {α : Type u}
    {F : (α → Prop) → α → Prop}
    (mono : PredMonotone F)
    (n k : Nat) :
    PredSubset (Iter F n) (Iter F (n + k)) :=
  iter_subset_add_of_monotone mono n k


/-- Paper-facing monotone iterate inclusion along `≤`. -/
theorem checked_iter_subset_of_le_of_monotone
    {α : Type u}
    {F : (α → Prop) → α → Prop}
    (mono : PredMonotone F)
    {i j : Nat}
    (hij : i ≤ j) :
    PredSubset (Iter F i) (Iter F j) :=
  iter_subset_of_le_of_monotone mono hij


/-- Paper-facing strict-growth witnesses at ordered heights are distinct. -/
theorem checked_strictGrowthWitnessAt_distinct_of_lt
    {α : Type u}
    {xs : List α}
    {F : (α → Prop) → α → Prop}
    (mono : PredMonotone F)
    {i j : Nat}
    (hij : i < j)
    (Wi : StrictGrowthWitnessAt xs F i)
    (Wj : StrictGrowthWitnessAt xs F j) :
    Wi.elem ≠ Wj.elem :=
  strictGrowthWitnessAt_distinct_of_lt
    mono hij Wi Wj


/-- Paper-facing extracted witnesses at ordered strict-growth heights are distinct. -/
theorem checked_extracted_strictGrowthWitness_distinct_of_lt
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
  extracted_strictGrowthWitness_distinct_of_lt
    mono hij hi hj


/-- Paper-facing later witness fresh against all earlier witnesses. -/
theorem checked_later_witness_fresh_against_all_earlier_witnesses
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
  later_witness_fresh_against_all_earlier_witnesses
    mono Wj Wi


/-- Paper-facing canonical selected witnesses at ordered heights are distinct. -/
theorem checked_canonicalStrictGrowthWitnessSelector_distinct_of_lt
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
  canonicalStrictGrowthWitnessSelector_distinct_of_lt
    mono hi_le hj_le hij hi hj

end PaperFacingStrictGrowthWitnessFreshness
end JALC
end LeanCfgProject
