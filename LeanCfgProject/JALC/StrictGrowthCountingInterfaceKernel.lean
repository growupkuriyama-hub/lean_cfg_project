import LeanCfgProject.JALC.StrictGrowthWitnessFreshnessKernel

namespace LeanCfgProject
namespace JALC
namespace StrictGrowthCountingInterfaceKernel

/-
Strict-growth counting interface.

The previous freshness target proves that strict-growth witnesses at ordered
heights are distinct.  This file packages the counting interface needed for the
next finite-support argument:

  strict growth at every height up to fuel
  => a fresh witness family indexed by heights up to fuel.

Conversely, if such a fresh family is impossible, then strict growth cannot
hold at every height up to fuel; hence some no-strict-growth height exists, and
bounded search succeeds.
-/

universe u

open FiniteClosureKernel
open FiniteUniverseListEnumerationKernel
open ListStabilityKernel
open BoundedListStabilitySearchKernel
open ListGrowthStabilizationKernel
open StrictGrowthWitnessFreshnessKernel


/-- Strict growth occurs at every height up to the fuel. -/
def StrictGrowthRun
    {α : Type u}
    (xs : List α)
    (F : (α → Prop) → α → Prop)
    (fuel : Nat) : Prop :=
  ∀ n : Nat, n ≤ fuel → StrictGrowthAt xs F n


/--
A fresh strict-growth witness family indexed by heights up to the fuel.
-/
structure FreshStrictGrowthFamily
    {α : Type u}
    (xs : List α)
    (F : (α → Prop) → α → Prop)
    (fuel : Nat) : Type (u + 1) where
  witness_at :
    ∀ n : Nat, n ≤ fuel → StrictGrowthWitnessAt xs F n
  distinct_of_lt :
    ∀ {i j : Nat},
      (hi : i ≤ fuel) →
      (hj : j ≤ fuel) →
      i < j →
      (witness_at i hi).elem ≠
        (witness_at j hj).elem


/--
A strict-growth run yields a fresh witness family.
-/
noncomputable def freshFamily_of_strictGrowthRun
    {α : Type u}
    {xs : List α}
    {F : (α → Prop) → α → Prop}
    {fuel : Nat}
    (mono : PredMonotone F)
    (run : StrictGrowthRun xs F fuel) :
    FreshStrictGrowthFamily xs F fuel :=
  { witness_at :=
      fun n hn =>
        strictGrowthWitnessAt_of_strictGrowthAt (run n hn),
    distinct_of_lt :=
      by
        intro i j hi hj hij
        exact
          extracted_strictGrowthWitness_distinct_of_lt
            mono hij (run i hi) (run j hj) }


/--
Every selected witness in a fresh family lies in the support list.
-/
theorem freshFamily_witness_mem
    {α : Type u}
    {xs : List α}
    {F : (α → Prop) → α → Prop}
    {fuel n : Nat}
    (Fam : FreshStrictGrowthFamily xs F fuel)
    (hn : n ≤ fuel) :
    (Fam.witness_at n hn).elem ∈ xs :=
  (Fam.witness_at n hn).elem_mem


/--
Every selected witness in a fresh family is in the next iterate at its height.
-/
theorem freshFamily_witness_next
    {α : Type u}
    {xs : List α}
    {F : (α → Prop) → α → Prop}
    {fuel n : Nat}
    (Fam : FreshStrictGrowthFamily xs F fuel)
    (hn : n ≤ fuel) :
    F (Iter F n) ((Fam.witness_at n hn).elem) :=
  (Fam.witness_at n hn).elem_next


/--
Every selected witness in a fresh family is absent from the current iterate at
its height.
-/
theorem freshFamily_witness_not_current
    {α : Type u}
    {xs : List α}
    {F : (α → Prop) → α → Prop}
    {fuel n : Nat}
    (Fam : FreshStrictGrowthFamily xs F fuel)
    (hn : n ≤ fuel) :
    ¬ Iter F n ((Fam.witness_at n hn).elem) :=
  (Fam.witness_at n hn).elem_not_current


/--
A strict-growth run gives a fresh family.
-/
theorem freshFamily_exists_of_strictGrowthRun
    {α : Type u}
    {xs : List α}
    {F : (α → Prop) → α → Prop}
    {fuel : Nat}
    (mono : PredMonotone F)
    (run : StrictGrowthRun xs F fuel) :
    Nonempty (FreshStrictGrowthFamily xs F fuel) :=
  ⟨freshFamily_of_strictGrowthRun mono run⟩


/--
The finite counting obstruction expected from the next layer: no fresh family
of the requested height range exists.
-/
def FreshFamilyImpossible
    {α : Type u}
    (xs : List α)
    (F : (α → Prop) → α → Prop)
    (fuel : Nat) : Prop :=
  ∀ Fam : FreshStrictGrowthFamily xs F fuel, False


/--
If a fresh family is impossible, then strict growth cannot occur at every
height up to the fuel.
-/
theorem not_strictGrowthRun_of_freshFamilyImpossible
    {α : Type u}
    {xs : List α}
    {F : (α → Prop) → α → Prop}
    {fuel : Nat}
    (mono : PredMonotone F)
    (himp : FreshFamilyImpossible xs F fuel) :
    ¬ StrictGrowthRun xs F fuel :=
  by
    intro run
    exact himp (freshFamily_of_strictGrowthRun mono run)


/--
Failure of a strict-growth run yields an explicit height with no strict growth.
-/
theorem exists_noStrictGrowth_height_of_not_strictGrowthRun
    {α : Type u}
    {xs : List α}
    {F : (α → Prop) → α → Prop}
    {fuel : Nat}
    (hnot : ¬ StrictGrowthRun xs F fuel) :
    ∃ n : Nat,
      n ≤ fuel ∧
      ¬ StrictGrowthAt xs F n :=
  by
    classical
    by_contra hno
    apply hnot
    intro n hn
    by_contra hgrowth
    exact hno ⟨n, hn, hgrowth⟩


/--
A failed strict-growth run gives the no-strict-growth certificate expected by
the bounded-search bridge.
-/
noncomputable def noStrictGrowthWithinBound_of_not_strictGrowthRun
    {α : Type u}
    (U : UniverseList α)
    (F : (α → Prop) → α → Prop)
    (fuel : Nat)
    (hnot : ¬ StrictGrowthRun U.support F fuel) :
    NoStrictGrowthWithinBound U F fuel :=
  let h :=
    exists_noStrictGrowth_height_of_not_strictGrowthRun
      (xs := U.support) (F := F) (fuel := fuel) hnot
  { height := h.choose,
    height_le_fuel := h.choose_spec.1,
    no_strict_growth := h.choose_spec.2 }


/--
If strict growth cannot hold at every height up to the fuel, bounded search
succeeds.
-/
theorem boundedSearch_of_not_strictGrowthRun
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
    (hnot : ¬ StrictGrowthRun U.support F fuel) :
    ∃ W : ListStabilityWitness U F,
      findListStabilityWitness U F dec fuel = some W :=
  boundedSearch_accepts_noStrictGrowthWithinBound
    U F mono dec fuel
    (noStrictGrowthWithinBound_of_not_strictGrowthRun
      U F fuel hnot)


/--
If the finite counting obstruction rules out a fresh family up to the fuel, then
bounded search succeeds.
-/
theorem boundedSearch_of_freshFamilyImpossible
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
    (himp : FreshFamilyImpossible U.support F fuel) :
    ∃ W : ListStabilityWitness U F,
      findListStabilityWitness U F dec fuel = some W :=
  boundedSearch_of_not_strictGrowthRun
    U F mono dec fuel
    (not_strictGrowthRun_of_freshFamilyImpossible mono himp)


/--
The same finite counting obstruction yields both search success and a closure
certificate.
-/
theorem closureCertificate_of_freshFamilyImpossible
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
    (himp : FreshFamilyImpossible U.support F fuel) :
    ∃ W : ListStabilityWitness U F,
      findListStabilityWitness U F dec fuel = some W ∧
      StableAt F W.height :=
  by
    let H :=
      noStrictGrowthWithinBound_of_not_strictGrowthRun
        U F fuel
        (not_strictGrowthRun_of_freshFamilyImpossible mono himp)
    exact
      closureCertificate_exists_of_no_strictGrowth_le_fuel
        U F mono dec fuel H.height H.height_le_fuel
        H.no_strict_growth

end StrictGrowthCountingInterfaceKernel
end JALC
end LeanCfgProject
