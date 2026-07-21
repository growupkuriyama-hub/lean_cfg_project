/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG2.ConcreteCanonicalLearnerWorkingGrammarObservationSelectionRankSensitivity

/-!
# ConcreteCanonicalLearnerWorkingGrammarObservationSelectionCostOverhead.lean

The preceding files compare observation-selection cost models and prove
quantitative rank sensitivity under bounded perturbations.

This file treats an exact normalization operation: adding one fixed overhead to
the cost of every selected observation set.

## Fixed-overhead cost

For

```lean
selectionCost : Finset ι → Nat
overhead : Nat
```

define

```lean
costWithOverhead(S) = selectionCost S + overhead.
```

This models a fixed setup, compilation, or deployment charge that is paid once
whenever an observation design is used.

## Shifted feasibility

A selected set has overhead cost at most `budget + overhead` exactly when its
original cost is at most `budget`.

Consequently:

```text
Profile(cost,budget)
  =
Profile(costWithOverhead,budget+overhead),

Layer(cost,budget)
  =
Layer(costWithOverhead,budget+overhead).
```

Selection existence is unchanged.

## Exact rank shift

The semantic minimum cost shifts exactly:

```text
minimum(costWithOverhead,L)
  =
minimum(cost,L)+overhead.
```

Therefore every full ambient-product target satisfies

```text
rank(costWithOverhead,L)
  =
rank(cost,L)+overhead.
```

Exact rank shells shift by the same amount:

```text
L ∈ ExactRank(cost,r)
  ↔
L ∈ ExactRank(costWithOverhead,r+overhead).
```

The set of minimizing selected subsets is unchanged semantically.

## Pareto invariance

Adding the same overhead to every selected set preserves weak and strict
dominance.  Hence it preserves Pareto optimality and the explicit finite Pareto
frontier exactly.

The first profile coordinate, selected-set cardinality, is unchanged, and the
second coordinate is translated by `overhead`.

## Certified same-selection theorem

A minimum-cost selected subset for the original cost is also a minimum-cost
selected subset for the overhead cost.  The selected product itself is
unchanged, so the same selected-product certified learner identifies the target
and the same checked grammar output satisfies its minimum certified-description
rank budgets.

Only the observation-selection cost rank changes, by the exact overhead.

## Boundary

The normalization is semantic.  No executable target-class decider or
optimization algorithm is asserted.

No target grammar is supplied to any learner.
No `sorry`, `admit`, or `axiom` is used.
-/

namespace MCFG

universe u v w z


section FixedOverheadCostDefinition

variable {ι : Type v}

/-- Add one fixed overhead to every finite observation-selection cost. -/
def correctedConcreteObservationSelectionCostWithOverhead
    (selectionCost : Finset ι → Nat)
    (overhead : Nat)
    (S : Finset ι) :
    Nat :=
  selectionCost S + overhead

/-- Original cost is pointwise no greater than cost with overhead. -/
theorem observationSelectionCost_le_costWithOverhead
    (selectionCost : Finset ι → Nat)
    (overhead : Nat) :
    CorrectedConcreteObservationSelectionCostPointwiseLe
      selectionCost
      (correctedConcreteObservationSelectionCostWithOverhead
        selectionCost overhead) := by

  intro S

  unfold
    correctedConcreteObservationSelectionCostWithOverhead

  omega

/-- Cost with overhead is bounded by original cost plus exactly the overhead
inside every ambient candidate set. -/
theorem observationSelectionCostWithOverhead_leUpToWithin
    (U : Finset ι)
    (selectionCost : Finset ι → Nat)
    (overhead : Nat) :
    CorrectedConcreteObservationSelectionCostLeUpToWithin
      U
      selectionCost
      (correctedConcreteObservationSelectionCostWithOverhead
        selectionCost overhead)
      overhead := by

  intro S hSU

  exact
    Nat.le_refl _

/-- Adding overhead preserves subset-monotonicity. -/
theorem observationSelectionCostWithOverhead_monotone
    {selectionCost : Finset ι → Nat}
    (hMonotone :
      CorrectedConcreteObservationSelectionCostMonotone
        selectionCost)
    (overhead : Nat) :
    CorrectedConcreteObservationSelectionCostMonotone
      (correctedConcreteObservationSelectionCostWithOverhead
        selectionCost overhead) := by

  intro R S hRS

  unfold
    correctedConcreteObservationSelectionCostWithOverhead

  exact
    Nat.add_le_add_right
      (hMonotone hRS)
      overhead

/-- Adding overhead preserves strict subset-monotonicity. -/
theorem observationSelectionCostWithOverhead_strictlyMonotone
    {selectionCost : Finset ι → Nat}
    (hStrict :
      CorrectedConcreteObservationSelectionCostStrictlyMonotone
        selectionCost)
    (overhead : Nat) :
    CorrectedConcreteObservationSelectionCostStrictlyMonotone
      (correctedConcreteObservationSelectionCostWithOverhead
        selectionCost overhead) := by

  intro R S hRS

  unfold
    correctedConcreteObservationSelectionCostWithOverhead

  exact
    Nat.add_lt_add_right
      (hStrict hRS)
      overhead

end FixedOverheadCostDefinition


section ShiftedFeasibility

variable {α : Type u}
variable {ι : Type v}
variable {M : Type w}
variable [Monoid M]
variable {obsFamily : ι → α → M}
variable {f : Nat}
variable {selectionCost : Finset ι → Nat}
variable {overhead : Nat}
variable {U : Finset ι}
variable {language : Set (Word α)}

/-- Exact shifted feasibility theorem for a fixed cost overhead. -/
theorem observationSelectionAtCostWithOverhead_iff
    (costBudget : Nat) :
    CorrectedConcreteObservationSelectionAtCost
        (obsFamily := obsFamily)
        (f := f)
        (correctedConcreteObservationSelectionCostWithOverhead
          selectionCost overhead)
        U
        language
        (costBudget + overhead) ↔
      CorrectedConcreteObservationSelectionAtCost
        (obsFamily := obsFamily)
        (f := f)
        selectionCost
        U
        language
        costBudget := by

  constructor

  · intro hSelection

    rcases hSelection with
      ⟨S, hSU, hCost, hTarget⟩

    refine
      ⟨S,
        hSU,
        ?_,
        hTarget⟩

    unfold
      correctedConcreteObservationSelectionCostWithOverhead
      at hCost

    omega

  · intro hSelection

    rcases hSelection with
      ⟨S, hSU, hCost, hTarget⟩

    refine
      ⟨S,
        hSU,
        ?_,
        hTarget⟩

    unfold
      correctedConcreteObservationSelectionCostWithOverhead

    omega

/-- Adding a fixed overhead does not change whether some finite observation
selection exists. -/
theorem hasObservationSelectionCostWithOverhead_iff :
    HasCorrectedConcreteObservationSelectionCost
        (obsFamily := obsFamily)
        (f := f)
        (correctedConcreteObservationSelectionCostWithOverhead
          selectionCost overhead)
        U
        language ↔
      HasCorrectedConcreteObservationSelectionCost
        (obsFamily := obsFamily)
        (f := f)
        selectionCost
        U
        language := by

  constructor

  · intro hSelection

    rcases hSelection with
      ⟨costBudget,
        S,
        hSU,
        hCost,
        hTarget⟩

    exact
      ⟨selectionCost S,
        S,
        hSU,
        Nat.le_refl _,
        hTarget⟩

  · intro hSelection

    rcases hSelection with
      ⟨costBudget, hAtCost⟩

    exact
      ⟨costBudget + overhead,
        (observationSelectionAtCostWithOverhead_iff
          (selectionCost := selectionCost)
          (overhead := overhead)
          costBudget).mpr
          hAtCost⟩

/-- Cumulative profiles are translated exactly by the fixed overhead. -/
theorem observationSelectionCostProfileClass_withOverhead_eq_shifted
    (costBudget : Nat) :
    CorrectedConcreteObservationSelectionCostProfileClass
        (z := z)
        α
        ι
        M
        obsFamily
        f
        (correctedConcreteObservationSelectionCostWithOverhead
          selectionCost overhead)
        U
        (costBudget + overhead) =
      CorrectedConcreteObservationSelectionCostProfileClass
        (z := z)
        α
        ι
        M
        obsFamily
        f
        selectionCost
        U
        costBudget := by

  ext target

  exact
    observationSelectionAtCostWithOverhead_iff
      (selectionCost := selectionCost)
      (overhead := overhead)
      costBudget

end ShiftedFeasibility


section ShiftedBudgetFiltration

variable {α : Type u}
variable {ι : Type v}
variable {M : Type w}
variable [DecidableEq ι]
variable [Monoid M]
variable {obsFamily : ι → α → M}
variable {f : Nat}
variable {selectionCost : Finset ι → Nat}
variable {overhead : Nat}
variable {U : Finset ι}
variable {language : Set (Word α)}

/-- Finite budget filtrations are translated exactly by a fixed overhead. -/
theorem observationCostBudgetFiltration_withOverhead_eq_shifted
    (costBudget : Nat) :
    correctedConcreteObservationCostBudgetFiltration
        (z := z)
        obsFamily
        f
        (correctedConcreteObservationSelectionCostWithOverhead
          selectionCost overhead)
        U
        language
        (costBudget + overhead) =
      correctedConcreteObservationCostBudgetFiltration
        (z := z)
        obsFamily
        f
        selectionCost
        U
        language
        costBudget := by

  ext S

  constructor

  · intro hS

    rcases
        (mem_correctedConcreteObservationCostBudgetFiltration_iff
          (z := z)).mp
          hS with
      ⟨hSU, hCost, hTarget⟩

    refine
      (mem_correctedConcreteObservationCostBudgetFiltration_iff
        (z := z)).mpr
        ⟨hSU,
          ?_,
          hTarget⟩

    unfold
      correctedConcreteObservationSelectionCostWithOverhead
      at hCost

    omega

  · intro hS

    rcases
        (mem_correctedConcreteObservationCostBudgetFiltration_iff
          (z := z)).mp
          hS with
      ⟨hSU, hCost, hTarget⟩

    refine
      (mem_correctedConcreteObservationCostBudgetFiltration_iff
        (z := z)).mpr
        ⟨hSU,
          ?_,
          hTarget⟩

    unfold
      correctedConcreteObservationSelectionCostWithOverhead

    omega

end ShiftedBudgetFiltration


section MinimumCostOverheadShift

variable {α : Type u}
variable {ι : Type v}
variable {M : Type w}
variable [Monoid M]
variable {obsFamily : ι → α → M}
variable {f : Nat}
variable {selectionCost : Finset ι → Nat}
variable {overhead : Nat}
variable {U : Finset ι}
variable {language : Set (Word α)}

/-- Adding a fixed overhead shifts the semantic minimum observation-selection
cost by exactly that overhead. -/
theorem observationSelectionMinimumCost_withOverhead_eq
    (hSelection :
      HasCorrectedConcreteObservationSelectionCost
        (obsFamily := obsFamily)
        (f := f)
        selectionCost
        U
        language)
    (hSelectionOverhead :
      HasCorrectedConcreteObservationSelectionCost
        (obsFamily := obsFamily)
        (f := f)
        (correctedConcreteObservationSelectionCostWithOverhead
          selectionCost overhead)
        U
        language) :
    correctedConcreteObservationSelectionMinimumCost
        (correctedConcreteObservationSelectionCostWithOverhead
          selectionCost overhead)
        hSelectionOverhead =
      correctedConcreteObservationSelectionMinimumCost
          selectionCost
          hSelection +
        overhead := by

  apply Nat.le_antisymm

  · rcases hSelection.exists_selection_exact_minimumCost with
      ⟨S, hSU, hCost, hTarget⟩

    apply
      hSelectionOverhead.minimumCost_le_of_selection

    refine
      ⟨S,
        hSU,
        ?_,
        hTarget⟩

    unfold
      correctedConcreteObservationSelectionCostWithOverhead

    rw [hCost]

  · rcases hSelectionOverhead.exists_selection_exact_minimumCost with
      ⟨S, hSU, hCost, hTarget⟩

    have hMinimum :
        correctedConcreteObservationSelectionMinimumCost
            selectionCost
            hSelection <=
          selectionCost S := by

      apply
        hSelection.minimumCost_le_of_selection

      exact
        ⟨S,
          hSU,
          Nat.le_refl _,
          hTarget⟩

    unfold
      correctedConcreteObservationSelectionCostWithOverhead
      at hCost

    rw [← hCost]

    exact
      Nat.add_le_add_right
        hMinimum
        overhead

/-- The same feasible selected subset is minimum for original cost exactly when
it is minimum for the overhead cost. -/
theorem observationSelection_isMinimumCost_iff_isMinimumCostWithOverhead
    (hSelection :
      HasCorrectedConcreteObservationSelectionCost
        (obsFamily := obsFamily)
        (f := f)
        selectionCost
        U
        language)
    (hSelectionOverhead :
      HasCorrectedConcreteObservationSelectionCost
        (obsFamily := obsFamily)
        (f := f)
        (correctedConcreteObservationSelectionCostWithOverhead
          selectionCost overhead)
        U
        language)
    {S : Finset ι}
    (hSU : S ⊆ U)
    (hTarget :
      language ∈
        StartRootedCorrectedConcreteTargetClass
          (v := z)
          α
          (↥S → M)
          (selectedObservationProduct obsFamily S)
          f) :
    selectionCost S =
        correctedConcreteObservationSelectionMinimumCost
          selectionCost
          hSelection ↔
      correctedConcreteObservationSelectionCostWithOverhead
          selectionCost overhead S =
        correctedConcreteObservationSelectionMinimumCost
          (correctedConcreteObservationSelectionCostWithOverhead
            selectionCost overhead)
          hSelectionOverhead := by

  rw [
    observationSelectionMinimumCost_withOverhead_eq
      hSelection
      hSelectionOverhead
  ]

  unfold
    correctedConcreteObservationSelectionCostWithOverhead

  omega

end MinimumCostOverheadShift


section ExactRankOverheadShift

variable {α : Type u}
variable {ι : Type v}
variable {M : Type w}
variable [Monoid M]
variable {obsFamily : ι → α → M}
variable {f : Nat}
variable {selectionCost : Finset ι → Nat}
variable {overhead : Nat}
variable {U : Finset ι}
variable {language : Set (Word α)}

/-- Exact rank shells are translated exactly by a fixed cost overhead. -/
theorem observationSelection_mem_exactRankWithOverhead_iff
    (rank : Nat) :
    language ∈
        CorrectedConcreteObservationSelectionExactCostRankClass
          (z := z)
          α
          ι
          M
          obsFamily
          f
          (correctedConcreteObservationSelectionCostWithOverhead
            selectionCost overhead)
          U
          (rank + overhead) ↔
      language ∈
        CorrectedConcreteObservationSelectionExactCostRankClass
          (z := z)
          α
          ι
          M
          obsFamily
          f
          selectionCost
          U
          rank := by

  constructor

  · intro hOverhead

    let hSelectionOverhead :
        HasCorrectedConcreteObservationSelectionCost
          (obsFamily := obsFamily)
          (f := f)
          (correctedConcreteObservationSelectionCostWithOverhead
            selectionCost overhead)
          U
          language :=
      ⟨rank + overhead,
        hOverhead.1⟩

    let hSelection :
        HasCorrectedConcreteObservationSelectionCost
          (obsFamily := obsFamily)
          (f := f)
          selectionCost
          U
          language :=
      (hasObservationSelectionCostWithOverhead_iff
        (selectionCost := selectionCost)
        (overhead := overhead)).mp
        hSelectionOverhead

    have hOverheadRank :
        rank + overhead =
          correctedConcreteObservationSelectionMinimumCost
            (correctedConcreteObservationSelectionCostWithOverhead
              selectionCost overhead)
            hSelectionOverhead :=
      (observationSelection_mem_exactCostRankClass_iff_rank_eq_minimum
        (z := z)
        hSelectionOverhead
        (rank + overhead)).mp
        hOverhead

    have hMinimumShift :
        correctedConcreteObservationSelectionMinimumCost
            (correctedConcreteObservationSelectionCostWithOverhead
              selectionCost overhead)
            hSelectionOverhead =
          correctedConcreteObservationSelectionMinimumCost
              selectionCost
              hSelection +
            overhead :=
      observationSelectionMinimumCost_withOverhead_eq
        hSelection
        hSelectionOverhead

    have hRank :
        rank =
          correctedConcreteObservationSelectionMinimumCost
            selectionCost
            hSelection := by

      omega

    exact
      (observationSelection_mem_exactCostRankClass_iff_rank_eq_minimum
        (z := z)
        hSelection
        rank).mpr
        hRank

  · intro hOriginal

    let hSelection :
        HasCorrectedConcreteObservationSelectionCost
          (obsFamily := obsFamily)
          (f := f)
          selectionCost
          U
          language :=
      ⟨rank,
        hOriginal.1⟩

    let hSelectionOverhead :
        HasCorrectedConcreteObservationSelectionCost
          (obsFamily := obsFamily)
          (f := f)
          (correctedConcreteObservationSelectionCostWithOverhead
            selectionCost overhead)
          U
          language :=
      (hasObservationSelectionCostWithOverhead_iff
        (selectionCost := selectionCost)
        (overhead := overhead)).mpr
        hSelection

    have hRank :
        rank =
          correctedConcreteObservationSelectionMinimumCost
            selectionCost
            hSelection :=
      (observationSelection_mem_exactCostRankClass_iff_rank_eq_minimum
        (z := z)
        hSelection
        rank).mp
        hOriginal

    have hMinimumShift :
        correctedConcreteObservationSelectionMinimumCost
            (correctedConcreteObservationSelectionCostWithOverhead
              selectionCost overhead)
            hSelectionOverhead =
          correctedConcreteObservationSelectionMinimumCost
              selectionCost
              hSelection +
            overhead :=
      observationSelectionMinimumCost_withOverhead_eq
        hSelection
        hSelectionOverhead

    apply
      (observationSelection_mem_exactCostRankClass_iff_rank_eq_minimum
        (z := z)
        hSelectionOverhead
        (rank + overhead)).mpr

    omega

end ExactRankOverheadShift


section AmbientRankOverheadShift

variable {α : Type u}
variable {ι : Type v}
variable {M : Type w}
variable [Monoid M]
variable (obsFamily : ι → α → M)
variable (f : Nat)
variable (selectionCost : Finset ι → Nat)
variable (overhead : Nat)
variable (U : Finset ι)

/-- Paper-facing observation-selection rank shifts exactly under a fixed cost
overhead. -/
theorem ambientTargetObservationSelectionCostRank_withOverhead_eq
    {language : Set (Word α)}
    (hTarget :
      language ∈
        StartRootedCorrectedConcreteTargetClass
          (v := z)
          α
          (↥U → M)
          (selectedObservationProduct obsFamily U)
          f) :
    ambientTargetObservationSelectionCostRank
        (z := z)
        obsFamily
        f
        (correctedConcreteObservationSelectionCostWithOverhead
          selectionCost overhead)
        U
        hTarget =
      ambientTargetObservationSelectionCostRank
          (z := z)
          obsFamily
          f
          selectionCost
          U
          hTarget +
        overhead := by

  let hSelection :=
    hasCorrectedConcreteObservationSelectionCost_of_fullProductTarget
      (obsFamily := obsFamily)
      (f := f)
      selectionCost
      hTarget

  let hSelectionOverhead :=
    hasCorrectedConcreteObservationSelectionCost_of_fullProductTarget
      (obsFamily := obsFamily)
      (f := f)
      (correctedConcreteObservationSelectionCostWithOverhead
        selectionCost overhead)
      hTarget

  simpa [
    ambientTargetObservationSelectionCostRank,
    ambientTargetObservationSelectionMinimumCost,
    hSelection,
    hSelectionOverhead
  ] using
    observationSelectionMinimumCost_withOverhead_eq
      hSelection
      hSelectionOverhead

end AmbientRankOverheadShift


section ParetoOverheadInvariance

variable {α : Type u}
variable {ι : Type v}
variable {M : Type w}
variable [Monoid M]
variable {obsFamily : ι → α → M}
variable {f : Nat}
variable {selectionCost : Finset ι → Nat}
variable {overhead : Nat}
variable {U : Finset ι}
variable {language : Set (Word α)}

/-- Weak dominance is invariant under adding a fixed overhead. -/
theorem observationSelectionWeakDominance_withOverhead_iff
    (R S : Finset ι) :
    CorrectedConcreteObservationSelectionWeaklyDominates
        (correctedConcreteObservationSelectionCostWithOverhead
          selectionCost overhead)
        R
        S ↔
      CorrectedConcreteObservationSelectionWeaklyDominates
        selectionCost
        R
        S := by

  constructor

  · intro hDominance

    refine
      ⟨hDominance.1,
        ?_⟩

    unfold
      correctedConcreteObservationSelectionCostWithOverhead
      at hDominance

    omega

  · intro hDominance

    refine
      ⟨hDominance.1,
        ?_⟩

    unfold
      correctedConcreteObservationSelectionCostWithOverhead

    omega

/-- Strict dominance is invariant under adding a fixed overhead. -/
theorem observationSelectionStrictDominance_withOverhead_iff
    (R S : Finset ι) :
    CorrectedConcreteObservationSelectionStrictlyDominates
        (correctedConcreteObservationSelectionCostWithOverhead
          selectionCost overhead)
        R
        S ↔
      CorrectedConcreteObservationSelectionStrictlyDominates
        selectionCost
        R
        S := by

  constructor

  · intro hDominance

    refine
      ⟨(observationSelectionWeakDominance_withOverhead_iff
          (selectionCost := selectionCost)
          (overhead := overhead)
          R
          S).mp
          hDominance.1,
        ?_⟩

    rcases hDominance.2 with
      hCard | hCost

    · exact Or.inl hCard

    · right

      unfold
        correctedConcreteObservationSelectionCostWithOverhead
        at hCost

      omega

  · intro hDominance

    refine
      ⟨(observationSelectionWeakDominance_withOverhead_iff
          (selectionCost := selectionCost)
          (overhead := overhead)
          R
          S).mpr
          hDominance.1,
        ?_⟩

    rcases hDominance.2 with
      hCard | hCost

    · exact Or.inl hCard

    · right

      unfold
        correctedConcreteObservationSelectionCostWithOverhead

      omega

/-- Pareto optimality is invariant under adding a fixed overhead. -/
theorem observationSelectionParetoOptimal_withOverhead_iff
    (S : Finset ι) :
    CorrectedConcreteObservationSelectionParetoOptimal
        (z := z)
        obsFamily
        f
        (correctedConcreteObservationSelectionCostWithOverhead
          selectionCost overhead)
        U
        language
        S ↔
      CorrectedConcreteObservationSelectionParetoOptimal
        (z := z)
        obsFamily
        f
        selectionCost
        U
        language
        S := by

  constructor

  · intro hPareto

    refine
      ⟨hPareto.1,
        hPareto.2.1,
        ?_⟩

    intro R hRU hRTarget hDominates

    exact
      hPareto.2.2
        R
        hRU
        hRTarget
        ((observationSelectionStrictDominance_withOverhead_iff
          (selectionCost := selectionCost)
          (overhead := overhead)
          R
          S).mpr
          hDominates)

  · intro hPareto

    refine
      ⟨hPareto.1,
        hPareto.2.1,
        ?_⟩

    intro R hRU hRTarget hDominates

    exact
      hPareto.2.2
        R
        hRU
        hRTarget
        ((observationSelectionStrictDominance_withOverhead_iff
          (selectionCost := selectionCost)
          (overhead := overhead)
          R
          S).mp
          hDominates)

end ParetoOverheadInvariance


section FiniteParetoOverheadInvariance

variable {α : Type u}
variable {ι : Type v}
variable {M : Type w}
variable [DecidableEq ι]
variable [Monoid M]
variable {obsFamily : ι → α → M}
variable {f : Nat}
variable {selectionCost : Finset ι → Nat}
variable {overhead : Nat}
variable {U : Finset ι}
variable {language : Set (Word α)}

/-- The explicit finite Pareto frontier is unchanged by a fixed overhead. -/
theorem correctedConcreteObservationParetoSelections_withOverhead_eq :
    correctedConcreteObservationParetoSelections
        (z := z)
        obsFamily
        f
        (correctedConcreteObservationSelectionCostWithOverhead
          selectionCost overhead)
        U
        language =
      correctedConcreteObservationParetoSelections
        (z := z)
        obsFamily
        f
        selectionCost
        U
        language := by

  ext S

  constructor

  · intro hS

    apply
      (mem_correctedConcreteObservationParetoSelections_iff
        (z := z)
        obsFamily
        f
        selectionCost
        U
        language).mpr

    exact
      (observationSelectionParetoOptimal_withOverhead_iff
        (selectionCost := selectionCost)
        (overhead := overhead)
        S).mp
        ((mem_correctedConcreteObservationParetoSelections_iff
          (z := z)
          obsFamily
          f
          (correctedConcreteObservationSelectionCostWithOverhead
            selectionCost overhead)
          U
          language).mp
          hS)

  · intro hS

    apply
      (mem_correctedConcreteObservationParetoSelections_iff
        (z := z)
        obsFamily
        f
        (correctedConcreteObservationSelectionCostWithOverhead
          selectionCost overhead)
        U
        language).mpr

    exact
      (observationSelectionParetoOptimal_withOverhead_iff
        (selectionCost := selectionCost)
        (overhead := overhead)
        S).mpr
        ((mem_correctedConcreteObservationParetoSelections_iff
          (z := z)
          obsFamily
          f
          selectionCost
          U
          language).mp
          hS)

end FiniteParetoOverheadInvariance


section MinimumSelectionCertifiedOverheadPackage

variable {α : Type u}
variable {ι : Type v}
variable {M : Type w}
variable [Fintype M]
variable [DecidableEq α]
variable [DecidableEq ι]
variable [DecidableEq M]
variable [Monoid M]
variable (hα : Nonempty α)
variable (obsFamily : ι → α → M)
variable (f : Nat)
variable (selectionCost : Finset ι → Nat)
variable (overhead : Nat)
variable (U : Finset ι)

/-- A minimum selection for the original cost is the same semantic minimum
selection for the overhead cost, with exactly shifted observation-selection
rank and the same selected-product certified learner. -/
theorem ambientTarget_sameMinimumSelection_underCostOverhead_certified_package
    {language : Set (Word α)}
    (hTarget :
      language ∈
        StartRootedCorrectedConcreteTargetClass
          (v := z)
          α
          (↥U → M)
          (selectedObservationProduct obsFamily U)
          f) :
    ∃
      (S : Finset ι)
      (hSelected :
        language ∈
          StartRootedCorrectedConcreteTargetClass
            (v := z)
            α
            (↥S → M)
            (selectedObservationProduct obsFamily S)
            f),
      selectionCost S =
          ambientTargetObservationSelectionCostRank
            (z := z)
            obsFamily
            f
            selectionCost
            U
            hTarget ∧
        correctedConcreteObservationSelectionCostWithOverhead
            selectionCost overhead S =
          ambientTargetObservationSelectionCostRank
            (z := z)
            obsFamily
            f
            (correctedConcreteObservationSelectionCostWithOverhead
              selectionCost overhead)
            U
            hTarget ∧
        ambientTargetObservationSelectionCostRank
            (z := z)
            obsFamily
            f
            (correctedConcreteObservationSelectionCostWithOverhead
              selectionCost overhead)
            U
            hTarget =
          ambientTargetObservationSelectionCostRank
              (z := z)
              obsFamily
              f
              selectionCost
              U
              hTarget +
            overhead ∧
        IdentifiesLanguageFromPositiveData
          (correctedConcreteCertifiedWorkingGrammarHypLanguage
            (selectedObservationProduct obsFamily S)
            f)
          (correctedConcreteCertifiedWorkingGrammarLearner
            hα
            (selectedObservationProduct obsFamily S)
            f)
          language ∧
        ∃
          C :
            CorrectedConcreteCertifiedWorkingGrammarHypothesis
              α
              (↥S → M)
              (selectedObservationProduct obsFamily S)
              f,
          C.output.grammar.StringLanguage =
              language ∧
            C.bits.length <=
              correctedConcreteCertifiedRankBitBudget
                (startRootedTargetCertifiedDescriptionRank
                  (v := z)
                  hα
                  (selectedObservationProduct obsFamily S)
                  f
                  hSelected)
                f ∧
            C.canonicalSearch.length <=
              correctedConcreteCertifiedRankSearchBudget
                (startRootedTargetCertifiedDescriptionRank
                  (v := z)
                  hα
                  (selectedObservationProduct obsFamily S)
                  f
                  hSelected)
                f := by

  let hSelection :=
    hasCorrectedConcreteObservationSelectionCost_of_fullProductTarget
      (obsFamily := obsFamily)
      (f := f)
      selectionCost
      hTarget

  let result :=
    correctedConcreteObservationMinimumCostSelectionResult
      (z := z)
      obsFamily
      f
      selectionCost
      U
      language
      hSelection

  have hCertified :=
    correctedConcreteObservationMinimumCostSelectionResult_certified_package
      (z := z)
      hα
      obsFamily
      f
      selectionCost
      U
      language
      hSelection
      result

  have hOriginalCost :
      selectionCost result.selected =
        ambientTargetObservationSelectionCostRank
          (z := z)
          obsFamily
          f
          selectionCost
          U
          hTarget := by

    simpa [
      ambientTargetObservationSelectionCostRank,
      ambientTargetObservationSelectionMinimumCost,
      hSelection
    ] using
      result.selected_cost_eq_minimum

  have hRankShift :
      ambientTargetObservationSelectionCostRank
          (z := z)
          obsFamily
          f
          (correctedConcreteObservationSelectionCostWithOverhead
            selectionCost overhead)
          U
          hTarget =
        ambientTargetObservationSelectionCostRank
            (z := z)
            obsFamily
            f
            selectionCost
            U
            hTarget +
          overhead :=
    ambientTargetObservationSelectionCostRank_withOverhead_eq
      (z := z)
      obsFamily
      f
      selectionCost
      overhead
      U
      hTarget

  have hOverheadCost :
      correctedConcreteObservationSelectionCostWithOverhead
          selectionCost overhead result.selected =
        ambientTargetObservationSelectionCostRank
          (z := z)
          obsFamily
          f
          (correctedConcreteObservationSelectionCostWithOverhead
            selectionCost overhead)
          U
          hTarget := by

    unfold
      correctedConcreteObservationSelectionCostWithOverhead

    rw [hOriginalCost, hRankShift]

  exact
    ⟨result.selected,
      result.selected_target,
      hOriginalCost,
      hOverheadCost,
      hRankShift,
      hCertified.1,
      hCertified.2.2⟩

end MinimumSelectionCertifiedOverheadPackage


section ObservationCostOverheadFinalPackage

variable {α : Type u}
variable {ι : Type v}
variable {M : Type w}
variable [Fintype M]
variable [DecidableEq α]
variable [DecidableEq ι]
variable [DecidableEq M]
variable [Monoid M]
variable (hα : Nonempty α)
variable (obsFamily : ι → α → M)
variable (f : Nat)
variable (selectionCost : Finset ι → Nat)
variable (overhead : Nat)
variable (U : Finset ι)

/-- Final shifted-profile, shifted-filtration, exact-rank, Pareto-invariance,
and certified same-selection package for a fixed cost overhead. -/
theorem
    correctedConcreteCertifiedWorkingGrammar_observationSelectionCostOverhead_package :
    (∀ costBudget : Nat,
      CorrectedConcreteObservationSelectionCostProfileClass
          (z := z)
          α
          ι
          M
          obsFamily
          f
          (correctedConcreteObservationSelectionCostWithOverhead
            selectionCost overhead)
          U
          (costBudget + overhead) =
        CorrectedConcreteObservationSelectionCostProfileClass
          (z := z)
          α
          ι
          M
          obsFamily
          f
          selectionCost
          U
          costBudget) ∧
      (∀
        language : Set (Word α),
        ∀ costBudget : Nat,
          correctedConcreteObservationCostBudgetFiltration
              (z := z)
              obsFamily
              f
              (correctedConcreteObservationSelectionCostWithOverhead
                selectionCost overhead)
              U
              language
              (costBudget + overhead) =
            correctedConcreteObservationCostBudgetFiltration
              (z := z)
              obsFamily
              f
              selectionCost
              U
              language
              costBudget) ∧
      (∀
        language : Set (Word α),
        ∀ rank : Nat,
          (language ∈
              CorrectedConcreteObservationSelectionExactCostRankClass
                (z := z)
                α
                ι
                M
                obsFamily
                f
                (correctedConcreteObservationSelectionCostWithOverhead
                  selectionCost overhead)
                U
                (rank + overhead) ↔
            language ∈
              CorrectedConcreteObservationSelectionExactCostRankClass
                (z := z)
                α
                ι
                M
                obsFamily
                f
                selectionCost
                U
                rank)) ∧
      (∀
        language : Set (Word α),
          correctedConcreteObservationParetoSelections
              (z := z)
              obsFamily
              f
              (correctedConcreteObservationSelectionCostWithOverhead
                selectionCost overhead)
              U
              language =
            correctedConcreteObservationParetoSelections
              (z := z)
              obsFamily
              f
              selectionCost
              U
              language) ∧
      (∀
        language : Set (Word α),
        ∀ hTarget :
          language ∈
            StartRootedCorrectedConcreteTargetClass
              (v := z)
              α
              (↥U → M)
              (selectedObservationProduct obsFamily U)
              f,
          ambientTargetObservationSelectionCostRank
              (z := z)
              obsFamily
              f
              (correctedConcreteObservationSelectionCostWithOverhead
                selectionCost overhead)
              U
              hTarget =
            ambientTargetObservationSelectionCostRank
                (z := z)
                obsFamily
                f
                selectionCost
                U
                hTarget +
              overhead) ∧
      (∀
        language : Set (Word α),
        ∀ hTarget :
          language ∈
            StartRootedCorrectedConcreteTargetClass
              (v := z)
              α
              (↥U → M)
              (selectedObservationProduct obsFamily U)
              f,
          ∃
            (S : Finset ι)
            (hSelected :
              language ∈
                StartRootedCorrectedConcreteTargetClass
                  (v := z)
                  α
                  (↥S → M)
                  (selectedObservationProduct obsFamily S)
                  f),
            selectionCost S =
                ambientTargetObservationSelectionCostRank
                  (z := z)
                  obsFamily
                  f
                  selectionCost
                  U
                  hTarget ∧
              correctedConcreteObservationSelectionCostWithOverhead
                  selectionCost overhead S =
                ambientTargetObservationSelectionCostRank
                  (z := z)
                  obsFamily
                  f
                  (correctedConcreteObservationSelectionCostWithOverhead
                    selectionCost overhead)
                  U
                  hTarget ∧
              IdentifiesLanguageFromPositiveData
                (correctedConcreteCertifiedWorkingGrammarHypLanguage
                  (selectedObservationProduct obsFamily S)
                  f)
                (correctedConcreteCertifiedWorkingGrammarLearner
                  hα
                  (selectedObservationProduct obsFamily S)
                  f)
                language) := by

  refine
    ⟨?_,
      ?_,
      ?_,
      ?_,
      ?_,
      ?_⟩

  · intro costBudget

    exact
      observationSelectionCostProfileClass_withOverhead_eq_shifted
        (z := z)
        costBudget

  · intro language costBudget

    exact
      observationCostBudgetFiltration_withOverhead_eq_shifted
        (z := z)
        costBudget

  · intro language rank

    exact
      observationSelection_mem_exactRankWithOverhead_iff
        (z := z)
        rank

  · intro language

    exact
      correctedConcreteObservationParetoSelections_withOverhead_eq
        (z := z)

  · intro language hTarget

    exact
      ambientTargetObservationSelectionCostRank_withOverhead_eq
        (z := z)
        obsFamily
        f
        selectionCost
        overhead
        U
        hTarget

  · intro language hTarget

    rcases
        ambientTarget_sameMinimumSelection_underCostOverhead_certified_package
          (z := z)
          hα
          obsFamily
          f
          selectionCost
          overhead
          U
          hTarget with
      ⟨S,
        hSelected,
        hOriginalCost,
        hOverheadCost,
        hRankShift,
        hIdentifies,
        C,
        hLanguage,
        hBits,
        hSearch⟩

    exact
      ⟨S,
        hSelected,
        hOriginalCost,
        hOverheadCost,
        hIdentifies⟩

end ObservationCostOverheadFinalPackage

end MCFG
