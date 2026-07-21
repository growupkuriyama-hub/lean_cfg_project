/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG2.ConcreteCanonicalLearnerWorkingGrammarObservationAdditiveWeights

/-!
# ConcreteCanonicalLearnerWorkingGrammarObservationFiniteOptimization.lean

The preceding files develop cardinality, weighted, additive-weight, and Pareto
observation selection.

This file packages those semantic optimization problems as explicit finite
search spaces over the powerset of a finite ambient candidate set.

## Feasible selections

For a finite ambient set

```lean
U : Finset ι
```

define

```lean
correctedConcreteObservationFeasibleSelections
```

as the finite subset of `U.powerset` whose selected-product observations
represent the target language.

Membership is exact:

```text
S is in the finite feasible-selection search
  ↔
S ⊆ U and Product(S) represents the target.
```

The search is nonempty exactly when some finite-cost selection exists.

## Budget-feasible and minimum-cost selections

For an arbitrary cost

```lean
selectionCost : Finset ι → Nat
```

the cost-budget search filters feasible selections by

```text
selectionCost S ≤ costBudget.
```

Its nonemptiness is exactly
`CorrectedConcreteObservationSelectionAtCost`.

Given a proof that some selection exists, the minimum-cost search filters by

```text
selectionCost S = correctedConcreteObservationSelectionMinimumCost ...
```

and is nonempty.  Every member is a genuinely feasible ambient subset attaining
the semantic `Nat.find` minimum.

The same construction applies to the positive additive cost introduced in the
preceding file.

## Finite Pareto frontier

The finite Pareto search consists exactly of the selections satisfying
`CorrectedConcreteObservationSelectionParetoOptimal`.

For every target represented by the full ambient product, this finite frontier
is nonempty.  Its image under the profile map

```text
S ↦ (S.card, selectionCost S)
```

is a finite Pareto-profile search and is also nonempty.

## Explicit search-space bound

Every search in this file is a sub-finset of `U.powerset`.  Hence

```text
number of feasible selections ≤ 2^|U|,
number of cost-budget selections ≤ 2^|U|,
number of minimum-cost selections ≤ 2^|U|,
number of Pareto selections ≤ 2^|U|.
```

These are exhaustive finite-search bounds, not polynomial-time bounds.

## Certified hypotheses from finite Pareto candidates

When the terminal alphabet and observation monoid are finite and decidable,
every member of the finite Pareto search represents the target language.
Therefore its selected-product certified learner identifies the target and has
one exact checked output satisfying the bit and finite-search budgets at the
selected product's minimum certified-description rank.

This gives a finite search object whose successful candidates carry the full
certified-learning conclusion.

## Boundary

The finite filters are classical because semantic target-class membership is
not yet executable.  This file proves finiteness and exhaustiveness, not a
decidable polynomial optimization algorithm.

No target grammar is supplied to any learner.
No `sorry`, `admit`, or `axiom` is used.
-/

namespace MCFG

universe u v w z


section FiniteFeasibleSelectionSearch

variable {α : Type u}
variable {ι : Type v}
variable {M : Type w}
variable [Monoid M]
variable (obsFamily : ι → α → M)
variable (f : Nat)
variable (U : Finset ι)
variable (language : Set (Word α))

/-- Explicit finite search space of all ambient subsets whose selected products
represent the target language. -/
noncomputable def correctedConcreteObservationFeasibleSelections :
    Finset (Finset ι) := by

  classical

  exact
    U.powerset.filter
      (fun S =>
        language ∈
          StartRootedCorrectedConcreteTargetClass
            (v := z)
            α
            (↥S → M)
            (selectedObservationProduct obsFamily S)
            f)

/-- Exact membership theorem for the finite feasible-selection search. -/
theorem mem_correctedConcreteObservationFeasibleSelections_iff
    [DecidableEq ι]
    {S : Finset ι} :
    S ∈
        correctedConcreteObservationFeasibleSelections
          (z := z)
          obsFamily f U language ↔
      S ⊆ U ∧
        language ∈
          StartRootedCorrectedConcreteTargetClass
            (v := z)
            α
            (↥S → M)
            (selectedObservationProduct obsFamily S)
            f := by

  classical

  simp [
    correctedConcreteObservationFeasibleSelections
  ]

/-- Every feasible candidate belongs to the ambient powerset. -/
theorem correctedConcreteObservationFeasibleSelections_subset_powerset
    [DecidableEq ι] :
    correctedConcreteObservationFeasibleSelections
        (z := z)
        obsFamily f U language ⊆
      U.powerset := by

  intro S hS

  exact
    Finset.mem_powerset.mpr
      ((mem_correctedConcreteObservationFeasibleSelections_iff
        (z := z)
        obsFamily f U language).mp
        hS).1

/-- The finite feasible-selection search has at most `2^|U|` candidates. -/
theorem correctedConcreteObservationFeasibleSelections_card_le_two_pow
    [DecidableEq ι] :
    (correctedConcreteObservationFeasibleSelections
        (z := z)
        obsFamily f U language).card <=
      2 ^ U.card := by

  calc
    (correctedConcreteObservationFeasibleSelections
        (z := z)
        obsFamily f U language).card <=
      U.powerset.card :=
        Finset.card_le_card
          (correctedConcreteObservationFeasibleSelections_subset_powerset
            (z := z)
            obsFamily f U language)

    _ =
      2 ^ U.card := by
        simpa using
          Finset.card_powerset U

end FiniteFeasibleSelectionSearch


section FeasibleSearchExistence

variable {α : Type u}
variable {ι : Type v}
variable {M : Type w}
variable [DecidableEq ι]
variable [Monoid M]
variable {obsFamily : ι → α → M}
variable {f : Nat}
variable {selectionCost : Finset ι → Nat}
variable {U : Finset ι}
variable {language : Set (Word α)}

/-- The finite feasible-selection search is nonempty exactly when some
finite-cost observation selection exists. -/
theorem
    correctedConcreteObservationFeasibleSelections_nonempty_iff_hasSelectionCost :
    (correctedConcreteObservationFeasibleSelections
          (z := z)
          obsFamily f U language).Nonempty ↔
      HasCorrectedConcreteObservationSelectionCost
        (obsFamily := obsFamily)
        (f := f)
        selectionCost
        U language := by

  constructor

  · intro hNonempty

    rcases hNonempty with
      ⟨S, hS⟩

    rcases
        (mem_correctedConcreteObservationFeasibleSelections_iff
          (z := z)
          obsFamily f U language).mp
          hS with
      ⟨hSU, hTarget⟩

    exact
      ⟨selectionCost S,
        S,
        hSU,
        Nat.le_refl _,
        hTarget⟩

  · intro hSelection

    rcases hSelection with
      ⟨costBudget,
        S,
        hSU,
        hCost,
        hTarget⟩

    exact
      ⟨S,
        (mem_correctedConcreteObservationFeasibleSelections_iff
          (z := z)
          obsFamily f U language).mpr
          ⟨hSU, hTarget⟩⟩

/-- A full ambient-product target makes the finite feasible-selection search
nonempty. -/
theorem
    correctedConcreteObservationFeasibleSelections_nonempty_of_fullProductTarget
    (hTarget :
      language ∈
        StartRootedCorrectedConcreteTargetClass
          (v := z)
          α
          (↥U → M)
          (selectedObservationProduct obsFamily U)
          f) :
    (correctedConcreteObservationFeasibleSelections
        (z := z)
        obsFamily f U language).Nonempty := by

  exact
    ⟨U,
      (mem_correctedConcreteObservationFeasibleSelections_iff
        (z := z)
        obsFamily f U language).mpr
        ⟨by
            intro index hindex
            exact hindex,
          hTarget⟩⟩

end FeasibleSearchExistence


section FiniteCostBudgetSearch

variable {α : Type u}
variable {ι : Type v}
variable {M : Type w}
variable [Monoid M]
variable (obsFamily : ι → α → M)
variable (f : Nat)
variable (selectionCost : Finset ι → Nat)
variable (U : Finset ι)
variable (language : Set (Word α))
variable (costBudget : Nat)

/-- Explicit finite search of all feasible ambient selections within one cost
budget. -/
noncomputable def correctedConcreteObservationCostFeasibleSelections :
    Finset (Finset ι) := by

  classical

  exact
    (correctedConcreteObservationFeasibleSelections
      (z := z)
      obsFamily f U language).filter
      (fun S =>
        selectionCost S <= costBudget)

/-- Exact membership theorem for the finite cost-budget search. -/
theorem mem_correctedConcreteObservationCostFeasibleSelections_iff
    [DecidableEq ι]
    {S : Finset ι} :
    S ∈
        correctedConcreteObservationCostFeasibleSelections
          (z := z)
          obsFamily f selectionCost U language costBudget ↔
      S ⊆ U ∧
        selectionCost S <= costBudget ∧
        language ∈
          StartRootedCorrectedConcreteTargetClass
            (v := z)
            α
            (↥S → M)
            (selectedObservationProduct obsFamily S)
            f := by

  classical

  constructor

  · intro hS

    rcases Finset.mem_filter.mp hS with
      ⟨hFeasible, hCost⟩

    rcases
        (mem_correctedConcreteObservationFeasibleSelections_iff
          (z := z)
          obsFamily f U language).mp
          hFeasible with
      ⟨hSU, hTarget⟩

    exact
      ⟨hSU,
        hCost,
        hTarget⟩

  · intro hS

    rcases hS with
      ⟨hSU, hCost, hTarget⟩

    exact
      Finset.mem_filter.mpr
        ⟨(mem_correctedConcreteObservationFeasibleSelections_iff
            (z := z)
            obsFamily f U language).mpr
            ⟨hSU, hTarget⟩,
          hCost⟩

/-- Nonemptiness of the finite cost-budget search is exactly weighted
selection feasibility at that budget. -/
theorem
    correctedConcreteObservationCostFeasibleSelections_nonempty_iff :
    (correctedConcreteObservationCostFeasibleSelections
          (z := z)
          obsFamily f selectionCost U language costBudget).Nonempty ↔
      CorrectedConcreteObservationSelectionAtCost
        (obsFamily := obsFamily)
        (f := f)
        selectionCost
        U language costBudget := by

  constructor

  · intro hNonempty

    rcases hNonempty with
      ⟨S, hS⟩

    rcases
        (mem_correctedConcreteObservationCostFeasibleSelections_iff
          (z := z)
          obsFamily f selectionCost U language costBudget).mp
          hS with
      ⟨hSU, hCost, hTarget⟩

    exact
      ⟨S,
        hSU,
        hCost,
        hTarget⟩

  · intro hSelection

    rcases hSelection with
      ⟨S, hSU, hCost, hTarget⟩

    exact
      ⟨S,
        (mem_correctedConcreteObservationCostFeasibleSelections_iff
          (z := z)
          obsFamily f selectionCost U language costBudget).mpr
          ⟨hSU, hCost, hTarget⟩⟩

/-- The finite cost-budget search is contained in the ambient powerset. -/
theorem
    correctedConcreteObservationCostFeasibleSelections_subset_powerset
    [DecidableEq ι] :
    correctedConcreteObservationCostFeasibleSelections
        (z := z)
        obsFamily f selectionCost U language costBudget ⊆
      U.powerset := by

  intro S hS

  exact
    Finset.mem_powerset.mpr
      ((mem_correctedConcreteObservationCostFeasibleSelections_iff
        (z := z)
        obsFamily f selectionCost U language costBudget).mp
        hS).1

/-- The finite cost-budget search has at most `2^|U|` candidates. -/
theorem
    correctedConcreteObservationCostFeasibleSelections_card_le_two_pow
    [DecidableEq ι] :
    (correctedConcreteObservationCostFeasibleSelections
        (z := z)
        obsFamily f selectionCost U language costBudget).card <=
      2 ^ U.card := by

  calc
    (correctedConcreteObservationCostFeasibleSelections
        (z := z)
        obsFamily f selectionCost U language costBudget).card <=
      U.powerset.card :=
        Finset.card_le_card
          (correctedConcreteObservationCostFeasibleSelections_subset_powerset
            (z := z)
            obsFamily f selectionCost U language costBudget)

    _ =
      2 ^ U.card := by
        simpa using
          Finset.card_powerset U

end FiniteCostBudgetSearch


section FiniteMinimumCostSearch

variable {α : Type u}
variable {ι : Type v}
variable {M : Type w}
variable [Monoid M]
variable {obsFamily : ι → α → M}
variable {f : Nat}
variable (selectionCost : Finset ι → Nat)
variable {U : Finset ι}
variable {language : Set (Word α)}

/-- Explicit finite search of all selections attaining the semantic minimum
cost. -/
noncomputable def correctedConcreteObservationMinimumCostSelections
    (hSelection :
      HasCorrectedConcreteObservationSelectionCost
        (obsFamily := obsFamily)
        (f := f)
        selectionCost
        U language) :
    Finset (Finset ι) := by

  classical

  exact
    (correctedConcreteObservationFeasibleSelections
      (z := z)
      obsFamily f U language).filter
      (fun S =>
        selectionCost S =
          correctedConcreteObservationSelectionMinimumCost
            selectionCost hSelection)

/-- Exact membership theorem for the finite minimum-cost search. -/
theorem mem_correctedConcreteObservationMinimumCostSelections_iff
    [DecidableEq ι]
    (hSelection :
      HasCorrectedConcreteObservationSelectionCost
        (obsFamily := obsFamily)
        (f := f)
        selectionCost
        U language)
    {S : Finset ι} :
    S ∈
        correctedConcreteObservationMinimumCostSelections
          (z := z)
          selectionCost hSelection ↔
      S ⊆ U ∧
        language ∈
          StartRootedCorrectedConcreteTargetClass
            (v := z)
            α
            (↥S → M)
            (selectedObservationProduct obsFamily S)
            f ∧
        selectionCost S =
          correctedConcreteObservationSelectionMinimumCost
            selectionCost hSelection := by

  classical

  constructor

  · intro hS

    rcases Finset.mem_filter.mp hS with
      ⟨hFeasible, hCost⟩

    rcases
        (mem_correctedConcreteObservationFeasibleSelections_iff
          (z := z)
          obsFamily f U language).mp
          hFeasible with
      ⟨hSU, hTarget⟩

    exact
      ⟨hSU,
        hTarget,
        hCost⟩

  · intro hS

    rcases hS with
      ⟨hSU, hTarget, hCost⟩

    exact
      Finset.mem_filter.mpr
        ⟨(mem_correctedConcreteObservationFeasibleSelections_iff
            (z := z)
            obsFamily f U language).mpr
            ⟨hSU, hTarget⟩,
          hCost⟩

/-- The finite minimum-cost search is nonempty. -/
theorem correctedConcreteObservationMinimumCostSelections_nonempty
    [DecidableEq ι]
    (hSelection :
      HasCorrectedConcreteObservationSelectionCost
        (obsFamily := obsFamily)
        (f := f)
        selectionCost
        U language) :
    (correctedConcreteObservationMinimumCostSelections
        (z := z)
        selectionCost hSelection).Nonempty := by

  rcases hSelection.exists_selection_exact_minimumCost with
    ⟨S, hSU, hCost, hTarget⟩

  exact
    ⟨S,
      (mem_correctedConcreteObservationMinimumCostSelections_iff
        (z := z)
        selectionCost hSelection).mpr
        ⟨hSU,
          hTarget,
          hCost⟩⟩

/-- Every member of the minimum-cost search has cost no greater than any other
feasible ambient selection. -/
theorem correctedConcreteObservationMinimumCostSelections_le_every_feasible
    [DecidableEq ι]
    (hSelection :
      HasCorrectedConcreteObservationSelectionCost
        (obsFamily := obsFamily)
        (f := f)
        selectionCost
        U language)
    {S R : Finset ι}
    (hS :
      S ∈
        correctedConcreteObservationMinimumCostSelections
          (z := z)
          selectionCost hSelection)
    (hRU : R ⊆ U)
    (hRTarget :
      language ∈
        StartRootedCorrectedConcreteTargetClass
          (v := z)
          α
          (↥R → M)
          (selectedObservationProduct obsFamily R)
          f) :
    selectionCost S <=
      selectionCost R := by

  have hSCost :
      selectionCost S =
        correctedConcreteObservationSelectionMinimumCost
          selectionCost hSelection :=
    ((mem_correctedConcreteObservationMinimumCostSelections_iff
      (z := z)
      selectionCost hSelection).mp
      hS).2.2

  rw [hSCost]

  apply
    hSelection.minimumCost_le_of_selection

  exact
    ⟨R,
      hRU,
      Nat.le_refl _,
      hRTarget⟩

/-- The finite minimum-cost search is contained in the ambient powerset. -/
theorem correctedConcreteObservationMinimumCostSelections_subset_powerset
    [DecidableEq ι]
    (hSelection :
      HasCorrectedConcreteObservationSelectionCost
        (obsFamily := obsFamily)
        (f := f)
        selectionCost
        U language) :
    correctedConcreteObservationMinimumCostSelections
        (z := z)
        selectionCost hSelection ⊆
      U.powerset := by

  intro S hS

  exact
    Finset.mem_powerset.mpr
      ((mem_correctedConcreteObservationMinimumCostSelections_iff
        (z := z)
        selectionCost hSelection).mp
        hS).1

/-- The finite minimum-cost search has at most `2^|U|` candidates. -/
theorem correctedConcreteObservationMinimumCostSelections_card_le_two_pow
    [DecidableEq ι]
    (hSelection :
      HasCorrectedConcreteObservationSelectionCost
        (obsFamily := obsFamily)
        (f := f)
        selectionCost
        U language) :
    (correctedConcreteObservationMinimumCostSelections
        (z := z)
        selectionCost hSelection).card <=
      2 ^ U.card := by

  calc
    (correctedConcreteObservationMinimumCostSelections
        (z := z)
        selectionCost hSelection).card <=
      U.powerset.card :=
        Finset.card_le_card
          (correctedConcreteObservationMinimumCostSelections_subset_powerset
            (z := z)
            selectionCost hSelection)

    _ =
      2 ^ U.card := by
        simpa using
          Finset.card_powerset U

end FiniteMinimumCostSearch


section FiniteParetoSearch

variable {α : Type u}
variable {ι : Type v}
variable {M : Type w}
variable [Monoid M]
variable (obsFamily : ι → α → M)
variable (f : Nat)
variable (selectionCost : Finset ι → Nat)
variable (U : Finset ι)
variable (language : Set (Word α))

/-- Explicit finite Pareto frontier over the ambient powerset. -/
noncomputable def correctedConcreteObservationParetoSelections :
    Finset (Finset ι) := by

  classical

  exact
    U.powerset.filter
      (fun S =>
        CorrectedConcreteObservationSelectionParetoOptimal
          (z := z)
          obsFamily f selectionCost U language S)

/-- Exact membership theorem for the finite Pareto search. -/
theorem mem_correctedConcreteObservationParetoSelections_iff
    [DecidableEq ι]
    {S : Finset ι} :
    S ∈
        correctedConcreteObservationParetoSelections
          (z := z)
          obsFamily f selectionCost U language ↔
      CorrectedConcreteObservationSelectionParetoOptimal
        (z := z)
        obsFamily f selectionCost U language S := by

  classical

  constructor

  · intro hS

    exact
      (Finset.mem_filter.mp hS).2

  · intro hPareto

    exact
      Finset.mem_filter.mpr
        ⟨Finset.mem_powerset.mpr
            hPareto.1,
          hPareto⟩

/-- The finite Pareto search is nonempty for every full ambient-product
target. -/
theorem correctedConcreteObservationParetoSelections_nonempty_of_fullProductTarget
    [DecidableEq ι]
    (hTarget :
      language ∈
        StartRootedCorrectedConcreteTargetClass
          (v := z)
          α
          (↥U → M)
          (selectedObservationProduct obsFamily U)
          f) :
    (correctedConcreteObservationParetoSelections
        (z := z)
        obsFamily f selectionCost U language).Nonempty := by

  rcases
      ambientTarget_exists_paretoObservationSelection
        (z := z)
        obsFamily f selectionCost U hTarget with
    ⟨S, hPareto⟩

  exact
    ⟨S,
      (mem_correctedConcreteObservationParetoSelections_iff
        (z := z)
        obsFamily f selectionCost U language).mpr
        hPareto⟩

/-- The finite Pareto search is contained in the ambient powerset. -/
theorem correctedConcreteObservationParetoSelections_subset_powerset
    [DecidableEq ι] :
    correctedConcreteObservationParetoSelections
        (z := z)
        obsFamily f selectionCost U language ⊆
      U.powerset := by

  intro S hS

  exact
    Finset.mem_powerset.mpr
      ((mem_correctedConcreteObservationParetoSelections_iff
        (z := z)
        obsFamily f selectionCost U language).mp
        hS).1

/-- The finite Pareto frontier has at most `2^|U|` selected subsets. -/
theorem correctedConcreteObservationParetoSelections_card_le_two_pow
    [DecidableEq ι] :
    (correctedConcreteObservationParetoSelections
        (z := z)
        obsFamily f selectionCost U language).card <=
      2 ^ U.card := by

  calc
    (correctedConcreteObservationParetoSelections
        (z := z)
        obsFamily f selectionCost U language).card <=
      U.powerset.card :=
        Finset.card_le_card
          (correctedConcreteObservationParetoSelections_subset_powerset
            (z := z)
            obsFamily f selectionCost U language)

    _ =
      2 ^ U.card := by
        simpa using
          Finset.card_powerset U

/-- Finite image of the Pareto frontier under the two-criterion profile map. -/
noncomputable def correctedConcreteObservationParetoProfiles :
    Finset (Nat × Nat) := by

  classical

  exact
    (correctedConcreteObservationParetoSelections
      (z := z)
      obsFamily f selectionCost U language).image
      (correctedConcreteObservationSelectionProfile
        selectionCost)

/-- Exact membership theorem for the finite Pareto-profile search. -/
theorem mem_correctedConcreteObservationParetoProfiles_iff
    [DecidableEq ι]
    {profile : Nat × Nat} :
    profile ∈
        correctedConcreteObservationParetoProfiles
          (z := z)
          obsFamily f selectionCost U language ↔
      ∃ S : Finset ι,
        CorrectedConcreteObservationSelectionParetoOptimal
            (z := z)
            obsFamily f selectionCost U language S ∧
          profile =
            correctedConcreteObservationSelectionProfile
              selectionCost S := by

  classical

  constructor

  · intro hProfile

    rcases Finset.mem_image.mp hProfile with
      ⟨S, hS, hEq⟩

    exact
      ⟨S,
        (mem_correctedConcreteObservationParetoSelections_iff
          (z := z)
          obsFamily f selectionCost U language).mp
          hS,
        hEq.symm⟩

  · intro hProfile

    rcases hProfile with
      ⟨S, hPareto, hEq⟩

    apply Finset.mem_image.mpr

    exact
      ⟨S,
        (mem_correctedConcreteObservationParetoSelections_iff
          (z := z)
          obsFamily f selectionCost U language).mpr
          hPareto,
        hEq.symm⟩

/-- The finite Pareto-profile search is nonempty for every full ambient-product
target. -/
theorem correctedConcreteObservationParetoProfiles_nonempty_of_fullProductTarget
    [DecidableEq ι]
    (hTarget :
      language ∈
        StartRootedCorrectedConcreteTargetClass
          (v := z)
          α
          (↥U → M)
          (selectedObservationProduct obsFamily U)
          f) :
    (correctedConcreteObservationParetoProfiles
        (z := z)
        obsFamily f selectionCost U language).Nonempty := by

  rcases
      correctedConcreteObservationParetoSelections_nonempty_of_fullProductTarget
        (z := z)
        obsFamily f selectionCost U language hTarget with
    ⟨S, hS⟩

  exact
    ⟨correctedConcreteObservationSelectionProfile
        selectionCost S,
      Finset.mem_image.mpr
        ⟨S, hS, rfl⟩⟩

/-- The number of distinct Pareto profiles is at most the number of selected
subsets and hence at most `2^|U|`. -/
theorem correctedConcreteObservationParetoProfiles_card_le_two_pow
    [DecidableEq ι] :
    (correctedConcreteObservationParetoProfiles
        (z := z)
        obsFamily f selectionCost U language).card <=
      2 ^ U.card := by

  calc
    (correctedConcreteObservationParetoProfiles
        (z := z)
        obsFamily f selectionCost U language).card <=
      (correctedConcreteObservationParetoSelections
        (z := z)
        obsFamily f selectionCost U language).card :=
          Finset.card_image_le

    _ <=
      2 ^ U.card :=
        correctedConcreteObservationParetoSelections_card_le_two_pow
          (z := z)
          obsFamily f selectionCost U language

end FiniteParetoSearch


section ScalarMinimumSearchInsidePareto

variable {α : Type u}
variable {ι : Type v}
variable {M : Type w}
variable [DecidableEq ι]
variable [Monoid M]
variable {obsFamily : ι → α → M}
variable {f : Nat}
variable {selectionCost : Finset ι → Nat}
variable {U : Finset ι}
variable {language : Set (Word α)}

/-- Every exact minimum of the scalarized cost belongs to the finite Pareto
search. -/
theorem
    correctedConcreteObservationScalarMinimumSelections_subset_paretoSelections
    (hSelection :
      HasCorrectedConcreteObservationSelectionCost
        (obsFamily := obsFamily)
        (f := f)
        (correctedConcreteObservationSelectionParetoScalarCost
          selectionCost)
        U language) :
    correctedConcreteObservationMinimumCostSelections
        (z := z)
        (correctedConcreteObservationSelectionParetoScalarCost
          selectionCost)
        hSelection ⊆
      correctedConcreteObservationParetoSelections
        (z := z)
        obsFamily f selectionCost U language := by

  intro S hS

  rcases
      (mem_correctedConcreteObservationMinimumCostSelections_iff
        (z := z)
        (correctedConcreteObservationSelectionParetoScalarCost
          selectionCost)
        hSelection).mp
        hS with
    ⟨hSU, hTarget, hScalar⟩

  apply
    (mem_correctedConcreteObservationParetoSelections_iff
      (z := z)
      obsFamily f selectionCost U language).mpr

  exact
    observationSelection_exactScalarMinimum_isPareto
      (z := z)
      hSelection hSU hScalar hTarget

end ScalarMinimumSearchInsidePareto


section FiniteParetoCertifiedCandidates

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
variable (U : Finset ι)
variable (language : Set (Word α))

/-- Every member of the explicit finite Pareto search has its own certified
learner and exact minimum-description-rank checked output. -/
theorem correctedConcreteObservationParetoSelection_certified_package
    {S : Finset ι}
    (hS :
      S ∈
        correctedConcreteObservationParetoSelections
          (z := z)
          obsFamily f selectionCost U language) :
    IdentifiesLanguageFromPositiveData
        (correctedConcreteCertifiedWorkingGrammarHypLanguage
          (selectedObservationProduct obsFamily S)
          f)
        (correctedConcreteCertifiedWorkingGrammarLearner
          hα
          (selectedObservationProduct obsFamily S)
          f)
        language ∧
      language ∈
        CorrectedConcreteCertifiedRankProfileClass
          (α := α)
          (M := ↥S → M)
          (selectedObservationProduct obsFamily S)
          f
          (startRootedTargetCertifiedDescriptionRank
            (v := z)
            hα
            (selectedObservationProduct obsFamily S)
            f
            ((mem_correctedConcreteObservationParetoSelections_iff
              (z := z)
              obsFamily f selectionCost U language).mp
              hS).2.1) ∧
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
                ((mem_correctedConcreteObservationParetoSelections_iff
                  (z := z)
                  obsFamily f selectionCost U language).mp
                  hS).2.1)
              f ∧
          C.canonicalSearch.length <=
            correctedConcreteCertifiedRankSearchBudget
              (startRootedTargetCertifiedDescriptionRank
                (v := z)
                hα
                (selectedObservationProduct obsFamily S)
                f
                ((mem_correctedConcreteObservationParetoSelections_iff
                  (z := z)
                  obsFamily f selectionCost U language).mp
                  hS).2.1)
              f := by

  let hPareto :=
    (mem_correctedConcreteObservationParetoSelections_iff
      (z := z)
      obsFamily f selectionCost U language).mp
      hS

  let hTarget :=
    hPareto.2.1

  exact
    ⟨selectedProductCertifiedLearner_identifies_targetClass
        (z := z)
        hα obsFamily f S
        language hTarget,
      startRootedTarget_mem_minimumCertifiedDescriptionRankProfile
        (v := z)
        hα
        (selectedObservationProduct obsFamily S)
        f
        hTarget,
      startRootedTarget_exists_output_at_minimumCertifiedDescriptionRank
        (v := z)
        hα
        (selectedObservationProduct obsFamily S)
        f
        hTarget⟩

/-- A full ambient-product target yields a nonempty finite Pareto search, and
every candidate in that search carries the certified-learning conclusion. -/
theorem
    fullProductTarget_finiteParetoCertifiedSearch_package
    (hTarget :
      language ∈
        StartRootedCorrectedConcreteTargetClass
          (v := z)
          α
          (↥U → M)
          (selectedObservationProduct obsFamily U)
          f) :
    (correctedConcreteObservationParetoSelections
          (z := z)
          obsFamily f selectionCost U language).Nonempty ∧
      (correctedConcreteObservationParetoSelections
          (z := z)
          obsFamily f selectionCost U language).card <=
        2 ^ U.card ∧
      ∀ S : Finset ι,
        S ∈
          correctedConcreteObservationParetoSelections
            (z := z)
            obsFamily f selectionCost U language →
        IdentifiesLanguageFromPositiveData
          (correctedConcreteCertifiedWorkingGrammarHypLanguage
            (selectedObservationProduct obsFamily S)
            f)
          (correctedConcreteCertifiedWorkingGrammarLearner
            hα
            (selectedObservationProduct obsFamily S)
            f)
          language := by

  exact
    ⟨correctedConcreteObservationParetoSelections_nonempty_of_fullProductTarget
        (z := z)
        obsFamily f selectionCost U language hTarget,
      correctedConcreteObservationParetoSelections_card_le_two_pow
        (z := z)
        obsFamily f selectionCost U language,
      fun S hS =>
        (correctedConcreteObservationParetoSelection_certified_package
          (z := z)
          hα obsFamily f selectionCost U language hS).1⟩

end FiniteParetoCertifiedCandidates


section PositiveAdditiveFiniteOptimization

variable {α : Type u}
variable {ι : Type v}
variable {M : Type w}
variable [DecidableEq ι]
variable [Monoid M]
variable (obsFamily : ι → α → M)
variable (f : Nat)
variable (coordinateWeight : ι → Nat)
variable (U : Finset ι)
variable (language : Set (Word α))
variable (costBudget : Nat)

/-- Explicit finite search within a positive additive coordinate-cost budget. -/
noncomputable def
    correctedConcreteObservationPositiveAdditiveCostFeasibleSelections :
    Finset (Finset ι) :=
  correctedConcreteObservationCostFeasibleSelections
    (z := z)
    obsFamily
    f
    (correctedConcreteObservationSelectionPositiveAdditiveCost
      coordinateWeight)
    U
    language
    costBudget

/-- Exact membership theorem for the positive additive budget search. -/
theorem
    mem_correctedConcreteObservationPositiveAdditiveCostFeasibleSelections_iff
    {S : Finset ι} :
    S ∈
        correctedConcreteObservationPositiveAdditiveCostFeasibleSelections
          (z := z)
          obsFamily f coordinateWeight U language costBudget ↔
      S ⊆ U ∧
        correctedConcreteObservationSelectionPositiveAdditiveCost
            coordinateWeight S <=
          costBudget ∧
        language ∈
          StartRootedCorrectedConcreteTargetClass
            (v := z)
            α
            (↥S → M)
            (selectedObservationProduct obsFamily S)
            f := by

  exact
    mem_correctedConcreteObservationCostFeasibleSelections_iff
      (z := z)
      obsFamily
      f
      (correctedConcreteObservationSelectionPositiveAdditiveCost
        coordinateWeight)
      U
      language
      costBudget

/-- The positive additive budget search has at most `2^|U|` candidates. -/
theorem
    correctedConcreteObservationPositiveAdditiveCostFeasibleSelections_card_le_two_pow :
    (correctedConcreteObservationPositiveAdditiveCostFeasibleSelections
        (z := z)
        obsFamily f coordinateWeight U language costBudget).card <=
      2 ^ U.card := by

  exact
    correctedConcreteObservationCostFeasibleSelections_card_le_two_pow
      (z := z)
      obsFamily
      f
      (correctedConcreteObservationSelectionPositiveAdditiveCost
        coordinateWeight)
      U
      language
      costBudget

end PositiveAdditiveFiniteOptimization


section ObservationFiniteOptimizationFinalPackage

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
variable (U : Finset ι)

/-- Final explicit finite-search, cardinality-bound, Pareto-frontier, and
certified-candidate package. -/
theorem
    correctedConcreteCertifiedWorkingGrammar_observationFiniteOptimization_package :
    (∀ language : Set (Word α),
      (correctedConcreteObservationFeasibleSelections
          (z := z)
          obsFamily f U language).card <=
        2 ^ U.card) ∧
      (∀
        language : Set (Word α),
        ∀ costBudget : Nat,
          ((correctedConcreteObservationCostFeasibleSelections
              (z := z)
              obsFamily f selectionCost U language costBudget).Nonempty ↔
            CorrectedConcreteObservationSelectionAtCost
              (obsFamily := obsFamily)
              (f := f)
              selectionCost
              U
              language
              costBudget)) ∧
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
          (correctedConcreteObservationParetoSelections
              (z := z)
              obsFamily f selectionCost U language).Nonempty ∧
            (correctedConcreteObservationParetoSelections
              (z := z)
              obsFamily f selectionCost U language).card <=
              2 ^ U.card ∧
            ∀ S : Finset ι,
              S ∈
                correctedConcreteObservationParetoSelections
                  (z := z)
                  obsFamily f selectionCost U language →
              IdentifiesLanguageFromPositiveData
                (correctedConcreteCertifiedWorkingGrammarHypLanguage
                  (selectedObservationProduct obsFamily S)
                  f)
                (correctedConcreteCertifiedWorkingGrammarLearner
                  hα
                  (selectedObservationProduct obsFamily S)
                  f)
                language) := by

  exact
    ⟨fun language =>
        correctedConcreteObservationFeasibleSelections_card_le_two_pow
          (z := z)
          obsFamily f U language,
      fun language costBudget =>
        correctedConcreteObservationCostFeasibleSelections_nonempty_iff
          (z := z)
          obsFamily f selectionCost U language costBudget,
      fun language hTarget =>
        fullProductTarget_finiteParetoCertifiedSearch_package
          (z := z)
          hα obsFamily f selectionCost U language hTarget⟩

end ObservationFiniteOptimizationFinalPackage

end MCFG
