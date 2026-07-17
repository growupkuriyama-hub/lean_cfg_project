/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG.ConcreteCanonicalLearnerWorkingGrammarObservationSelection

/-!
# ConcreteCanonicalLearnerWorkingGrammarObservationSelectionIrredundancy.lean

The preceding file defines finite selected-observation products and the least
number of coordinates needed to represent a target language from a finite
ambient candidate set.

This file turns that numerical minimum into structural irredundancy and
lower-bound principles.

## Cardinality-minimum selections

For a finite ambient candidate set `U`, a selected subset `S` is a
cardinality-minimum observation selection for `language` when

```text
S ⊆ U,
language is represented by Product(S),
and
every representing R ⊆ U satisfies |S| ≤ |R|.
```

The `Nat.find` minimum from the preceding file is attained by such an `S`.

Every cardinality-minimum selection is inclusion-irredundant:

```text
R ⊂ S
⇒
language is not represented by Product(R).
```

Therefore every selected coordinate is essential.  If `i ∈ S`, deleting `i`
produces a strict observation refinement

```text
Product(S.erase i)  →  Product(S)
```

whose strict gain class contains the target language.  Equivalently, the target
class grows strictly and the observation-failure class shrinks strictly at
every coordinate of a minimum selection.

## Lower-bound criterion

The minimum selection cardinality has an exact obstruction form:

```text
selection is impossible at budget k
  ↔
k < minimum selection cardinality.
```

Hence, if every `S ⊆ U` of cardinality at most `k` fails to represent the
language, then the minimum selection cardinality is strictly larger than `k`.

This is the interface needed for future reductions and NP-hardness proofs:
a combinatorial lower-bound argument may work entirely by excluding all small
selected products.

We also characterize the zero level:

```text
minimum selection cardinality = 0
  ↔
the empty selected product represents the language.
```

Thus failure under the empty product implies that at least one observation
coordinate is necessary.

## Certified learner at an irredundant minimum

For a language represented by the full ambient product, there exists an actual
minimum-cardinality selected subset `S` such that

* `S` is inclusion-irredundant for the language;
* every coordinate of `S` is essential;
* the certified learner for `Product(S)` identifies the language; and
* one exact certified output satisfies the bit and finite-search budgets at the
  selected product's minimum certified-description rank.

No algorithm for finding this minimum subset is asserted.  The results are
semantic minimum and obstruction theorems over a finite ambient candidate set.

No target grammar is supplied to any learner.
No `sorry`, `admit`, or `axiom` is used.
-/

namespace MCFG

universe u v w z


section SelectionMinimumAndIrredundancyDefinitions

variable (α : Type u)
variable (ι : Type v)
variable (M : Type w)
variable [Monoid M]
variable (obsFamily : ι → α → M)
variable (f : Nat)

/-- A selected set is cardinality-minimal among all ambient subsets
representing the target language. -/
def CorrectedConcreteObservationSelectionIsCardinalityMinimum
    (U : Finset ι)
    (language : Set (Word α))
    (S : Finset ι) :
    Prop :=
  S ⊆ U ∧
    language ∈
      StartRootedCorrectedConcreteTargetClass
        (v := z)
        α
        (↥S → M)
        (selectedObservationProduct obsFamily S)
        f ∧
    ∀ R : Finset ι,
      R ⊆ U →
      language ∈
        StartRootedCorrectedConcreteTargetClass
          (v := z)
          α
          (↥R → M)
          (selectedObservationProduct obsFamily R)
          f →
      S.card <= R.card

/-- A selected set is inclusion-irredundant for a target when the target is
represented by the full selection but by no proper selected subset. -/
def CorrectedConcreteObservationSelectionIrredundant
    (language : Set (Word α))
    (S : Finset ι) :
    Prop :=
  language ∈
      StartRootedCorrectedConcreteTargetClass
        (v := z)
        α
        (↥S → M)
        (selectedObservationProduct obsFamily S)
        f ∧
    ∀ R : Finset ι,
      R ⊂ S →
      language ∉
        StartRootedCorrectedConcreteTargetClass
          (v := z)
          α
          (↥R → M)
          (selectedObservationProduct obsFamily R)
          f

/-- A selected coordinate is essential for one target language when deleting
that coordinate destroys target membership. -/
def CorrectedConcreteSelectedObservationCoordinateEssential
    (language : Set (Word α))
    (S : Finset ι)
    (index : ι) :
    Prop :=
  index ∈ S ∧
    language ∉
      StartRootedCorrectedConcreteTargetClass
        (v := z)
        α
        (↥(S.erase index) → M)
        (selectedObservationProduct obsFamily (S.erase index))
        f

end SelectionMinimumAndIrredundancyDefinitions


section MinimumSelectionStructuralProperties

variable {α : Type u}
variable {ι : Type v}
variable {M : Type w}
variable [DecidableEq ι]
variable [Monoid M]
variable {obsFamily : ι → α → M}
variable {f : Nat}
variable {U : Finset ι}
variable {language : Set (Word α)}

/-- An exact `Nat.find` minimum witness is cardinality-minimal among all
representing ambient subsets. -/
theorem
    observationSelection_exactCardinality_isCardinalityMinimum
    (hSelection :
      HasCorrectedConcreteObservationSelection
        (obsFamily := obsFamily)
        (f := f)
        U language)
    {S : Finset ι}
    (hSU : S ⊆ U)
    (hcard :
      S.card =
        correctedConcreteObservationSelectionCardinality
          hSelection)
    (hTarget :
      language ∈
        StartRootedCorrectedConcreteTargetClass
          (v := z)
          α
          (↥S → M)
          (selectedObservationProduct obsFamily S)
          f) :
    CorrectedConcreteObservationSelectionIsCardinalityMinimum
      (z := z)
      α ι M obsFamily f U language S := by

  refine
    ⟨hSU,
      hTarget,
      ?_⟩

  intro R hRU hRTarget

  have hminimum :
      correctedConcreteObservationSelectionCardinality
          hSelection <=
        R.card := by

    apply
      hSelection.cardinality_le_of_selection

    exact
      ⟨R,
        hRU,
        Nat.le_refl _,
        hRTarget⟩

  simpa [hcard] using hminimum

/-- Every cardinality-minimum selection is inclusion-irredundant. -/
theorem
    observationSelection_cardinalityMinimum_irredundant
    {S : Finset ι}
    (hMinimum :
      CorrectedConcreteObservationSelectionIsCardinalityMinimum
        (z := z)
        α ι M obsFamily f U language S) :
    CorrectedConcreteObservationSelectionIrredundant
      (z := z)
      α ι M obsFamily f language S := by

  refine
    ⟨hMinimum.2.1,
      ?_⟩

  intro R hRS hRTarget

  have hSubsetNe :
      R ⊆ S ∧
        R ≠ S :=
    Finset.ssubset_iff_subset_ne.mp
      hRS

  have hRU :
      R ⊆ U := by

    intro index hindex

    exact
      hMinimum.1
        (hSubsetNe.1 hindex)

  have hMinimumCard :
      S.card <= R.card :=
    hMinimum.2.2
      R hRU hRTarget

  have hStrictCard :
      R.card < S.card :=
    Finset.card_lt_card
      hRS

  omega

/-- Every exact minimum-cardinality witness is inclusion-irredundant. -/
theorem
    observationSelection_exactCardinality_irredundant
    (hSelection :
      HasCorrectedConcreteObservationSelection
        (obsFamily := obsFamily)
        (f := f)
        U language)
    {S : Finset ι}
    (hSU : S ⊆ U)
    (hcard :
      S.card =
        correctedConcreteObservationSelectionCardinality
          hSelection)
    (hTarget :
      language ∈
        StartRootedCorrectedConcreteTargetClass
          (v := z)
          α
          (↥S → M)
          (selectedObservationProduct obsFamily S)
          f) :
    CorrectedConcreteObservationSelectionIrredundant
      (z := z)
      α ι M obsFamily f language S := by

  exact
    observationSelection_cardinalityMinimum_irredundant
      (observationSelection_exactCardinality_isCardinalityMinimum
        (z := z)
        hSelection hSU hcard hTarget)

/-- Every coordinate of an irredundant selection is essential for the target
language. -/
theorem
    observationSelection_irredundant_coordinateEssential
    {S : Finset ι}
    (hIrredundant :
      CorrectedConcreteObservationSelectionIrredundant
        (z := z)
        α ι M obsFamily f language S)
    {index : ι}
    (hindex : index ∈ S) :
    CorrectedConcreteSelectedObservationCoordinateEssential
      (z := z)
      α ι M obsFamily f language S index := by

  refine
    ⟨hindex,
      ?_⟩

  apply
    hIrredundant.2
      (S.erase index)

  apply
    Finset.ssubset_iff_subset_ne.mpr

  refine
    ⟨Finset.erase_subset index S,
      ?_⟩

  intro hErase

  have hmem :
      index ∈ S.erase index := by

    rw [hErase]

    exact hindex

  simpa using hmem

/-- Every proper subset of an irredundant selection fails to represent the
target. -/
theorem
    observationSelection_irredundant_not_target_of_ssubset
    {S R : Finset ι}
    (hIrredundant :
      CorrectedConcreteObservationSelectionIrredundant
        (z := z)
        α ι M obsFamily f language S)
    (hRS : R ⊂ S) :
    language ∉
      StartRootedCorrectedConcreteTargetClass
        (v := z)
        α
        (↥R → M)
        (selectedObservationProduct obsFamily R)
        f := by

  exact
    hIrredundant.2 R hRS

/-- A minimum-cardinality selection cannot contain an unused coordinate. -/
theorem
    observationSelection_minimum_coordinateDeletion_fails
    (hSelection :
      HasCorrectedConcreteObservationSelection
        (obsFamily := obsFamily)
        (f := f)
        U language)
    {S : Finset ι}
    (hSU : S ⊆ U)
    (hcard :
      S.card =
        correctedConcreteObservationSelectionCardinality
          hSelection)
    (hTarget :
      language ∈
        StartRootedCorrectedConcreteTargetClass
          (v := z)
          α
          (↥S → M)
          (selectedObservationProduct obsFamily S)
          f)
    {index : ι}
    (hindex : index ∈ S) :
    language ∉
      StartRootedCorrectedConcreteTargetClass
        (v := z)
        α
        (↥(S.erase index) → M)
        (selectedObservationProduct obsFamily (S.erase index))
        f := by

  exact
    (observationSelection_irredundant_coordinateEssential
      (z := z)
      (observationSelection_exactCardinality_irredundant
        (z := z)
        hSelection hSU hcard hTarget)
      hindex).2

end MinimumSelectionStructuralProperties


section MinimumSelectionCoordinateAblation

variable {α : Type u}
variable {ι : Type v}
variable {M : Type w}
variable [DecidableEq ι]
variable [Monoid M]
variable {obsFamily : ι → α → M}
variable {f : Nat}
variable {language : Set (Word α)}

/-- Deleting any coordinate from an irredundant selection gives an essential
refinement step back to the complete selection. -/
theorem
    observationSelection_irredundant_coordinateRefinementEssential
    {S : Finset ι}
    (hIrredundant :
      CorrectedConcreteObservationSelectionIrredundant
        (z := z)
        α ι M obsFamily f language S)
    {index : ι}
    (hindex : index ∈ S) :
    CorrectedConcreteObservationRefinementEssential
      (z := z)
      α
      (↥(S.erase index) → M)
      (↥S → M)
      (selectedObservationProduct obsFamily (S.erase index))
      (selectedObservationProduct obsFamily S)
      f := by

  exact
    ⟨language,
      hIrredundant.1,
      (observationSelection_irredundant_coordinateEssential
        (z := z)
        hIrredundant hindex).2⟩

/-- Every coordinate of an irredundant selection causes strict target-class
growth when restored after deletion. -/
theorem
    observationSelection_irredundant_coordinate_strictTargetGrowth
    {S : Finset ι}
    (hIrredundant :
      CorrectedConcreteObservationSelectionIrredundant
        (z := z)
        α ι M obsFamily f language S)
    {index : ι}
    (hindex : index ∈ S) :
    (StartRootedCorrectedConcreteTargetClass
        (v := z)
        α
        (↥(S.erase index) → M)
        (selectedObservationProduct obsFamily (S.erase index))
        f ⊆
      StartRootedCorrectedConcreteTargetClass
        (v := z)
        α
        (↥S → M)
        (selectedObservationProduct obsFamily S)
        f) ∧
      (StartRootedCorrectedConcreteTargetClass
        (v := z)
        α
        (↥(S.erase index) → M)
        (selectedObservationProduct obsFamily (S.erase index))
        f ≠
      StartRootedCorrectedConcreteTargetClass
        (v := z)
        α
        (↥S → M)
        (selectedObservationProduct obsFamily S)
        f) := by

  exact
    (observationRefinementEssential_iff_strict_targetClass_growth
      (z := z)
      f
      (Refines.selectedObservationProductOfSubset
        obsFamily
        (Finset.erase_subset index S))).mp
      (observationSelection_irredundant_coordinateRefinementEssential
        (z := z)
        hIrredundant hindex)

/-- Every coordinate of an irredundant selection causes strict failure-class
shrinkage when restored after deletion. -/
theorem
    observationSelection_irredundant_coordinate_strictFailureShrinkage
    {S : Finset ι}
    (hIrredundant :
      CorrectedConcreteObservationSelectionIrredundant
        (z := z)
        α ι M obsFamily f language S)
    {index : ι}
    (hindex : index ∈ S) :
    (StartRootedCorrectedConcreteObservationFailureClass
        (z := z)
        α
        (↥S → M)
        (selectedObservationProduct obsFamily S)
        f ⊆
      StartRootedCorrectedConcreteObservationFailureClass
        (z := z)
        α
        (↥(S.erase index) → M)
        (selectedObservationProduct obsFamily (S.erase index))
        f) ∧
      (StartRootedCorrectedConcreteObservationFailureClass
        (z := z)
        α
        (↥S → M)
        (selectedObservationProduct obsFamily S)
        f ≠
      StartRootedCorrectedConcreteObservationFailureClass
        (z := z)
        α
        (↥(S.erase index) → M)
        (selectedObservationProduct obsFamily (S.erase index))
        f) := by

  exact
    (observationRefinementEssential_iff_strict_failureClass_shrinkage
      (z := z)
      f
      (Refines.selectedObservationProductOfSubset
        obsFamily
        (Finset.erase_subset index S))).mp
      (observationSelection_irredundant_coordinateRefinementEssential
        (z := z)
        hIrredundant hindex)

/-- The target itself belongs to the strict gain created by restoring any
coordinate of an irredundant selection. -/
theorem
    observationSelection_irredundant_target_mem_coordinateGain
    {S : Finset ι}
    (hIrredundant :
      CorrectedConcreteObservationSelectionIrredundant
        (z := z)
        α ι M obsFamily f language S)
    {index : ι}
    (hindex : index ∈ S) :
    language ∈
      StartRootedCorrectedConcreteSelectedObservationExtensionGainClass
        (z := z)
        obsFamily f
        (S.erase index)
        S := by

  exact
    ⟨hIrredundant.1,
      (observationSelection_irredundant_coordinateEssential
        (z := z)
        hIrredundant hindex).2⟩

/-- Compact coordinatewise irredundancy/ablation package. -/
theorem observationSelection_irredundant_coordinate_package
    {S : Finset ι}
    (hIrredundant :
      CorrectedConcreteObservationSelectionIrredundant
        (z := z)
        α ι M obsFamily f language S) :
    (∀ index : ι,
      index ∈ S →
      CorrectedConcreteSelectedObservationCoordinateEssential
        (z := z)
        α ι M obsFamily f language S index) ∧
      (∀ index : ι,
        index ∈ S →
        CorrectedConcreteObservationRefinementEssential
          (z := z)
          α
          (↥(S.erase index) → M)
          (↥S → M)
          (selectedObservationProduct obsFamily (S.erase index))
          (selectedObservationProduct obsFamily S)
          f) ∧
      (∀ index : ι,
        index ∈ S →
        language ∈
          StartRootedCorrectedConcreteSelectedObservationExtensionGainClass
            (z := z)
            obsFamily f
            (S.erase index)
            S) := by

  exact
    ⟨fun index hindex =>
        observationSelection_irredundant_coordinateEssential
          (z := z)
          hIrredundant hindex,
      fun index hindex =>
        observationSelection_irredundant_coordinateRefinementEssential
          (z := z)
          hIrredundant hindex,
      fun index hindex =>
        observationSelection_irredundant_target_mem_coordinateGain
          (z := z)
          hIrredundant hindex⟩

end MinimumSelectionCoordinateAblation


section SelectionCardinalityObstructions

variable {α : Type u}
variable {ι : Type v}
variable {M : Type w}
variable [Monoid M]
variable {obsFamily : ι → α → M}
variable {f : Nat}
variable {U : Finset ι}
variable {language : Set (Word α)}

/-- Exact obstruction form of minimum observation-selection cardinality. -/
theorem
    observationSelection_not_atCardinality_iff_lt_minimum
    (hSelection :
      HasCorrectedConcreteObservationSelection
        (obsFamily := obsFamily)
        (f := f)
        U language)
    (budget : Nat) :
    ¬
        CorrectedConcreteObservationSelectionAtCardinality
          (obsFamily := obsFamily)
          (f := f)
          U language budget ↔
      budget <
        correctedConcreteObservationSelectionCardinality
          hSelection := by

  constructor

  · intro hNot

    by_contra hNotLt

    have hMinimum :
        correctedConcreteObservationSelectionCardinality
            hSelection <=
          budget := by
      omega

    exact
      hNot
        ((hSelection.selectionAtCardinality_iff_minimum_le
          budget).mpr
          hMinimum)

  · intro hLt hSelectionBudget

    have hMinimum :
        correctedConcreteObservationSelectionCardinality
            hSelection <=
          budget :=
      (hSelection.selectionAtCardinality_iff_minimum_le
        budget).mp
        hSelectionBudget

    omega

/-- Excluding every ambient subset of cardinality at most `budget` proves a
strict lower bound on the minimum selection cardinality. -/
theorem
    observationSelection_minimum_gt_of_all_small_selections_fail
    (hSelection :
      HasCorrectedConcreteObservationSelection
        (obsFamily := obsFamily)
        (f := f)
        U language)
    (budget : Nat)
    (hFail :
      ∀ S : Finset ι,
        S ⊆ U →
        S.card <= budget →
        language ∉
          StartRootedCorrectedConcreteTargetClass
            (v := z)
            α
            (↥S → M)
            (selectedObservationProduct obsFamily S)
            f) :
    budget <
      correctedConcreteObservationSelectionCardinality
        hSelection := by

  apply
    (observationSelection_not_atCardinality_iff_lt_minimum
      hSelection budget).mp

  intro hAtBudget

  rcases hAtBudget with
    ⟨S, hSU, hcard, hTarget⟩

  exact
    hFail S hSU hcard hTarget

/-- A strict lower bound is equivalent to failure of every selection within the
corresponding cardinality budget. -/
theorem
    observationSelection_minimum_gt_iff_all_small_selections_fail
    (hSelection :
      HasCorrectedConcreteObservationSelection
        (obsFamily := obsFamily)
        (f := f)
        U language)
    (budget : Nat) :
    budget <
        correctedConcreteObservationSelectionCardinality
          hSelection ↔
      ∀ S : Finset ι,
        S ⊆ U →
        S.card <= budget →
        language ∉
          StartRootedCorrectedConcreteTargetClass
            (v := z)
            α
            (↥S → M)
            (selectedObservationProduct obsFamily S)
            f := by

  constructor

  · intro hLower S hSU hcard hTarget

    have hAtBudget :
        CorrectedConcreteObservationSelectionAtCardinality
          (obsFamily := obsFamily)
          (f := f)
          U language budget :=
      ⟨S,
        hSU,
        hcard,
        hTarget⟩

    exact
      (observationSelection_not_atCardinality_iff_lt_minimum
        hSelection budget).mpr
        hLower
        hAtBudget

  · intro hFail

    exact
      observationSelection_minimum_gt_of_all_small_selections_fail
        hSelection budget hFail

/-- Minimum selection cardinality is zero exactly when the empty selected
product represents the target. -/
theorem observationSelectionCardinality_eq_zero_iff_emptyProductTarget
    (hSelection :
      HasCorrectedConcreteObservationSelection
        (obsFamily := obsFamily)
        (f := f)
        U language) :
    correctedConcreteObservationSelectionCardinality
          hSelection =
        0 ↔
      language ∈
        StartRootedCorrectedConcreteTargetClass
          (v := z)
          α
          (↥(∅ : Finset ι) → M)
          (selectedObservationProduct obsFamily ∅)
          f := by

  constructor

  · intro hZero

    rcases hSelection.exists_selection_exact_cardinality with
      ⟨S, hSU, hcard, hTarget⟩

    have hCardZero :
        S.card = 0 := by
      simpa [hZero] using hcard

    have hSEmpty :
        S = ∅ :=
      Finset.card_eq_zero.mp
        hCardZero

    simpa [hSEmpty] using hTarget

  · intro hEmptyTarget

    have hAtZero :
        CorrectedConcreteObservationSelectionAtCardinality
          (obsFamily := obsFamily)
          (f := f)
          U language 0 := by

      exact
        ⟨∅,
          by
            intro index hindex
            simp at hindex,
          by
            simp,
          hEmptyTarget⟩

    have hMinimum :
        correctedConcreteObservationSelectionCardinality
            hSelection <=
          0 :=
      hSelection.cardinality_le_of_selection
        hAtZero

    omega

/-- Failure under the empty selected product forces at least one selected
coordinate. -/
theorem observationSelectionCardinality_pos_of_not_emptyProductTarget
    (hSelection :
      HasCorrectedConcreteObservationSelection
        (obsFamily := obsFamily)
        (f := f)
        U language)
    (hNotEmpty :
      language ∉
        StartRootedCorrectedConcreteTargetClass
          (v := z)
          α
          (↥(∅ : Finset ι) → M)
          (selectedObservationProduct obsFamily ∅)
          f) :
    0 <
      correctedConcreteObservationSelectionCardinality
        hSelection := by

  by_contra hNotPositive

  have hZero :
      correctedConcreteObservationSelectionCardinality
          hSelection =
        0 := by
    omega

  exact
    hNotEmpty
      ((observationSelectionCardinality_eq_zero_iff_emptyProductTarget
        hSelection).mp
        hZero)

/-- Compact cardinality obstruction package. -/
theorem observationSelectionCardinality_obstruction_package
    (hSelection :
      HasCorrectedConcreteObservationSelection
        (obsFamily := obsFamily)
        (f := f)
        U language) :
    (∀ budget : Nat,
      (¬
        CorrectedConcreteObservationSelectionAtCardinality
          (obsFamily := obsFamily)
          (f := f)
          U language budget ↔
        budget <
          correctedConcreteObservationSelectionCardinality
            hSelection)) ∧
      (∀ budget : Nat,
        (budget <
            correctedConcreteObservationSelectionCardinality
              hSelection ↔
          ∀ S : Finset ι,
            S ⊆ U →
            S.card <= budget →
            language ∉
              StartRootedCorrectedConcreteTargetClass
                (v := z)
                α
                (↥S → M)
                (selectedObservationProduct obsFamily S)
                f)) ∧
      (correctedConcreteObservationSelectionCardinality
            hSelection =
          0 ↔
        language ∈
          StartRootedCorrectedConcreteTargetClass
            (v := z)
            α
            (↥(∅ : Finset ι) → M)
            (selectedObservationProduct obsFamily ∅)
            f) := by

  exact
    ⟨fun budget =>
        observationSelection_not_atCardinality_iff_lt_minimum
          hSelection budget,
      fun budget =>
        observationSelection_minimum_gt_iff_all_small_selections_fail
          hSelection budget,
      observationSelectionCardinality_eq_zero_iff_emptyProductTarget
        hSelection⟩

end SelectionCardinalityObstructions


section AmbientMinimumIrredundantSelection

variable {α : Type u}
variable {ι : Type v}
variable {M : Type w}
variable [DecidableEq ι]
variable [Monoid M]
variable (obsFamily : ι → α → M)
variable (f : Nat)
variable (U : Finset ι)

/-- Every ambient-product target has an actual minimum-cardinality selection
that is inclusion-irredundant and coordinatewise essential. -/
theorem ambientTarget_exists_minimumIrredundantObservationSelection
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
      (S : Finset ι),
      S ⊆ U ∧
        S.card =
          ambientTargetObservationSelectionCardinality
            (z := z)
            obsFamily f U hTarget ∧
        CorrectedConcreteObservationSelectionIrredundant
          (z := z)
          α ι M obsFamily f language S ∧
        ∀ index : ι,
          index ∈ S →
          CorrectedConcreteObservationRefinementEssential
            (z := z)
            α
            (↥(S.erase index) → M)
            (↥S → M)
            (selectedObservationProduct obsFamily (S.erase index))
            (selectedObservationProduct obsFamily S)
            f := by

  rcases
      ambientTarget_exists_minimumObservationSelection
        (z := z)
        obsFamily f U hTarget with
    ⟨S, hSU, hcard, hSelected⟩

  let hSelection :=
    hasCorrectedConcreteObservationSelection_of_fullProductTarget
      (obsFamily := obsFamily)
      (f := f)
      hTarget

  have hIrredundant :
      CorrectedConcreteObservationSelectionIrredundant
        (z := z)
        α ι M obsFamily f language S := by

    apply
      observationSelection_exactCardinality_irredundant
        (z := z)
        hSelection hSU

    · simpa [
        ambientTargetObservationSelectionCardinality,
        hSelection
      ] using hcard

    · exact hSelected

  exact
    ⟨S,
      hSU,
      hcard,
      hIrredundant,
      fun index hindex =>
        observationSelection_irredundant_coordinateRefinementEssential
          (z := z)
          hIrredundant hindex⟩

end AmbientMinimumIrredundantSelection


section MinimumIrredundantSelectionCertifiedLearner

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
variable (U : Finset ι)

/-- An ambient-product target admits an irredundant minimum-cardinality
selection whose own certified learner identifies the target and returns an
exact minimum-description-rank checked output. -/
theorem
    ambientTarget_exists_minimumIrredundantCertifiedObservationSelection
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
      (hSU : S ⊆ U)
      (hSelected :
        language ∈
          StartRootedCorrectedConcreteTargetClass
            (v := z)
            α
            (↥S → M)
            (selectedObservationProduct obsFamily S)
            f),
      S.card =
          ambientTargetObservationSelectionCardinality
            (z := z)
            obsFamily f U hTarget ∧
        CorrectedConcreteObservationSelectionIrredundant
          (z := z)
          α ι M obsFamily f language S ∧
        (∀ index : ι,
          index ∈ S →
          CorrectedConcreteObservationRefinementEssential
            (z := z)
            α
            (↥(S.erase index) → M)
            (↥S → M)
            (selectedObservationProduct obsFamily (S.erase index))
            (selectedObservationProduct obsFamily S)
            f) ∧
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

  rcases
      ambientTarget_exists_minimumCertifiedObservationSelection
        (z := z)
        hα obsFamily f U hTarget with
    ⟨S,
      hSU,
      hSelected,
      hcard,
      hIdentifies,
      hProfile,
      C,
      hLanguage,
      hBits,
      hSearch⟩

  let hSelection :=
    hasCorrectedConcreteObservationSelection_of_fullProductTarget
      (obsFamily := obsFamily)
      (f := f)
      hTarget

  have hIrredundant :
      CorrectedConcreteObservationSelectionIrredundant
        (z := z)
        α ι M obsFamily f language S := by

    apply
      observationSelection_exactCardinality_irredundant
        (z := z)
        hSelection hSU

    · simpa [
        ambientTargetObservationSelectionCardinality,
        hSelection
      ] using hcard

    · exact hSelected

  exact
    ⟨S,
      hSU,
      hSelected,
      hcard,
      hIrredundant,
      fun index hindex =>
        observationSelection_irredundant_coordinateRefinementEssential
          (z := z)
          hIrredundant hindex,
      hIdentifies,
      C,
      hLanguage,
      hBits,
      hSearch⟩

end MinimumIrredundantSelectionCertifiedLearner


section ObservationSelectionIrredundancyFinalPackage

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
variable (U : Finset ι)

/-- Final minimum-cardinality, proper-subset obstruction, coordinatewise
essentiality, and certified-learning package. -/
theorem
    correctedConcreteCertifiedWorkingGrammar_observationSelectionIrredundancy_package :
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
        (S : Finset ι),
        S ⊆ U ∧
          S.card =
            ambientTargetObservationSelectionCardinality
              (z := z)
              obsFamily f U hTarget ∧
          CorrectedConcreteObservationSelectionIrredundant
            (z := z)
            α ι M obsFamily f language S ∧
          ∀ index : ι,
            index ∈ S →
            CorrectedConcreteObservationRefinementEssential
              (z := z)
              α
              (↥(S.erase index) → M)
              (↥S → M)
              (selectedObservationProduct obsFamily (S.erase index))
              (selectedObservationProduct obsFamily S)
              f) ∧
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
        ∀ budget : Nat,
          (budget <
              ambientTargetObservationSelectionCardinality
                (z := z)
                obsFamily f U hTarget ↔
            ∀ S : Finset ι,
              S ⊆ U →
              S.card <= budget →
              language ∉
                StartRootedCorrectedConcreteTargetClass
                  (v := z)
                  α
                  (↥S → M)
                  (selectedObservationProduct obsFamily S)
                  f)) ∧
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
          (hSU : S ⊆ U)
          (hSelected :
            language ∈
              StartRootedCorrectedConcreteTargetClass
                (v := z)
                α
                (↥S → M)
                (selectedObservationProduct obsFamily S)
                f),
          S.card =
              ambientTargetObservationSelectionCardinality
                (z := z)
                obsFamily f U hTarget ∧
            CorrectedConcreteObservationSelectionIrredundant
              (z := z)
              α ι M obsFamily f language S ∧
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
                    f) := by

  refine
    ⟨?_,
      ?_,
      ?_⟩

  · intro language hTarget

    exact
      ambientTarget_exists_minimumIrredundantObservationSelection
        (z := z)
        obsFamily f U hTarget

  · intro language hTarget budget

    let hSelection :=
      hasCorrectedConcreteObservationSelection_of_fullProductTarget
        (obsFamily := obsFamily)
        (f := f)
        hTarget

    simpa [
      ambientTargetObservationSelectionCardinality,
      hSelection
    ] using
      observationSelection_minimum_gt_iff_all_small_selections_fail
        hSelection budget

  · intro language hTarget

    rcases
        ambientTarget_exists_minimumIrredundantCertifiedObservationSelection
          (z := z)
          hα obsFamily f U hTarget with
      ⟨S,
        hSU,
        hSelected,
        hcard,
        hIrredundant,
        hEssential,
        hIdentifies,
        C,
        hLanguage,
        hBits,
        hSearch⟩

    exact
      ⟨S,
        hSU,
        hSelected,
        hcard,
        hIrredundant,
        hIdentifies,
        C,
        hLanguage,
        hBits,
        hSearch⟩

end ObservationSelectionIrredundancyFinalPackage

end MCFG
