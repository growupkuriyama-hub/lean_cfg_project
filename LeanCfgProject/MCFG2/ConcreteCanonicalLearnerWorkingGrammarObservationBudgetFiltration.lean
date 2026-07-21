/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG2.ConcreteCanonicalLearnerWorkingGrammarObservationOptimizationSelector

/-!
# ConcreteCanonicalLearnerWorkingGrammarObservationBudgetFiltration.lean

The preceding files construct explicit finite optimization searches and
classically select actual minimum-cost and Pareto-optimal observation subsets.

This file organizes all cost-bounded searches into a monotone budget
filtration.

## Cost-budget filtration

For a finite ambient candidate set `U`, target language `L`, and cost function

```lean
selectionCost : Finset ι → Nat
```

define the budget layer at `b` to be the finite set of all `S ⊆ U` such that

```text
selectionCost S ≤ b
and
Product(S) represents L.
```

This is the previously constructed finite cost-feasible search, now viewed as a
function of the budget.

The filtration is monotone:

```text
b ≤ b'
⇒
Layer(b) ⊆ Layer(b').
```

Every layer is contained in `U.powerset` and therefore has at most `2^|U|`
members.

## Exact threshold

Assume that at least one observation selection represents the target.  Let

```lean
minimumCost
```

be the semantic `Nat.find` minimum.

Then

```text
Layer(b) is nonempty
  ↔
minimumCost ≤ b,

Layer(b) is empty
  ↔
b < minimumCost.
```

Thus the minimum cost is exactly the first nonempty budget.

At the threshold,

```text
Layer(minimumCost)
  =
the finite set of all exact minimum-cost selections.
```

So the selected result from the preceding file belongs to the first nonempty
layer.

## Entry stage of one feasible selection

Every feasible selected subset `S` enters the filtration at its own cost:

```text
S ∈ Layer(selectionCost S).
```

It belongs to every later layer and to no earlier layer.

Therefore `selectionCost S` is the exact entry stage of `S`.

## Certified candidates in every nonempty layer

Every member of every budget layer represents the target language.  When the
terminal alphabet and observation monoid are finite and decidable, its own
selected-product certified learner identifies the target and returns one exact
checked output at the selected product's minimum certified-description rank.

## Positive additive specialization

The filtration is specialized to the positive additive coordinate cost

```text
|S| + ∑ i ∈ S, coordinateWeight i.
```

Its first nonempty budget is the minimum positive additive observation cost from
the preceding files.

## Boundary

The layers are explicit finite sets but use a classical semantic filter.
This file proves exact finite-search threshold behavior, not an executable
decision procedure for target-class membership.

No target grammar is supplied to any learner.
No `sorry`, `admit`, or `axiom` is used.
-/

namespace MCFG

universe u v w z


section ObservationCostBudgetFiltrationDefinition

variable {α : Type u}
variable {ι : Type v}
variable {M : Type w}
variable [Monoid M]

/-- Cost-bounded finite observation-selection search, viewed as a filtration in
the budget parameter. -/
noncomputable def correctedConcreteObservationCostBudgetFiltration
    (obsFamily : ι → α → M)
    (f : Nat)
    (selectionCost : Finset ι → Nat)
    (U : Finset ι)
    (language : Set (Word α))
    (costBudget : Nat) :
    Finset (Finset ι) :=
  correctedConcreteObservationCostFeasibleSelections
    (z := z)
    obsFamily
    f
    selectionCost
    U
    language
    costBudget

/-- Exact membership theorem for one budget layer. -/
theorem mem_correctedConcreteObservationCostBudgetFiltration_iff
    [DecidableEq ι]
    {obsFamily : ι → α → M}
    {f : Nat}
    {selectionCost : Finset ι → Nat}
    {U : Finset ι}
    {language : Set (Word α)}
    {costBudget : Nat}
    {S : Finset ι} :
    S ∈
        correctedConcreteObservationCostBudgetFiltration
          (z := z)
          obsFamily
          f
          selectionCost
          U
          language
          costBudget ↔
      S ⊆ U ∧
        selectionCost S <= costBudget ∧
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
      selectionCost
      U
      language
      costBudget

end ObservationCostBudgetFiltrationDefinition


section ObservationCostBudgetFiltrationMonotonicity

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

/-- Increasing the cost budget can only enlarge the finite candidate layer. -/
theorem correctedConcreteObservationCostBudgetFiltration_mono
    {costBudget costBudget' : Nat}
    (hBudget :
      costBudget <= costBudget') :
    correctedConcreteObservationCostBudgetFiltration
        (z := z)
        obsFamily
        f
        selectionCost
        U
        language
        costBudget ⊆
      correctedConcreteObservationCostBudgetFiltration
        (z := z)
        obsFamily
        f
        selectionCost
        U
        language
        costBudget' := by

  intro S hS

  rcases
      (mem_correctedConcreteObservationCostBudgetFiltration_iff
        (z := z)).mp
        hS with
    ⟨hSU, hCost, hTarget⟩

  exact
    (mem_correctedConcreteObservationCostBudgetFiltration_iff
      (z := z)).mpr
      ⟨hSU,
        hCost.trans hBudget,
        hTarget⟩

/-- Every budget layer is contained in the ambient powerset. -/
theorem
    correctedConcreteObservationCostBudgetFiltration_subset_powerset
    (costBudget : Nat) :
    correctedConcreteObservationCostBudgetFiltration
        (z := z)
        obsFamily
        f
        selectionCost
        U
        language
        costBudget ⊆
      U.powerset := by

  intro S hS

  exact
    Finset.mem_powerset.mpr
      ((mem_correctedConcreteObservationCostBudgetFiltration_iff
        (z := z)).mp
        hS).1

/-- Every budget layer has at most `2^|U|` candidates. -/
theorem
    correctedConcreteObservationCostBudgetFiltration_card_le_two_pow
    (costBudget : Nat) :
    (correctedConcreteObservationCostBudgetFiltration
        (z := z)
        obsFamily
        f
        selectionCost
        U
        language
        costBudget).card <=
      2 ^ U.card := by

  exact
    correctedConcreteObservationCostFeasibleSelections_card_le_two_pow
      (z := z)
      obsFamily
      f
      selectionCost
      U
      language
      costBudget

end ObservationCostBudgetFiltrationMonotonicity


section ObservationCostBudgetThreshold

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
variable
  (hSelection :
    HasCorrectedConcreteObservationSelectionCost
      (obsFamily := obsFamily)
      (f := f)
      selectionCost
      U
      language)

/-- A budget layer is nonempty exactly at and above the minimum cost. -/
theorem
    correctedConcreteObservationCostBudgetFiltration_nonempty_iff_minimum_le
    (costBudget : Nat) :
    (correctedConcreteObservationCostBudgetFiltration
          (z := z)
          obsFamily
          f
          selectionCost
          U
          language
          costBudget).Nonempty ↔
      correctedConcreteObservationSelectionMinimumCost
          selectionCost
          hSelection <=
        costBudget := by

  calc
    (correctedConcreteObservationCostBudgetFiltration
          (z := z)
          obsFamily
          f
          selectionCost
          U
          language
          costBudget).Nonempty
        ↔
      CorrectedConcreteObservationSelectionAtCost
        (obsFamily := obsFamily)
        (f := f)
        selectionCost
        U
        language
        costBudget :=
          correctedConcreteObservationCostFeasibleSelections_nonempty_iff
            (z := z)
            obsFamily
            f
            selectionCost
            U
            language
            costBudget

    _ ↔
      correctedConcreteObservationSelectionMinimumCost
          selectionCost
          hSelection <=
        costBudget :=
          hSelection.selectionAtCost_iff_minimumCost_le
            costBudget

/-- A budget layer is empty exactly below the minimum cost. -/
theorem
    correctedConcreteObservationCostBudgetFiltration_eq_empty_iff_lt_minimum
    (costBudget : Nat) :
    correctedConcreteObservationCostBudgetFiltration
          (z := z)
          obsFamily
          f
          selectionCost
          U
          language
          costBudget =
        ∅ ↔
      costBudget <
        correctedConcreteObservationSelectionMinimumCost
          selectionCost
          hSelection := by

  constructor

  · intro hEmpty

    by_contra hNotLt

    have hMinimum :
        correctedConcreteObservationSelectionMinimumCost
            selectionCost
            hSelection <=
          costBudget := by
      omega

    have hNonempty :
        (correctedConcreteObservationCostBudgetFiltration
          (z := z)
          obsFamily
          f
          selectionCost
          U
          language
          costBudget).Nonempty :=
      (correctedConcreteObservationCostBudgetFiltration_nonempty_iff_minimum_le
        hSelection
        costBudget).mpr
        hMinimum

    rcases hNonempty with
      ⟨S, hS⟩

    rw [hEmpty] at hS
    simp at hS

  · intro hLt

    ext S

    constructor

    · intro hS

      have hNonempty :
          (correctedConcreteObservationCostBudgetFiltration
            (z := z)
            obsFamily
            f
            selectionCost
            U
            language
            costBudget).Nonempty :=
        ⟨S, hS⟩

      have hMinimum :
          correctedConcreteObservationSelectionMinimumCost
              selectionCost
              hSelection <=
            costBudget :=
        (correctedConcreteObservationCostBudgetFiltration_nonempty_iff_minimum_le
          hSelection
          costBudget).mp
          hNonempty

      omega

    · intro hS

      simp at hS

/-- The minimum-cost budget layer is nonempty. -/
theorem
    correctedConcreteObservationCostBudgetFiltration_minimum_nonempty :
    (correctedConcreteObservationCostBudgetFiltration
      (z := z)
      obsFamily
      f
      selectionCost
      U
      language
      (correctedConcreteObservationSelectionMinimumCost
        selectionCost
        hSelection)).Nonempty := by

  exact
    (correctedConcreteObservationCostBudgetFiltration_nonempty_iff_minimum_le
      hSelection
      (correctedConcreteObservationSelectionMinimumCost
        selectionCost
        hSelection)).mpr
      (Nat.le_refl _)

/-- Every strictly smaller budget layer is empty. -/
theorem
    correctedConcreteObservationCostBudgetFiltration_empty_below_minimum
    {costBudget : Nat}
    (hBudget :
      costBudget <
        correctedConcreteObservationSelectionMinimumCost
          selectionCost
          hSelection) :
    correctedConcreteObservationCostBudgetFiltration
        (z := z)
        obsFamily
        f
        selectionCost
        U
        language
        costBudget =
      ∅ := by

  exact
    (correctedConcreteObservationCostBudgetFiltration_eq_empty_iff_lt_minimum
      hSelection
      costBudget).mpr
      hBudget

/-- Exact first-nonempty-budget package. -/
theorem
    correctedConcreteObservationCostBudgetFiltration_firstNonempty_package :
    (correctedConcreteObservationCostBudgetFiltration
        (z := z)
        obsFamily
        f
        selectionCost
        U
        language
        (correctedConcreteObservationSelectionMinimumCost
          selectionCost
          hSelection)).Nonempty ∧
      ∀ costBudget : Nat,
        costBudget <
            correctedConcreteObservationSelectionMinimumCost
              selectionCost
              hSelection →
          correctedConcreteObservationCostBudgetFiltration
              (z := z)
              obsFamily
              f
              selectionCost
              U
              language
              costBudget =
            ∅ := by

  exact
    ⟨correctedConcreteObservationCostBudgetFiltration_minimum_nonempty
        hSelection,
      fun costBudget hBudget =>
        correctedConcreteObservationCostBudgetFiltration_empty_below_minimum
          hSelection
          hBudget⟩

end ObservationCostBudgetThreshold


section ThresholdLayerEqualsMinimumSelections

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
variable
  (hSelection :
    HasCorrectedConcreteObservationSelectionCost
      (obsFamily := obsFamily)
      (f := f)
      selectionCost
      U
      language)

/-- The first nonempty budget layer is exactly the finite set of all exact
minimum-cost selections. -/
theorem
    correctedConcreteObservationCostBudgetFiltration_minimum_eq_minimumCostSelections :
    correctedConcreteObservationCostBudgetFiltration
        (z := z)
        obsFamily
        f
        selectionCost
        U
        language
        (correctedConcreteObservationSelectionMinimumCost
          selectionCost
          hSelection) =
      correctedConcreteObservationMinimumCostSelections
        (z := z)
        selectionCost
        hSelection := by

  ext S

  constructor

  · intro hS

    rcases
        (mem_correctedConcreteObservationCostBudgetFiltration_iff
          (z := z)).mp
          hS with
      ⟨hSU, hCost, hTarget⟩

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

    have hCostEq :
        selectionCost S =
          correctedConcreteObservationSelectionMinimumCost
            selectionCost
            hSelection :=
      Nat.le_antisymm
        hCost
        hMinimum

    exact
      (mem_correctedConcreteObservationMinimumCostSelections_iff
        (z := z)
        selectionCost
        hSelection).mpr
        ⟨hSU,
          hTarget,
          hCostEq⟩

  · intro hS

    rcases
        (mem_correctedConcreteObservationMinimumCostSelections_iff
          (z := z)
          selectionCost
          hSelection).mp
          hS with
      ⟨hSU, hTarget, hCostEq⟩

    exact
      (mem_correctedConcreteObservationCostBudgetFiltration_iff
        (z := z)).mpr
        ⟨hSU,
          by
            rw [hCostEq],
          hTarget⟩

/-- The selected minimum-cost result belongs to the first nonempty budget
layer. -/
theorem
    correctedConcreteObservationMinimumCostSelectionResult_mem_firstNonemptyLayer
    (result :
      CorrectedConcreteObservationMinimumCostSelectionResult
        (z := z)
        obsFamily
        f
        selectionCost
        U
        language
        hSelection) :
    result.selected ∈
      correctedConcreteObservationCostBudgetFiltration
        (z := z)
        obsFamily
        f
        selectionCost
        U
        language
        (correctedConcreteObservationSelectionMinimumCost
          selectionCost
          hSelection) := by

  rw [
    correctedConcreteObservationCostBudgetFiltration_minimum_eq_minimumCostSelections
      hSelection
  ]

  exact
    result.selected_mem

end ThresholdLayerEqualsMinimumSelections


section FeasibleSelectionEntryStage

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
variable {S : Finset ι}
variable (hSU : S ⊆ U)
variable
  (hTarget :
    language ∈
      StartRootedCorrectedConcreteTargetClass
        (v := z)
        α
        (↥S → M)
        (selectedObservationProduct obsFamily S)
        f)

/-- Every feasible selection enters the filtration at its own cost. -/
theorem correctedConcreteObservationSelection_mem_ownCostLayer :
    S ∈
      correctedConcreteObservationCostBudgetFiltration
        (z := z)
        obsFamily
        f
        selectionCost
        U
        language
        (selectionCost S) := by

  exact
    (mem_correctedConcreteObservationCostBudgetFiltration_iff
      (z := z)).mpr
      ⟨hSU,
        Nat.le_refl _,
        hTarget⟩

/-- A feasible selection belongs to every layer at or above its own cost. -/
theorem correctedConcreteObservationSelection_mem_laterCostLayer
    {costBudget : Nat}
    (hCost :
      selectionCost S <= costBudget) :
    S ∈
      correctedConcreteObservationCostBudgetFiltration
        (z := z)
        obsFamily
        f
        selectionCost
        U
        language
        costBudget := by

  exact
    (mem_correctedConcreteObservationCostBudgetFiltration_iff
      (z := z)).mpr
      ⟨hSU,
        hCost,
        hTarget⟩

/-- A feasible selection belongs to no layer below its own cost. -/
theorem correctedConcreteObservationSelection_not_mem_earlierCostLayer
    {costBudget : Nat}
    (hCost :
      costBudget < selectionCost S) :
    S ∉
      correctedConcreteObservationCostBudgetFiltration
        (z := z)
        obsFamily
        f
        selectionCost
        U
        language
        costBudget := by

  intro hS

  have hBound :
      selectionCost S <= costBudget :=
    ((mem_correctedConcreteObservationCostBudgetFiltration_iff
      (z := z)).mp
      hS).2.1

  omega

/-- Exact entry-stage characterization for one feasible selected subset. -/
theorem
    correctedConcreteObservationSelection_mem_costLayer_iff_cost_le
    (costBudget : Nat) :
    S ∈
        correctedConcreteObservationCostBudgetFiltration
          (z := z)
          obsFamily
          f
          selectionCost
          U
          language
          costBudget ↔
      selectionCost S <= costBudget := by

  constructor

  · intro hS

    exact
      ((mem_correctedConcreteObservationCostBudgetFiltration_iff
        (z := z)).mp
        hS).2.1

  · intro hCost

    exact
      correctedConcreteObservationSelection_mem_laterCostLayer
        hSU
        hTarget
        hCost

end FeasibleSelectionEntryStage


section BudgetLayerCertifiedCandidates

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
variable (costBudget : Nat)

/-- Every candidate in every budget layer has its own certified learner and
exact minimum-description-rank checked output. -/
theorem correctedConcreteObservationCostBudgetCandidate_certified_package
    {S : Finset ι}
    (hS :
      S ∈
        correctedConcreteObservationCostBudgetFiltration
          (z := z)
          obsFamily
          f
          selectionCost
          U
          language
          costBudget) :
    selectionCost S <= costBudget ∧
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
            ((mem_correctedConcreteObservationCostBudgetFiltration_iff
              (z := z)).mp
              hS).2.2) ∧
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
                ((mem_correctedConcreteObservationCostBudgetFiltration_iff
                  (z := z)).mp
                  hS).2.2)
              f ∧
          C.canonicalSearch.length <=
            correctedConcreteCertifiedRankSearchBudget
              (startRootedTargetCertifiedDescriptionRank
                (v := z)
                hα
                (selectedObservationProduct obsFamily S)
                f
                ((mem_correctedConcreteObservationCostBudgetFiltration_iff
                  (z := z)).mp
                  hS).2.2)
              f := by

  let hMembership :=
    (mem_correctedConcreteObservationCostBudgetFiltration_iff
      (z := z)).mp
      hS

  let hTarget :=
    hMembership.2.2

  exact
    ⟨hMembership.2.1,
      selectedProductCertifiedLearner_identifies_targetClass
        (z := z)
        hα
        obsFamily
        f
        S
        language
        hTarget,
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

end BudgetLayerCertifiedCandidates


section PositiveAdditiveBudgetFiltration

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

/-- Positive-additive-cost budget filtration. -/
noncomputable def
    correctedConcreteObservationPositiveAdditiveBudgetFiltration
    (costBudget : Nat) :
    Finset (Finset ι) :=
  correctedConcreteObservationCostBudgetFiltration
    (z := z)
    obsFamily
    f
    (correctedConcreteObservationSelectionPositiveAdditiveCost
      coordinateWeight)
    U
    language
    costBudget

/-- Exact membership theorem for a positive-additive budget layer. -/
theorem
    mem_correctedConcreteObservationPositiveAdditiveBudgetFiltration_iff
    {costBudget : Nat}
    {S : Finset ι} :
    S ∈
        correctedConcreteObservationPositiveAdditiveBudgetFiltration
          (z := z)
          obsFamily
          f
          coordinateWeight
          U
          language
          costBudget ↔
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
    mem_correctedConcreteObservationCostBudgetFiltration_iff
      (z := z)

/-- Positive-additive budget layers are monotone. -/
theorem
    correctedConcreteObservationPositiveAdditiveBudgetFiltration_mono
    {costBudget costBudget' : Nat}
    (hBudget :
      costBudget <= costBudget') :
    correctedConcreteObservationPositiveAdditiveBudgetFiltration
        (z := z)
        obsFamily
        f
        coordinateWeight
        U
        language
        costBudget ⊆
      correctedConcreteObservationPositiveAdditiveBudgetFiltration
        (z := z)
        obsFamily
        f
        coordinateWeight
        U
        language
        costBudget' := by

  exact
    correctedConcreteObservationCostBudgetFiltration_mono
      (z := z)
      hBudget

end PositiveAdditiveBudgetFiltration


section ObservationBudgetFiltrationFinalPackage

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

/-- Final monotone budget-filtration, exact-threshold, and certified-candidate
package. -/
theorem
    correctedConcreteCertifiedWorkingGrammar_observationBudgetFiltration_package :
    (∀
      language : Set (Word α),
      ∀ costBudget costBudget' : Nat,
        costBudget <= costBudget' →
        correctedConcreteObservationCostBudgetFiltration
            (z := z)
            obsFamily
            f
            selectionCost
            U
            language
            costBudget ⊆
          correctedConcreteObservationCostBudgetFiltration
            (z := z)
            obsFamily
            f
            selectionCost
            U
            language
            costBudget') ∧
      (∀
        language : Set (Word α),
        ∀ hSelection :
          HasCorrectedConcreteObservationSelectionCost
            (obsFamily := obsFamily)
            (f := f)
            selectionCost
            U
            language,
          (correctedConcreteObservationCostBudgetFiltration
              (z := z)
              obsFamily
              f
              selectionCost
              U
              language
              (correctedConcreteObservationSelectionMinimumCost
                selectionCost
                hSelection)).Nonempty ∧
            (∀ costBudget : Nat,
              costBudget <
                  correctedConcreteObservationSelectionMinimumCost
                    selectionCost
                    hSelection →
                correctedConcreteObservationCostBudgetFiltration
                    (z := z)
                    obsFamily
                    f
                    selectionCost
                    U
                    language
                    costBudget =
                  ∅) ∧
            correctedConcreteObservationCostBudgetFiltration
                (z := z)
                obsFamily
                f
                selectionCost
                U
                language
                (correctedConcreteObservationSelectionMinimumCost
                  selectionCost
                  hSelection) =
              correctedConcreteObservationMinimumCostSelections
                (z := z)
                selectionCost
                hSelection) ∧
      (∀
        language : Set (Word α),
        ∀ costBudget : Nat,
        ∀ S : Finset ι,
          S ∈
              correctedConcreteObservationCostBudgetFiltration
                (z := z)
                obsFamily
                f
                selectionCost
                U
                language
                costBudget →
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
      ?_⟩

  · intro language costBudget costBudget' hBudget

    exact
      correctedConcreteObservationCostBudgetFiltration_mono
        (z := z)
        hBudget

  · intro language hSelection

    exact
      ⟨correctedConcreteObservationCostBudgetFiltration_minimum_nonempty
          hSelection,
        fun costBudget hBudget =>
          correctedConcreteObservationCostBudgetFiltration_empty_below_minimum
            hSelection
            hBudget,
        correctedConcreteObservationCostBudgetFiltration_minimum_eq_minimumCostSelections
          hSelection⟩

  · intro language costBudget S hS

    exact
      (correctedConcreteObservationCostBudgetCandidate_certified_package
        (z := z)
        hα
        obsFamily
        f
        selectionCost
        U
        language
        costBudget
        hS).2.1

end ObservationBudgetFiltrationFinalPackage

end MCFG
