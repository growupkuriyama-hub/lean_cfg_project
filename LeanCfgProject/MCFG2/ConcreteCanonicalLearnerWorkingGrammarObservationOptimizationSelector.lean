/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG2.ConcreteCanonicalLearnerWorkingGrammarObservationFiniteOptimization

/-!
# ConcreteCanonicalLearnerWorkingGrammarObservationOptimizationSelector.lean

The preceding file turns observation design into explicit finite searches over
the powerset of a finite ambient candidate set.

This file selects actual optimization results from those finite searches and
packages their semantic and certified-learning guarantees.

## Minimum-cost selector

Given a proof that some selected observation product represents the target, the
finite minimum-cost search is nonempty.  We select one member and package it as

```lean
CorrectedConcreteObservationMinimumCostSelectionResult.
```

The selected subset

* belongs to the ambient powerset;
* represents the target language;
* has cost exactly equal to the semantic minimum cost; and
* has cost no greater than every other feasible ambient selection.

The selector is classical because target-class membership is not yet decidable,
but it selects from the explicit finite search constructed in the preceding
file.

## Pareto selector

For every language represented by the full ambient product, the finite Pareto
search is nonempty.  We select one member and package it as

```lean
CorrectedConcreteObservationParetoSelectionResult.
```

The selected subset is Pareto optimal and represents the target.  Its own
selected-product certified learner identifies the target and returns one exact
checked output at the selected product's minimum certified-description rank.

Under subset-monotone cost, the selected Pareto solution is additionally

* inclusion-irredundant;
* coordinatewise essential; and
* a strict observation-gain witness for every selected coordinate.

## Positive additive weights

The selector is specialized to the positive additive coordinate cost

```text
|S| + ∑ i ∈ S, coordinateWeight i.
```

This cost is strictly monotone.  Therefore its selected minimum-cost result is
automatically irredundant and coordinatewise essential.

## Boundary

No computable tie-breaking order is asserted.  The selectors use classical
choice over nonempty finite searches.  They provide exact finite optimization
outputs and certificates, not an extracted optimization algorithm.

No target grammar is supplied to any learner.
No `sorry`, `admit`, or `axiom` is used.
-/

namespace MCFG

universe u v w z


section MinimumCostSelectionResult

variable {α : Type u}
variable {ι : Type v}
variable {M : Type w}
variable [Monoid M]
variable (obsFamily : ι → α → M)
variable (f : Nat)
variable (selectionCost : Finset ι → Nat)
variable (U : Finset ι)
variable (language : Set (Word α))
variable
  (hSelection :
    HasCorrectedConcreteObservationSelectionCost
      (obsFamily := obsFamily)
      (f := f)
      selectionCost
      U
      language)

/-- One selected member of the explicit finite minimum-cost search. -/
structure CorrectedConcreteObservationMinimumCostSelectionResult where

  selected :
    Finset ι

  selected_mem :
    selected ∈
      correctedConcreteObservationMinimumCostSelections
        (z := z)
        selectionCost
        hSelection

/-- Select one actual minimum-cost observation subset from the finite search. -/
noncomputable def
    correctedConcreteObservationMinimumCostSelectionResult :
    CorrectedConcreteObservationMinimumCostSelectionResult
      (z := z)
      obsFamily
      f
      selectionCost
      U
      language
      hSelection := by

  classical

  let hNonempty :=
    correctedConcreteObservationMinimumCostSelections_nonempty
      (z := z)
      selectionCost
      hSelection

  exact
    ⟨hNonempty.choose,
      hNonempty.choose_spec⟩

namespace CorrectedConcreteObservationMinimumCostSelectionResult

variable {obsFamily f selectionCost U language hSelection}

/-- The selected minimum-cost result lies inside the ambient candidate set. -/
theorem selected_subset
    (result :
      CorrectedConcreteObservationMinimumCostSelectionResult
        (z := z)
        obsFamily
        f
        selectionCost
        U
        language
        hSelection) :
    result.selected ⊆ U := by

  exact
    ((mem_correctedConcreteObservationMinimumCostSelections_iff
      (z := z)
      selectionCost
      hSelection).mp
      result.selected_mem).1

/-- The selected minimum-cost product represents the target language. -/
theorem selected_target
    (result :
      CorrectedConcreteObservationMinimumCostSelectionResult
        (z := z)
        obsFamily
        f
        selectionCost
        U
        language
        hSelection) :
    language ∈
      StartRootedCorrectedConcreteTargetClass
        (v := z)
        α
        (↥result.selected → M)
        (selectedObservationProduct obsFamily result.selected)
        f := by

  exact
    ((mem_correctedConcreteObservationMinimumCostSelections_iff
      (z := z)
      selectionCost
      hSelection).mp
      result.selected_mem).2.1

/-- The selected result attains the semantic minimum cost exactly. -/
theorem selected_cost_eq_minimum
    (result :
      CorrectedConcreteObservationMinimumCostSelectionResult
        (z := z)
        obsFamily
        f
        selectionCost
        U
        language
        hSelection) :
    selectionCost result.selected =
      correctedConcreteObservationSelectionMinimumCost
        selectionCost
        hSelection := by

  exact
    ((mem_correctedConcreteObservationMinimumCostSelections_iff
      (z := z)
      selectionCost
      hSelection).mp
      result.selected_mem).2.2

/-- The selected result has cost no greater than every feasible ambient
selection. -/
theorem selected_cost_le_every_feasible
    (result :
      CorrectedConcreteObservationMinimumCostSelectionResult
        (z := z)
        obsFamily
        f
        selectionCost
        U
        language
        hSelection)
    {R : Finset ι}
    (hRU : R ⊆ U)
    (hRTarget :
      language ∈
        StartRootedCorrectedConcreteTargetClass
          (v := z)
          α
          (↥R → M)
          (selectedObservationProduct obsFamily R)
          f) :
    selectionCost result.selected <=
      selectionCost R := by

  exact
    correctedConcreteObservationMinimumCostSelections_le_every_feasible
      (z := z)
      selectionCost
      hSelection
      result.selected_mem
      hRU
      hRTarget

/-- Compact semantic certificate carried by a minimum-cost selected result. -/
theorem semantic_package
    (result :
      CorrectedConcreteObservationMinimumCostSelectionResult
        (z := z)
        obsFamily
        f
        selectionCost
        U
        language
        hSelection) :
    result.selected ⊆ U ∧
      language ∈
        StartRootedCorrectedConcreteTargetClass
          (v := z)
          α
          (↥result.selected → M)
          (selectedObservationProduct obsFamily result.selected)
          f ∧
      selectionCost result.selected =
        correctedConcreteObservationSelectionMinimumCost
          selectionCost
          hSelection ∧
      ∀ R : Finset ι,
        R ⊆ U →
        language ∈
          StartRootedCorrectedConcreteTargetClass
            (v := z)
            α
            (↥R → M)
            (selectedObservationProduct obsFamily R)
            f →
        selectionCost result.selected <=
          selectionCost R := by

  exact
    ⟨result.selected_subset,
      result.selected_target,
      result.selected_cost_eq_minimum,
      fun R hRU hRTarget =>
        result.selected_cost_le_every_feasible
          hRU
          hRTarget⟩

end CorrectedConcreteObservationMinimumCostSelectionResult

end MinimumCostSelectionResult


section MinimumCostSelectedCertifiedLearner

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
variable
  (hSelection :
    HasCorrectedConcreteObservationSelectionCost
      (obsFamily := obsFamily)
      (f := f)
      selectionCost
      U
      language)

/-- The selected minimum-cost product has its own certified learner and exact
minimum-description-rank checked output. -/
theorem
    correctedConcreteObservationMinimumCostSelectionResult_certified_package
    (result :
      CorrectedConcreteObservationMinimumCostSelectionResult
        (z := z)
        obsFamily
        f
        selectionCost
        U
        language
        hSelection) :
    IdentifiesLanguageFromPositiveData
        (correctedConcreteCertifiedWorkingGrammarHypLanguage
          (selectedObservationProduct obsFamily result.selected)
          f)
        (correctedConcreteCertifiedWorkingGrammarLearner
          hα
          (selectedObservationProduct obsFamily result.selected)
          f)
        language ∧
      language ∈
        CorrectedConcreteCertifiedRankProfileClass
          (α := α)
          (M := ↥result.selected → M)
          (selectedObservationProduct obsFamily result.selected)
          f
          (startRootedTargetCertifiedDescriptionRank
            (v := z)
            hα
            (selectedObservationProduct obsFamily result.selected)
            f
            result.selected_target) ∧
      ∃
        C :
          CorrectedConcreteCertifiedWorkingGrammarHypothesis
            α
            (↥result.selected → M)
            (selectedObservationProduct obsFamily result.selected)
            f,
        C.output.grammar.StringLanguage =
            language ∧
          C.bits.length <=
            correctedConcreteCertifiedRankBitBudget
              (startRootedTargetCertifiedDescriptionRank
                (v := z)
                hα
                (selectedObservationProduct obsFamily result.selected)
                f
                result.selected_target)
              f ∧
          C.canonicalSearch.length <=
            correctedConcreteCertifiedRankSearchBudget
              (startRootedTargetCertifiedDescriptionRank
                (v := z)
                hα
                (selectedObservationProduct obsFamily result.selected)
                f
                result.selected_target)
              f := by

  exact
    ⟨selectedProductCertifiedLearner_identifies_targetClass
        (z := z)
        hα
        obsFamily
        f
        result.selected
        language
        result.selected_target,
      startRootedTarget_mem_minimumCertifiedDescriptionRankProfile
        (v := z)
        hα
        (selectedObservationProduct obsFamily result.selected)
        f
        result.selected_target,
      startRootedTarget_exists_output_at_minimumCertifiedDescriptionRank
        (v := z)
        hα
        (selectedObservationProduct obsFamily result.selected)
        f
        result.selected_target⟩

end MinimumCostSelectedCertifiedLearner


section StrictMinimumCostSelectedIrredundancy

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
  {hSelection :
    HasCorrectedConcreteObservationSelectionCost
      (obsFamily := obsFamily)
      (f := f)
      selectionCost
      U
      language}

/-- Under strict cost monotonicity, a selected minimum-cost result is
inclusion-irredundant. -/
theorem
    correctedConcreteObservationMinimumCostSelectionResult_irredundant
    (hStrict :
      CorrectedConcreteObservationSelectionCostStrictlyMonotone
        selectionCost)
    (result :
      CorrectedConcreteObservationMinimumCostSelectionResult
        (z := z)
        obsFamily
        f
        selectionCost
        U
        language
        hSelection) :
    CorrectedConcreteObservationSelectionIrredundant
      (z := z)
      α
      ι
      M
      obsFamily
      f
      language
      result.selected := by

  exact
    observationSelection_exactMinimumCost_irredundant
      (z := z)
      hStrict
      hSelection
      result.selected_subset
      result.selected_cost_eq_minimum
      result.selected_target

/-- Every coordinate selected by a strict-cost minimum result is essential. -/
theorem
    correctedConcreteObservationMinimumCostSelectionResult_coordinateEssential
    (hStrict :
      CorrectedConcreteObservationSelectionCostStrictlyMonotone
        selectionCost)
    (result :
      CorrectedConcreteObservationMinimumCostSelectionResult
        (z := z)
        obsFamily
        f
        selectionCost
        U
        language
        hSelection)
    {index : ι}
    (hindex : index ∈ result.selected) :
    CorrectedConcreteSelectedObservationCoordinateEssential
      (z := z)
      α
      ι
      M
      obsFamily
      f
      language
      result.selected
      index := by

  exact
    observationSelection_irredundant_coordinateEssential
      (z := z)
      (correctedConcreteObservationMinimumCostSelectionResult_irredundant
        (z := z)
        hStrict
        result)
      hindex

/-- Restoring any deleted coordinate of a strict-cost minimum result is an
essential observation refinement. -/
theorem
    correctedConcreteObservationMinimumCostSelectionResult_coordinateRefinementEssential
    (hStrict :
      CorrectedConcreteObservationSelectionCostStrictlyMonotone
        selectionCost)
    (result :
      CorrectedConcreteObservationMinimumCostSelectionResult
        (z := z)
        obsFamily
        f
        selectionCost
        U
        language
        hSelection)
    {index : ι}
    (hindex : index ∈ result.selected) :
    CorrectedConcreteObservationRefinementEssential
      (z := z)
      α
      (↥(result.selected.erase index) → M)
      (↥result.selected → M)
      (selectedObservationProduct
        obsFamily
        (result.selected.erase index))
      (selectedObservationProduct
        obsFamily
        result.selected)
      f := by

  exact
    observationSelection_irredundant_coordinateRefinementEssential
      (z := z)
      (correctedConcreteObservationMinimumCostSelectionResult_irredundant
        (z := z)
        hStrict
        result)
      hindex

end StrictMinimumCostSelectedIrredundancy


section ParetoSelectionResult

variable {α : Type u}
variable {ι : Type v}
variable {M : Type w}
variable [DecidableEq ι]
variable [Monoid M]
variable (obsFamily : ι → α → M)
variable (f : Nat)
variable (selectionCost : Finset ι → Nat)
variable (U : Finset ι)
variable (language : Set (Word α))
variable
  (hTarget :
    language ∈
      StartRootedCorrectedConcreteTargetClass
        (v := z)
        α
        (↥U → M)
        (selectedObservationProduct obsFamily U)
        f)

/-- One selected member of the explicit finite Pareto search. -/
structure CorrectedConcreteObservationParetoSelectionResult where

  selected :
    Finset ι

  selected_mem :
    selected ∈
      correctedConcreteObservationParetoSelections
        (z := z)
        obsFamily
        f
        selectionCost
        U
        language

/-- Select one actual Pareto-optimal subset from the explicit finite Pareto
frontier. -/
noncomputable def correctedConcreteObservationParetoSelectionResult :
    CorrectedConcreteObservationParetoSelectionResult
      (z := z)
      obsFamily
      f
      selectionCost
      U
      language
      hTarget := by

  classical

  let hNonempty :=
    correctedConcreteObservationParetoSelections_nonempty_of_fullProductTarget
      (z := z)
      obsFamily
      f
      selectionCost
      U
      language
      hTarget

  exact
    ⟨hNonempty.choose,
      hNonempty.choose_spec⟩

namespace CorrectedConcreteObservationParetoSelectionResult

variable {obsFamily f selectionCost U language hTarget}

/-- The selected result satisfies the semantic Pareto-optimality predicate. -/
theorem selected_pareto
    (result :
      CorrectedConcreteObservationParetoSelectionResult
        (z := z)
        obsFamily
        f
        selectionCost
        U
        language
        hTarget) :
    CorrectedConcreteObservationSelectionParetoOptimal
      (z := z)
      obsFamily
      f
      selectionCost
      U
      language
      result.selected := by

  exact
    (mem_correctedConcreteObservationParetoSelections_iff
      (z := z)
      obsFamily
      f
      selectionCost
      U
      language).mp
      result.selected_mem

/-- The selected Pareto result lies inside the ambient candidate set. -/
theorem selected_subset
    (result :
      CorrectedConcreteObservationParetoSelectionResult
        (z := z)
        obsFamily
        f
        selectionCost
        U
        language
        hTarget) :
    result.selected ⊆ U := by

  exact
    result.selected_pareto.1

/-- The selected Pareto product represents the target language. -/
theorem selected_target
    (result :
      CorrectedConcreteObservationParetoSelectionResult
        (z := z)
        obsFamily
        f
        selectionCost
        U
        language
        hTarget) :
    language ∈
      StartRootedCorrectedConcreteTargetClass
        (v := z)
        α
        (↥result.selected → M)
        (selectedObservationProduct obsFamily result.selected)
        f := by

  exact
    result.selected_pareto.2.1

/-- No feasible ambient selection strictly dominates the selected result. -/
theorem not_strictlyDominated
    (result :
      CorrectedConcreteObservationParetoSelectionResult
        (z := z)
        obsFamily
        f
        selectionCost
        U
        language
        hTarget)
    {R : Finset ι}
    (hRU : R ⊆ U)
    (hRTarget :
      language ∈
        StartRootedCorrectedConcreteTargetClass
          (v := z)
          α
          (↥R → M)
          (selectedObservationProduct obsFamily R)
          f) :
    ¬
      CorrectedConcreteObservationSelectionStrictlyDominates
        selectionCost
        R
        result.selected := by

  exact
    result.selected_pareto.2.2
      R
      hRU
      hRTarget

/-- Compact semantic certificate carried by a selected Pareto result. -/
theorem semantic_package
    (result :
      CorrectedConcreteObservationParetoSelectionResult
        (z := z)
        obsFamily
        f
        selectionCost
        U
        language
        hTarget) :
    result.selected ⊆ U ∧
      language ∈
        StartRootedCorrectedConcreteTargetClass
          (v := z)
          α
          (↥result.selected → M)
          (selectedObservationProduct obsFamily result.selected)
          f ∧
      CorrectedConcreteObservationSelectionParetoOptimal
        (z := z)
        obsFamily
        f
        selectionCost
        U
        language
        result.selected := by

  exact
    ⟨result.selected_subset,
      result.selected_target,
      result.selected_pareto⟩

end CorrectedConcreteObservationParetoSelectionResult

end ParetoSelectionResult


section ParetoSelectedCertifiedLearner

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
variable
  (hTarget :
    language ∈
      StartRootedCorrectedConcreteTargetClass
        (v := z)
        α
        (↥U → M)
        (selectedObservationProduct obsFamily U)
        f)

/-- A selected Pareto result has its own certified learner and exact
minimum-description-rank checked output. -/
theorem correctedConcreteObservationParetoSelectionResult_certified_package
    (result :
      CorrectedConcreteObservationParetoSelectionResult
        (z := z)
        obsFamily
        f
        selectionCost
        U
        language
        hTarget) :
    IdentifiesLanguageFromPositiveData
        (correctedConcreteCertifiedWorkingGrammarHypLanguage
          (selectedObservationProduct obsFamily result.selected)
          f)
        (correctedConcreteCertifiedWorkingGrammarLearner
          hα
          (selectedObservationProduct obsFamily result.selected)
          f)
        language ∧
      language ∈
        CorrectedConcreteCertifiedRankProfileClass
          (α := α)
          (M := ↥result.selected → M)
          (selectedObservationProduct obsFamily result.selected)
          f
          (startRootedTargetCertifiedDescriptionRank
            (v := z)
            hα
            (selectedObservationProduct obsFamily result.selected)
            f
            result.selected_target) ∧
      ∃
        C :
          CorrectedConcreteCertifiedWorkingGrammarHypothesis
            α
            (↥result.selected → M)
            (selectedObservationProduct obsFamily result.selected)
            f,
        C.output.grammar.StringLanguage =
            language ∧
          C.bits.length <=
            correctedConcreteCertifiedRankBitBudget
              (startRootedTargetCertifiedDescriptionRank
                (v := z)
                hα
                (selectedObservationProduct obsFamily result.selected)
                f
                result.selected_target)
              f ∧
          C.canonicalSearch.length <=
            correctedConcreteCertifiedRankSearchBudget
              (startRootedTargetCertifiedDescriptionRank
                (v := z)
                hα
                (selectedObservationProduct obsFamily result.selected)
                f
                result.selected_target)
              f := by

  exact
    correctedConcreteObservationParetoSelection_certified_package
      (z := z)
      hα
      obsFamily
      f
      selectionCost
      U
      language
      result.selected_mem

end ParetoSelectedCertifiedLearner


section MonotoneCostParetoSelectedIrredundancy

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
  {hTarget :
    language ∈
      StartRootedCorrectedConcreteTargetClass
        (v := z)
        α
        (↥U → M)
        (selectedObservationProduct obsFamily U)
        f}

/-- Under subset-monotone cost, a selected Pareto result is
inclusion-irredundant. -/
theorem correctedConcreteObservationParetoSelectionResult_irredundant
    (hCostMonotone :
      CorrectedConcreteObservationSelectionCostMonotone
        selectionCost)
    (result :
      CorrectedConcreteObservationParetoSelectionResult
        (z := z)
        obsFamily
        f
        selectionCost
        U
        language
        hTarget) :
    CorrectedConcreteObservationSelectionIrredundant
      (z := z)
      α
      ι
      M
      obsFamily
      f
      language
      result.selected := by

  exact
    observationSelection_paretoOptimal_irredundant
      (z := z)
      hCostMonotone
      result.selected_pareto

/-- Every coordinate of a selected Pareto result is essential under
subset-monotone cost. -/
theorem
    correctedConcreteObservationParetoSelectionResult_coordinateEssential
    (hCostMonotone :
      CorrectedConcreteObservationSelectionCostMonotone
        selectionCost)
    (result :
      CorrectedConcreteObservationParetoSelectionResult
        (z := z)
        obsFamily
        f
        selectionCost
        U
        language
        hTarget)
    {index : ι}
    (hindex : index ∈ result.selected) :
    CorrectedConcreteSelectedObservationCoordinateEssential
      (z := z)
      α
      ι
      M
      obsFamily
      f
      language
      result.selected
      index := by

  exact
    observationSelection_irredundant_coordinateEssential
      (z := z)
      (correctedConcreteObservationParetoSelectionResult_irredundant
        (z := z)
        hCostMonotone
        result)
      hindex

/-- Restoring a deleted coordinate of a selected Pareto result is essential
under subset-monotone cost. -/
theorem
    correctedConcreteObservationParetoSelectionResult_coordinateRefinementEssential
    (hCostMonotone :
      CorrectedConcreteObservationSelectionCostMonotone
        selectionCost)
    (result :
      CorrectedConcreteObservationParetoSelectionResult
        (z := z)
        obsFamily
        f
        selectionCost
        U
        language
        hTarget)
    {index : ι}
    (hindex : index ∈ result.selected) :
    CorrectedConcreteObservationRefinementEssential
      (z := z)
      α
      (↥(result.selected.erase index) → M)
      (↥result.selected → M)
      (selectedObservationProduct
        obsFamily
        (result.selected.erase index))
      (selectedObservationProduct
        obsFamily
        result.selected)
      f := by

  exact
    observationSelection_irredundant_coordinateRefinementEssential
      (z := z)
      (correctedConcreteObservationParetoSelectionResult_irredundant
        (z := z)
        hCostMonotone
        result)
      hindex

end MonotoneCostParetoSelectedIrredundancy


section PositiveAdditiveMinimumSelector

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
variable
  (hTarget :
    language ∈
      StartRootedCorrectedConcreteTargetClass
        (v := z)
        α
        (↥U → M)
        (selectedObservationProduct obsFamily U)
        f)

private noncomputable def positiveAdditiveSelectionExists :
    HasCorrectedConcreteObservationSelectionCost
      (obsFamily := obsFamily)
      (f := f)
      (correctedConcreteObservationSelectionPositiveAdditiveCost
        coordinateWeight)
      U
      language :=
  hasCorrectedConcreteObservationSelectionCost_of_fullProductTarget
    (obsFamily := obsFamily)
    (f := f)
    (correctedConcreteObservationSelectionPositiveAdditiveCost
      coordinateWeight)
    hTarget

/-- Select one exact minimum-positive-additive-cost observation subset. -/
noncomputable def
    correctedConcreteObservationPositiveAdditiveMinimumSelectionResult :
    CorrectedConcreteObservationMinimumCostSelectionResult
      (z := z)
      obsFamily
      f
      (correctedConcreteObservationSelectionPositiveAdditiveCost
        coordinateWeight)
      U
      language
      (positiveAdditiveSelectionExists
        (z := z)
        obsFamily
        f
        coordinateWeight
        U
        language
        hTarget) :=
  correctedConcreteObservationMinimumCostSelectionResult
    (z := z)
    obsFamily
    f
    (correctedConcreteObservationSelectionPositiveAdditiveCost
      coordinateWeight)
    U
    language
    (positiveAdditiveSelectionExists
      (z := z)
      obsFamily
      f
      coordinateWeight
      U
      language
      hTarget)

/-- The selected positive-additive minimum is irredundant. -/
theorem
    correctedConcreteObservationPositiveAdditiveMinimumSelectionResult_irredundant :
    CorrectedConcreteObservationSelectionIrredundant
      (z := z)
      α
      ι
      M
      obsFamily
      f
      language
      (correctedConcreteObservationPositiveAdditiveMinimumSelectionResult
        (z := z)
        obsFamily
        f
        coordinateWeight
        U
        language
        hTarget).selected := by

  exact
    correctedConcreteObservationMinimumCostSelectionResult_irredundant
      (z := z)
      (correctedConcreteObservationSelectionPositiveAdditiveCost_strictlyMonotone
        coordinateWeight)
      (correctedConcreteObservationPositiveAdditiveMinimumSelectionResult
        (z := z)
        obsFamily
        f
        coordinateWeight
        U
        language
        hTarget)

end PositiveAdditiveMinimumSelector


section ObservationOptimizationSelectorFinalPackage

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

/-- Final finite minimum-cost and Pareto selector package. -/
theorem
    correctedConcreteCertifiedWorkingGrammar_observationOptimizationSelector_package :
    (∀
      language : Set (Word α),
      ∀ hSelection :
        HasCorrectedConcreteObservationSelectionCost
          (obsFamily := obsFamily)
          (f := f)
          selectionCost
          U
          language,
      let result :=
        correctedConcreteObservationMinimumCostSelectionResult
          (z := z)
          obsFamily
          f
          selectionCost
          U
          language
          hSelection
      result.selected ⊆ U ∧
        language ∈
          StartRootedCorrectedConcreteTargetClass
            (v := z)
            α
            (↥result.selected → M)
            (selectedObservationProduct obsFamily result.selected)
            f ∧
        selectionCost result.selected =
          correctedConcreteObservationSelectionMinimumCost
            selectionCost
            hSelection ∧
        IdentifiesLanguageFromPositiveData
          (correctedConcreteCertifiedWorkingGrammarHypLanguage
            (selectedObservationProduct obsFamily result.selected)
            f)
          (correctedConcreteCertifiedWorkingGrammarLearner
            hα
            (selectedObservationProduct obsFamily result.selected)
            f)
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
        let result :=
          correctedConcreteObservationParetoSelectionResult
            (z := z)
            obsFamily
            f
            selectionCost
            U
            language
            hTarget
        CorrectedConcreteObservationSelectionParetoOptimal
            (z := z)
            obsFamily
            f
            selectionCost
            U
            language
            result.selected ∧
          IdentifiesLanguageFromPositiveData
            (correctedConcreteCertifiedWorkingGrammarHypLanguage
              (selectedObservationProduct obsFamily result.selected)
              f)
            (correctedConcreteCertifiedWorkingGrammarLearner
              hα
              (selectedObservationProduct obsFamily result.selected)
              f)
            language ∧
          ∃
            C :
              CorrectedConcreteCertifiedWorkingGrammarHypothesis
                α
                (↥result.selected → M)
                (selectedObservationProduct obsFamily result.selected)
                f,
            C.output.grammar.StringLanguage =
                language ∧
              C.bits.length <=
                correctedConcreteCertifiedRankBitBudget
                  (startRootedTargetCertifiedDescriptionRank
                    (v := z)
                    hα
                    (selectedObservationProduct obsFamily result.selected)
                    f
                    result.selected_target)
                  f ∧
              C.canonicalSearch.length <=
                correctedConcreteCertifiedRankSearchBudget
                  (startRootedTargetCertifiedDescriptionRank
                    (v := z)
                    hα
                    (selectedObservationProduct obsFamily result.selected)
                    f
                    result.selected_target)
                  f) := by

  refine
    ⟨?_,
      ?_⟩

  · intro language hSelection

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

    exact
      ⟨result.selected_subset,
        result.selected_target,
        result.selected_cost_eq_minimum,
        hCertified.1⟩

  · intro language hTarget

    let result :=
      correctedConcreteObservationParetoSelectionResult
        (z := z)
        obsFamily
        f
        selectionCost
        U
        language
        hTarget

    have hCertified :=
      correctedConcreteObservationParetoSelectionResult_certified_package
        (z := z)
        hα
        obsFamily
        f
        selectionCost
        U
        language
        hTarget
        result

    exact
      ⟨result.selected_pareto,
        hCertified.1,
        hCertified.2.2⟩

end ObservationOptimizationSelectorFinalPackage

end MCFG
