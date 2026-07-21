/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG.ConcreteCanonicalLearnerWorkingGrammarObservationSelectionParetoRankEnvelope

/-!
# ConcreteCanonicalLearnerWorkingGrammarObservationSelectionParetoRankSelector.lean

The preceding file identifies positive additive observation-selection rank as
the minimum scalar value achieved on the finite additive Pareto frontier.

This file turns that envelope theorem into an explicit finite selector.

## Rank-minimizing Pareto selections

For a full ambient-product target, filter the explicit finite additive Pareto
frontier by the exact scalar equation

```text
PositiveAdditiveCost(S)
  =
PositiveAdditiveRank(language).
```

The resulting finite set is

```lean
correctedConcreteObservationPositiveAdditiveRankMinimizingParetoSelections.
```

It is nonempty, lies inside the explicit Pareto frontier, and has at most
`2^|U|` members.

Every member simultaneously

* is Pareto optimal for selected-set cardinality and additive weight;
* attains the exact positive additive observation-selection rank;
* is globally minimum among every feasible ambient selection;
* is inclusion-irredundant; and
* has every selected coordinate essential.

## Actual selector

A classical selector chooses one member of this finite nonempty set and
packages it as

```lean
CorrectedConcreteObservationPositiveAdditiveParetoRankSelectionResult.
```

The chosen subset is therefore an actual finite-search output, rather than only
an existential witness.

## Certified learner

The chosen selected product has its own certified learner.  It identifies the
target language from positive data and returns one exact checked grammar output
at the selected product's minimum certified-description rank.

The observation-selection rank and grammar-description rank remain distinct.

## Boundary

The finite frontier and selector use semantic target-class membership.
No executable decision procedure or tie-breaking order is asserted.

No target grammar is supplied to any learner.
No `sorry`, `admit`, or `axiom` is used.
-/

namespace MCFG

universe u v w z


section RankMinimizingParetoSelectionsDefinition

variable {α : Type u}
variable {ι : Type v}
variable {M : Type w}
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

/-- Explicit finite set of additive-Pareto selections whose positive additive
scalar value is exactly the target's observation-selection rank. -/
noncomputable def
    correctedConcreteObservationPositiveAdditiveRankMinimizingParetoSelections :
    Finset (Finset ι) := by

  classical

  exact
    (correctedConcreteObservationParetoSelections
      (z := z)
      obsFamily
      f
      (correctedConcreteObservationSelectionAdditiveCost
        coordinateWeight)
      U
      language).filter
      (fun S =>
        correctedConcreteObservationSelectionPositiveAdditiveCost
            coordinateWeight S =
          ambientTargetObservationSelectionPositiveAdditiveMinimumCost
            (z := z)
            obsFamily
            f
            coordinateWeight
            U
            hTarget)

end RankMinimizingParetoSelectionsDefinition


section RankMinimizingParetoSelectionsMembership

variable {α : Type u}
variable {ι : Type v}
variable {M : Type w}
variable [DecidableEq ι]
variable [Monoid M]
variable {obsFamily : ι → α → M}
variable {f : Nat}
variable {coordinateWeight : ι → Nat}
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

/-- Exact membership theorem for the finite rank-minimizing Pareto set. -/
theorem
    mem_correctedConcreteObservationPositiveAdditiveRankMinimizingParetoSelections_iff
    {S : Finset ι} :
    S ∈
        correctedConcreteObservationPositiveAdditiveRankMinimizingParetoSelections
          (z := z)
          obsFamily
          f
          coordinateWeight
          U
          language
          hTarget ↔
      CorrectedConcreteObservationSelectionParetoOptimal
          (z := z)
          obsFamily
          f
          (correctedConcreteObservationSelectionAdditiveCost
            coordinateWeight)
          U
          language
          S ∧
        correctedConcreteObservationSelectionPositiveAdditiveCost
            coordinateWeight S =
          ambientTargetObservationSelectionPositiveAdditiveMinimumCost
            (z := z)
            obsFamily
            f
            coordinateWeight
            U
            hTarget := by

  classical

  constructor

  · intro hS

    rcases Finset.mem_filter.mp hS with
      ⟨hFrontier, hCost⟩

    exact
      ⟨(mem_correctedConcreteObservationParetoSelections_iff
          (z := z)
          obsFamily
          f
          (correctedConcreteObservationSelectionAdditiveCost
            coordinateWeight)
          U
          language).mp
          hFrontier,
        hCost⟩

  · intro hS

    rcases hS with
      ⟨hPareto, hCost⟩

    exact
      Finset.mem_filter.mpr
        ⟨(mem_correctedConcreteObservationParetoSelections_iff
            (z := z)
            obsFamily
            f
            (correctedConcreteObservationSelectionAdditiveCost
              coordinateWeight)
            U
            language).mpr
            hPareto,
          hCost⟩

/-- The rank-minimizing Pareto set is nonempty for every full ambient-product
target. -/
theorem
    correctedConcreteObservationPositiveAdditiveRankMinimizingParetoSelections_nonempty :
    (correctedConcreteObservationPositiveAdditiveRankMinimizingParetoSelections
      (z := z)
      obsFamily
      f
      coordinateWeight
      U
      language
      hTarget).Nonempty := by

  have hRankMember :=
    (ambientTarget_positiveAdditiveRank_isMinimum_paretoRankValue
      (z := z)
      obsFamily
      f
      coordinateWeight
      U
      hTarget).1

  rcases
      (mem_correctedConcreteObservationPositiveAdditiveParetoRankValues_iff
        (z := z)
        obsFamily
        f
        coordinateWeight
        U
        language).mp
        hRankMember with
    ⟨S, hPareto, hRankEq⟩

  exact
    ⟨S,
      (mem_correctedConcreteObservationPositiveAdditiveRankMinimizingParetoSelections_iff
        (z := z)).mpr
        ⟨hPareto,
          hRankEq.symm⟩⟩

/-- Every rank-minimizing Pareto selection belongs to the explicit additive
Pareto frontier. -/
theorem
    correctedConcreteObservationPositiveAdditiveRankMinimizingParetoSelections_subset_paretoSelections :
    correctedConcreteObservationPositiveAdditiveRankMinimizingParetoSelections
        (z := z)
        obsFamily
        f
        coordinateWeight
        U
        language
        hTarget ⊆
      correctedConcreteObservationParetoSelections
        (z := z)
        obsFamily
        f
        (correctedConcreteObservationSelectionAdditiveCost
          coordinateWeight)
        U
        language := by

  intro S hS

  have hPareto :=
    ((mem_correctedConcreteObservationPositiveAdditiveRankMinimizingParetoSelections_iff
      (z := z)).mp
      hS).1

  exact
    (mem_correctedConcreteObservationParetoSelections_iff
      (z := z)
      obsFamily
      f
      (correctedConcreteObservationSelectionAdditiveCost
        coordinateWeight)
      U
      language).mpr
      hPareto

/-- The finite set of rank-minimizing Pareto selections has at most
`2^|U|` members. -/
theorem
    correctedConcreteObservationPositiveAdditiveRankMinimizingParetoSelections_card_le_two_pow :
    (correctedConcreteObservationPositiveAdditiveRankMinimizingParetoSelections
        (z := z)
        obsFamily
        f
        coordinateWeight
        U
        language
        hTarget).card <=
      2 ^ U.card := by

  calc
    (correctedConcreteObservationPositiveAdditiveRankMinimizingParetoSelections
        (z := z)
        obsFamily
        f
        coordinateWeight
        U
        language
        hTarget).card <=
      (correctedConcreteObservationParetoSelections
        (z := z)
        obsFamily
        f
        (correctedConcreteObservationSelectionAdditiveCost
          coordinateWeight)
        U
        language).card :=
          Finset.card_le_card
            correctedConcreteObservationPositiveAdditiveRankMinimizingParetoSelections_subset_paretoSelections

    _ <=
      2 ^ U.card :=
        correctedConcreteObservationParetoSelections_card_le_two_pow
          (z := z)
          obsFamily
          f
          (correctedConcreteObservationSelectionAdditiveCost
            coordinateWeight)
          U
          language

end RankMinimizingParetoSelectionsMembership


section ParetoRankSelectionResultDefinition

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

/-- One selected member of the finite rank-minimizing additive Pareto
frontier. -/
structure
    CorrectedConcreteObservationPositiveAdditiveParetoRankSelectionResult where

  selected :
    Finset ι

  selected_mem :
    selected ∈
      correctedConcreteObservationPositiveAdditiveRankMinimizingParetoSelections
        (z := z)
        obsFamily
        f
        coordinateWeight
        U
        language
        hTarget

/-- Select one actual rank-minimizing member of the finite additive Pareto
frontier. -/
noncomputable def
    correctedConcreteObservationPositiveAdditiveParetoRankSelectionResult :
    CorrectedConcreteObservationPositiveAdditiveParetoRankSelectionResult
      (z := z)
      obsFamily
      f
      coordinateWeight
      U
      language
      hTarget := by

  classical

  let hNonempty :=
    correctedConcreteObservationPositiveAdditiveRankMinimizingParetoSelections_nonempty
      (z := z)
      (obsFamily := obsFamily)
      (f := f)
      (coordinateWeight := coordinateWeight)
      (U := U)
      (language := language)
      (hTarget := hTarget)

  exact
    ⟨hNonempty.choose,
      hNonempty.choose_spec⟩

end ParetoRankSelectionResultDefinition


namespace CorrectedConcreteObservationPositiveAdditiveParetoRankSelectionResult

section SelectedParetoRankProperties

variable {α : Type u}
variable {ι : Type v}
variable {M : Type w}
variable [DecidableEq ι]
variable [Monoid M]
variable {obsFamily : ι → α → M}
variable {f : Nat}
variable {coordinateWeight : ι → Nat}
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
variable
  (result :
    CorrectedConcreteObservationPositiveAdditiveParetoRankSelectionResult
      (z := z)
      obsFamily
      f
      coordinateWeight
      U
      language
      hTarget)

/-- The selected result is Pareto optimal for cardinality and additive
coordinate weight. -/
theorem selected_pareto :
    CorrectedConcreteObservationSelectionParetoOptimal
      (z := z)
      obsFamily
      f
      (correctedConcreteObservationSelectionAdditiveCost
        coordinateWeight)
      U
      language
      result.selected := by

  exact
    ((mem_correctedConcreteObservationPositiveAdditiveRankMinimizingParetoSelections_iff
      (z := z)).mp
      result.selected_mem).1

/-- The selected result attains the exact ambient positive-additive rank. -/
theorem selected_cost_eq_rank :
    correctedConcreteObservationSelectionPositiveAdditiveCost
        coordinateWeight result.selected =
      ambientTargetObservationSelectionPositiveAdditiveMinimumCost
        (z := z)
        obsFamily
        f
        coordinateWeight
        U
        hTarget := by

  exact
    ((mem_correctedConcreteObservationPositiveAdditiveRankMinimizingParetoSelections_iff
      (z := z)).mp
      result.selected_mem).2

/-- The selected subset lies inside the ambient candidate set. -/
theorem selected_subset :
    result.selected ⊆ U := by

  exact
    result.selected_pareto.1

/-- The selected product represents the target language. -/
theorem selected_target :
    language ∈
      StartRootedCorrectedConcreteTargetClass
        (v := z)
        α
        (↥result.selected → M)
        (selectedObservationProduct obsFamily result.selected)
        f := by

  exact
    result.selected_pareto.2.1

/-- The ambient positive-additive rank is a lower bound on every feasible
ambient selection. -/
theorem rank_le_every_feasible
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
    ambientTargetObservationSelectionPositiveAdditiveMinimumCost
          (z := z)
          obsFamily
          f
          coordinateWeight
          U
          hTarget <=
      correctedConcreteObservationSelectionPositiveAdditiveCost
        coordinateWeight R := by

  let hSelection :=
    hasCorrectedConcreteObservationSelectionCost_of_fullProductTarget
      (obsFamily := obsFamily)
      (f := f)
      (correctedConcreteObservationSelectionPositiveAdditiveCost
        coordinateWeight)
      hTarget

  have hMinimum :
      correctedConcreteObservationSelectionMinimumCost
          (correctedConcreteObservationSelectionPositiveAdditiveCost
            coordinateWeight)
          hSelection <=
        correctedConcreteObservationSelectionPositiveAdditiveCost
          coordinateWeight R := by

    apply
      hSelection.minimumCost_le_of_selection

    exact
      ⟨R,
        hRU,
        Nat.le_refl _,
        hRTarget⟩

  simpa [
    ambientTargetObservationSelectionPositiveAdditiveMinimumCost,
    ambientTargetObservationSelectionMinimumCost,
    hSelection
  ] using
    hMinimum

/-- The selected result has no greater positive additive cost than any feasible
ambient selection. -/
theorem selected_cost_le_every_feasible
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
    correctedConcreteObservationSelectionPositiveAdditiveCost
          coordinateWeight result.selected <=
      correctedConcreteObservationSelectionPositiveAdditiveCost
        coordinateWeight R := by

  rw [result.selected_cost_eq_rank]

  exact
    result.rank_le_every_feasible
      hRU
      hRTarget

/-- The selected-set cardinality is bounded by the observation-selection
rank. -/
theorem selected_card_le_rank :
    result.selected.card <=
      ambientTargetObservationSelectionPositiveAdditiveMinimumCost
        (z := z)
        obsFamily
        f
        coordinateWeight
        U
        hTarget := by

  have hCost :=
    result.selected_cost_eq_rank

  unfold
    correctedConcreteObservationSelectionPositiveAdditiveCost
    at hCost

  omega

/-- The selected extra additive coordinate cost is bounded by the
observation-selection rank. -/
theorem selected_additiveCost_le_rank :
    correctedConcreteObservationSelectionAdditiveCost
        coordinateWeight result.selected <=
      ambientTargetObservationSelectionPositiveAdditiveMinimumCost
        (z := z)
        obsFamily
        f
        coordinateWeight
        U
        hTarget := by

  have hCost :=
    result.selected_cost_eq_rank

  unfold
    correctedConcreteObservationSelectionPositiveAdditiveCost
    at hCost

  omega

/-- The target belongs to the exact positive-additive rank shell indexed by the
selected scalar value. -/
theorem target_mem_exact_rank_shell :
    language ∈
      CorrectedConcreteObservationSelectionExactCostRankClass
        (z := z)
        α
        ι
        M
        obsFamily
        f
        (correctedConcreteObservationSelectionPositiveAdditiveCost
          coordinateWeight)
        U
        (ambientTargetObservationSelectionPositiveAdditiveMinimumCost
          (z := z)
          obsFamily
          f
          coordinateWeight
          U
          hTarget) := by

  exact
    ambientTarget_mem_exactObservationSelectionCostRankClass
      (z := z)
      obsFamily
      f
      (correctedConcreteObservationSelectionPositiveAdditiveCost
        coordinateWeight)
      U
      hTarget

/-- The selected Pareto-rank result is inclusion-irredundant. -/
theorem selected_irredundant :
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
      (correctedConcreteObservationSelectionAdditiveCost_monotone
        coordinateWeight)
      result.selected_pareto

/-- Every selected coordinate is essential. -/
theorem selected_coordinateEssential
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
    observationSelection_paretoOptimal_coordinateEssential
      (z := z)
      (correctedConcreteObservationSelectionAdditiveCost_monotone
        coordinateWeight)
      result.selected_pareto
      hindex

/-- Restoring any deleted selected coordinate is an essential observation
refinement. -/
theorem selected_coordinateRefinementEssential
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
    observationSelection_paretoOptimal_coordinateRefinementEssential
      (z := z)
      (correctedConcreteObservationSelectionAdditiveCost_monotone
        coordinateWeight)
      result.selected_pareto
      hindex

/-- Compact semantic package carried by the finite Pareto-rank selector. -/
theorem semantic_package :
    result.selected ⊆ U ∧
      language ∈
        StartRootedCorrectedConcreteTargetClass
          (v := z)
          α
          (↥result.selected → M)
          (selectedObservationProduct obsFamily result.selected)
          f ∧
      correctedConcreteObservationSelectionPositiveAdditiveCost
          coordinateWeight result.selected =
        ambientTargetObservationSelectionPositiveAdditiveMinimumCost
          (z := z)
          obsFamily
          f
          coordinateWeight
          U
          hTarget ∧
      CorrectedConcreteObservationSelectionParetoOptimal
        (z := z)
        obsFamily
        f
        (correctedConcreteObservationSelectionAdditiveCost
          coordinateWeight)
        U
        language
        result.selected ∧
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
    ⟨result.selected_subset,
      result.selected_target,
      result.selected_cost_eq_rank,
      result.selected_pareto,
      result.selected_irredundant⟩

end SelectedParetoRankProperties


section SelectedParetoRankCertifiedLearner

variable {α : Type u}
variable {ι : Type v}
variable {M : Type w}
variable [Fintype M]
variable [DecidableEq α]
variable [DecidableEq ι]
variable [DecidableEq M]
variable [Monoid M]
variable (hα : Nonempty α)
variable {obsFamily : ι → α → M}
variable {f : Nat}
variable {coordinateWeight : ι → Nat}
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
variable
  (result :
    CorrectedConcreteObservationPositiveAdditiveParetoRankSelectionResult
      (z := z)
      obsFamily
      f
      coordinateWeight
      U
      language
      hTarget)

/-- The selected Pareto-rank product has its own certified learner and an exact
checked output at minimum certified-description rank. -/
theorem certified_package :
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

end SelectedParetoRankCertifiedLearner

end CorrectedConcreteObservationPositiveAdditiveParetoRankSelectionResult


section ParetoRankSelectorFinalPackage

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
variable (coordinateWeight : ι → Nat)
variable (U : Finset ι)

/-- Final finite rank-minimizing Pareto search, actual selector, semantic
optimality, irredundancy, and certified-learning package. -/
theorem
    correctedConcreteCertifiedWorkingGrammar_observationSelectionParetoRankSelector_package :
    ∀
      language : Set (Word α),
      ∀ hTarget :
        language ∈
          StartRootedCorrectedConcreteTargetClass
            (v := z)
            α
            (↥U → M)
            (selectedObservationProduct obsFamily U)
            f,
      let candidates :=
        correctedConcreteObservationPositiveAdditiveRankMinimizingParetoSelections
          (z := z)
          obsFamily
          f
          coordinateWeight
          U
          language
          hTarget
      let result :=
        correctedConcreteObservationPositiveAdditiveParetoRankSelectionResult
          (z := z)
          obsFamily
          f
          coordinateWeight
          U
          language
          hTarget
      candidates.Nonempty ∧
        candidates.card <= 2 ^ U.card ∧
        result.selected ∈ candidates ∧
        result.selected ⊆ U ∧
        correctedConcreteObservationSelectionPositiveAdditiveCost
            coordinateWeight result.selected =
          ambientTargetObservationSelectionPositiveAdditiveMinimumCost
            (z := z)
            obsFamily
            f
            coordinateWeight
            U
            hTarget ∧
        CorrectedConcreteObservationSelectionParetoOptimal
          (z := z)
          obsFamily
          f
          (correctedConcreteObservationSelectionAdditiveCost
            coordinateWeight)
          U
          language
          result.selected ∧
        CorrectedConcreteObservationSelectionIrredundant
          (z := z)
          α
          ι
          M
          obsFamily
          f
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
          language := by

  intro language hTarget

  let candidates :=
    correctedConcreteObservationPositiveAdditiveRankMinimizingParetoSelections
      (z := z)
      obsFamily
      f
      coordinateWeight
      U
      language
      hTarget

  let result :=
    correctedConcreteObservationPositiveAdditiveParetoRankSelectionResult
      (z := z)
      obsFamily
      f
      coordinateWeight
      U
      language
      hTarget

  have hCertified :=
    CorrectedConcreteObservationPositiveAdditiveParetoRankSelectionResult.certified_package
      (z := z)
      hα
      result

  exact
    ⟨correctedConcreteObservationPositiveAdditiveRankMinimizingParetoSelections_nonempty
        (z := z)
        (obsFamily := obsFamily)
        (f := f)
        (coordinateWeight := coordinateWeight)
        (U := U)
        (language := language)
        (hTarget := hTarget),
      correctedConcreteObservationPositiveAdditiveRankMinimizingParetoSelections_card_le_two_pow
        (z := z)
        (obsFamily := obsFamily)
        (f := f)
        (coordinateWeight := coordinateWeight)
        (U := U)
        (language := language)
        (hTarget := hTarget),
      result.selected_mem,
      result.selected_subset,
      result.selected_cost_eq_rank,
      result.selected_pareto,
      result.selected_irredundant,
      hCertified.1⟩

end ParetoRankSelectorFinalPackage

end MCFG
