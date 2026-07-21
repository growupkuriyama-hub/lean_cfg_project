/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG2.ConcreteCanonicalLearnerWorkingGrammarObservationParetoSelection

/-!
# ConcreteCanonicalLearnerWorkingGrammarObservationAdditiveWeights.lean

The preceding files develop minimum-cardinality, minimum-cost, and Pareto
observation selection for an abstract cost function on finite selected sets.

This file specializes that theory to coordinatewise additive weights.

## Additive coordinate cost

For

```lean
coordinateWeight : ι → Nat
```

define

```lean
additiveCost(S) = ∑ i ∈ S, coordinateWeight i.
```

Natural-number additive cost is monotone under subset.

For optimization that must penalize every selected coordinate strictly, define

```lean
positiveAdditiveCost(S)
  =
S.card + additiveCost(S).
```

Equivalently, every selected coordinate has effective cost

```text
1 + coordinateWeight i.
```

This positive additive cost is strictly monotone under proper subset.  Hence
every minimum-positive-additive-cost selection is inclusion-irredundant and
every selected coordinate is essential.

When all extra weights are zero, positive additive cost reduces exactly to
cardinality.

## Minimum additive-weight selection

For every language represented by the full ambient selected product, there is
an actual minimum-positive-additive-cost subset.  Its cost is at most the cost
of the full ambient candidate set.

The exact weighted obstruction theorem becomes

```text
budget < minimum positive additive cost
  ↔
every ambient subset of positive additive cost at most budget
fails to represent the target.
```

The attained minimum subset has no removable coordinate.  Restoring any deleted
coordinate gives an essential observation refinement whose gain class contains
the target language.

## Additive Pareto frontier

Using the unshifted additive cost as the second objective, the Pareto profile is

```text
(number of selected coordinates,
 sum of coordinate weights).
```

Because additive cost is subset-monotone, every Pareto-optimal selection is
inclusion-irredundant and coordinatewise essential.

For every ambient-product target there exists an additive-weight
Pareto-optimal selected product whose own certified learner identifies the
target and returns an exact checked output at its minimum certified-description
rank.

## Boundary

The weights are parameters.  This file does not compute an optimal selection
algorithmically and does not classify the complexity of the weighted problem.

No target grammar is supplied to any learner.
No `sorry`, `admit`, or `axiom` is used.
-/

namespace MCFG

universe u v w z


section FiniteNaturalWeightedSum

variable {ι : Type v}

/-- Monotonicity of a finite natural-number weighted sum under subset.

This local theorem is kept explicit so the observation-selection layer does not
depend on a stronger ordered-sum API than needed. -/
theorem finsetNatWeightedSum_mono
    (coordinateWeight : ι → Nat)
    {R S : Finset ι}
    (hRS : R ⊆ S) :
    (∑ index in R, coordinateWeight index) <=
      ∑ index in S, coordinateWeight index := by

  classical

  induction S using Finset.induction_on generalizing R with

  | empty =>

      have hR :
          R = ∅ :=
        Finset.subset_empty.mp
          hRS

      subst R
      simp

  | @insert selectedIndex S hNotMem ih =>

      by_cases hSelected :
          selectedIndex ∈ R

      · have hEraseSubset :
            R.erase selectedIndex ⊆ S := by

          intro index hindex

          rcases Finset.mem_erase.mp hindex with
            ⟨hIndexNe, hIndexR⟩

          rcases
              Finset.mem_insert.mp
                (hRS hIndexR) with
            hIndexEq | hIndexS

          · exact
              False.elim
                (hIndexNe hIndexEq)

          · exact hIndexS

        have hInduction :
            (∑ index in R.erase selectedIndex,
                coordinateWeight index) <=
              ∑ index in S,
                coordinateWeight index :=
          ih hEraseSubset

        calc
          (∑ index in R, coordinateWeight index) =
              ∑ index in insert selectedIndex (R.erase selectedIndex),
                coordinateWeight index := by
                rw [Finset.insert_erase hSelected]

          _ =
              coordinateWeight selectedIndex +
                ∑ index in R.erase selectedIndex,
                  coordinateWeight index := by
                rw [
                  Finset.sum_insert
                    (Finset.not_mem_erase
                      selectedIndex R)
                ]

          _ <=
              coordinateWeight selectedIndex +
                ∑ index in S,
                  coordinateWeight index :=
            Nat.add_le_add_left
              hInduction
              (coordinateWeight selectedIndex)

          _ =
              ∑ index in insert selectedIndex S,
                coordinateWeight index := by
                rw [
                  Finset.sum_insert hNotMem
                ]

      · have hRSubset :
            R ⊆ S := by

          intro index hindex

          rcases
              Finset.mem_insert.mp
                (hRS hindex) with
            hIndexEq | hIndexS

          · subst index

            exact
              False.elim
                (hSelected hindex)

          · exact hIndexS

        have hInduction :
            (∑ index in R, coordinateWeight index) <=
              ∑ index in S,
                coordinateWeight index :=
          ih hRSubset

        rw [
          Finset.sum_insert hNotMem
        ]

        omega

end FiniteNaturalWeightedSum


section AdditiveObservationSelectionCostDefinitions

variable {ι : Type v}

/-- Sum of coordinate weights over one finite selected observation set. -/
def correctedConcreteObservationSelectionAdditiveCost
    (coordinateWeight : ι → Nat)
    (S : Finset ι) :
    Nat :=
  ∑ index in S,
    coordinateWeight index

/-- Strictly positive additive cost.  Each selected coordinate contributes
`1 + coordinateWeight index`. -/
def correctedConcreteObservationSelectionPositiveAdditiveCost
    (coordinateWeight : ι → Nat)
    (S : Finset ι) :
    Nat :=
  S.card +
    correctedConcreteObservationSelectionAdditiveCost
      coordinateWeight S

/-- Additive coordinate cost is monotone under selected-set inclusion. -/
theorem
    correctedConcreteObservationSelectionAdditiveCost_monotone
    (coordinateWeight : ι → Nat) :
    CorrectedConcreteObservationSelectionCostMonotone
      (correctedConcreteObservationSelectionAdditiveCost
        coordinateWeight) := by

  intro R S hRS

  exact
    finsetNatWeightedSum_mono
      coordinateWeight hRS

/-- Positive additive coordinate cost is monotone under inclusion. -/
theorem
    correctedConcreteObservationSelectionPositiveAdditiveCost_monotone
    (coordinateWeight : ι → Nat) :
    CorrectedConcreteObservationSelectionCostMonotone
      (correctedConcreteObservationSelectionPositiveAdditiveCost
        coordinateWeight) := by

  intro R S hRS

  have hCard :
      R.card <= S.card :=
    Finset.card_le_card hRS

  have hWeight :
      correctedConcreteObservationSelectionAdditiveCost
          coordinateWeight R <=
        correctedConcreteObservationSelectionAdditiveCost
          coordinateWeight S :=
    correctedConcreteObservationSelectionAdditiveCost_monotone
      coordinateWeight hRS

  unfold
    correctedConcreteObservationSelectionPositiveAdditiveCost

  omega

/-- Positive additive coordinate cost is strictly monotone under proper
subset. -/
theorem
    correctedConcreteObservationSelectionPositiveAdditiveCost_strictlyMonotone
    (coordinateWeight : ι → Nat) :
    CorrectedConcreteObservationSelectionCostStrictlyMonotone
      (correctedConcreteObservationSelectionPositiveAdditiveCost
        coordinateWeight) := by

  intro R S hRS

  have hSubset :
      R ⊆ S :=
    (Finset.ssubset_iff_subset_ne.mp hRS).1

  have hCard :
      R.card < S.card :=
    Finset.card_lt_card hRS

  have hWeight :
      correctedConcreteObservationSelectionAdditiveCost
          coordinateWeight R <=
        correctedConcreteObservationSelectionAdditiveCost
          coordinateWeight S :=
    correctedConcreteObservationSelectionAdditiveCost_monotone
      coordinateWeight hSubset

  unfold
    correctedConcreteObservationSelectionPositiveAdditiveCost

  omega

/-- With zero extra coordinate weights, positive additive cost is exactly
cardinality. -/
@[simp] theorem
    correctedConcreteObservationSelectionPositiveAdditiveCost_zero
    (S : Finset ι) :
    correctedConcreteObservationSelectionPositiveAdditiveCost
        (fun _ : ι => 0)
        S =
      correctedConcreteObservationSelectionCardinalityCost S := by

  simp [
    correctedConcreteObservationSelectionPositiveAdditiveCost,
    correctedConcreteObservationSelectionAdditiveCost,
    correctedConcreteObservationSelectionCardinalityCost
  ]

/-- The unshifted additive cost with zero coordinate weights is zero. -/
@[simp] theorem
    correctedConcreteObservationSelectionAdditiveCost_zero
    (S : Finset ι) :
    correctedConcreteObservationSelectionAdditiveCost
        (fun _ : ι => 0)
        S =
      0 := by

  simp [
    correctedConcreteObservationSelectionAdditiveCost
  ]

end AdditiveObservationSelectionCostDefinitions


section PositiveAdditiveCostCompatibility

variable {α : Type u}
variable {ι : Type v}
variable {M : Type w}
variable [Monoid M]
variable {obsFamily : ι → α → M}
variable {f : Nat}
variable {U : Finset ι}
variable {language : Set (Word α)}
variable {costBudget : Nat}

/-- Positive additive feasibility with zero extra weights is exactly the
cardinality-budget feasibility relation. -/
theorem observationSelectionAtZeroPositiveAdditiveCost_iff :
    CorrectedConcreteObservationSelectionAtCost
        (obsFamily := obsFamily)
        (f := f)
        (correctedConcreteObservationSelectionPositiveAdditiveCost
          (fun _ : ι => 0))
        U language costBudget ↔
      CorrectedConcreteObservationSelectionAtCardinality
        (obsFamily := obsFamily)
        (f := f)
        U language costBudget := by

  constructor

  · intro hSelection

    rcases hSelection with
      ⟨S, hSU, hcost, hTarget⟩

    exact
      ⟨S,
        hSU,
        by
          simpa using hcost,
        hTarget⟩

  · intro hSelection

    rcases hSelection with
      ⟨S, hSU, hcard, hTarget⟩

    exact
      ⟨S,
        hSU,
        by
          simpa using hcard,
        hTarget⟩

end PositiveAdditiveCostCompatibility


section AmbientPositiveAdditiveMinimum

variable {α : Type u}
variable {ι : Type v}
variable {M : Type w}
variable [Monoid M]
variable (obsFamily : ι → α → M)
variable (f : Nat)
variable (coordinateWeight : ι → Nat)
variable (U : Finset ι)

/-- Minimum strictly positive additive coordinate cost for an ambient-product
target. -/
noncomputable def
    ambientTargetObservationSelectionPositiveAdditiveMinimumCost
    {language : Set (Word α)}
    (hTarget :
      language ∈
        StartRootedCorrectedConcreteTargetClass
          (v := z)
          α
          (↥U → M)
          (selectedObservationProduct obsFamily U)
          f) :
    Nat :=
  ambientTargetObservationSelectionMinimumCost
    (z := z)
    obsFamily
    f
    (correctedConcreteObservationSelectionPositiveAdditiveCost
      coordinateWeight)
    U
    hTarget

/-- The minimum positive additive cost is bounded by the cost of selecting the
whole ambient candidate set. -/
theorem
    ambientTargetObservationSelectionPositiveAdditiveMinimumCost_le
    {language : Set (Word α)}
    (hTarget :
      language ∈
        StartRootedCorrectedConcreteTargetClass
          (v := z)
          α
          (↥U → M)
          (selectedObservationProduct obsFamily U)
          f) :
    ambientTargetObservationSelectionPositiveAdditiveMinimumCost
        (z := z)
        obsFamily f coordinateWeight U hTarget <=
      correctedConcreteObservationSelectionPositiveAdditiveCost
        coordinateWeight U := by

  exact
    ambientTargetObservationSelectionMinimumCost_le
      (z := z)
      obsFamily
      f
      (correctedConcreteObservationSelectionPositiveAdditiveCost
        coordinateWeight)
      U
      hTarget

/-- Exact lower-bound criterion for the minimum positive additive coordinate
cost. -/
theorem
    ambientTargetPositiveAdditiveMinimumCost_gt_iff_all_bounded_selections_fail
    {language : Set (Word α)}
    (hTarget :
      language ∈
        StartRootedCorrectedConcreteTargetClass
          (v := z)
          α
          (↥U → M)
          (selectedObservationProduct obsFamily U)
          f)
    (costBudget : Nat) :
    costBudget <
        ambientTargetObservationSelectionPositiveAdditiveMinimumCost
          (z := z)
          obsFamily f coordinateWeight U hTarget ↔
      ∀ S : Finset ι,
        S ⊆ U →
        correctedConcreteObservationSelectionPositiveAdditiveCost
            coordinateWeight S <=
          costBudget →
        language ∉
          StartRootedCorrectedConcreteTargetClass
            (v := z)
            α
            (↥S → M)
            (selectedObservationProduct obsFamily S)
            f := by

  let hSelection :=
    hasCorrectedConcreteObservationSelectionCost_of_fullProductTarget
      (obsFamily := obsFamily)
      (f := f)
      (correctedConcreteObservationSelectionPositiveAdditiveCost
        coordinateWeight)
      hTarget

  simpa [
    ambientTargetObservationSelectionPositiveAdditiveMinimumCost,
    ambientTargetObservationSelectionMinimumCost,
    hSelection
  ] using
    observationSelection_minimumCost_gt_iff_all_boundedCost_selections_fail
      hSelection
      costBudget

/-- Every ambient-product target has an attained positive-additive-minimum
selection that is irredundant and coordinatewise essential. -/
theorem
    ambientTarget_exists_positiveAdditiveMinimumIrredundantSelection
    [DecidableEq ι]
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
        correctedConcreteObservationSelectionPositiveAdditiveCost
            coordinateWeight S =
          ambientTargetObservationSelectionPositiveAdditiveMinimumCost
            (z := z)
            obsFamily f coordinateWeight U hTarget ∧
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

  exact
    ambientTarget_exists_minimumCostIrredundantObservationSelection
      (z := z)
      obsFamily
      f
      (correctedConcreteObservationSelectionPositiveAdditiveCost
        coordinateWeight)
      U
      (correctedConcreteObservationSelectionPositiveAdditiveCost_strictlyMonotone
        coordinateWeight)
      hTarget

end AmbientPositiveAdditiveMinimum


section PositiveAdditiveMinimumCertifiedLearner

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

/-- An ambient-product target admits a positive-additive-minimum selected
product that is irredundant, coordinatewise essential, and equipped with its
own certified learner. -/
theorem
    ambientTarget_exists_positiveAdditiveMinimumCertifiedSelection
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
      correctedConcreteObservationSelectionPositiveAdditiveCost
          coordinateWeight S =
        ambientTargetObservationSelectionPositiveAdditiveMinimumCost
          (z := z)
          obsFamily f coordinateWeight U hTarget ∧
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
      ambientTarget_exists_minimumCostIrredundantCertifiedObservationSelection
        (z := z)
        hα
        obsFamily
        f
        (correctedConcreteObservationSelectionPositiveAdditiveCost
          coordinateWeight)
        U
        (correctedConcreteObservationSelectionPositiveAdditiveCost_strictlyMonotone
          coordinateWeight)
        hTarget with
    ⟨S,
      hSU,
      hSelected,
      hcost,
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
      hcost,
      hIrredundant,
      hEssential,
      hIdentifies,
      C,
      hLanguage,
      hBits,
      hSearch⟩

end PositiveAdditiveMinimumCertifiedLearner


section AdditiveParetoCertifiedLearner

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

/-- Every ambient-product target has a Pareto-optimal selection for the profile

```text
(number of coordinates, sum of coordinate weights),
```

and that selection is irredundant, coordinatewise essential, and equipped with
its own certified learner. -/
theorem
    ambientTarget_exists_additiveParetoCertifiedObservationSelection
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
      (hPareto :
        CorrectedConcreteObservationSelectionParetoOptimal
          (z := z)
          obsFamily
          f
          (correctedConcreteObservationSelectionAdditiveCost
            coordinateWeight)
          U
          language
          S),
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
                  hPareto.2.1)
                f ∧
            C.canonicalSearch.length <=
              correctedConcreteCertifiedRankSearchBudget
                (startRootedTargetCertifiedDescriptionRank
                  (v := z)
                  hα
                  (selectedObservationProduct obsFamily S)
                  f
                  hPareto.2.1)
                f := by

  exact
    correctedConcreteCertifiedWorkingGrammar_observationMonotoneCostParetoSelection_package
      (z := z)
      hα
      obsFamily
      f
      (correctedConcreteObservationSelectionAdditiveCost
        coordinateWeight)
      U
      (correctedConcreteObservationSelectionAdditiveCost_monotone
        coordinateWeight)
      language
      hTarget

end AdditiveParetoCertifiedLearner


section ObservationAdditiveWeightsFinalPackage

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

/-- Final additive-weight minimum and Pareto observation-selection package. -/
theorem
    correctedConcreteCertifiedWorkingGrammar_observationAdditiveWeights_package :
    CorrectedConcreteObservationSelectionCostMonotone
        (correctedConcreteObservationSelectionAdditiveCost
          coordinateWeight) ∧
      CorrectedConcreteObservationSelectionCostStrictlyMonotone
        (correctedConcreteObservationSelectionPositiveAdditiveCost
          coordinateWeight) ∧
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
        ∀ costBudget : Nat,
          (costBudget <
              ambientTargetObservationSelectionPositiveAdditiveMinimumCost
                (z := z)
                obsFamily f coordinateWeight U hTarget ↔
            ∀ S : Finset ι,
              S ⊆ U →
              correctedConcreteObservationSelectionPositiveAdditiveCost
                  coordinateWeight S <=
                costBudget →
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
          correctedConcreteObservationSelectionPositiveAdditiveCost
              coordinateWeight S =
            ambientTargetObservationSelectionPositiveAdditiveMinimumCost
              (z := z)
              obsFamily f coordinateWeight U hTarget ∧
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
        ∃
          (S : Finset ι)
          (hPareto :
            CorrectedConcreteObservationSelectionParetoOptimal
              (z := z)
              obsFamily
              f
              (correctedConcreteObservationSelectionAdditiveCost
                coordinateWeight)
              U
              language
              S),
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
                      hPareto.2.1)
                    f ∧
                C.canonicalSearch.length <=
                  correctedConcreteCertifiedRankSearchBudget
                    (startRootedTargetCertifiedDescriptionRank
                      (v := z)
                      hα
                      (selectedObservationProduct obsFamily S)
                      f
                      hPareto.2.1)
                    f) := by

  refine
    ⟨correctedConcreteObservationSelectionAdditiveCost_monotone
        coordinateWeight,
      correctedConcreteObservationSelectionPositiveAdditiveCost_strictlyMonotone
        coordinateWeight,
      ?_,
      ?_,
      ?_⟩

  · intro language hTarget costBudget

    exact
      ambientTargetPositiveAdditiveMinimumCost_gt_iff_all_bounded_selections_fail
        (z := z)
        obsFamily f coordinateWeight U hTarget costBudget

  · intro language hTarget

    rcases
        ambientTarget_exists_positiveAdditiveMinimumCertifiedSelection
          (z := z)
          hα obsFamily f coordinateWeight U hTarget with
      ⟨S,
        hSU,
        hSelected,
        hcost,
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
        hcost,
        hIrredundant,
        hIdentifies,
        C,
        hLanguage,
        hBits,
        hSearch⟩

  · intro language hTarget

    rcases
        ambientTarget_exists_additiveParetoCertifiedObservationSelection
          (z := z)
          hα obsFamily f coordinateWeight U hTarget with
      ⟨S,
        hPareto,
        hIrredundant,
        hEssential,
        hIdentifies,
        C,
        hLanguage,
        hBits,
        hSearch⟩

    exact
      ⟨S,
        hPareto,
        hIrredundant,
        hIdentifies,
        C,
        hLanguage,
        hBits,
        hSearch⟩

end ObservationAdditiveWeightsFinalPackage

end MCFG
