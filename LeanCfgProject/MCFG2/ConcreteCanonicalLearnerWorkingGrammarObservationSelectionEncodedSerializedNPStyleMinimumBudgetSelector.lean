/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG2.ConcreteCanonicalLearnerWorkingGrammarObservationSelectionEncodedSerializedNPStyleThreshold

/-!
# ConcreteCanonicalLearnerWorkingGrammarObservationSelectionEncodedSerializedNPStyleMinimumBudgetSelector.lean

The preceding file proves that the ordinary-cost and Pareto serialized
NP-style decision families have the exact threshold

```text
minimumRank <= budget.
```

This file turns that threshold theorem into actual finite minimum-budget
selectors.

Given a ceiling `maxBudget` reaching the semantic minimum rank, we take the
`Finset.min'` of the finite ordinary and Pareto accepted-budget searches.  We
prove that

```text
selected ordinary minimum budget = minimumRank,
selected Pareto minimum budget   = minimumRank,
```

and hence both selected budgets are equal.

At each selected minimum budget we then choose a generic polynomial witness
from the serialized NP-style membership package.  The selected witness carries

* verifier acceptance;
* the degree-one certificate-size bound;
* the degree-one verifier-work bound.

The final package specializes the ceiling to the full positive-additive
observation-interface cost.

This remains relative to the already materialized semantic decision table and
does not assert compact-input NP membership or hardness.

No target grammar is supplied to any learner.
No `sorry`, `admit`, or `axiom` is used.
-/

namespace MCFG

universe u v w z


namespace CorrectedConcreteObservationSelectionDecisionTable

section SerializedNPStyleMinimumBudgetSelectors

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
  (table :
    CorrectedConcreteObservationSelectionDecisionTable
      (z := z)
      obsFamily
      f
      (correctedConcreteObservationSelectionAdditiveCost
        coordinateWeight)
      U
      language)
variable
  (hTarget :
    language ∈
      StartRootedCorrectedConcreteTargetClass
        (v := z)
        α
        (↥U → M)
        (selectedObservationProduct obsFamily U)
        f)

/-- Least accepted ordinary serialized NP-style budget below a supplied
ceiling. -/
noncomputable def selectedMinimumSerializedCostNPStyleBudget
    (maxBudget : Nat)
    (hBound :
      table.serializedNPStyleMinimumRank hTarget <=
        maxBudget) : Nat :=
  (table.serializedCostNPStyleAcceptedBudgets
    hTarget
    maxBudget).min'
    (table.serializedNPStyleAcceptedBudgets_nonempty
      hTarget
      hBound).1

/-- Least accepted Pareto serialized NP-style budget below a supplied
ceiling. -/
noncomputable def selectedMinimumSerializedParetoNPStyleBudget
    (maxBudget : Nat)
    (hBound :
      table.serializedNPStyleMinimumRank hTarget <=
        maxBudget) : Nat :=
  (table.serializedParetoNPStyleAcceptedBudgets
    hTarget
    maxBudget).min'
    (table.serializedNPStyleAcceptedBudgets_nonempty
      hTarget
      hBound).2

/-- The selected ordinary minimum budget belongs to the finite accepted-budget
search. -/
theorem selectedMinimumSerializedCostNPStyleBudget_mem
    (maxBudget : Nat)
    (hBound :
      table.serializedNPStyleMinimumRank hTarget <=
        maxBudget) :
    table.selectedMinimumSerializedCostNPStyleBudget
          hTarget
          maxBudget
          hBound ∈
      table.serializedCostNPStyleAcceptedBudgets
        hTarget
        maxBudget := by

  exact
    Finset.min'_mem
      (table.serializedCostNPStyleAcceptedBudgets
        hTarget
        maxBudget)
      (table.serializedNPStyleAcceptedBudgets_nonempty
        hTarget
        hBound).1

/-- The selected Pareto minimum budget belongs to the finite accepted-budget
search. -/
theorem selectedMinimumSerializedParetoNPStyleBudget_mem
    (maxBudget : Nat)
    (hBound :
      table.serializedNPStyleMinimumRank hTarget <=
        maxBudget) :
    table.selectedMinimumSerializedParetoNPStyleBudget
          hTarget
          maxBudget
          hBound ∈
      table.serializedParetoNPStyleAcceptedBudgets
        hTarget
        maxBudget := by

  exact
    Finset.min'_mem
      (table.serializedParetoNPStyleAcceptedBudgets
        hTarget
        maxBudget)
      (table.serializedNPStyleAcceptedBudgets_nonempty
        hTarget
        hBound).2

/-- The selected ordinary budget is no larger than any accepted ordinary
budget. -/
theorem selectedMinimumSerializedCostNPStyleBudget_le_of_mem
    (maxBudget : Nat)
    (hBound :
      table.serializedNPStyleMinimumRank hTarget <=
        maxBudget)
    {budget : Nat}
    (hBudget :
      budget ∈
        table.serializedCostNPStyleAcceptedBudgets
          hTarget
          maxBudget) :
    table.selectedMinimumSerializedCostNPStyleBudget
          hTarget
          maxBudget
          hBound <=
      budget := by

  exact
    Finset.min'_le
      (table.serializedCostNPStyleAcceptedBudgets
        hTarget
        maxBudget)
      budget
      hBudget

/-- The selected Pareto budget is no larger than any accepted Pareto budget. -/
theorem selectedMinimumSerializedParetoNPStyleBudget_le_of_mem
    (maxBudget : Nat)
    (hBound :
      table.serializedNPStyleMinimumRank hTarget <=
        maxBudget)
    {budget : Nat}
    (hBudget :
      budget ∈
        table.serializedParetoNPStyleAcceptedBudgets
          hTarget
          maxBudget) :
    table.selectedMinimumSerializedParetoNPStyleBudget
          hTarget
          maxBudget
          hBound <=
      budget := by

  exact
    Finset.min'_le
      (table.serializedParetoNPStyleAcceptedBudgets
        hTarget
        maxBudget)
      budget
      hBudget

/-- The finite ordinary selector returns exactly the semantic minimum rank. -/
theorem selectedMinimumSerializedCostNPStyleBudget_eq_minimumRank
    (maxBudget : Nat)
    (hBound :
      table.serializedNPStyleMinimumRank hTarget <=
        maxBudget) :
    table.selectedMinimumSerializedCostNPStyleBudget
          hTarget
          maxBudget
          hBound =
      table.serializedNPStyleMinimumRank hTarget := by

  apply Nat.le_antisymm

  · have hMinimumMem :
        table.serializedNPStyleMinimumRank hTarget ∈
          table.serializedCostNPStyleAcceptedBudgets
            hTarget
            maxBudget :=
      (table.mem_serializedCostNPStyleAcceptedBudgets_iff
        hTarget
        maxBudget
        (table.serializedNPStyleMinimumRank hTarget)).mpr
        ⟨Nat.le_refl _, hBound⟩

    exact
      table.selectedMinimumSerializedCostNPStyleBudget_le_of_mem
        hTarget
        maxBudget
        hBound
        hMinimumMem

  · have hSelectedMem :=
      table.selectedMinimumSerializedCostNPStyleBudget_mem
        hTarget
        maxBudget
        hBound

    exact
      ((table.mem_serializedCostNPStyleAcceptedBudgets_iff
        hTarget
        maxBudget
        (table.selectedMinimumSerializedCostNPStyleBudget
          hTarget
          maxBudget
          hBound)).mp
        hSelectedMem).1

/-- The finite Pareto selector returns exactly the semantic minimum rank. -/
theorem selectedMinimumSerializedParetoNPStyleBudget_eq_minimumRank
    (maxBudget : Nat)
    (hBound :
      table.serializedNPStyleMinimumRank hTarget <=
        maxBudget) :
    table.selectedMinimumSerializedParetoNPStyleBudget
          hTarget
          maxBudget
          hBound =
      table.serializedNPStyleMinimumRank hTarget := by

  apply Nat.le_antisymm

  · have hMinimumMem :
        table.serializedNPStyleMinimumRank hTarget ∈
          table.serializedParetoNPStyleAcceptedBudgets
            hTarget
            maxBudget :=
      (table.mem_serializedParetoNPStyleAcceptedBudgets_iff
        hTarget
        maxBudget
        (table.serializedNPStyleMinimumRank hTarget)).mpr
        ⟨Nat.le_refl _, hBound⟩

    exact
      table.selectedMinimumSerializedParetoNPStyleBudget_le_of_mem
        hTarget
        maxBudget
        hBound
        hMinimumMem

  · have hSelectedMem :=
      table.selectedMinimumSerializedParetoNPStyleBudget_mem
        hTarget
        maxBudget
        hBound

    exact
      ((table.mem_serializedParetoNPStyleAcceptedBudgets_iff
        hTarget
        maxBudget
        (table.selectedMinimumSerializedParetoNPStyleBudget
          hTarget
          maxBudget
          hBound)).mp
        hSelectedMem).1

/-- Ordinary and Pareto finite minimum-budget selectors agree. -/
theorem selectedMinimumSerializedCostNPStyleBudget_eq_pareto
    (maxBudget : Nat)
    (hBound :
      table.serializedNPStyleMinimumRank hTarget <=
        maxBudget) :
    table.selectedMinimumSerializedCostNPStyleBudget
          hTarget
          maxBudget
          hBound =
      table.selectedMinimumSerializedParetoNPStyleBudget
        hTarget
        maxBudget
        hBound := by

  rw [
    table.selectedMinimumSerializedCostNPStyleBudget_eq_minimumRank
      hTarget
      maxBudget
      hBound,
    table.selectedMinimumSerializedParetoNPStyleBudget_eq_minimumRank
      hTarget
      maxBudget
      hBound
  ]

/-- The ordinary packaged decision is positive at the selected ordinary
minimum budget. -/
theorem selectedMinimumSerializedCostNPStyleBudget_decision
    (maxBudget : Nat)
    (hBound :
      table.serializedNPStyleMinimumRank hTarget <=
        maxBudget) :
    (table.serializedCostNPStyleMembershipAt
      hTarget
      (table.selectedMinimumSerializedCostNPStyleBudget
        hTarget
        maxBudget
        hBound)).decision =
      true := by

  exact
    (table.serializedCostNPStyleDecisionAt_eq_true_iff
      hTarget
      (table.selectedMinimumSerializedCostNPStyleBudget
        hTarget
        maxBudget
        hBound)).mpr
      (by
        rw [
          table.selectedMinimumSerializedCostNPStyleBudget_eq_minimumRank
            hTarget
            maxBudget
            hBound
        ])

/-- The Pareto packaged decision is positive at the selected Pareto minimum
budget. -/
theorem selectedMinimumSerializedParetoNPStyleBudget_decision
    (maxBudget : Nat)
    (hBound :
      table.serializedNPStyleMinimumRank hTarget <=
        maxBudget) :
    (table.serializedParetoNPStyleMembershipAt
      hTarget
      (table.selectedMinimumSerializedParetoNPStyleBudget
        hTarget
        maxBudget
        hBound)).decision =
      true := by

  exact
    (table.serializedParetoNPStyleDecisionAt_eq_true_iff
      hTarget
      (table.selectedMinimumSerializedParetoNPStyleBudget
        hTarget
        maxBudget
        hBound)).mpr
      (by
        rw [
          table.selectedMinimumSerializedParetoNPStyleBudget_eq_minimumRank
            hTarget
            maxBudget
            hBound
        ])

/-- Select a polynomial ordinary witness at the least accepted ordinary
budget. -/
noncomputable def selectedMinimumSerializedCostNPStyleWitness
    (maxBudget : Nat)
    (hBound :
      table.serializedNPStyleMinimumRank hTarget <=
        maxBudget) :
    (table.serializedCostNPStyleMembershipAt
      hTarget
      (table.selectedMinimumSerializedCostNPStyleBudget
        hTarget
        maxBudget
        hBound)).PolynomialWitness :=
  (table.serializedCostNPStyleMembershipAt
    hTarget
    (table.selectedMinimumSerializedCostNPStyleBudget
      hTarget
      maxBudget
      hBound)).selectedPolynomialWitness
    (table.selectedMinimumSerializedCostNPStyleBudget_decision
      hTarget
      maxBudget
      hBound)

/-- Select a polynomial Pareto witness at the least accepted Pareto budget. -/
noncomputable def selectedMinimumSerializedParetoNPStyleWitness
    (maxBudget : Nat)
    (hBound :
      table.serializedNPStyleMinimumRank hTarget <=
        maxBudget) :
    (table.serializedParetoNPStyleMembershipAt
      hTarget
      (table.selectedMinimumSerializedParetoNPStyleBudget
        hTarget
        maxBudget
        hBound)).PolynomialWitness :=
  (table.serializedParetoNPStyleMembershipAt
    hTarget
    (table.selectedMinimumSerializedParetoNPStyleBudget
      hTarget
      maxBudget
      hBound)).selectedPolynomialWitness
    (table.selectedMinimumSerializedParetoNPStyleBudget_decision
      hTarget
      maxBudget
      hBound)

/-- Complete minimum-budget and selected-witness package. -/
theorem serializedNPStyleMinimumBudgetSelector_package
    (maxBudget : Nat)
    (hBound :
      table.serializedNPStyleMinimumRank hTarget <=
        maxBudget) :
    table.selectedMinimumSerializedCostNPStyleBudget
          hTarget
          maxBudget
          hBound =
        table.serializedNPStyleMinimumRank hTarget ∧
      table.selectedMinimumSerializedParetoNPStyleBudget
          hTarget
          maxBudget
          hBound =
        table.serializedNPStyleMinimumRank hTarget ∧
      table.selectedMinimumSerializedCostNPStyleBudget
          hTarget
          maxBudget
          hBound =
        table.selectedMinimumSerializedParetoNPStyleBudget
          hTarget
          maxBudget
          hBound ∧
      (table.selectedMinimumSerializedCostNPStyleWitness
        hTarget
        maxBudget
        hBound).accepted ∧
      (table.selectedMinimumSerializedParetoNPStyleWitness
        hTarget
        maxBudget
        hBound).accepted ∧
      (table.selectedMinimumSerializedCostNPStyleWitness
        hTarget
        maxBudget
        hBound).certificateSize_le ∧
      (table.selectedMinimumSerializedCostNPStyleWitness
        hTarget
        maxBudget
        hBound).verifierWork_le ∧
      (table.selectedMinimumSerializedParetoNPStyleWitness
        hTarget
        maxBudget
        hBound).certificateSize_le ∧
      (table.selectedMinimumSerializedParetoNPStyleWitness
        hTarget
        maxBudget
        hBound).verifierWork_le := by

  exact
    ⟨table.selectedMinimumSerializedCostNPStyleBudget_eq_minimumRank
      hTarget
      maxBudget
      hBound,
      table.selectedMinimumSerializedParetoNPStyleBudget_eq_minimumRank
        hTarget
        maxBudget
        hBound,
      table.selectedMinimumSerializedCostNPStyleBudget_eq_pareto
        hTarget
        maxBudget
        hBound,
      (table.selectedMinimumSerializedCostNPStyleWitness
        hTarget
        maxBudget
        hBound).accepted,
      (table.selectedMinimumSerializedParetoNPStyleWitness
        hTarget
        maxBudget
        hBound).accepted,
      (table.selectedMinimumSerializedCostNPStyleWitness
        hTarget
        maxBudget
        hBound).certificateSize_le,
      (table.selectedMinimumSerializedCostNPStyleWitness
        hTarget
        maxBudget
        hBound).verifierWork_le,
      (table.selectedMinimumSerializedParetoNPStyleWitness
        hTarget
        maxBudget
        hBound).certificateSize_le,
      (table.selectedMinimumSerializedParetoNPStyleWitness
        hTarget
        maxBudget
        hBound).verifierWork_le⟩

end SerializedNPStyleMinimumBudgetSelectors

end CorrectedConcreteObservationSelectionDecisionTable


section EncodedSerializedNPStyleMinimumBudgetSelectorFinalPackage

variable {α : Type u}
variable {ι : Type v}
variable {M : Type w}
variable [DecidableEq ι]
variable [Monoid M]
variable (obsFamily : ι → α → M)
variable (f : Nat)
variable (coordinateWeight : ι → Nat)
variable (U : Finset ι)

/-- Final positive-additive finite minimum-budget selector package.

Using the full-interface positive-additive cost as a ceiling, the ordinary and
Pareto serialized NP-style searches both select the exact semantic minimum
rank.  Each selected minimum query carries an accepted polynomial witness with
degree-one certificate-size and verifier-work bounds. -/
theorem
    correctedConcreteWorkingGrammar_observationSelectionEncodedSerializedNPStyleMinimumBudgetSelector_package
    (language : Set (Word α))
    (hTarget :
      language ∈
        StartRootedCorrectedConcreteTargetClass
          (v := z)
          α
          (↥U → M)
          (selectedObservationProduct obsFamily U)
          f) :
    let table :=
      correctedConcreteObservationSelectionSemanticDecisionTable
        (z := z)
        obsFamily
        f
        (correctedConcreteObservationSelectionAdditiveCost
          coordinateWeight)
        U
        language
    let minimumRank :=
      table.serializedNPStyleMinimumRank hTarget
    let maxBudget :=
      correctedConcreteObservationSelectionPositiveAdditiveCost
        coordinateWeight
        U
    let hBound :
        minimumRank <= maxBudget :=
      ambientTargetObservationSelectionPositiveAdditiveMinimumCost_le
        (z := z)
        obsFamily
        f
        coordinateWeight
        U
        hTarget
    let costBudget :=
      table.selectedMinimumSerializedCostNPStyleBudget
        hTarget
        maxBudget
        hBound
    let paretoBudget :=
      table.selectedMinimumSerializedParetoNPStyleBudget
        hTarget
        maxBudget
        hBound
    let costWitness :=
      table.selectedMinimumSerializedCostNPStyleWitness
        hTarget
        maxBudget
        hBound
    let paretoWitness :=
      table.selectedMinimumSerializedParetoNPStyleWitness
        hTarget
        maxBudget
        hBound
    costBudget = minimumRank ∧
      paretoBudget = minimumRank ∧
      costBudget = paretoBudget ∧
      costWitness.accepted ∧
      paretoWitness.accepted ∧
      costWitness.certificateSize_le ∧
      costWitness.verifierWork_le ∧
      paretoWitness.certificateSize_le ∧
      paretoWitness.verifierWork_le := by

  let table :=
    correctedConcreteObservationSelectionSemanticDecisionTable
      (z := z)
      obsFamily
      f
      (correctedConcreteObservationSelectionAdditiveCost
        coordinateWeight)
      U
      language

  let minimumRank :=
    table.serializedNPStyleMinimumRank hTarget

  let maxBudget :=
    correctedConcreteObservationSelectionPositiveAdditiveCost
      coordinateWeight
      U

  let hBound :
      minimumRank <= maxBudget :=
    ambientTargetObservationSelectionPositiveAdditiveMinimumCost_le
      (z := z)
      obsFamily
      f
      coordinateWeight
      U
      hTarget

  exact
    table.serializedNPStyleMinimumBudgetSelector_package
      hTarget
      maxBudget
      hBound

end EncodedSerializedNPStyleMinimumBudgetSelectorFinalPackage

end MCFG
