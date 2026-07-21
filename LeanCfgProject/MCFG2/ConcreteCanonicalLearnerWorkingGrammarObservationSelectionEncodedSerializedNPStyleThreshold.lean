/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG2.ConcreteCanonicalLearnerWorkingGrammarObservationSelectionEncodedSerializedNPStyleMembership

/-!
# ConcreteCanonicalLearnerWorkingGrammarObservationSelectionEncodedSerializedNPStyleThreshold.lean

The preceding file packages one serialized observation-selection query in a
generic NP-style membership interface.  This file organizes those packages
over all budget values and proves their exact threshold behavior.

For a fixed positive-additive observation-selection target, let

```text
minimumRank
```

be the exact semantic minimum positive-additive observation-selection cost.
At every budget `b`, form the canonical encoded instance and its ordinary or
Pareto serialized NP-style membership package.

We prove

```text
ordinary packaged decision at b = true
  iff minimumRank <= b;

Pareto packaged decision at b = true
  iff minimumRank <= b;

an ordinary packaged witness exists at b
  iff minimumRank <= b;

a Pareto packaged witness exists at b
  iff minimumRank <= b.
```

Consequently

* no packaged witness exists below the semantic minimum rank;
* both witness kinds exist at the minimum rank and every larger budget;
* the accepted budgets up to a ceiling are exactly the finite interval from
  the semantic minimum rank to that ceiling;
* ordinary and Pareto accepted-budget searches agree exactly.

This connects the serialized NP-style witness layer back to the exact
optimization threshold.  It remains relative to the materialized semantic
decision table and therefore is not yet compact-input NP membership or a
hardness result.

No target grammar is supplied to any learner.
No `sorry`, `admit`, or `axiom` is used.
-/

namespace MCFG

universe u v w z


namespace CorrectedConcreteObservationSelectionDecisionTable

section PositiveAdditiveSerializedNPStyleThreshold

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

/-- The semantic positive-additive minimum rank used throughout this file. -/
noncomputable def serializedNPStyleMinimumRank : Nat :=
  ambientTargetObservationSelectionPositiveAdditiveMinimumCost
    (z := z)
    obsFamily
    f
    coordinateWeight
    U
    hTarget

/-- Ordinary serialized NP-style membership package at one budget. -/
noncomputable def serializedCostNPStyleMembershipAt
    (budget : Nat) :
    CorrectedConcreteSerializedNPStyleMembership :=
  (table.encodedObservationSelectionInstance
    budget).serializedCostNPStyleMembership

/-- Pareto serialized NP-style membership package at one budget. -/
noncomputable def serializedParetoNPStyleMembershipAt
    (budget : Nat) :
    CorrectedConcreteSerializedNPStyleMembership :=
  (table.encodedObservationSelectionInstance
    budget).serializedParetoNPStyleMembership

/-- Exact ordinary packaged-decision threshold. -/
theorem serializedCostNPStyleDecisionAt_eq_true_iff
    (budget : Nat) :
    (table.serializedCostNPStyleMembershipAt
      hTarget
      budget).decision =
        true ↔
      table.serializedNPStyleMinimumRank hTarget <=
        budget := by

  change
    (table.encodedObservationSelectionInstance
      budget).serializedCostNPStyleMembership.decision =
        true ↔
      ambientTargetObservationSelectionPositiveAdditiveMinimumCost
          (z := z)
          obsFamily
          f
          coordinateWeight
          U
          hTarget <=
        budget

  rw [
    (table.encodedObservationSelectionInstance
      budget).serializedCostNPStyleMembership_decision_iff_tableDecision
  ]

  change
    table.minimumRankAtMostDecision budget = true ↔
      ambientTargetObservationSelectionPositiveAdditiveMinimumCost
          (z := z)
          obsFamily
          f
          coordinateWeight
          U
          hTarget <=
        budget

  exact
    table.minimumRankAtMostDecision_eq_true_iff
      hTarget
      budget

/-- Exact Pareto packaged-decision threshold. -/
theorem serializedParetoNPStyleDecisionAt_eq_true_iff
    (budget : Nat) :
    (table.serializedParetoNPStyleMembershipAt
      hTarget
      budget).decision =
        true ↔
      table.serializedNPStyleMinimumRank hTarget <=
        budget := by

  change
    (table.encodedObservationSelectionInstance
      budget).serializedParetoNPStyleMembership.decision =
        true ↔
      ambientTargetObservationSelectionPositiveAdditiveMinimumCost
          (z := z)
          obsFamily
          f
          coordinateWeight
          U
          hTarget <=
        budget

  rw [
    (table.encodedObservationSelectionInstance
      budget).serializedParetoNPStyleMembership_decision_iff_tableDecision
  ]

  exact
    table.positiveAdditiveParetoScalarDecision_eq_true_iff_minimumRank_le
      hTarget
      budget

/-- An ordinary packaged witness exists exactly at and above the semantic
minimum rank. -/
theorem exists_serializedCostNPStyleWitnessAt_iff
    (budget : Nat) :
    (∃ code : Nat,
      (table.serializedCostNPStyleMembershipAt
        hTarget
        budget).Witness code) ↔
      table.serializedNPStyleMinimumRank hTarget <=
        budget := by

  exact
    (table.serializedCostNPStyleMembershipAt
      hTarget
      budget).decision_eq_true_iff_exists_witness.symm.trans
      (table.serializedCostNPStyleDecisionAt_eq_true_iff
        hTarget
        budget)

/-- A Pareto packaged witness exists exactly at and above the semantic minimum
rank. -/
theorem exists_serializedParetoNPStyleWitnessAt_iff
    (budget : Nat) :
    (∃ code : Nat,
      (table.serializedParetoNPStyleMembershipAt
        hTarget
        budget).Witness code) ↔
      table.serializedNPStyleMinimumRank hTarget <=
        budget := by

  exact
    (table.serializedParetoNPStyleMembershipAt
      hTarget
      budget).decision_eq_true_iff_exists_witness.symm.trans
      (table.serializedParetoNPStyleDecisionAt_eq_true_iff
        hTarget
        budget)

/-- No ordinary serialized NP-style witness exists strictly below the semantic
minimum rank. -/
theorem no_serializedCostNPStyleWitnessAt_of_lt
    {budget : Nat}
    (hBudget :
      budget <
        table.serializedNPStyleMinimumRank hTarget) :
    ¬ ∃ code : Nat,
        (table.serializedCostNPStyleMembershipAt
          hTarget
          budget).Witness code := by

  intro hWitness

  have hMinimumLe :
      table.serializedNPStyleMinimumRank hTarget <=
        budget :=
    (table.exists_serializedCostNPStyleWitnessAt_iff
      hTarget
      budget).mp
      hWitness

  omega

/-- No Pareto serialized NP-style witness exists strictly below the semantic
minimum rank. -/
theorem no_serializedParetoNPStyleWitnessAt_of_lt
    {budget : Nat}
    (hBudget :
      budget <
        table.serializedNPStyleMinimumRank hTarget) :
    ¬ ∃ code : Nat,
        (table.serializedParetoNPStyleMembershipAt
          hTarget
          budget).Witness code := by

  intro hWitness

  have hMinimumLe :
      table.serializedNPStyleMinimumRank hTarget <=
        budget :=
    (table.exists_serializedParetoNPStyleWitnessAt_iff
      hTarget
      budget).mp
      hWitness

  omega

/-- An ordinary packaged witness exists at the exact semantic minimum rank. -/
theorem exists_serializedCostNPStyleWitnessAt_minimum :
    ∃ code : Nat,
      (table.serializedCostNPStyleMembershipAt
        hTarget
        (table.serializedNPStyleMinimumRank hTarget)).Witness
          code := by

  exact
    (table.exists_serializedCostNPStyleWitnessAt_iff
      hTarget
      (table.serializedNPStyleMinimumRank hTarget)).mpr
      (Nat.le_refl _)

/-- A Pareto packaged witness exists at the exact semantic minimum rank. -/
theorem exists_serializedParetoNPStyleWitnessAt_minimum :
    ∃ code : Nat,
      (table.serializedParetoNPStyleMembershipAt
        hTarget
        (table.serializedNPStyleMinimumRank hTarget)).Witness
          code := by

  exact
    (table.exists_serializedParetoNPStyleWitnessAt_iff
      hTarget
      (table.serializedNPStyleMinimumRank hTarget)).mpr
      (Nat.le_refl _)

/-- Finite ordinary packaged-decision search up to a supplied budget ceiling. -/
noncomputable def serializedCostNPStyleAcceptedBudgets
    (maxBudget : Nat) : Finset Nat :=
  (Finset.range (maxBudget + 1)).filter
    (fun budget =>
      (table.serializedCostNPStyleMembershipAt
        hTarget
        budget).decision =
          true)

/-- Finite Pareto packaged-decision search up to a supplied budget ceiling. -/
noncomputable def serializedParetoNPStyleAcceptedBudgets
    (maxBudget : Nat) : Finset Nat :=
  (Finset.range (maxBudget + 1)).filter
    (fun budget =>
      (table.serializedParetoNPStyleMembershipAt
        hTarget
        budget).decision =
          true)

/-- Exact membership characterization of the finite ordinary accepted-budget
search. -/
theorem mem_serializedCostNPStyleAcceptedBudgets_iff
    (maxBudget budget : Nat) :
    budget ∈
        table.serializedCostNPStyleAcceptedBudgets
          hTarget
          maxBudget ↔
      table.serializedNPStyleMinimumRank hTarget <=
          budget ∧
        budget <= maxBudget := by

  unfold serializedCostNPStyleAcceptedBudgets

  rw [Finset.mem_filter]

  constructor

  · rintro ⟨hRange, hDecision⟩

    have hBudgetLe :
        budget <= maxBudget := by

      simpa using hRange

    have hMinimumLe :
        table.serializedNPStyleMinimumRank hTarget <=
          budget :=
      (table.serializedCostNPStyleDecisionAt_eq_true_iff
        hTarget
        budget).mp
        hDecision

    exact ⟨hMinimumLe, hBudgetLe⟩

  · rintro ⟨hMinimumLe, hBudgetLe⟩

    exact
      ⟨by
          simpa using hBudgetLe,
        (table.serializedCostNPStyleDecisionAt_eq_true_iff
          hTarget
          budget).mpr
          hMinimumLe⟩

/-- Exact membership characterization of the finite Pareto accepted-budget
search. -/
theorem mem_serializedParetoNPStyleAcceptedBudgets_iff
    (maxBudget budget : Nat) :
    budget ∈
        table.serializedParetoNPStyleAcceptedBudgets
          hTarget
          maxBudget ↔
      table.serializedNPStyleMinimumRank hTarget <=
          budget ∧
        budget <= maxBudget := by

  unfold serializedParetoNPStyleAcceptedBudgets

  rw [Finset.mem_filter]

  constructor

  · rintro ⟨hRange, hDecision⟩

    have hBudgetLe :
        budget <= maxBudget := by

      simpa using hRange

    have hMinimumLe :
        table.serializedNPStyleMinimumRank hTarget <=
          budget :=
      (table.serializedParetoNPStyleDecisionAt_eq_true_iff
        hTarget
        budget).mp
        hDecision

    exact ⟨hMinimumLe, hBudgetLe⟩

  · rintro ⟨hMinimumLe, hBudgetLe⟩

    exact
      ⟨by
          simpa using hBudgetLe,
        (table.serializedParetoNPStyleDecisionAt_eq_true_iff
          hTarget
          budget).mpr
          hMinimumLe⟩

/-- Ordinary accepted budgets form exactly the closed finite interval from the
semantic minimum rank to the supplied ceiling. -/
theorem serializedCostNPStyleAcceptedBudgets_eq_Icc
    (maxBudget : Nat) :
    table.serializedCostNPStyleAcceptedBudgets
        hTarget
        maxBudget =
      Finset.Icc
        (table.serializedNPStyleMinimumRank hTarget)
        maxBudget := by

  ext budget

  rw [
    table.mem_serializedCostNPStyleAcceptedBudgets_iff
      hTarget
      maxBudget
      budget
  ]

  simp

/-- Pareto accepted budgets form exactly the same closed finite interval. -/
theorem serializedParetoNPStyleAcceptedBudgets_eq_Icc
    (maxBudget : Nat) :
    table.serializedParetoNPStyleAcceptedBudgets
        hTarget
        maxBudget =
      Finset.Icc
        (table.serializedNPStyleMinimumRank hTarget)
        maxBudget := by

  ext budget

  rw [
    table.mem_serializedParetoNPStyleAcceptedBudgets_iff
      hTarget
      maxBudget
      budget
  ]

  simp

/-- Ordinary and Pareto packaged accepted-budget searches agree exactly. -/
theorem serializedCostNPStyleAcceptedBudgets_eq_pareto
    (maxBudget : Nat) :
    table.serializedCostNPStyleAcceptedBudgets
        hTarget
        maxBudget =
      table.serializedParetoNPStyleAcceptedBudgets
        hTarget
        maxBudget := by

  rw [
    table.serializedCostNPStyleAcceptedBudgets_eq_Icc
      hTarget
      maxBudget,
    table.serializedParetoNPStyleAcceptedBudgets_eq_Icc
      hTarget
      maxBudget
  ]

/-- Both finite accepted-budget searches are nonempty whenever the ceiling
reaches the semantic minimum rank. -/
theorem serializedNPStyleAcceptedBudgets_nonempty
    {maxBudget : Nat}
    (hBound :
      table.serializedNPStyleMinimumRank hTarget <=
        maxBudget) :
    (table.serializedCostNPStyleAcceptedBudgets
        hTarget
        maxBudget).Nonempty ∧
      (table.serializedParetoNPStyleAcceptedBudgets
        hTarget
        maxBudget).Nonempty := by

  constructor

  · exact
      ⟨table.serializedNPStyleMinimumRank hTarget,
        (table.mem_serializedCostNPStyleAcceptedBudgets_iff
          hTarget
          maxBudget
          (table.serializedNPStyleMinimumRank hTarget)).mpr
          ⟨Nat.le_refl _, hBound⟩⟩

  · exact
      ⟨table.serializedNPStyleMinimumRank hTarget,
        (table.mem_serializedParetoNPStyleAcceptedBudgets_iff
          hTarget
          maxBudget
          (table.serializedNPStyleMinimumRank hTarget)).mpr
          ⟨Nat.le_refl _, hBound⟩⟩

/-- Complete budget-threshold package for the serialized NP-style family. -/
theorem serializedNPStyleThreshold_package
    (maxBudget : Nat) :
    (∀ budget : Nat,
      (table.serializedCostNPStyleMembershipAt
        hTarget
        budget).decision =
          true ↔
        table.serializedNPStyleMinimumRank hTarget <=
          budget) ∧
      (∀ budget : Nat,
        (table.serializedParetoNPStyleMembershipAt
          hTarget
          budget).decision =
            true ↔
          table.serializedNPStyleMinimumRank hTarget <=
            budget) ∧
      table.serializedCostNPStyleAcceptedBudgets
          hTarget
          maxBudget =
        Finset.Icc
          (table.serializedNPStyleMinimumRank hTarget)
          maxBudget ∧
      table.serializedParetoNPStyleAcceptedBudgets
          hTarget
          maxBudget =
        Finset.Icc
          (table.serializedNPStyleMinimumRank hTarget)
          maxBudget ∧
      table.serializedCostNPStyleAcceptedBudgets
          hTarget
          maxBudget =
        table.serializedParetoNPStyleAcceptedBudgets
          hTarget
          maxBudget := by

  exact
    ⟨table.serializedCostNPStyleDecisionAt_eq_true_iff
      hTarget,
      table.serializedParetoNPStyleDecisionAt_eq_true_iff
        hTarget,
      table.serializedCostNPStyleAcceptedBudgets_eq_Icc
        hTarget
        maxBudget,
      table.serializedParetoNPStyleAcceptedBudgets_eq_Icc
        hTarget
        maxBudget,
      table.serializedCostNPStyleAcceptedBudgets_eq_pareto
        hTarget
        maxBudget⟩

end PositiveAdditiveSerializedNPStyleThreshold

end CorrectedConcreteObservationSelectionDecisionTable


section EncodedSerializedNPStyleThresholdFinalPackage

variable {α : Type u}
variable {ι : Type v}
variable {M : Type w}
variable [DecidableEq ι]
variable [Monoid M]
variable (obsFamily : ι → α → M)
variable (f : Nat)
variable (coordinateWeight : ι → Nat)
variable (U : Finset ι)

/-- Final positive-additive serialized NP-style threshold package.

The ordinary and Pareto serialized NP-style problems have the exact same
threshold: a witness exists at budget `b` exactly when the semantic minimum
positive-additive rank is at most `b`.  Up to the ambient full-interface
ceiling, their accepted-budget sets are the same exact finite interval. -/
theorem
    correctedConcreteWorkingGrammar_observationSelectionEncodedSerializedNPStyleThreshold_package
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
    (∀ budget : Nat,
      (∃ code : Nat,
        (table.serializedCostNPStyleMembershipAt
          hTarget
          budget).Witness code) ↔
        minimumRank <= budget) ∧
      (∀ budget : Nat,
        (∃ code : Nat,
          (table.serializedParetoNPStyleMembershipAt
            hTarget
            budget).Witness code) ↔
          minimumRank <= budget) ∧
      (¬ ∃ budget code : Nat,
        budget < minimumRank ∧
          (table.serializedParetoNPStyleMembershipAt
            hTarget
            budget).Witness code) ∧
      (∃ code : Nat,
        (table.serializedCostNPStyleMembershipAt
          hTarget
          minimumRank).Witness code) ∧
      (∃ code : Nat,
        (table.serializedParetoNPStyleMembershipAt
          hTarget
          minimumRank).Witness code) ∧
      table.serializedCostNPStyleAcceptedBudgets
          hTarget
          maxBudget =
        Finset.Icc minimumRank maxBudget ∧
      table.serializedParetoNPStyleAcceptedBudgets
          hTarget
          maxBudget =
        Finset.Icc minimumRank maxBudget ∧
      table.serializedCostNPStyleAcceptedBudgets
          hTarget
          maxBudget =
        table.serializedParetoNPStyleAcceptedBudgets
          hTarget
          maxBudget := by

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

  have hNoBelow :
      ¬ ∃ budget code : Nat,
        budget < minimumRank ∧
          (table.serializedParetoNPStyleMembershipAt
            hTarget
            budget).Witness code := by

    rintro ⟨budget, code, hBudget, hWitness⟩

    exact
      table.no_serializedParetoNPStyleWitnessAt_of_lt
        hTarget
        hBudget
        ⟨code, hWitness⟩

  exact
    ⟨table.exists_serializedCostNPStyleWitnessAt_iff
      hTarget,
      table.exists_serializedParetoNPStyleWitnessAt_iff
        hTarget,
      hNoBelow,
      table.exists_serializedCostNPStyleWitnessAt_minimum
        hTarget,
      table.exists_serializedParetoNPStyleWitnessAt_minimum
        hTarget,
      table.serializedCostNPStyleAcceptedBudgets_eq_Icc
        hTarget
        maxBudget,
      table.serializedParetoNPStyleAcceptedBudgets_eq_Icc
        hTarget
        maxBudget,
      table.serializedCostNPStyleAcceptedBudgets_eq_pareto
        hTarget
        maxBudget⟩

end EncodedSerializedNPStyleThresholdFinalPackage

end MCFG
