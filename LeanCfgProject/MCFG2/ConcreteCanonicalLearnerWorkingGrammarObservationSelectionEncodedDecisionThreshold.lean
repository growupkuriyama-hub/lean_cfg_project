/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG2.ConcreteCanonicalLearnerWorkingGrammarObservationSelectionEncodedCertifiedSelector

/-!
# ConcreteCanonicalLearnerWorkingGrammarObservationSelectionEncodedDecisionThreshold.lean

The preceding encoded selector returns a minimum accepted budget, the least
accepted dense certificate code at that budget, and the decoded certificate.
This file identifies the selected budget as the exact threshold of the Boolean
decision procedure.

For both ordinary cost feasibility and Pareto-scalar feasibility, the selected
certified output satisfies

```text
decision budget = true  ↔  selectedBudget ≤ budget.
```

Consequently:

* every smaller budget is rejected;
* the selected budget is accepted;
* every larger budget is accepted;
* the complete bounded yes-set is an interval beginning at the selected budget.

The final positive-additive package identifies this Boolean threshold with the
semantic minimum positive-additive observation-selection rank while retaining
the canonical dense certificate.

This is still a finite-table result.  It does not claim that construction of
the semantic table is polynomial-time, and it makes no NP-hardness claim.

No target grammar is supplied to any learner.
No `sorry`, `admit`, or `axiom` is used.
-/

namespace MCFG

universe u v w z

namespace CorrectedConcreteObservationSelectionDecisionTable

section EncodedMinimumCostDecisionThreshold

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
  (table :
    CorrectedConcreteObservationSelectionDecisionTable
      (z := z)
      obsFamily
      f
      selectionCost
      U
      language)

/-- A certified ordinary-cost selector together with the theorem that its
selected budget is the exact Boolean feasibility threshold. -/
structure CorrectedConcreteEncodedMinimumCostDecisionThreshold
    (maxBudget : Nat) where

  output :
    table.CorrectedConcreteEncodedMinimumCostSelectionOutput
      maxBudget

  decision_exact :
    ∀ budget : Nat,
      table.costFeasibleDecision budget = true ↔
        output.budget <= budget

/-- Construct the exact ordinary-cost Boolean threshold from the encoded
certified selector. -/
noncomputable def selectedEncodedMinimumCostDecisionThreshold
    (maxBudget : Nat)
    (hAccepted :
      table.HasAcceptedCostBudgetUpTo maxBudget) :
    table.CorrectedConcreteEncodedMinimumCostDecisionThreshold
      maxBudget := by

  let output :=
    table.selectedEncodedMinimumCostSelectionOutput
      maxBudget
      hAccepted

  refine
    { output := output
      decision_exact := ?_ }

  intro budget

  constructor

  · intro hDecision

    by_cases hBudget :
        budget <= maxBudget

    · exact
        output.budget_minimal
          budget
          hBudget
          hDecision

    · have hMaxLt :
          maxBudget < budget :=
        Nat.lt_of_not_ge hBudget

      exact
        output.budget_le_max.trans
          (Nat.le_of_lt hMaxLt)

  · intro hBudget

    exact
      table.costFeasibleDecision_mono
        hBudget
        output.budget_decision

/-- The selected ordinary-cost threshold budget is accepted. -/
theorem selectedEncodedMinimumCostDecisionThreshold_at_selected
    (maxBudget : Nat)
    (hAccepted :
      table.HasAcceptedCostBudgetUpTo maxBudget) :
    let threshold :=
      table.selectedEncodedMinimumCostDecisionThreshold
        maxBudget
        hAccepted
    table.costFeasibleDecision threshold.output.budget =
      true := by

  let threshold :=
    table.selectedEncodedMinimumCostDecisionThreshold
      maxBudget
      hAccepted

  exact
    (threshold.decision_exact threshold.output.budget).2
      (Nat.le_refl threshold.output.budget)

/-- Every budget strictly below the selected ordinary-cost threshold is
rejected. -/
theorem selectedEncodedMinimumCostDecisionThreshold_below_rejected
    (maxBudget : Nat)
    (hAccepted :
      table.HasAcceptedCostBudgetUpTo maxBudget)
    (budget : Nat)
    (hBudget :
      budget <
        (table.selectedEncodedMinimumCostDecisionThreshold
          maxBudget
          hAccepted).output.budget) :
    table.costFeasibleDecision budget ≠ true := by

  intro hDecision

  have hThresholdLe :
      (table.selectedEncodedMinimumCostDecisionThreshold
        maxBudget
        hAccepted).output.budget <=
        budget :=
    ((table.selectedEncodedMinimumCostDecisionThreshold
      maxBudget
      hAccepted).decision_exact budget).1
      hDecision

  exact
    (Nat.not_le_of_lt hBudget)
      hThresholdLe

/-- Every budget at or above the selected ordinary-cost threshold is
accepted. -/
theorem selectedEncodedMinimumCostDecisionThreshold_above_accepted
    (maxBudget : Nat)
    (hAccepted :
      table.HasAcceptedCostBudgetUpTo maxBudget)
    (budget : Nat)
    (hBudget :
      (table.selectedEncodedMinimumCostDecisionThreshold
        maxBudget
        hAccepted).output.budget <=
        budget) :
    table.costFeasibleDecision budget = true := by

  exact
    ((table.selectedEncodedMinimumCostDecisionThreshold
      maxBudget
      hAccepted).decision_exact budget).2
      hBudget

/-- The exact ordinary-cost threshold retains the certified dense code,
checked decoder, and least-code property from the previous selector. -/
theorem selectedEncodedMinimumCostDecisionThreshold_package
    (maxBudget : Nat)
    (hAccepted :
      table.HasAcceptedCostBudgetUpTo maxBudget) :
    let threshold :=
      table.selectedEncodedMinimumCostDecisionThreshold
        maxBudget
        hAccepted
    (∀ budget : Nat,
      table.costFeasibleDecision budget = true ↔
        threshold.output.budget <= budget) ∧
      threshold.output.code < 2 ^ U.card ∧
      correctedConcreteDenseCertificateDecode
            U
            threshold.output.code =
        some threshold.output.certificate ∧
      correctedConcreteDenseCertificateCode
            U
            threshold.output.certificate =
        threshold.output.code ∧
      table.verifiesCostCertificate
            threshold.output.budget
            threshold.output.certificate =
        true ∧
      (∀ competingCode : Nat,
        competingCode ∈
            table.verifiedDenseCostCertificateCodes
              threshold.output.budget →
          threshold.output.code <= competingCode) := by

  let threshold :=
    table.selectedEncodedMinimumCostDecisionThreshold
      maxBudget
      hAccepted

  exact
    ⟨threshold.decision_exact,
      threshold.output.code_lt,
      threshold.output.decode_eq,
      threshold.output.reencode_eq,
      threshold.output.certificate_verifies,
      threshold.output.code_minimal⟩

end EncodedMinimumCostDecisionThreshold


section EncodedMinimumParetoScalarDecisionThreshold

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
  (table :
    CorrectedConcreteObservationSelectionDecisionTable
      (z := z)
      obsFamily
      f
      selectionCost
      U
      language)

/-- A certified Pareto-scalar selector together with the theorem that its
selected scalar budget is the exact Boolean feasibility threshold. -/
structure CorrectedConcreteEncodedMinimumParetoScalarDecisionThreshold
    (maxBudget : Nat) where

  output :
    table.CorrectedConcreteEncodedMinimumParetoScalarSelectionOutput
      maxBudget

  decision_exact :
    ∀ budget : Nat,
      table.paretoScalarFeasibleDecision budget = true ↔
        output.budget <= budget

/-- Construct the exact Pareto-scalar Boolean threshold from the encoded
certified selector. -/
noncomputable def selectedEncodedMinimumParetoScalarDecisionThreshold
    (maxBudget : Nat)
    (hAccepted :
      table.HasAcceptedParetoScalarBudgetUpTo maxBudget) :
    table.CorrectedConcreteEncodedMinimumParetoScalarDecisionThreshold
      maxBudget := by

  let output :=
    table.selectedEncodedMinimumParetoScalarSelectionOutput
      maxBudget
      hAccepted

  refine
    { output := output
      decision_exact := ?_ }

  intro budget

  constructor

  · intro hDecision

    by_cases hBudget :
        budget <= maxBudget

    · exact
        output.budget_minimal
          budget
          hBudget
          hDecision

    · have hMaxLt :
          maxBudget < budget :=
        Nat.lt_of_not_ge hBudget

      exact
        output.budget_le_max.trans
          (Nat.le_of_lt hMaxLt)

  · intro hBudget

    exact
      table.paretoScalarFeasibleDecision_mono
        hBudget
        output.budget_decision

/-- The selected Pareto-scalar threshold budget is accepted. -/
theorem selectedEncodedMinimumParetoScalarDecisionThreshold_at_selected
    (maxBudget : Nat)
    (hAccepted :
      table.HasAcceptedParetoScalarBudgetUpTo maxBudget) :
    let threshold :=
      table.selectedEncodedMinimumParetoScalarDecisionThreshold
        maxBudget
        hAccepted
    table.paretoScalarFeasibleDecision
        threshold.output.budget =
      true := by

  let threshold :=
    table.selectedEncodedMinimumParetoScalarDecisionThreshold
      maxBudget
      hAccepted

  exact
    (threshold.decision_exact threshold.output.budget).2
      (Nat.le_refl threshold.output.budget)

/-- Every budget strictly below the selected Pareto-scalar threshold is
rejected. -/
theorem
    selectedEncodedMinimumParetoScalarDecisionThreshold_below_rejected
    (maxBudget : Nat)
    (hAccepted :
      table.HasAcceptedParetoScalarBudgetUpTo maxBudget)
    (budget : Nat)
    (hBudget :
      budget <
        (table.selectedEncodedMinimumParetoScalarDecisionThreshold
          maxBudget
          hAccepted).output.budget) :
    table.paretoScalarFeasibleDecision budget ≠ true := by

  intro hDecision

  have hThresholdLe :
      (table.selectedEncodedMinimumParetoScalarDecisionThreshold
        maxBudget
        hAccepted).output.budget <=
        budget :=
    ((table.selectedEncodedMinimumParetoScalarDecisionThreshold
      maxBudget
      hAccepted).decision_exact budget).1
      hDecision

  exact
    (Nat.not_le_of_lt hBudget)
      hThresholdLe

/-- Every budget at or above the selected Pareto-scalar threshold is
accepted. -/
theorem
    selectedEncodedMinimumParetoScalarDecisionThreshold_above_accepted
    (maxBudget : Nat)
    (hAccepted :
      table.HasAcceptedParetoScalarBudgetUpTo maxBudget)
    (budget : Nat)
    (hBudget :
      (table.selectedEncodedMinimumParetoScalarDecisionThreshold
        maxBudget
        hAccepted).output.budget <=
        budget) :
    table.paretoScalarFeasibleDecision budget = true := by

  exact
    ((table.selectedEncodedMinimumParetoScalarDecisionThreshold
      maxBudget
      hAccepted).decision_exact budget).2
      hBudget

/-- The exact Pareto-scalar threshold retains Pareto optimality, its checked
dense certificate, and the least-code property. -/
theorem
    selectedEncodedMinimumParetoScalarDecisionThreshold_package
    (maxBudget : Nat)
    (hAccepted :
      table.HasAcceptedParetoScalarBudgetUpTo maxBudget) :
    let threshold :=
      table.selectedEncodedMinimumParetoScalarDecisionThreshold
        maxBudget
        hAccepted
    (∀ budget : Nat,
      table.paretoScalarFeasibleDecision budget = true ↔
        threshold.output.budget <= budget) ∧
      CorrectedConcreteObservationSelectionParetoOptimal
        (z := z)
        obsFamily
        f
        selectionCost
        U
        language
        threshold.output.certificate ∧
      correctedConcreteObservationSelectionParetoScalarCost
            selectionCost
            threshold.output.certificate <=
        threshold.output.budget ∧
      threshold.output.code < 2 ^ U.card ∧
      correctedConcreteDenseCertificateDecode
            U
            threshold.output.code =
        some threshold.output.certificate ∧
      correctedConcreteDenseCertificateCode
            U
            threshold.output.certificate =
        threshold.output.code ∧
      table.verifiesParetoScalarCertificate
            threshold.output.budget
            threshold.output.certificate =
        true ∧
      (∀ competingCode : Nat,
        competingCode ∈
            table.verifiedDenseParetoScalarCertificateCodes
              threshold.output.budget →
          threshold.output.code <= competingCode) := by

  let threshold :=
    table.selectedEncodedMinimumParetoScalarDecisionThreshold
      maxBudget
      hAccepted

  exact
    ⟨threshold.decision_exact,
      threshold.output.pareto_optimal,
      threshold.output.scalar_le_budget,
      threshold.output.code_lt,
      threshold.output.decode_eq,
      threshold.output.reencode_eq,
      threshold.output.certificate_verifies,
      threshold.output.code_minimal⟩

end EncodedMinimumParetoScalarDecisionThreshold

end CorrectedConcreteObservationSelectionDecisionTable


section EncodedDecisionThresholdFinalPackage

variable {α : Type u}
variable {ι : Type v}
variable {M : Type w}
variable [DecidableEq ι]
variable [Monoid M]
variable (obsFamily : ι → α → M)
variable (f : Nat)
variable (coordinateWeight : ι → Nat)
variable (U : Finset ι)

/-- Final positive-additive exact-decision-threshold package.

The selected encoded Pareto certificate realizes the semantic minimum
positive-additive rank, and the Boolean Pareto-scalar decision accepts exactly
the budgets at or above that rank. -/
theorem
    correctedConcreteWorkingGrammar_observationSelectionEncodedDecisionThreshold_package
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
    let maxBudget :=
      correctedConcreteObservationSelectionPositiveAdditiveCost
        coordinateWeight
        U
    let hBound :
        ambientTargetObservationSelectionPositiveAdditiveMinimumCost
              (z := z)
              obsFamily
              f
              coordinateWeight
              U
              hTarget <=
            maxBudget :=
      ambientTargetObservationSelectionPositiveAdditiveMinimumCost_le
        (z := z)
        obsFamily
        f
        coordinateWeight
        U
        hTarget
    let hAccepted :=
      table.hasAcceptedParetoScalarBudgetUpTo_of_positiveAdditiveMinimum_le
        hTarget
        maxBudget
        hBound
    let threshold :=
      table.selectedEncodedMinimumParetoScalarDecisionThreshold
        maxBudget
        hAccepted
    threshold.output.budget =
        ambientTargetObservationSelectionPositiveAdditiveMinimumCost
          (z := z)
          obsFamily
          f
          coordinateWeight
          U
          hTarget ∧
      (∀ budget : Nat,
        table.paretoScalarFeasibleDecision budget = true ↔
          ambientTargetObservationSelectionPositiveAdditiveMinimumCost
              (z := z)
              obsFamily
              f
              coordinateWeight
              U
              hTarget <=
            budget) ∧
      correctedConcreteObservationSelectionParetoScalarCost
            (correctedConcreteObservationSelectionAdditiveCost
              coordinateWeight)
            threshold.output.certificate =
        threshold.output.budget ∧
      CorrectedConcreteObservationSelectionParetoOptimal
        (z := z)
        obsFamily
        f
        (correctedConcreteObservationSelectionAdditiveCost
          coordinateWeight)
        U
        language
        threshold.output.certificate ∧
      threshold.output.code < 2 ^ U.card ∧
      correctedConcreteDenseCertificateDecode
            U
            threshold.output.code =
        some threshold.output.certificate := by

  let table :=
    correctedConcreteObservationSelectionSemanticDecisionTable
      (z := z)
      obsFamily
      f
      (correctedConcreteObservationSelectionAdditiveCost
        coordinateWeight)
      U
      language

  let maxBudget :=
    correctedConcreteObservationSelectionPositiveAdditiveCost
      coordinateWeight
      U

  let hBound :
      ambientTargetObservationSelectionPositiveAdditiveMinimumCost
            (z := z)
            obsFamily
            f
            coordinateWeight
            U
            hTarget <=
          maxBudget :=
    ambientTargetObservationSelectionPositiveAdditiveMinimumCost_le
      (z := z)
      obsFamily
      f
      coordinateWeight
      U
      hTarget

  let hAccepted :=
    table.hasAcceptedParetoScalarBudgetUpTo_of_positiveAdditiveMinimum_le
      hTarget
      maxBudget
      hBound

  let threshold :=
    table.selectedEncodedMinimumParetoScalarDecisionThreshold
      maxBudget
      hAccepted

  have hBudgetEq :
      threshold.output.budget =
        ambientTargetObservationSelectionPositiveAdditiveMinimumCost
          (z := z)
          obsFamily
          f
          coordinateWeight
          U
          hTarget := by

    change
      table.selectedMinimumAcceptedParetoScalarBudget
            maxBudget
            hAccepted =
        ambientTargetObservationSelectionPositiveAdditiveMinimumCost
          (z := z)
          obsFamily
          f
          coordinateWeight
          U
          hTarget

    exact
      table.selectedMinimumAcceptedParetoScalarBudget_eq_positiveAdditiveMinimum
        hTarget
        maxBudget
        hBound

  have hDecisionExact :
      ∀ budget : Nat,
        table.paretoScalarFeasibleDecision budget = true ↔
          ambientTargetObservationSelectionPositiveAdditiveMinimumCost
              (z := z)
              obsFamily
              f
              coordinateWeight
              U
              hTarget <=
            budget := by

    intro budget

    rw [← hBudgetEq]

    exact
      threshold.decision_exact budget

  have hCertified :=
    correctedConcreteWorkingGrammar_observationSelectionEncodedCertifiedSelector_package
      (z := z)
      obsFamily
      f
      coordinateWeight
      U
      language
      hTarget

  have hScalarEq :
      correctedConcreteObservationSelectionParetoScalarCost
            (correctedConcreteObservationSelectionAdditiveCost
              coordinateWeight)
            threshold.output.certificate =
        threshold.output.budget := by

    exact hCertified.2.1

  exact
    ⟨hBudgetEq,
      hDecisionExact,
      hScalarEq,
      threshold.output.pareto_optimal,
      threshold.output.code_lt,
      threshold.output.decode_eq⟩

end EncodedDecisionThresholdFinalPackage

end MCFG
