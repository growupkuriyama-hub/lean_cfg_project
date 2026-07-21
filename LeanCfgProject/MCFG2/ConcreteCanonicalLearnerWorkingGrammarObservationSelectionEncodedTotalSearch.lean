/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG.ConcreteCanonicalLearnerWorkingGrammarObservationSelectionEncodedThresholdSearch

/-!
# ConcreteCanonicalLearnerWorkingGrammarObservationSelectionEncodedTotalSearch.lean

The preceding encoded threshold-search layer requires a proof that some budget
below the supplied ceiling is accepted.  This file internalizes that proof and
turns the construction into a total optional search.

For ordinary cost and Pareto-scalar feasibility, the total search returns

```text
none
```

exactly when no budget at most the ceiling is accepted, and otherwise returns

```text
some success
```

where `success` contains

* the bounded acceptance witness;
* the complete accepted-budget interval;
* its least accepted budget;
* the least accepted dense certificate code at that budget;
* the checked decoded certificate and all semantic proofs.

Thus the caller no longer supplies a proof argument merely to run the finite
optimization search.

The final positive-additive theorem proves that the total Pareto-scalar search
succeeds at the ambient positive-additive budget and returns the semantic
minimum positive-additive observation-selection rank with its canonical dense
Pareto certificate.

This remains a total search relative to a supplied finite decision table.
It does not construct the semantic table in polynomial time, and it makes no
NP-hardness or NP-completeness claim.

No target grammar is supplied to any learner.
No `sorry`, `admit`, or `axiom` is used.
-/

namespace MCFG

universe u v w z

namespace CorrectedConcreteObservationSelectionDecisionTable

section TotalEncodedCostSearch

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

/-- Successful output of the total encoded ordinary-cost search.  The bounded
acceptance proof is stored internally and indexes the certified threshold
search. -/
structure CorrectedConcreteEncodedCostSearchSuccess
    (maxBudget : Nat) where

  accepted :
    table.HasAcceptedCostBudgetUpTo maxBudget

  search :
    table.CorrectedConcreteEncodedCostThresholdSearch
      maxBudget
      accepted

/-- Total optional ordinary-cost optimization search. -/
noncomputable def runEncodedCostThresholdSearch
    (maxBudget : Nat) :
    Option
      (table.CorrectedConcreteEncodedCostSearchSuccess
        maxBudget) := by

  classical

  by_cases hAccepted :
      table.HasAcceptedCostBudgetUpTo maxBudget

  · exact
      some
        { accepted := hAccepted
          search :=
            table.selectedEncodedCostThresholdSearch
              maxBudget
              hAccepted }

  · exact none

/-- The total ordinary-cost search returns `none` exactly when no bounded
accepted budget exists. -/
theorem runEncodedCostThresholdSearch_eq_none_iff
    (maxBudget : Nat) :
    table.runEncodedCostThresholdSearch maxBudget = none ↔
      ¬ table.HasAcceptedCostBudgetUpTo maxBudget := by

  classical

  by_cases hAccepted :
      table.HasAcceptedCostBudgetUpTo maxBudget

  · simp [runEncodedCostThresholdSearch, hAccepted]

  · simp [runEncodedCostThresholdSearch, hAccepted]

/-- Failure of the total ordinary-cost search is exactly rejection of the
terminal budget. -/
theorem runEncodedCostThresholdSearch_eq_none_iff_terminal_rejected
    (maxBudget : Nat) :
    table.runEncodedCostThresholdSearch maxBudget = none ↔
      table.costFeasibleDecision maxBudget ≠ true := by

  constructor

  · intro hNone hTerminal

    have hNotAccepted :
        ¬ table.HasAcceptedCostBudgetUpTo maxBudget :=
      (table.runEncodedCostThresholdSearch_eq_none_iff
        maxBudget).mp
        hNone

    exact
      hNotAccepted
        ((table.hasAcceptedCostBudgetUpTo_iff_terminalDecision
          maxBudget).mpr
          hTerminal)

  · intro hTerminal

    apply
      (table.runEncodedCostThresholdSearch_eq_none_iff
        maxBudget).mpr

    intro hAccepted

    exact
      hTerminal
        ((table.hasAcceptedCostBudgetUpTo_iff_terminalDecision
          maxBudget).mp
          hAccepted)

/-- Acceptance of the terminal ordinary-cost budget produces an actual
successful total-search result. -/
theorem runEncodedCostThresholdSearch_exists_of_terminal_accepted
    (maxBudget : Nat)
    (hTerminal :
      table.costFeasibleDecision maxBudget = true) :
    ∃ success :
        table.CorrectedConcreteEncodedCostSearchSuccess
          maxBudget,
      table.runEncodedCostThresholdSearch maxBudget =
        some success := by

  classical

  let hAccepted :
      table.HasAcceptedCostBudgetUpTo maxBudget :=
    (table.hasAcceptedCostBudgetUpTo_iff_terminalDecision
      maxBudget).mpr
      hTerminal

  let success :
      table.CorrectedConcreteEncodedCostSearchSuccess
        maxBudget :=
    { accepted := hAccepted
      search :=
        table.selectedEncodedCostThresholdSearch
          maxBudget
          hAccepted }

  refine ⟨success, ?_⟩

  simp [runEncodedCostThresholdSearch, hAccepted, success]

/-- Every successful ordinary-cost total-search value carries the complete
threshold interval and the checked canonical dense certificate. -/
theorem runEncodedCostThresholdSearch_success_package
    (maxBudget : Nat)
    (success :
      table.CorrectedConcreteEncodedCostSearchSuccess
        maxBudget) :
    success.search.acceptedBudgets =
        Finset.Icc
          success.search.threshold.output.budget
          maxBudget ∧
      success.search.threshold.output.budget ∈
        success.search.acceptedBudgets ∧
      (∀ budget : Nat,
        budget ∈ success.search.acceptedBudgets →
          success.search.threshold.output.budget <= budget) ∧
      success.search.threshold.output.code < 2 ^ U.card ∧
      correctedConcreteDenseCertificateDecode
            U
            success.search.threshold.output.code =
        some success.search.threshold.output.certificate ∧
      table.verifiesCostCertificate
            success.search.threshold.output.budget
            success.search.threshold.output.certificate =
        true := by

  exact
    ⟨table.selectedEncodedCostThresholdSearch_eq_Icc
        maxBudget
        success.accepted,
      success.search.selected_mem,
      success.search.selected_le,
      success.search.threshold.output.code_lt,
      success.search.threshold.output.decode_eq,
      success.search.threshold.output.certificate_verifies⟩

end TotalEncodedCostSearch


section TotalEncodedParetoScalarSearch

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

/-- Successful output of the total encoded Pareto-scalar search. -/
structure CorrectedConcreteEncodedParetoScalarSearchSuccess
    (maxBudget : Nat) where

  accepted :
    table.HasAcceptedParetoScalarBudgetUpTo maxBudget

  search :
    table.CorrectedConcreteEncodedParetoScalarThresholdSearch
      maxBudget
      accepted

/-- Total optional Pareto-scalar optimization search. -/
noncomputable def runEncodedParetoScalarThresholdSearch
    (maxBudget : Nat) :
    Option
      (table.CorrectedConcreteEncodedParetoScalarSearchSuccess
        maxBudget) := by

  classical

  by_cases hAccepted :
      table.HasAcceptedParetoScalarBudgetUpTo maxBudget

  · exact
      some
        { accepted := hAccepted
          search :=
            table.selectedEncodedParetoScalarThresholdSearch
              maxBudget
              hAccepted }

  · exact none

/-- The total Pareto-scalar search returns `none` exactly when no bounded
accepted scalar budget exists. -/
theorem runEncodedParetoScalarThresholdSearch_eq_none_iff
    (maxBudget : Nat) :
    table.runEncodedParetoScalarThresholdSearch maxBudget = none ↔
      ¬ table.HasAcceptedParetoScalarBudgetUpTo maxBudget := by

  classical

  by_cases hAccepted :
      table.HasAcceptedParetoScalarBudgetUpTo maxBudget

  · simp [runEncodedParetoScalarThresholdSearch, hAccepted]

  · simp [runEncodedParetoScalarThresholdSearch, hAccepted]

/-- Failure of the total Pareto-scalar search is exactly rejection of the
terminal scalar budget. -/
theorem
    runEncodedParetoScalarThresholdSearch_eq_none_iff_terminal_rejected
    (maxBudget : Nat) :
    table.runEncodedParetoScalarThresholdSearch maxBudget = none ↔
      table.paretoScalarFeasibleDecision maxBudget ≠ true := by

  constructor

  · intro hNone hTerminal

    have hNotAccepted :
        ¬ table.HasAcceptedParetoScalarBudgetUpTo maxBudget :=
      (table.runEncodedParetoScalarThresholdSearch_eq_none_iff
        maxBudget).mp
        hNone

    exact
      hNotAccepted
        ((table.hasAcceptedParetoScalarBudgetUpTo_iff_terminalDecision
          maxBudget).mpr
          hTerminal)

  · intro hTerminal

    apply
      (table.runEncodedParetoScalarThresholdSearch_eq_none_iff
        maxBudget).mpr

    intro hAccepted

    exact
      hTerminal
        ((table.hasAcceptedParetoScalarBudgetUpTo_iff_terminalDecision
          maxBudget).mp
          hAccepted)

/-- Acceptance of the terminal Pareto-scalar budget produces an actual
successful total-search result. -/
theorem
    runEncodedParetoScalarThresholdSearch_exists_of_terminal_accepted
    (maxBudget : Nat)
    (hTerminal :
      table.paretoScalarFeasibleDecision maxBudget = true) :
    ∃ success :
        table.CorrectedConcreteEncodedParetoScalarSearchSuccess
          maxBudget,
      table.runEncodedParetoScalarThresholdSearch maxBudget =
        some success := by

  classical

  let hAccepted :
      table.HasAcceptedParetoScalarBudgetUpTo maxBudget :=
    (table.hasAcceptedParetoScalarBudgetUpTo_iff_terminalDecision
      maxBudget).mpr
      hTerminal

  let success :
      table.CorrectedConcreteEncodedParetoScalarSearchSuccess
        maxBudget :=
    { accepted := hAccepted
      search :=
        table.selectedEncodedParetoScalarThresholdSearch
          maxBudget
          hAccepted }

  refine ⟨success, ?_⟩

  simp [runEncodedParetoScalarThresholdSearch, hAccepted, success]

/-- Every successful Pareto-scalar total-search value carries the complete
threshold interval, Pareto optimality, and its checked canonical dense
certificate. -/
theorem runEncodedParetoScalarThresholdSearch_success_package
    (maxBudget : Nat)
    (success :
      table.CorrectedConcreteEncodedParetoScalarSearchSuccess
        maxBudget) :
    success.search.acceptedBudgets =
        Finset.Icc
          success.search.threshold.output.budget
          maxBudget ∧
      success.search.threshold.output.budget ∈
        success.search.acceptedBudgets ∧
      (∀ budget : Nat,
        budget ∈ success.search.acceptedBudgets →
          success.search.threshold.output.budget <= budget) ∧
      CorrectedConcreteObservationSelectionParetoOptimal
        (z := z)
        obsFamily
        f
        selectionCost
        U
        language
        success.search.threshold.output.certificate ∧
      success.search.threshold.output.code < 2 ^ U.card ∧
      correctedConcreteDenseCertificateDecode
            U
            success.search.threshold.output.code =
        some success.search.threshold.output.certificate ∧
      table.verifiesParetoScalarCertificate
            success.search.threshold.output.budget
            success.search.threshold.output.certificate =
        true := by

  exact
    ⟨table.selectedEncodedParetoScalarThresholdSearch_eq_Icc
        maxBudget
        success.accepted,
      success.search.selected_mem,
      success.search.selected_le,
      success.search.threshold.output.pareto_optimal,
      success.search.threshold.output.code_lt,
      success.search.threshold.output.decode_eq,
      success.search.threshold.output.certificate_verifies⟩

end TotalEncodedParetoScalarSearch

end CorrectedConcreteObservationSelectionDecisionTable


section EncodedTotalSearchFinalPackage

variable {α : Type u}
variable {ι : Type v}
variable {M : Type w}
variable [DecidableEq ι]
variable [Monoid M]
variable (obsFamily : ι → α → M)
variable (f : Nat)
variable (coordinateWeight : ι → Nat)
variable (U : Finset ι)

/-- Final positive-additive total-search package.

At the ambient positive-additive budget, the optional Pareto-scalar search
returns a successful value whose least accepted budget is exactly the semantic
minimum positive-additive rank and whose certificate is the canonical checked
dense Pareto witness. -/
theorem
    correctedConcreteWorkingGrammar_observationSelectionEncodedTotalSearch_package
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
    ∃ success :
        table.CorrectedConcreteEncodedParetoScalarSearchSuccess
          maxBudget,
      table.runEncodedParetoScalarThresholdSearch maxBudget =
          some success ∧
        success.search.threshold.output.budget =
          ambientTargetObservationSelectionPositiveAdditiveMinimumCost
            (z := z)
            obsFamily
            f
            coordinateWeight
            U
            hTarget ∧
        success.search.acceptedBudgets =
          Finset.Icc
            (ambientTargetObservationSelectionPositiveAdditiveMinimumCost
              (z := z)
              obsFamily
              f
              coordinateWeight
              U
              hTarget)
            maxBudget ∧
        CorrectedConcreteObservationSelectionParetoOptimal
          (z := z)
          obsFamily
          f
          (correctedConcreteObservationSelectionAdditiveCost
            coordinateWeight)
          U
          language
          success.search.threshold.output.certificate ∧
        success.search.threshold.output.code < 2 ^ U.card ∧
        correctedConcreteDenseCertificateDecode
              U
              success.search.threshold.output.code =
          some success.search.threshold.output.certificate := by

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

  let hAccepted :
      table.HasAcceptedParetoScalarBudgetUpTo maxBudget :=
    table.hasAcceptedParetoScalarBudgetUpTo_of_positiveAdditiveMinimum_le
      hTarget
      maxBudget
      hBound

  let success :
      table.CorrectedConcreteEncodedParetoScalarSearchSuccess
        maxBudget :=
    { accepted := hAccepted
      search :=
        table.selectedEncodedParetoScalarThresholdSearch
          maxBudget
          hAccepted }

  refine ⟨success, ?_, ?_, ?_, ?_, ?_, ?_⟩

  · simp [CorrectedConcreteObservationSelectionDecisionTable.runEncodedParetoScalarThresholdSearch,
      hAccepted,
      success]

  · exact
      (correctedConcreteWorkingGrammar_observationSelectionEncodedThresholdSearch_package
        (z := z)
        obsFamily
        f
        coordinateWeight
        U
        language
        hTarget).1

  · exact
      (correctedConcreteWorkingGrammar_observationSelectionEncodedThresholdSearch_package
        (z := z)
        obsFamily
        f
        coordinateWeight
        U
        language
        hTarget).2.1

  · exact success.search.threshold.output.pareto_optimal

  · exact success.search.threshold.output.code_lt

  · exact success.search.threshold.output.decode_eq

end EncodedTotalSearchFinalPackage

end MCFG
