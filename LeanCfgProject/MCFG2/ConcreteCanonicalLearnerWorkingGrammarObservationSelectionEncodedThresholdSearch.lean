/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG2.ConcreteCanonicalLearnerWorkingGrammarObservationSelectionEncodedDecisionThreshold

/-!
# ConcreteCanonicalLearnerWorkingGrammarObservationSelectionEncodedThresholdSearch.lean

The preceding file identifies the selected encoded budget as the exact Boolean
decision threshold.  This file packages the complete bounded Boolean search,
its least accepted budget, and its canonical encoded certificate into one
finite-search result.

For every ceiling `maxBudget`, the search explicitly retains the accepted
budgets in `0, ..., maxBudget`.  Whenever the terminal budget is accepted, the
result stores:

```text
the complete finite accepted-budget set;
the selected least accepted budget;
the certified encoded threshold output;
proof that the selected budget belongs to the search;
proof that it is below every searched accepted budget;
proof that the search is exactly the interval
  [selectedBudget, maxBudget].
```

Ordinary-cost and Pareto-scalar versions are provided.  The final
positive-additive package identifies the selected search value with the
semantic minimum positive-additive observation-selection rank.

This remains a finite-table search theorem.  It does not claim polynomial-time
construction of the semantic feasibility table, and it makes no NP-hardness or
NP-completeness claim.

No target grammar is supplied to any learner.
No `sorry`, `admit`, or `axiom` is used.
-/

namespace MCFG

universe u v w z

namespace CorrectedConcreteObservationSelectionDecisionTable

section EncodedCostThresholdSearch

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

/-- Complete bounded ordinary-cost threshold search together with its certified
least accepted encoded output. -/
structure CorrectedConcreteEncodedCostThresholdSearch
    (maxBudget : Nat)
    (hAccepted :
      table.HasAcceptedCostBudgetUpTo maxBudget) where

  acceptedBudgets : Finset Nat

  threshold :
    table.CorrectedConcreteEncodedMinimumCostDecisionThreshold
      maxBudget

  acceptedBudgets_eq :
    acceptedBudgets =
      table.acceptedCostBudgets maxBudget

  selected_mem :
    threshold.output.budget ∈ acceptedBudgets

  selected_le :
    ∀ budget : Nat,
      budget ∈ acceptedBudgets →
        threshold.output.budget <= budget

  mem_iff_interval :
    ∀ budget : Nat,
      budget ∈ acceptedBudgets ↔
        threshold.output.budget <= budget ∧
          budget <= maxBudget

/-- Construct the complete bounded ordinary-cost threshold search. -/
noncomputable def selectedEncodedCostThresholdSearch
    (maxBudget : Nat)
    (hAccepted :
      table.HasAcceptedCostBudgetUpTo maxBudget) :
    table.CorrectedConcreteEncodedCostThresholdSearch
      maxBudget
      hAccepted := by

  let threshold :=
    table.selectedEncodedMinimumCostDecisionThreshold
      maxBudget
      hAccepted

  refine
    { acceptedBudgets :=
        table.acceptedCostBudgets maxBudget
      threshold := threshold
      acceptedBudgets_eq := rfl
      selected_mem := ?_
      selected_le := ?_
      mem_iff_interval := ?_ }

  · exact
      (table.mem_acceptedCostBudgets_iff
        maxBudget
        threshold.output.budget).mpr
        ⟨threshold.output.budget_le_max,
          threshold.output.budget_decision⟩

  · intro budget hBudget

    rcases
        (table.mem_acceptedCostBudgets_iff
          maxBudget
          budget).mp
          hBudget with
      ⟨hBudgetLe, hDecision⟩

    exact
      threshold.output.budget_minimal
        budget
        hBudgetLe
        hDecision

  · intro budget

    rw [table.mem_acceptedCostBudgets_iff]
    rw [threshold.decision_exact]

    constructor

    · rintro ⟨hUpper, hLower⟩
      exact ⟨hLower, hUpper⟩

    · rintro ⟨hLower, hUpper⟩
      exact ⟨hUpper, hLower⟩

/-- The complete accepted ordinary-cost search is exactly the finite interval
from the selected threshold to the search ceiling. -/
theorem selectedEncodedCostThresholdSearch_eq_Icc
    (maxBudget : Nat)
    (hAccepted :
      table.HasAcceptedCostBudgetUpTo maxBudget) :
    let search :=
      table.selectedEncodedCostThresholdSearch
        maxBudget
        hAccepted
    search.acceptedBudgets =
      Finset.Icc
        search.threshold.output.budget
        maxBudget := by

  let search :=
    table.selectedEncodedCostThresholdSearch
      maxBudget
      hAccepted

  ext budget

  rw [search.mem_iff_interval]

  simp only [Finset.mem_Icc]

/-- The selected threshold is the unique least member of the complete bounded
ordinary-cost search. -/
theorem selectedEncodedCostThresholdSearch_least
    (maxBudget : Nat)
    (hAccepted :
      table.HasAcceptedCostBudgetUpTo maxBudget) :
    let search :=
      table.selectedEncodedCostThresholdSearch
        maxBudget
        hAccepted
    search.threshold.output.budget ∈
        search.acceptedBudgets ∧
      ∀ budget : Nat,
        budget ∈ search.acceptedBudgets →
          search.threshold.output.budget <= budget := by

  let search :=
    table.selectedEncodedCostThresholdSearch
      maxBudget
      hAccepted

  exact
    ⟨search.selected_mem,
      search.selected_le⟩

/-- Complete proof-carrying ordinary-cost finite-search package. -/
theorem selectedEncodedCostThresholdSearch_package
    (maxBudget : Nat)
    (hAccepted :
      table.HasAcceptedCostBudgetUpTo maxBudget) :
    let search :=
      table.selectedEncodedCostThresholdSearch
        maxBudget
        hAccepted
    search.acceptedBudgets =
        table.acceptedCostBudgets maxBudget ∧
      search.acceptedBudgets =
        Finset.Icc
          search.threshold.output.budget
          maxBudget ∧
      search.threshold.output.budget ∈
        search.acceptedBudgets ∧
      (∀ budget : Nat,
        budget ∈ search.acceptedBudgets →
          search.threshold.output.budget <= budget) ∧
      search.threshold.output.code < 2 ^ U.card ∧
      correctedConcreteDenseCertificateDecode
            U
            search.threshold.output.code =
        some search.threshold.output.certificate ∧
      table.verifiesCostCertificate
            search.threshold.output.budget
            search.threshold.output.certificate =
        true := by

  let search :=
    table.selectedEncodedCostThresholdSearch
      maxBudget
      hAccepted

  exact
    ⟨search.acceptedBudgets_eq,
      table.selectedEncodedCostThresholdSearch_eq_Icc
        maxBudget
        hAccepted,
      search.selected_mem,
      search.selected_le,
      search.threshold.output.code_lt,
      search.threshold.output.decode_eq,
      search.threshold.output.certificate_verifies⟩

end EncodedCostThresholdSearch


section EncodedParetoScalarThresholdSearch

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

/-- Complete bounded Pareto-scalar threshold search together with its certified
least accepted encoded output. -/
structure CorrectedConcreteEncodedParetoScalarThresholdSearch
    (maxBudget : Nat)
    (hAccepted :
      table.HasAcceptedParetoScalarBudgetUpTo maxBudget) where

  acceptedBudgets : Finset Nat

  threshold :
    table.CorrectedConcreteEncodedMinimumParetoScalarDecisionThreshold
      maxBudget

  acceptedBudgets_eq :
    acceptedBudgets =
      table.acceptedParetoScalarBudgets maxBudget

  selected_mem :
    threshold.output.budget ∈ acceptedBudgets

  selected_le :
    ∀ budget : Nat,
      budget ∈ acceptedBudgets →
        threshold.output.budget <= budget

  mem_iff_interval :
    ∀ budget : Nat,
      budget ∈ acceptedBudgets ↔
        threshold.output.budget <= budget ∧
          budget <= maxBudget

/-- Construct the complete bounded Pareto-scalar threshold search. -/
noncomputable def selectedEncodedParetoScalarThresholdSearch
    (maxBudget : Nat)
    (hAccepted :
      table.HasAcceptedParetoScalarBudgetUpTo maxBudget) :
    table.CorrectedConcreteEncodedParetoScalarThresholdSearch
      maxBudget
      hAccepted := by

  let threshold :=
    table.selectedEncodedMinimumParetoScalarDecisionThreshold
      maxBudget
      hAccepted

  refine
    { acceptedBudgets :=
        table.acceptedParetoScalarBudgets maxBudget
      threshold := threshold
      acceptedBudgets_eq := rfl
      selected_mem := ?_
      selected_le := ?_
      mem_iff_interval := ?_ }

  · exact
      (table.mem_acceptedParetoScalarBudgets_iff
        maxBudget
        threshold.output.budget).mpr
        ⟨threshold.output.budget_le_max,
          threshold.output.budget_decision⟩

  · intro budget hBudget

    rcases
        (table.mem_acceptedParetoScalarBudgets_iff
          maxBudget
          budget).mp
          hBudget with
      ⟨hBudgetLe, hDecision⟩

    exact
      threshold.output.budget_minimal
        budget
        hBudgetLe
        hDecision

  · intro budget

    rw [table.mem_acceptedParetoScalarBudgets_iff]
    rw [threshold.decision_exact]

    constructor

    · rintro ⟨hUpper, hLower⟩
      exact ⟨hLower, hUpper⟩

    · rintro ⟨hLower, hUpper⟩
      exact ⟨hUpper, hLower⟩

/-- The complete accepted Pareto-scalar search is exactly the finite interval
from the selected threshold to the search ceiling. -/
theorem selectedEncodedParetoScalarThresholdSearch_eq_Icc
    (maxBudget : Nat)
    (hAccepted :
      table.HasAcceptedParetoScalarBudgetUpTo maxBudget) :
    let search :=
      table.selectedEncodedParetoScalarThresholdSearch
        maxBudget
        hAccepted
    search.acceptedBudgets =
      Finset.Icc
        search.threshold.output.budget
        maxBudget := by

  let search :=
    table.selectedEncodedParetoScalarThresholdSearch
      maxBudget
      hAccepted

  ext budget

  rw [search.mem_iff_interval]

  simp only [Finset.mem_Icc]

/-- The selected threshold is the unique least member of the complete bounded
Pareto-scalar search. -/
theorem selectedEncodedParetoScalarThresholdSearch_least
    (maxBudget : Nat)
    (hAccepted :
      table.HasAcceptedParetoScalarBudgetUpTo maxBudget) :
    let search :=
      table.selectedEncodedParetoScalarThresholdSearch
        maxBudget
        hAccepted
    search.threshold.output.budget ∈
        search.acceptedBudgets ∧
      ∀ budget : Nat,
        budget ∈ search.acceptedBudgets →
          search.threshold.output.budget <= budget := by

  let search :=
    table.selectedEncodedParetoScalarThresholdSearch
      maxBudget
      hAccepted

  exact
    ⟨search.selected_mem,
      search.selected_le⟩

/-- Complete proof-carrying Pareto-scalar finite-search package. -/
theorem selectedEncodedParetoScalarThresholdSearch_package
    (maxBudget : Nat)
    (hAccepted :
      table.HasAcceptedParetoScalarBudgetUpTo maxBudget) :
    let search :=
      table.selectedEncodedParetoScalarThresholdSearch
        maxBudget
        hAccepted
    search.acceptedBudgets =
        table.acceptedParetoScalarBudgets maxBudget ∧
      search.acceptedBudgets =
        Finset.Icc
          search.threshold.output.budget
          maxBudget ∧
      search.threshold.output.budget ∈
        search.acceptedBudgets ∧
      (∀ budget : Nat,
        budget ∈ search.acceptedBudgets →
          search.threshold.output.budget <= budget) ∧
      CorrectedConcreteObservationSelectionParetoOptimal
        (z := z)
        obsFamily
        f
        selectionCost
        U
        language
        search.threshold.output.certificate ∧
      search.threshold.output.code < 2 ^ U.card ∧
      correctedConcreteDenseCertificateDecode
            U
            search.threshold.output.code =
        some search.threshold.output.certificate ∧
      table.verifiesParetoScalarCertificate
            search.threshold.output.budget
            search.threshold.output.certificate =
        true := by

  let search :=
    table.selectedEncodedParetoScalarThresholdSearch
      maxBudget
      hAccepted

  exact
    ⟨search.acceptedBudgets_eq,
      table.selectedEncodedParetoScalarThresholdSearch_eq_Icc
        maxBudget
        hAccepted,
      search.selected_mem,
      search.selected_le,
      search.threshold.output.pareto_optimal,
      search.threshold.output.code_lt,
      search.threshold.output.decode_eq,
      search.threshold.output.certificate_verifies⟩

end EncodedParetoScalarThresholdSearch

end CorrectedConcreteObservationSelectionDecisionTable


section EncodedThresholdSearchFinalPackage

variable {α : Type u}
variable {ι : Type v}
variable {M : Type w}
variable [DecidableEq ι]
variable [Monoid M]
variable (obsFamily : ι → α → M)
variable (f : Nat)
variable (coordinateWeight : ι → Nat)
variable (U : Finset ι)

/-- Final positive-additive bounded-search package.

The complete accepted Pareto-scalar budget search is exactly the interval from
the semantic minimum positive-additive rank to the ambient search ceiling.  Its
least member carries the canonical dense Pareto certificate. -/
theorem
    correctedConcreteWorkingGrammar_observationSelectionEncodedThresholdSearch_package
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
    let search :=
      table.selectedEncodedParetoScalarThresholdSearch
        maxBudget
        hAccepted
    search.threshold.output.budget =
        ambientTargetObservationSelectionPositiveAdditiveMinimumCost
          (z := z)
          obsFamily
          f
          coordinateWeight
          U
          hTarget ∧
      search.acceptedBudgets =
        Finset.Icc
          (ambientTargetObservationSelectionPositiveAdditiveMinimumCost
            (z := z)
            obsFamily
            f
            coordinateWeight
            U
            hTarget)
          maxBudget ∧
      search.threshold.output.budget ∈
        search.acceptedBudgets ∧
      CorrectedConcreteObservationSelectionParetoOptimal
        (z := z)
        obsFamily
        f
        (correctedConcreteObservationSelectionAdditiveCost
          coordinateWeight)
        U
        language
        search.threshold.output.certificate ∧
      search.threshold.output.code < 2 ^ U.card ∧
      correctedConcreteDenseCertificateDecode
            U
            search.threshold.output.code =
        some search.threshold.output.certificate := by

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

  let search :=
    table.selectedEncodedParetoScalarThresholdSearch
      maxBudget
      hAccepted

  have hThreshold :=
    correctedConcreteWorkingGrammar_observationSelectionEncodedDecisionThreshold_package
      (z := z)
      obsFamily
      f
      coordinateWeight
      U
      language
      hTarget

  have hBudgetEq :
      search.threshold.output.budget =
        ambientTargetObservationSelectionPositiveAdditiveMinimumCost
          (z := z)
          obsFamily
          f
          coordinateWeight
          U
          hTarget := by

    exact hThreshold.1

  have hSearchInterval :
      search.acceptedBudgets =
        Finset.Icc
          search.threshold.output.budget
          maxBudget :=
    table.selectedEncodedParetoScalarThresholdSearch_eq_Icc
      maxBudget
      hAccepted

  have hSearchSemantic :
      search.acceptedBudgets =
        Finset.Icc
          (ambientTargetObservationSelectionPositiveAdditiveMinimumCost
            (z := z)
            obsFamily
            f
            coordinateWeight
            U
            hTarget)
          maxBudget := by

    rw [hSearchInterval, hBudgetEq]

  exact
    ⟨hBudgetEq,
      hSearchSemantic,
      search.selected_mem,
      search.threshold.output.pareto_optimal,
      search.threshold.output.code_lt,
      search.threshold.output.decode_eq⟩

end EncodedThresholdSearchFinalPackage

end MCFG
