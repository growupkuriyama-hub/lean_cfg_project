/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG2.ConcreteCanonicalLearnerWorkingGrammarObservationSelectionEncodedTotalSearch

/-!
# ConcreteCanonicalLearnerWorkingGrammarObservationSelectionEncodedDecisionOptimization.lean

This file gives a unified decision/optimization interface for the total encoded
observation-selection searches.

For an arbitrary correct finite decision table, it proves that existence of a
successful total-search output is exactly the terminal Boolean decision:

```text
some encoded cost optimization output exists
  iff costFeasibleDecision maxBudget = true;

some encoded Pareto-scalar optimization output exists
  iff paretoScalarFeasibleDecision maxBudget = true.
```

For the semantic positive-additive table, the ordinary-cost and Pareto-scalar
procedures are then compared directly.  At every budget they succeed or fail
together.  At the ambient full-interface ceiling they both succeed, return the
same semantic minimum rank, and enumerate the same accepted-budget interval.
The two canonical certificates need not be equal: the Pareto procedure carries
the stronger Pareto-optimality specification.

This remains a finite-table theorem.  It does not construct the semantic table
in polynomial time, and it makes no NP-hardness or NP-completeness claim.

No target grammar is supplied to any learner.
No `sorry`, `admit`, or `axiom` is used.
-/

namespace MCFG

universe u v w z

namespace CorrectedConcreteObservationSelectionDecisionTable

section GeneralDecisionOptimizationInterface

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

/-- Existence of a successful total ordinary-cost optimization output is
exactly the terminal ordinary-cost Boolean decision. -/
theorem runEncodedCostThresholdSearch_exists_iff_terminal_accepted
    (maxBudget : Nat) :
    (∃ success :
        table.CorrectedConcreteEncodedCostSearchSuccess
          maxBudget,
      table.runEncodedCostThresholdSearch maxBudget =
        some success) ↔
      table.costFeasibleDecision maxBudget = true := by

  constructor

  · rintro ⟨success, hRun⟩

    by_contra hRejected

    have hNone :
        table.runEncodedCostThresholdSearch maxBudget = none :=
      (table.runEncodedCostThresholdSearch_eq_none_iff_terminal_rejected
        maxBudget).mpr
        hRejected

    rw [hNone] at hRun

    cases hRun

  · intro hAccepted

    exact
      table.runEncodedCostThresholdSearch_exists_of_terminal_accepted
        maxBudget
        hAccepted

/-- Existence of a successful total Pareto-scalar optimization output is
exactly the terminal Pareto-scalar Boolean decision. -/
theorem
    runEncodedParetoScalarThresholdSearch_exists_iff_terminal_accepted
    (maxBudget : Nat) :
    (∃ success :
        table.CorrectedConcreteEncodedParetoScalarSearchSuccess
          maxBudget,
      table.runEncodedParetoScalarThresholdSearch maxBudget =
        some success) ↔
      table.paretoScalarFeasibleDecision maxBudget = true := by

  constructor

  · rintro ⟨success, hRun⟩

    by_contra hRejected

    have hNone :
        table.runEncodedParetoScalarThresholdSearch maxBudget = none :=
      (table.runEncodedParetoScalarThresholdSearch_eq_none_iff_terminal_rejected
        maxBudget).mpr
        hRejected

    rw [hNone] at hRun

    cases hRun

  · intro hAccepted

    exact
      table.runEncodedParetoScalarThresholdSearch_exists_of_terminal_accepted
        maxBudget
        hAccepted

/-- The total ordinary-cost search has exactly one of the two externally
observable outcomes: rejection at the terminal budget, or a successful
certified optimization output. -/
theorem runEncodedCostThresholdSearch_dichotomy
    (maxBudget : Nat) :
    (table.runEncodedCostThresholdSearch maxBudget = none ∧
      table.costFeasibleDecision maxBudget ≠ true) ∨
      ∃ success :
          table.CorrectedConcreteEncodedCostSearchSuccess
            maxBudget,
        table.runEncodedCostThresholdSearch maxBudget =
            some success ∧
          table.costFeasibleDecision maxBudget = true := by

  by_cases hDecision :
      table.costFeasibleDecision maxBudget = true

  · right

    rcases
        table.runEncodedCostThresholdSearch_exists_of_terminal_accepted
          maxBudget
          hDecision with
      ⟨success, hRun⟩

    exact
      ⟨success, hRun, hDecision⟩

  · left

    exact
      ⟨(table.runEncodedCostThresholdSearch_eq_none_iff_terminal_rejected
          maxBudget).mpr
          hDecision,
        hDecision⟩

/-- Pareto-scalar counterpart of the total decision/optimization dichotomy. -/
theorem runEncodedParetoScalarThresholdSearch_dichotomy
    (maxBudget : Nat) :
    (table.runEncodedParetoScalarThresholdSearch maxBudget = none ∧
      table.paretoScalarFeasibleDecision maxBudget ≠ true) ∨
      ∃ success :
          table.CorrectedConcreteEncodedParetoScalarSearchSuccess
            maxBudget,
        table.runEncodedParetoScalarThresholdSearch maxBudget =
            some success ∧
          table.paretoScalarFeasibleDecision maxBudget = true := by

  by_cases hDecision :
      table.paretoScalarFeasibleDecision maxBudget = true

  · right

    rcases
        table.runEncodedParetoScalarThresholdSearch_exists_of_terminal_accepted
          maxBudget
          hDecision with
      ⟨success, hRun⟩

    exact
      ⟨success, hRun, hDecision⟩

  · left

    exact
      ⟨(table.runEncodedParetoScalarThresholdSearch_eq_none_iff_terminal_rejected
          maxBudget).mpr
          hDecision,
        hDecision⟩

end GeneralDecisionOptimizationInterface


section PositiveAdditiveDecisionOptimizationAgreement

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

/-- At every ceiling, ordinary positive-additive cost search succeeds exactly
when Pareto-scalar search succeeds. -/
theorem positiveAdditive_totalSearch_success_equivalence
    (maxBudget : Nat) :
    (∃ costSuccess :
        table.CorrectedConcreteEncodedCostSearchSuccess
          maxBudget,
      table.runEncodedCostThresholdSearch maxBudget =
        some costSuccess) ↔
      ∃ paretoSuccess :
        table.CorrectedConcreteEncodedParetoScalarSearchSuccess
          maxBudget,
      table.runEncodedParetoScalarThresholdSearch maxBudget =
        some paretoSuccess := by

  rw [
    table.runEncodedCostThresholdSearch_exists_iff_terminal_accepted,
    table.runEncodedParetoScalarThresholdSearch_exists_iff_terminal_accepted
  ]

  let hDecision :=
    table.positiveAdditiveDecision_equivalence_package
      hTarget
      maxBudget

  exact
    hDecision.1.trans
      hDecision.2.1

/-- At every ceiling, ordinary positive-additive cost search returns `none`
exactly when Pareto-scalar search returns `none`. -/
theorem positiveAdditive_totalSearch_none_equivalence
    (maxBudget : Nat) :
    table.runEncodedCostThresholdSearch maxBudget = none ↔
      table.runEncodedParetoScalarThresholdSearch maxBudget = none := by

  rw [
    table.runEncodedCostThresholdSearch_eq_none_iff_terminal_rejected,
    table.runEncodedParetoScalarThresholdSearch_eq_none_iff_terminal_rejected
  ]

  let hDecision :=
    table.positiveAdditiveDecision_equivalence_package
      hTarget
      maxBudget

  let hCostPareto :
      table.costFeasibleDecision maxBudget = true ↔
        table.paretoScalarFeasibleDecision maxBudget = true :=
    hDecision.1.trans
      hDecision.2.1

  constructor

  · intro hCostRejected hParetoAccepted

    exact
      hCostRejected
        (hCostPareto.mpr hParetoAccepted)

  · intro hParetoRejected hCostAccepted

    exact
      hParetoRejected
        (hCostPareto.mp hCostAccepted)

/-- If successful outputs are supplied for both positive-additive procedures
at the same ceiling, their selected minimum budgets are equal. -/
theorem positiveAdditive_success_budget_eq
    (maxBudget : Nat)
    (costSuccess :
      table.CorrectedConcreteEncodedCostSearchSuccess
        maxBudget)
    (paretoSuccess :
      table.CorrectedConcreteEncodedParetoScalarSearchSuccess
        maxBudget) :
    costSuccess.search.threshold.output.budget =
      paretoSuccess.search.threshold.output.budget := by

  have hCostEq :
      costSuccess.search.threshold.output.budget =
        ambientTargetObservationSelectionPositiveAdditiveMinimumCost
          (z := z)
          obsFamily
          f
          coordinateWeight
          U
          hTarget := by

    change
      table.selectedMinimumAcceptedCostBudget
            maxBudget
            costSuccess.accepted =
        ambientTargetObservationSelectionPositiveAdditiveMinimumCost
          (z := z)
          obsFamily
          f
          coordinateWeight
          U
          hTarget

    exact
      table.selectedMinimumAcceptedCostBudget_eq_positiveAdditiveMinimum
        hTarget
        maxBudget
        (by
          exact
            (table.positiveAdditiveDecision_equivalence_package
              hTarget
              maxBudget).2.2.mp
              ((table.hasAcceptedCostBudgetUpTo_iff_terminalDecision
                maxBudget).mp
                costSuccess.accepted))

  have hParetoEq :
      paretoSuccess.search.threshold.output.budget =
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
            paretoSuccess.accepted =
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
        ((table.positiveAdditiveParetoScalarDecision_eq_true_iff_minimumRank_le
          hTarget
          maxBudget).mp
          ((table.hasAcceptedParetoScalarBudgetUpTo_iff_terminalDecision
            maxBudget).mp
            paretoSuccess.accepted))

  exact hCostEq.trans hParetoEq.symm

/-- Successful ordinary-cost and Pareto-scalar searches enumerate the same
accepted-budget interval. -/
theorem positiveAdditive_success_acceptedBudgets_eq
    (maxBudget : Nat)
    (costSuccess :
      table.CorrectedConcreteEncodedCostSearchSuccess
        maxBudget)
    (paretoSuccess :
      table.CorrectedConcreteEncodedParetoScalarSearchSuccess
        maxBudget) :
    costSuccess.search.acceptedBudgets =
      paretoSuccess.search.acceptedBudgets := by

  calc
    costSuccess.search.acceptedBudgets =
        Finset.Icc
          costSuccess.search.threshold.output.budget
          maxBudget :=
      table.selectedEncodedCostThresholdSearch_eq_Icc
        maxBudget
        costSuccess.accepted

    _ =
        Finset.Icc
          paretoSuccess.search.threshold.output.budget
          maxBudget := by
      rw [
        table.positiveAdditive_success_budget_eq
          hTarget
          maxBudget
          costSuccess
          paretoSuccess
      ]

    _ =
        paretoSuccess.search.acceptedBudgets :=
      (table.selectedEncodedParetoScalarThresholdSearch_eq_Icc
        maxBudget
        paretoSuccess.accepted).symm

end PositiveAdditiveDecisionOptimizationAgreement

end CorrectedConcreteObservationSelectionDecisionTable


section EncodedDecisionOptimizationFinalPackage

variable {α : Type u}
variable {ι : Type v}
variable {M : Type w}
variable [DecidableEq ι]
variable [Monoid M]
variable (obsFamily : ι → α → M)
variable (f : Nat)
variable (coordinateWeight : ι → Nat)
variable (U : Finset ι)

/-- Final unified positive-additive decision/optimization package.

At the ambient full-interface budget, the ordinary-cost and Pareto-scalar total
searches both return successful certified outputs.  Their selected budgets are
the same semantic minimum rank and their complete accepted-budget sets agree.
The Pareto output additionally carries a checked Pareto-optimal canonical dense
certificate. -/
theorem
    correctedConcreteWorkingGrammar_observationSelectionEncodedDecisionOptimization_package
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
    ∃ costSuccess :
        table.CorrectedConcreteEncodedCostSearchSuccess
          maxBudget,
      ∃ paretoSuccess :
          table.CorrectedConcreteEncodedParetoScalarSearchSuccess
            maxBudget,
        table.runEncodedCostThresholdSearch maxBudget =
            some costSuccess ∧
          table.runEncodedParetoScalarThresholdSearch maxBudget =
            some paretoSuccess ∧
          costSuccess.search.threshold.output.budget =
            ambientTargetObservationSelectionPositiveAdditiveMinimumCost
              (z := z)
              obsFamily
              f
              coordinateWeight
              U
              hTarget ∧
          paretoSuccess.search.threshold.output.budget =
            ambientTargetObservationSelectionPositiveAdditiveMinimumCost
              (z := z)
              obsFamily
              f
              coordinateWeight
              U
              hTarget ∧
          costSuccess.search.acceptedBudgets =
            paretoSuccess.search.acceptedBudgets ∧
          table.verifiesCostCertificate
                costSuccess.search.threshold.output.budget
                costSuccess.search.threshold.output.certificate =
            true ∧
          CorrectedConcreteObservationSelectionParetoOptimal
            (z := z)
            obsFamily
            f
            (correctedConcreteObservationSelectionAdditiveCost
              coordinateWeight)
            U
            language
            paretoSuccess.search.threshold.output.certificate ∧
          paretoSuccess.search.threshold.output.code < 2 ^ U.card ∧
          correctedConcreteDenseCertificateDecode
                U
                paretoSuccess.search.threshold.output.code =
            some paretoSuccess.search.threshold.output.certificate := by

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

  let minimumCost :=
    ambientTargetObservationSelectionPositiveAdditiveMinimumCost
      (z := z)
      obsFamily
      f
      coordinateWeight
      U
      hTarget

  let hBound :
      minimumCost <= maxBudget :=
    ambientTargetObservationSelectionPositiveAdditiveMinimumCost_le
      (z := z)
      obsFamily
      f
      coordinateWeight
      U
      hTarget

  let hCostAccepted :
      table.HasAcceptedCostBudgetUpTo maxBudget :=
    table.hasAcceptedCostBudgetUpTo_of_positiveAdditiveMinimum_le
      hTarget
      maxBudget
      hBound

  let hParetoAccepted :
      table.HasAcceptedParetoScalarBudgetUpTo maxBudget :=
    table.hasAcceptedParetoScalarBudgetUpTo_of_positiveAdditiveMinimum_le
      hTarget
      maxBudget
      hBound

  let costSuccess :
      table.CorrectedConcreteEncodedCostSearchSuccess
        maxBudget :=
    { accepted := hCostAccepted
      search :=
        table.selectedEncodedCostThresholdSearch
          maxBudget
          hCostAccepted }

  let paretoSuccess :
      table.CorrectedConcreteEncodedParetoScalarSearchSuccess
        maxBudget :=
    { accepted := hParetoAccepted
      search :=
        table.selectedEncodedParetoScalarThresholdSearch
          maxBudget
          hParetoAccepted }

  refine
    ⟨costSuccess,
      paretoSuccess,
      ?_,
      ?_,
      ?_,
      ?_,
      ?_,
      ?_,
      ?_,
      ?_,
      ?_⟩

  · simp [
      CorrectedConcreteObservationSelectionDecisionTable.runEncodedCostThresholdSearch,
      hCostAccepted,
      costSuccess
    ]

  · simp [
      CorrectedConcreteObservationSelectionDecisionTable.runEncodedParetoScalarThresholdSearch,
      hParetoAccepted,
      paretoSuccess
    ]

  · change
      table.selectedMinimumAcceptedCostBudget
            maxBudget
            hCostAccepted =
        minimumCost

    exact
      table.selectedMinimumAcceptedCostBudget_eq_positiveAdditiveMinimum
        hTarget
        maxBudget
        hBound

  · change
      table.selectedMinimumAcceptedParetoScalarBudget
            maxBudget
            hParetoAccepted =
        minimumCost

    exact
      table.selectedMinimumAcceptedParetoScalarBudget_eq_positiveAdditiveMinimum
        hTarget
        maxBudget
        hBound

  · exact
      table.positiveAdditive_success_acceptedBudgets_eq
        hTarget
        maxBudget
        costSuccess
        paretoSuccess

  · exact
      costSuccess.search.threshold.output.certificate_verifies

  · exact
      paretoSuccess.search.threshold.output.pareto_optimal

  · exact
      paretoSuccess.search.threshold.output.code_lt

  · exact
      paretoSuccess.search.threshold.output.decode_eq

end EncodedDecisionOptimizationFinalPackage

end MCFG
