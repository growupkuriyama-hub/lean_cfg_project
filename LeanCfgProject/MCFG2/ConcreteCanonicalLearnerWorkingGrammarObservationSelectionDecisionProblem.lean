/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG.ConcreteCanonicalLearnerWorkingGrammarObservationSelectionParetoRankProfileOffsetGapSelectionFamily

/-!
# ConcreteCanonicalLearnerWorkingGrammarObservationSelectionDecisionProblem.lean

The preceding files construct the semantic finite observation-selection
optimization theory, including feasible, minimum-cost, Pareto, rank, profile,
and gap objects.

Those semantic finite searches are classical because their filters mention
membership in the semantic target class directly.

This file isolates that non-effective semantic predicate behind a finite
proof-carrying decision table.

## Finite decision table

For one fixed natural-valued selection cost, a decision table stores two finite
sets of ambient subsets:

* the feasible selected observation interfaces;
* the Pareto-optimal selected observation interfaces.

The computational data are ordinary `Finset` objects.  Correctness is supplied
separately by proofs identifying table membership with the existing semantic
notions.

Thus all decision functions below inspect only finite encoded table data, costs,
and natural-number bounds.  They do not call semantic target-class membership.

## Decision variants

The file defines Boolean questions:

```text
is there a feasible selection of cost at most b?
is there a Pareto selection of scalar value at most b?
is the minimum observation-selection rank at most b?
```

The first two are implemented by finite filtering and nonemptiness tests.  The
rank decision is the cost-feasibility decision viewed through the exact minimum-
cost threshold theorem.

For positive additive observation cost, the Pareto-scalar decision is proved
equivalent to the ambient positive-additive rank bound.  Hence the ordinary
budget decision, the minimum-rank decision, and the additive-Pareto-envelope
decision agree under a correct table.

## Canonical semantic table

A canonical cost-indexed table is constructed noncomputably from the already
verified semantic finite searches.  This proves that the interface is
satisfiable and recovers the previous theory exactly.

The point of the abstraction is that a later executable or complexity file may
supply the same table from an external finite encoding and prove only the table-
correctness interface.  The Boolean decision functions themselves then remain
unchanged.

## Boundary

This file does not yet provide a polynomial-time algorithm for constructing a
correct table from an arbitrary language or grammar encoding.  It establishes
the finite decision-problem interface and its semantic correctness, which is the
foundation needed for certificate verification and NP membership.

No target grammar is supplied to any learner.
No `sorry`, `admit`, or `axiom` is used.
-/

namespace MCFG

universe u v w z


section DecisionTableDefinition

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

/-- Finite proof-carrying table for observation-selection feasibility and
Pareto optimality under one fixed selection cost.

The two stored finsets are the computational input.  The correctness fields
connect them to the semantic target-class predicates. -/
structure CorrectedConcreteObservationSelectionDecisionTable where

  feasibleSelections :
    Finset (Finset ι)

  paretoSelections :
    Finset (Finset ι)

  feasible_correct :
    ∀ S : Finset ι,
      S ∈ feasibleSelections ↔
        S ⊆ U ∧
          language ∈
            StartRootedCorrectedConcreteTargetClass
              (v := z)
              α
              (↥S → M)
              (selectedObservationProduct obsFamily S)
              f

  pareto_correct :
    ∀ S : Finset ι,
      S ∈ paretoSelections ↔
        CorrectedConcreteObservationSelectionParetoOptimal
          (z := z)
          obsFamily
          f
          selectionCost
          U
          language
          S

end DecisionTableDefinition


namespace CorrectedConcreteObservationSelectionDecisionTable

section TableBasicProperties

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

/-- Every stored feasible selection is an ambient subset. -/
theorem feasible_subset_powerset :
    table.feasibleSelections ⊆ U.powerset := by

  intro S hS

  exact
    Finset.mem_powerset.mpr
      ((table.feasible_correct S).mp hS).1

/-- Every stored Pareto selection is semantically feasible. -/
theorem pareto_mem_feasible
    {S : Finset ι}
    (hS : S ∈ table.paretoSelections) :
    S ∈ table.feasibleSelections := by

  have hPareto :=
    (table.pareto_correct S).mp
      hS

  exact
    (table.feasible_correct S).mpr
      ⟨hPareto.1,
        hPareto.2.1⟩

/-- Every stored Pareto selection is an ambient subset. -/
theorem pareto_subset_powerset :
    table.paretoSelections ⊆ U.powerset := by

  intro S hS

  exact
    table.feasible_subset_powerset
      (table.pareto_mem_feasible hS)

/-- Both stored candidate families have the expected exhaustive powerset
cardinality bound. -/
theorem table_cardinality_package :
    table.feasibleSelections.card <= 2 ^ U.card ∧
      table.paretoSelections.card <= 2 ^ U.card := by

  constructor

  · calc
      table.feasibleSelections.card <=
          U.powerset.card :=
        Finset.card_le_card
          table.feasible_subset_powerset

      _ = 2 ^ U.card := by
        simpa using
          Finset.card_powerset U

  · calc
      table.paretoSelections.card <=
          U.powerset.card :=
        Finset.card_le_card
          table.pareto_subset_powerset

      _ = 2 ^ U.card := by
        simpa using
          Finset.card_powerset U

end TableBasicProperties


section EncodedBudgetCandidates

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

/-- Finite encoded feasible candidates whose selection cost is at most the
specified budget.  This definition inspects only the supplied finite table. -/
def costFeasibleSelections
    (costBudget : Nat) :
    Finset (Finset ι) :=
  table.feasibleSelections.filter
    (fun S => selectionCost S <= costBudget)

/-- Exact membership theorem for the table-based budget search. -/
theorem mem_costFeasibleSelections_iff
    (costBudget : Nat)
    {S : Finset ι} :
    S ∈ table.costFeasibleSelections costBudget ↔
      S ⊆ U ∧
        selectionCost S <= costBudget ∧
        language ∈
          StartRootedCorrectedConcreteTargetClass
            (v := z)
            α
            (↥S → M)
            (selectedObservationProduct obsFamily S)
            f := by

  constructor

  · intro hS

    rcases Finset.mem_filter.mp hS with
      ⟨hFeasible, hCost⟩

    rcases (table.feasible_correct S).mp hFeasible with
      ⟨hSU, hTarget⟩

    exact
      ⟨hSU,
        hCost,
        hTarget⟩

  · intro hS

    rcases hS with
      ⟨hSU, hCost, hTarget⟩

    exact
      Finset.mem_filter.mpr
        ⟨(table.feasible_correct S).mpr
            ⟨hSU, hTarget⟩,
          hCost⟩

/-- The table-based budget search is exactly the existing semantic finite
budget search. -/
theorem costFeasibleSelections_eq_semantic
    (costBudget : Nat) :
    table.costFeasibleSelections costBudget =
      correctedConcreteObservationCostFeasibleSelections
        (z := z)
        obsFamily
        f
        selectionCost
        U
        language
        costBudget := by

  ext S

  rw [
    table.mem_costFeasibleSelections_iff
      costBudget,
    mem_correctedConcreteObservationCostFeasibleSelections_iff
      (z := z)
      obsFamily
      f
      selectionCost
      U
      language
      costBudget
  ]

/-- Table-only Boolean budget-feasibility decision. -/
def costFeasibleDecision
    (costBudget : Nat) :
    Bool :=
  decide
    (table.costFeasibleSelections costBudget).Nonempty

/-- Correctness of the table-only budget-feasibility decision. -/
theorem costFeasibleDecision_eq_true_iff
    (costBudget : Nat) :
    table.costFeasibleDecision costBudget = true ↔
      CorrectedConcreteObservationSelectionAtCost
        (obsFamily := obsFamily)
        (f := f)
        selectionCost
        U
        language
        costBudget := by

  unfold costFeasibleDecision

  rw [decide_eq_true_eq]

  constructor

  · intro hNonempty

    rcases hNonempty with
      ⟨S, hS⟩

    rcases
        (table.mem_costFeasibleSelections_iff
          costBudget).mp
          hS with
      ⟨hSU, hCost, hTarget⟩

    exact
      ⟨S,
        hSU,
        hCost,
        hTarget⟩

  · intro hSelection

    rcases hSelection with
      ⟨S, hSU, hCost, hTarget⟩

    exact
      ⟨S,
        (table.mem_costFeasibleSelections_iff
          costBudget).mpr
          ⟨hSU, hCost, hTarget⟩⟩

/-- The Boolean budget decision is monotone in the budget. -/
theorem costFeasibleDecision_mono
    {costBudget costBudget' : Nat}
    (hBudget : costBudget <= costBudget')
    (hDecision :
      table.costFeasibleDecision costBudget = true) :
    table.costFeasibleDecision costBudget' = true := by

  apply
    (table.costFeasibleDecision_eq_true_iff
      costBudget').mpr

  exact
    correctedConcreteObservationSelectionAtCost_mono
      selectionCost
      hBudget
      ((table.costFeasibleDecision_eq_true_iff
        costBudget).mp
        hDecision)

end EncodedBudgetCandidates


section EncodedParetoCandidates

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

/-- Finite encoded Pareto candidates whose scalar profile value is at most the
specified budget.  This definition inspects only the stored Pareto finset. -/
def paretoScalarFeasibleSelections
    (scalarBudget : Nat) :
    Finset (Finset ι) :=
  table.paretoSelections.filter
    (fun S =>
      correctedConcreteObservationSelectionParetoScalarCost
          selectionCost S <=
        scalarBudget)

/-- Exact membership theorem for the encoded Pareto-scalar search. -/
theorem mem_paretoScalarFeasibleSelections_iff
    (scalarBudget : Nat)
    {S : Finset ι} :
    S ∈ table.paretoScalarFeasibleSelections scalarBudget ↔
      CorrectedConcreteObservationSelectionParetoOptimal
          (z := z)
          obsFamily
          f
          selectionCost
          U
          language
          S ∧
        correctedConcreteObservationSelectionParetoScalarCost
            selectionCost S <=
          scalarBudget := by

  constructor

  · intro hS

    rcases Finset.mem_filter.mp hS with
      ⟨hPareto, hScalar⟩

    exact
      ⟨(table.pareto_correct S).mp hPareto,
        hScalar⟩

  · intro hS

    rcases hS with
      ⟨hPareto, hScalar⟩

    exact
      Finset.mem_filter.mpr
        ⟨(table.pareto_correct S).mpr hPareto,
          hScalar⟩

/-- The table-based Pareto-scalar search is exactly the corresponding filter of
the existing semantic finite Pareto frontier. -/
theorem paretoScalarFeasibleSelections_eq_semantic
    (scalarBudget : Nat) :
    table.paretoScalarFeasibleSelections scalarBudget =
      (correctedConcreteObservationParetoSelections
        (z := z)
        obsFamily
        f
        selectionCost
        U
        language).filter
        (fun S =>
          correctedConcreteObservationSelectionParetoScalarCost
              selectionCost S <=
            scalarBudget) := by

  ext S

  constructor

  · intro hS

    rcases
        (table.mem_paretoScalarFeasibleSelections_iff
          scalarBudget).mp
          hS with
      ⟨hPareto, hScalar⟩

    exact
      Finset.mem_filter.mpr
        ⟨(mem_correctedConcreteObservationParetoSelections_iff
            (z := z)
            obsFamily
            f
            selectionCost
            U
            language).mpr
            hPareto,
          hScalar⟩

  · intro hS

    rcases Finset.mem_filter.mp hS with
      ⟨hPareto, hScalar⟩

    exact
      (table.mem_paretoScalarFeasibleSelections_iff
        scalarBudget).mpr
        ⟨(mem_correctedConcreteObservationParetoSelections_iff
            (z := z)
            obsFamily
            f
            selectionCost
            U
            language).mp
            hPareto,
          hScalar⟩

/-- Table-only Boolean Pareto-scalar decision. -/
def paretoScalarFeasibleDecision
    (scalarBudget : Nat) :
    Bool :=
  decide
    (table.paretoScalarFeasibleSelections scalarBudget).Nonempty

/-- Correctness of the table-only Pareto-scalar decision. -/
theorem paretoScalarFeasibleDecision_eq_true_iff
    (scalarBudget : Nat) :
    table.paretoScalarFeasibleDecision scalarBudget = true ↔
      ∃ S : Finset ι,
        CorrectedConcreteObservationSelectionParetoOptimal
            (z := z)
            obsFamily
            f
            selectionCost
            U
            language
            S ∧
          correctedConcreteObservationSelectionParetoScalarCost
              selectionCost S <=
            scalarBudget := by

  unfold paretoScalarFeasibleDecision

  rw [decide_eq_true_eq]

  constructor

  · intro hNonempty

    rcases hNonempty with
      ⟨S, hS⟩

    exact
      ⟨S,
        (table.mem_paretoScalarFeasibleSelections_iff
          scalarBudget).mp
          hS⟩

  · intro hExists

    rcases hExists with
      ⟨S, hPareto, hScalar⟩

    exact
      ⟨S,
        (table.mem_paretoScalarFeasibleSelections_iff
          scalarBudget).mpr
          ⟨hPareto, hScalar⟩⟩

end EncodedParetoCandidates


section EncodedRankDecision

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

/-- The minimum-rank-at-most decision uses exactly the finite budget-feasibility
query. -/
def minimumRankAtMostDecision
    (rankBudget : Nat) :
    Bool :=
  table.costFeasibleDecision rankBudget

/-- Under a full-product target witness, the table decision is exactly the
minimum observation-selection rank threshold. -/
theorem minimumRankAtMostDecision_eq_true_iff
    (hTarget :
      language ∈
        StartRootedCorrectedConcreteTargetClass
          (v := z)
          α
          (↥U → M)
          (selectedObservationProduct obsFamily U)
          f)
    (rankBudget : Nat) :
    table.minimumRankAtMostDecision rankBudget = true ↔
      ambientTargetObservationSelectionMinimumCost
          (z := z)
          obsFamily
          f
          selectionCost
          U
          hTarget <=
        rankBudget := by

  unfold minimumRankAtMostDecision

  rw [table.costFeasibleDecision_eq_true_iff]

  let hSelection :=
    hasCorrectedConcreteObservationSelectionCost_of_fullProductTarget
      (obsFamily := obsFamily)
      (f := f)
      selectionCost
      hTarget

  unfold
    ambientTargetObservationSelectionMinimumCost

  exact
    hSelection.selectionAtCost_iff_minimumCost_le
      rankBudget

end EncodedRankDecision

end CorrectedConcreteObservationSelectionDecisionTable


section CanonicalSemanticDecisionTable

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

/-- Canonical proof-carrying table obtained from the already verified semantic
finite searches.

This construction is intentionally noncomputable because the semantic target
predicate remains non-effective.  Later executable developments may replace
this table while reusing every decision theorem in this file. -/
noncomputable def
    correctedConcreteObservationSelectionSemanticDecisionTable :
    CorrectedConcreteObservationSelectionDecisionTable
      (z := z)
      obsFamily
      f
      selectionCost
      U
      language := by

  classical

  exact
    ⟨correctedConcreteObservationFeasibleSelections
        (z := z)
        obsFamily
        f
        U
        language,
      correctedConcreteObservationParetoSelections
        (z := z)
        obsFamily
        f
        selectionCost
        U
        language,
      fun S =>
        mem_correctedConcreteObservationFeasibleSelections_iff
          (z := z)
          obsFamily
          f
          U
          language,
      fun S =>
        mem_correctedConcreteObservationParetoSelections_iff
          (z := z)
          obsFamily
          f
          selectionCost
          U
          language⟩

/-- The canonical table stores exactly the existing semantic feasible search. -/
theorem semanticDecisionTable_feasibleSelections_eq :
    (correctedConcreteObservationSelectionSemanticDecisionTable
      (z := z)
      obsFamily
      f
      selectionCost
      U
      language).feasibleSelections =
      correctedConcreteObservationFeasibleSelections
        (z := z)
        obsFamily
        f
        U
        language := by

  rfl

/-- The canonical table stores exactly the existing semantic Pareto search. -/
theorem semanticDecisionTable_paretoSelections_eq :
    (correctedConcreteObservationSelectionSemanticDecisionTable
      (z := z)
      obsFamily
      f
      selectionCost
      U
      language).paretoSelections =
      correctedConcreteObservationParetoSelections
        (z := z)
        obsFamily
        f
        selectionCost
        U
        language := by

  rfl

end CanonicalSemanticDecisionTable


section PositiveAdditiveDecisionEquivalence

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

/-- For positive additive observation cost, the finite Pareto-scalar decision is
exactly the positive-additive minimum-rank threshold. -/
theorem
    positiveAdditiveParetoScalarDecision_eq_true_iff_minimumRank_le
    (rankBudget : Nat) :
    table.paretoScalarFeasibleDecision rankBudget = true ↔
      ambientTargetObservationSelectionPositiveAdditiveMinimumCost
          (z := z)
          obsFamily
          f
          coordinateWeight
          U
          hTarget <=
        rankBudget := by

  rw [
    table.paretoScalarFeasibleDecision_eq_true_iff
  ]

  constructor

  · intro hExists

    rcases hExists with
      ⟨S, hPareto, hScalar⟩

    let hSelection :=
      hasCorrectedConcreteObservationSelectionCost_of_fullProductTarget
        (obsFamily := obsFamily)
        (f := f)
        (correctedConcreteObservationSelectionPositiveAdditiveCost
          coordinateWeight)
        hTarget

    have hAtCost :
        CorrectedConcreteObservationSelectionAtCost
          (obsFamily := obsFamily)
          (f := f)
          (correctedConcreteObservationSelectionPositiveAdditiveCost
            coordinateWeight)
          U
          language
          (correctedConcreteObservationSelectionPositiveAdditiveCost
            coordinateWeight S) :=
      ⟨S,
        hPareto.1,
        Nat.le_refl _,
        hPareto.2.1⟩

    have hMinimumLe :
        ambientTargetObservationSelectionPositiveAdditiveMinimumCost
              (z := z)
              obsFamily
              f
              coordinateWeight
              U
              hTarget <=
          correctedConcreteObservationSelectionPositiveAdditiveCost
            coordinateWeight S := by

      unfold
        ambientTargetObservationSelectionPositiveAdditiveMinimumCost
        ambientTargetObservationSelectionMinimumCost

      exact
        hSelection.minimumCost_le_of_selection
          hAtCost

    have hPositiveCostLe :
        correctedConcreteObservationSelectionPositiveAdditiveCost
              coordinateWeight S <=
          rankBudget := by

      rw [
        observationSelectionPositiveAdditiveCost_eq_additiveParetoScalarCost
      ]

      exact hScalar

    exact
      hMinimumLe.trans
        hPositiveCostLe

  · intro hMinimumLe

    rcases
        ambientTarget_exists_minimumCostObservationSelection
          (z := z)
          obsFamily
          f
          (correctedConcreteObservationSelectionPositiveAdditiveCost
            coordinateWeight)
          U
          hTarget with
      ⟨S, hSU, hCost, hSelected⟩

    have hPareto :
        CorrectedConcreteObservationSelectionParetoOptimal
          (z := z)
          obsFamily
          f
          (correctedConcreteObservationSelectionAdditiveCost
            coordinateWeight)
          U
          language
          S :=
      ambientTarget_positiveAdditiveMinimumSelection_is_additivePareto
        (z := z)
        obsFamily
        f
        coordinateWeight
        U
        hTarget
        hSU
        hCost
        hSelected

    have hScalar :
        correctedConcreteObservationSelectionParetoScalarCost
              (correctedConcreteObservationSelectionAdditiveCost
                coordinateWeight)
              S <=
          rankBudget := by

      rw [
        ← observationSelectionPositiveAdditiveCost_eq_additiveParetoScalarCost,
        hCost
      ]

      exact hMinimumLe

    exact
      ⟨S,
        hPareto,
        hScalar⟩

/-- The ordinary finite budget decision, the minimum-rank decision, and the
additive-Pareto scalar decision have the same Boolean truth value. -/
theorem positiveAdditiveDecision_equivalence_package
    (rankBudget : Nat) :
    (table.costFeasibleDecision rankBudget = true ↔
      table.minimumRankAtMostDecision rankBudget = true) ∧
      (table.minimumRankAtMostDecision rankBudget = true ↔
        table.paretoScalarFeasibleDecision rankBudget = true) ∧
      (table.costFeasibleDecision rankBudget = true ↔
        ambientTargetObservationSelectionPositiveAdditiveMinimumCost
            (z := z)
            obsFamily
            f
            coordinateWeight
            U
            hTarget <=
          rankBudget) := by

  constructor

  · rfl

  constructor

  · rw [
      table.minimumRankAtMostDecision_eq_true_iff
        hTarget,
      table.positiveAdditiveParetoScalarDecision_eq_true_iff_minimumRank_le
        hTarget
    ]

    rfl

  · rw [
      table.costFeasibleDecision_eq_true_iff
    ]

    let hSelection :=
      hasCorrectedConcreteObservationSelectionCost_of_fullProductTarget
        (obsFamily := obsFamily)
        (f := f)
        (correctedConcreteObservationSelectionPositiveAdditiveCost
          coordinateWeight)
        hTarget

    unfold
      ambientTargetObservationSelectionPositiveAdditiveMinimumCost
      ambientTargetObservationSelectionMinimumCost

    exact
      hSelection.selectionAtCost_iff_minimumCost_le
        rankBudget

end PositiveAdditiveDecisionEquivalence


section DecisionProblemFinalPackage

variable {α : Type u}
variable {ι : Type v}
variable {M : Type w}
variable [DecidableEq ι]
variable [Monoid M]
variable (obsFamily : ι → α → M)
variable (f : Nat)
variable (coordinateWeight : ι → Nat)
variable (U : Finset ι)

/-- Final finite encoded decision-problem package for a full-product target. -/
theorem
    correctedConcreteWorkingGrammar_observationSelectionDecisionProblem_package
    (language : Set (Word α))
    (hTarget :
      language ∈
        StartRootedCorrectedConcreteTargetClass
          (v := z)
          α
          (↥U → M)
          (selectedObservationProduct obsFamily U)
          f) :
    ∀ rankBudget : Nat,
      let table :=
        correctedConcreteObservationSelectionSemanticDecisionTable
          (z := z)
          obsFamily
          f
          (correctedConcreteObservationSelectionAdditiveCost
            coordinateWeight)
          U
          language
      (table.costFeasibleDecision rankBudget = true ↔
        CorrectedConcreteObservationSelectionAtCost
          (obsFamily := obsFamily)
          (f := f)
          (correctedConcreteObservationSelectionAdditiveCost
            coordinateWeight)
          U
          language
          rankBudget) ∧
        (table.minimumRankAtMostDecision rankBudget = true ↔
          ambientTargetObservationSelectionPositiveAdditiveMinimumCost
              (z := z)
              obsFamily
              f
              coordinateWeight
              U
              hTarget <=
            rankBudget) ∧
        (table.paretoScalarFeasibleDecision rankBudget = true ↔
          ambientTargetObservationSelectionPositiveAdditiveMinimumCost
              (z := z)
              obsFamily
              f
              coordinateWeight
              U
              hTarget <=
            rankBudget) ∧
        table.feasibleSelections.card <= 2 ^ U.card ∧
        table.paretoSelections.card <= 2 ^ U.card := by

  intro rankBudget

  let table :=
    correctedConcreteObservationSelectionSemanticDecisionTable
      (z := z)
      obsFamily
      f
      (correctedConcreteObservationSelectionAdditiveCost
        coordinateWeight)
      U
      language

  have hCardinality :=
    table.table_cardinality_package

  exact
    ⟨table.costFeasibleDecision_eq_true_iff
        rankBudget,
      table.minimumRankAtMostDecision_eq_true_iff
        hTarget
        rankBudget,
      table.positiveAdditiveParetoScalarDecision_eq_true_iff_minimumRank_le
        hTarget
        rankBudget,
      hCardinality.1,
      hCardinality.2⟩

end DecisionProblemFinalPackage

end MCFG
