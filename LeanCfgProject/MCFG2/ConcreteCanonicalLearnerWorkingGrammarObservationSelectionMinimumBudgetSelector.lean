/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG.ConcreteCanonicalLearnerWorkingGrammarObservationSelectionBoundedDecisionSearch

/-!
# ConcreteCanonicalLearnerWorkingGrammarObservationSelectionMinimumBudgetSelector.lean

The preceding file constructs, for every finite search ceiling, the complete
finite set of accepted cost budgets and accepted Pareto-scalar budgets.

This file selects the first accepted budget and proves its exact meaning.

## Main construction

For a fixed ceiling `maxBudget`, the bounded existence predicates say that some
budget at most `maxBudget` is accepted by the supplied finite decision table.
Whenever such a witness exists, `Nat.find` selects the least accepted budget.
The selected value is proved to

* lie below the search ceiling;
* be accepted by the corresponding Boolean decision;
* be no larger than every other accepted budget in the bounded search.

## Semantic exactness

Under a full-product target witness and a ceiling at least the true minimum
selection cost, the selected cost budget is exactly the semantic minimum cost.
For positive additive observation cost, the independently selected
Pareto-scalar budget is the same minimum positive-additive rank.
Consequently the ordinary cost selector and the Pareto-envelope selector agree.

The selectors in this file are proof-carrying minimum operators.  They do not
yet attach a machine-cost model to the bounded search, and no hardness claim is
made.

No target grammar is supplied to any learner.
No `sorry`, `admit`, or `axiom` is used.
-/

namespace MCFG

universe u v w z

namespace CorrectedConcreteObservationSelectionDecisionTable

section CostMinimumSelector

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

/-- Some ordinary cost budget at most `maxBudget` is accepted by the finite
selection table. -/
def HasAcceptedCostBudgetUpTo
    (maxBudget : Nat) :
    Prop :=
  ∃ budget : Nat,
    budget <= maxBudget ∧
      table.costFeasibleDecision budget = true

/-- Bounded cost acceptance is equivalent to acceptance of the terminal
budget.  This is the proposition-level version of the preceding finite-search
nonemptiness theorem. -/
theorem hasAcceptedCostBudgetUpTo_iff_terminalDecision
    (maxBudget : Nat) :
    table.HasAcceptedCostBudgetUpTo maxBudget ↔
      table.costFeasibleDecision maxBudget = true := by

  constructor

  · rintro ⟨budget, hBudget, hDecision⟩

    exact
      table.costFeasibleDecision_mono
        hBudget
        hDecision

  · intro hDecision

    exact
      ⟨maxBudget,
        Nat.le_refl maxBudget,
        hDecision⟩

/-- Bounded cost acceptance is equivalent to nonemptiness of the explicitly
enumerated accepted-budget finset. -/
theorem hasAcceptedCostBudgetUpTo_iff_searchNonempty
    (maxBudget : Nat) :
    table.HasAcceptedCostBudgetUpTo maxBudget ↔
      (table.acceptedCostBudgets maxBudget).Nonempty := by

  rw [table.hasAcceptedCostBudgetUpTo_iff_terminalDecision]

  exact
    (table.acceptedCostBudgets_nonempty_iff_terminalDecision
      maxBudget).symm

/-- Least accepted ordinary cost budget below the supplied ceiling. -/
noncomputable def selectedMinimumAcceptedCostBudget
    (maxBudget : Nat)
    (hAccepted :
      table.HasAcceptedCostBudgetUpTo maxBudget) :
    Nat :=
  Nat.find hAccepted

/-- The selected ordinary cost budget is below the ceiling and is accepted. -/
theorem selectedMinimumAcceptedCostBudget_spec
    (maxBudget : Nat)
    (hAccepted :
      table.HasAcceptedCostBudgetUpTo maxBudget) :
    table.selectedMinimumAcceptedCostBudget
          maxBudget
          hAccepted <=
        maxBudget ∧
      table.costFeasibleDecision
          (table.selectedMinimumAcceptedCostBudget
            maxBudget
            hAccepted) =
        true := by

  exact
    Nat.find_spec hAccepted

/-- The selected ordinary cost budget is no larger than every other accepted
budget below the same ceiling. -/
theorem selectedMinimumAcceptedCostBudget_le
    (maxBudget : Nat)
    (hAccepted :
      table.HasAcceptedCostBudgetUpTo maxBudget)
    {budget : Nat}
    (hBudget : budget <= maxBudget)
    (hDecision :
      table.costFeasibleDecision budget = true) :
    table.selectedMinimumAcceptedCostBudget
        maxBudget
        hAccepted <=
      budget := by

  exact
    Nat.find_min'
      hAccepted
      ⟨hBudget, hDecision⟩

/-- The selected value belongs to the explicit bounded accepted-cost search. -/
theorem selectedMinimumAcceptedCostBudget_mem_search
    (maxBudget : Nat)
    (hAccepted :
      table.HasAcceptedCostBudgetUpTo maxBudget) :
    table.selectedMinimumAcceptedCostBudget
          maxBudget
          hAccepted ∈
        table.acceptedCostBudgets maxBudget := by

  rcases
      table.selectedMinimumAcceptedCostBudget_spec
        maxBudget
        hAccepted with
    ⟨hBudget, hDecision⟩

  exact
    (table.mem_acceptedCostBudgets_iff
      maxBudget
      (table.selectedMinimumAcceptedCostBudget
        maxBudget
        hAccepted)).mpr
      ⟨hBudget, hDecision⟩

/-- A full-product target and a sufficiently large ceiling provide a bounded
accepted ordinary cost budget. -/
theorem hasAcceptedCostBudgetUpTo_of_minimumCost_le
    (hTarget :
      language ∈
        StartRootedCorrectedConcreteTargetClass
          (v := z)
          α
          (↥U → M)
          (selectedObservationProduct obsFamily U)
          f)
    (maxBudget : Nat)
    (hBound :
      ambientTargetObservationSelectionMinimumCost
            (z := z)
            obsFamily
            f
            selectionCost
            U
            hTarget <=
          maxBudget) :
    table.HasAcceptedCostBudgetUpTo maxBudget := by

  let minimumCost :=
    ambientTargetObservationSelectionMinimumCost
      (z := z)
      obsFamily
      f
      selectionCost
      U
      hTarget

  refine
    ⟨minimumCost,
      hBound,
      ?_⟩

  change
    table.minimumRankAtMostDecision minimumCost = true

  exact
    (table.minimumRankAtMostDecision_eq_true_iff
      hTarget
      minimumCost).mpr
      (Nat.le_refl minimumCost)

/-- Under a correct full-product target witness, the selected first accepted
cost budget is exactly the semantic minimum selection cost. -/
theorem selectedMinimumAcceptedCostBudget_eq_minimumCost
    (hTarget :
      language ∈
        StartRootedCorrectedConcreteTargetClass
          (v := z)
          α
          (↥U → M)
          (selectedObservationProduct obsFamily U)
          f)
    (maxBudget : Nat)
    (hBound :
      ambientTargetObservationSelectionMinimumCost
            (z := z)
            obsFamily
            f
            selectionCost
            U
            hTarget <=
          maxBudget) :
    let hAccepted :=
      table.hasAcceptedCostBudgetUpTo_of_minimumCost_le
        hTarget
        maxBudget
        hBound
    table.selectedMinimumAcceptedCostBudget
        maxBudget
        hAccepted =
      ambientTargetObservationSelectionMinimumCost
        (z := z)
        obsFamily
        f
        selectionCost
        U
        hTarget := by

  let minimumCost :=
    ambientTargetObservationSelectionMinimumCost
      (z := z)
      obsFamily
      f
      selectionCost
      U
      hTarget

  let hAccepted :=
    table.hasAcceptedCostBudgetUpTo_of_minimumCost_le
      hTarget
      maxBudget
      hBound

  apply Nat.le_antisymm

  · apply
      table.selectedMinimumAcceptedCostBudget_le
        maxBudget
        hAccepted
        hBound

    change
      table.minimumRankAtMostDecision minimumCost = true

    exact
      (table.minimumRankAtMostDecision_eq_true_iff
        hTarget
        minimumCost).mpr
        (Nat.le_refl minimumCost)

  · rcases
        table.selectedMinimumAcceptedCostBudget_spec
          maxBudget
          hAccepted with
      ⟨_, hDecision⟩

    change
      table.minimumRankAtMostDecision
          (table.selectedMinimumAcceptedCostBudget
            maxBudget
            hAccepted) =
        true at hDecision

    exact
      (table.minimumRankAtMostDecision_eq_true_iff
        hTarget
        (table.selectedMinimumAcceptedCostBudget
          maxBudget
          hAccepted)).mp
        hDecision

end CostMinimumSelector


section ParetoScalarMinimumSelector

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

/-- Some Pareto scalar budget at most `maxBudget` is accepted by the finite
selection table. -/
def HasAcceptedParetoScalarBudgetUpTo
    (maxBudget : Nat) :
    Prop :=
  ∃ budget : Nat,
    budget <= maxBudget ∧
      table.paretoScalarFeasibleDecision budget = true

/-- Bounded Pareto-scalar acceptance is equivalent to acceptance of the
terminal scalar budget. -/
theorem hasAcceptedParetoScalarBudgetUpTo_iff_terminalDecision
    (maxBudget : Nat) :
    table.HasAcceptedParetoScalarBudgetUpTo maxBudget ↔
      table.paretoScalarFeasibleDecision maxBudget = true := by

  constructor

  · rintro ⟨budget, hBudget, hDecision⟩

    exact
      table.paretoScalarFeasibleDecision_mono
        hBudget
        hDecision

  · intro hDecision

    exact
      ⟨maxBudget,
        Nat.le_refl maxBudget,
        hDecision⟩

/-- Bounded Pareto-scalar acceptance is equivalent to nonemptiness of the
explicitly enumerated Pareto-scalar budget search. -/
theorem hasAcceptedParetoScalarBudgetUpTo_iff_searchNonempty
    (maxBudget : Nat) :
    table.HasAcceptedParetoScalarBudgetUpTo maxBudget ↔
      (table.acceptedParetoScalarBudgets maxBudget).Nonempty := by

  rw [table.hasAcceptedParetoScalarBudgetUpTo_iff_terminalDecision]

  exact
    (table.acceptedParetoScalarBudgets_nonempty_iff_terminalDecision
      maxBudget).symm

/-- Least accepted Pareto scalar budget below the supplied ceiling. -/
noncomputable def selectedMinimumAcceptedParetoScalarBudget
    (maxBudget : Nat)
    (hAccepted :
      table.HasAcceptedParetoScalarBudgetUpTo maxBudget) :
    Nat :=
  Nat.find hAccepted

/-- The selected Pareto scalar budget is below the ceiling and is accepted. -/
theorem selectedMinimumAcceptedParetoScalarBudget_spec
    (maxBudget : Nat)
    (hAccepted :
      table.HasAcceptedParetoScalarBudgetUpTo maxBudget) :
    table.selectedMinimumAcceptedParetoScalarBudget
          maxBudget
          hAccepted <=
        maxBudget ∧
      table.paretoScalarFeasibleDecision
          (table.selectedMinimumAcceptedParetoScalarBudget
            maxBudget
            hAccepted) =
        true := by

  exact
    Nat.find_spec hAccepted

/-- The selected Pareto scalar budget is no larger than every other accepted
scalar budget below the same ceiling. -/
theorem selectedMinimumAcceptedParetoScalarBudget_le
    (maxBudget : Nat)
    (hAccepted :
      table.HasAcceptedParetoScalarBudgetUpTo maxBudget)
    {budget : Nat}
    (hBudget : budget <= maxBudget)
    (hDecision :
      table.paretoScalarFeasibleDecision budget = true) :
    table.selectedMinimumAcceptedParetoScalarBudget
        maxBudget
        hAccepted <=
      budget := by

  exact
    Nat.find_min'
      hAccepted
      ⟨hBudget, hDecision⟩

/-- The selected value belongs to the explicit bounded accepted Pareto-scalar
search. -/
theorem selectedMinimumAcceptedParetoScalarBudget_mem_search
    (maxBudget : Nat)
    (hAccepted :
      table.HasAcceptedParetoScalarBudgetUpTo maxBudget) :
    table.selectedMinimumAcceptedParetoScalarBudget
          maxBudget
          hAccepted ∈
        table.acceptedParetoScalarBudgets maxBudget := by

  rcases
      table.selectedMinimumAcceptedParetoScalarBudget_spec
        maxBudget
        hAccepted with
    ⟨hBudget, hDecision⟩

  exact
    (table.mem_acceptedParetoScalarBudgets_iff
      maxBudget
      (table.selectedMinimumAcceptedParetoScalarBudget
        maxBudget
        hAccepted)).mpr
      ⟨hBudget, hDecision⟩

end ParetoScalarMinimumSelector


section PositiveAdditiveSelectorAgreement

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

/-- A sufficiently large ceiling supplies an accepted ordinary cost budget under
the additive-table/positive-additive-rank convention. -/
theorem hasAcceptedCostBudgetUpTo_of_positiveAdditiveMinimum_le
    (maxBudget : Nat)
    (hBound :
      ambientTargetObservationSelectionPositiveAdditiveMinimumCost
            (z := z)
            obsFamily
            f
            coordinateWeight
            U
            hTarget <=
          maxBudget) :
    table.HasAcceptedCostBudgetUpTo maxBudget := by

  let minimumCost :=
    ambientTargetObservationSelectionPositiveAdditiveMinimumCost
      (z := z)
      obsFamily
      f
      coordinateWeight
      U
      hTarget

  refine
    ⟨minimumCost,
      hBound,
      ?_⟩

  exact
    ((table.positiveAdditiveDecision_equivalence_package
      hTarget
      minimumCost).2.2).mpr
      (Nat.le_refl minimumCost)

/-- The first accepted ordinary cost budget under the additive table is exactly
the minimum positive-additive observation-selection rank. -/
theorem selectedMinimumAcceptedCostBudget_eq_positiveAdditiveMinimum
    (maxBudget : Nat)
    (hBound :
      ambientTargetObservationSelectionPositiveAdditiveMinimumCost
            (z := z)
            obsFamily
            f
            coordinateWeight
            U
            hTarget <=
          maxBudget) :
    let hAccepted :=
      table.hasAcceptedCostBudgetUpTo_of_positiveAdditiveMinimum_le
        hTarget
        maxBudget
        hBound
    table.selectedMinimumAcceptedCostBudget
        maxBudget
        hAccepted =
      ambientTargetObservationSelectionPositiveAdditiveMinimumCost
        (z := z)
        obsFamily
        f
        coordinateWeight
        U
        hTarget := by

  let minimumCost :=
    ambientTargetObservationSelectionPositiveAdditiveMinimumCost
      (z := z)
      obsFamily
      f
      coordinateWeight
      U
      hTarget

  let hAccepted :=
    table.hasAcceptedCostBudgetUpTo_of_positiveAdditiveMinimum_le
      hTarget
      maxBudget
      hBound

  apply Nat.le_antisymm

  · apply
      table.selectedMinimumAcceptedCostBudget_le
        maxBudget
        hAccepted
        hBound

    exact
      ((table.positiveAdditiveDecision_equivalence_package
        hTarget
        minimumCost).2.2).mpr
        (Nat.le_refl minimumCost)

  · rcases
        table.selectedMinimumAcceptedCostBudget_spec
          maxBudget
          hAccepted with
      ⟨_, hDecision⟩

    exact
      ((table.positiveAdditiveDecision_equivalence_package
        hTarget
        (table.selectedMinimumAcceptedCostBudget
          maxBudget
          hAccepted)).2.2).mp
        hDecision

/-- A sufficiently large ceiling supplies an accepted positive-additive Pareto
scalar budget. -/
theorem hasAcceptedParetoScalarBudgetUpTo_of_positiveAdditiveMinimum_le
    (maxBudget : Nat)
    (hBound :
      ambientTargetObservationSelectionPositiveAdditiveMinimumCost
            (z := z)
            obsFamily
            f
            coordinateWeight
            U
            hTarget <=
          maxBudget) :
    table.HasAcceptedParetoScalarBudgetUpTo maxBudget := by

  let minimumCost :=
    ambientTargetObservationSelectionPositiveAdditiveMinimumCost
      (z := z)
      obsFamily
      f
      coordinateWeight
      U
      hTarget

  refine
    ⟨minimumCost,
      hBound,
      ?_⟩

  exact
    (table.positiveAdditiveParetoScalarDecision_eq_true_iff_minimumRank_le
      hTarget
      minimumCost).mpr
      (Nat.le_refl minimumCost)

/-- The first accepted Pareto scalar budget is exactly the minimum
positive-additive observation-selection rank. -/
theorem selectedMinimumAcceptedParetoScalarBudget_eq_positiveAdditiveMinimum
    (maxBudget : Nat)
    (hBound :
      ambientTargetObservationSelectionPositiveAdditiveMinimumCost
            (z := z)
            obsFamily
            f
            coordinateWeight
            U
            hTarget <=
          maxBudget) :
    let hAccepted :=
      table.hasAcceptedParetoScalarBudgetUpTo_of_positiveAdditiveMinimum_le
        hTarget
        maxBudget
        hBound
    table.selectedMinimumAcceptedParetoScalarBudget
        maxBudget
        hAccepted =
      ambientTargetObservationSelectionPositiveAdditiveMinimumCost
        (z := z)
        obsFamily
        f
        coordinateWeight
        U
        hTarget := by

  let minimumCost :=
    ambientTargetObservationSelectionPositiveAdditiveMinimumCost
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

  apply Nat.le_antisymm

  · apply
      table.selectedMinimumAcceptedParetoScalarBudget_le
        maxBudget
        hAccepted
        hBound

    exact
      (table.positiveAdditiveParetoScalarDecision_eq_true_iff_minimumRank_le
        hTarget
        minimumCost).mpr
        (Nat.le_refl minimumCost)

  · rcases
        table.selectedMinimumAcceptedParetoScalarBudget_spec
          maxBudget
          hAccepted with
      ⟨_, hDecision⟩

    exact
      (table.positiveAdditiveParetoScalarDecision_eq_true_iff_minimumRank_le
        hTarget
        (table.selectedMinimumAcceptedParetoScalarBudget
          maxBudget
          hAccepted)).mp
        hDecision

/-- The ordinary positive-additive cost selector and the Pareto-envelope
selector independently recover the same minimum rank. -/
theorem selectedPositiveAdditiveCostBudget_eq_selectedParetoScalarBudget
    (maxBudget : Nat)
    (hBound :
      ambientTargetObservationSelectionPositiveAdditiveMinimumCost
            (z := z)
            obsFamily
            f
            coordinateWeight
            U
            hTarget <=
          maxBudget) :
    let hCostAccepted :=
      table.hasAcceptedCostBudgetUpTo_of_positiveAdditiveMinimum_le
        hTarget
        maxBudget
        hBound
    let hParetoAccepted :=
      table.hasAcceptedParetoScalarBudgetUpTo_of_positiveAdditiveMinimum_le
        hTarget
        maxBudget
        hBound
    table.selectedMinimumAcceptedCostBudget
        maxBudget
        hCostAccepted =
      table.selectedMinimumAcceptedParetoScalarBudget
        maxBudget
        hParetoAccepted := by

  rw [table.selectedMinimumAcceptedCostBudget_eq_positiveAdditiveMinimum
      hTarget
      maxBudget
      hBound]

  rw [table.selectedMinimumAcceptedParetoScalarBudget_eq_positiveAdditiveMinimum
      hTarget
      maxBudget
      hBound]

/-- Combined exactness package for the two minimum-budget selectors. -/
theorem positiveAdditiveMinimumBudgetSelector_package
    (maxBudget : Nat)
    (hBound :
      ambientTargetObservationSelectionPositiveAdditiveMinimumCost
            (z := z)
            obsFamily
            f
            coordinateWeight
            U
            hTarget <=
          maxBudget) :
    let hCostAccepted :=
      table.hasAcceptedCostBudgetUpTo_of_positiveAdditiveMinimum_le
        hTarget
        maxBudget
        hBound
    let hParetoAccepted :=
      table.hasAcceptedParetoScalarBudgetUpTo_of_positiveAdditiveMinimum_le
        hTarget
        maxBudget
        hBound
    table.selectedMinimumAcceptedCostBudget
          maxBudget
          hCostAccepted =
        ambientTargetObservationSelectionPositiveAdditiveMinimumCost
          (z := z)
          obsFamily
          f
          coordinateWeight
          U
          hTarget ∧
      table.selectedMinimumAcceptedParetoScalarBudget
          maxBudget
          hParetoAccepted =
        ambientTargetObservationSelectionPositiveAdditiveMinimumCost
          (z := z)
          obsFamily
          f
          coordinateWeight
          U
          hTarget ∧
      table.selectedMinimumAcceptedCostBudget
          maxBudget
          hCostAccepted =
        table.selectedMinimumAcceptedParetoScalarBudget
          maxBudget
          hParetoAccepted := by

  exact
    ⟨table.selectedMinimumAcceptedCostBudget_eq_positiveAdditiveMinimum
        hTarget
        maxBudget
        hBound,
      table.selectedMinimumAcceptedParetoScalarBudget_eq_positiveAdditiveMinimum
        hTarget
        maxBudget
        hBound,
      table.selectedPositiveAdditiveCostBudget_eq_selectedParetoScalarBudget
        hTarget
        maxBudget
        hBound⟩

end PositiveAdditiveSelectorAgreement

end CorrectedConcreteObservationSelectionDecisionTable


section MinimumBudgetSelectorFinalPackage

variable {α : Type u}
variable {ι : Type v}
variable {M : Type w}
variable [DecidableEq ι]
variable [Monoid M]
variable (obsFamily : ι → α → M)
variable (f : Nat)
variable (coordinateWeight : ι → Nat)
variable (U : Finset ι)

/-- Final minimum-budget-selector package for the canonical semantic decision
table.  The ambient full-set cost is always a sufficient search ceiling. -/
theorem
    correctedConcreteWorkingGrammar_observationSelectionMinimumBudgetSelector_package
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
    let hCostAccepted :=
      table.hasAcceptedCostBudgetUpTo_of_positiveAdditiveMinimum_le
        hTarget
        maxBudget
        hBound
    let hParetoAccepted :=
      table.hasAcceptedParetoScalarBudgetUpTo_of_positiveAdditiveMinimum_le
        hTarget
        maxBudget
        hBound
    table.selectedMinimumAcceptedCostBudget
          maxBudget
          hCostAccepted =
        ambientTargetObservationSelectionPositiveAdditiveMinimumCost
          (z := z)
          obsFamily
          f
          coordinateWeight
          U
          hTarget ∧
      table.selectedMinimumAcceptedParetoScalarBudget
          maxBudget
          hParetoAccepted =
        ambientTargetObservationSelectionPositiveAdditiveMinimumCost
          (z := z)
          obsFamily
          f
          coordinateWeight
          U
          hTarget ∧
      table.selectedMinimumAcceptedCostBudget
          maxBudget
          hCostAccepted =
        table.selectedMinimumAcceptedParetoScalarBudget
          maxBudget
          hParetoAccepted := by

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

  exact
    table.positiveAdditiveMinimumBudgetSelector_package
      hTarget
      maxBudget
      hBound

end MinimumBudgetSelectorFinalPackage

end MCFG
