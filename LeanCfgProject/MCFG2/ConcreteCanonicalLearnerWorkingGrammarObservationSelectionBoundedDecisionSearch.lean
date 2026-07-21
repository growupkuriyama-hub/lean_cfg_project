/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG2.ConcreteCanonicalLearnerWorkingGrammarObservationSelectionComplexity

/-!
# ConcreteCanonicalLearnerWorkingGrammarObservationSelectionBoundedDecisionSearch.lean

The preceding files isolate observation-selection feasibility behind a finite
correct decision table and provide bounded subset certificates for its Boolean
queries.

This file turns those pointwise Boolean queries into explicit bounded searches
through the natural-number budget space.

For a maximum budget `B`, the search enumerates the finite set

```text
{ b | b <= B and the table answers yes at budget b }.
```

The construction is entirely table based.  It inspects only the previously
defined Boolean decision procedures and the finite range `0, ..., B`.

## Main facts

* the accepted-budget search has at most `B + 1` entries;
* it is nonempty exactly when the terminal budget `B` is accepted;
* accepted cost budgets are upward closed inside the searched range;
* under a full-product target witness, the accepted cost budgets are exactly
  the interval from the semantic minimum selection cost to `B`;
* under positive additive cost, the Pareto-scalar search yields exactly the
  same threshold interval.

Thus the minimum-rank threshold is not only characterized pointwise by a
Boolean query: every bounded truth table has the exact one-switch interval
shape required by a linear or binary search implementation.

This file does not yet attach a machine-cost model to that search and does not
claim NP-hardness or NP-completeness.

No target grammar is supplied to any learner.
No `sorry`, `admit`, or `axiom` is used.
-/

namespace MCFG

universe u v w z

namespace CorrectedConcreteObservationSelectionDecisionTable

section CostBudgetSearch

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

/-- Explicit bounded search through all natural cost budgets at most
`maxBudget`.  The predicate being filtered is the finite-table Boolean decision
from the preceding decision-problem file. -/
def acceptedCostBudgets
    (maxBudget : Nat) :
    Finset Nat :=
  (Finset.range (maxBudget + 1)).filter
    (fun budget =>
      table.costFeasibleDecision budget = true)

/-- Exact membership theorem for the bounded cost-budget search. -/
theorem mem_acceptedCostBudgets_iff
    (maxBudget budget : Nat) :
    budget ∈ table.acceptedCostBudgets maxBudget ↔
      budget <= maxBudget ∧
        table.costFeasibleDecision budget = true := by

  simp [acceptedCostBudgets, Nat.lt_succ_iff]

/-- The bounded search is contained in the enumerated natural-number range. -/
theorem acceptedCostBudgets_subset_range
    (maxBudget : Nat) :
    table.acceptedCostBudgets maxBudget ⊆
      Finset.range (maxBudget + 1) := by

  intro budget hBudget

  exact
    (Finset.mem_filter.mp hBudget).1

/-- At most `maxBudget + 1` cost budgets are inspected and retained. -/
theorem acceptedCostBudgets_card_le
    (maxBudget : Nat) :
    (table.acceptedCostBudgets maxBudget).card <=
      maxBudget + 1 := by

  calc
    (table.acceptedCostBudgets maxBudget).card <=
        (Finset.range (maxBudget + 1)).card :=
      Finset.card_le_card
        (table.acceptedCostBudgets_subset_range maxBudget)

    _ = maxBudget + 1 := by
      simp

/-- A bounded cost search is nonempty exactly when its largest searched budget
is accepted.  The reverse direction uses monotonicity of the cost decision. -/
theorem acceptedCostBudgets_nonempty_iff_terminalDecision
    (maxBudget : Nat) :
    (table.acceptedCostBudgets maxBudget).Nonempty ↔
      table.costFeasibleDecision maxBudget = true := by

  constructor

  · intro hNonempty

    rcases hNonempty with
      ⟨budget, hBudget⟩

    rcases
        (table.mem_acceptedCostBudgets_iff
          maxBudget
          budget).mp
          hBudget with
      ⟨hBudgetLe, hDecision⟩

    exact
      table.costFeasibleDecision_mono
        hBudgetLe
        hDecision

  · intro hDecision

    exact
      ⟨maxBudget,
        (table.mem_acceptedCostBudgets_iff
          maxBudget
          maxBudget).mpr
          ⟨Nat.le_refl maxBudget,
            hDecision⟩⟩

/-- Accepted cost budgets are upward closed inside the searched range. -/
theorem acceptedCostBudgets_upwardClosed
    {maxBudget budget budget' : Nat}
    (hBudget :
      budget ∈ table.acceptedCostBudgets maxBudget)
    (hLe : budget <= budget')
    (hUpper : budget' <= maxBudget) :
    budget' ∈ table.acceptedCostBudgets maxBudget := by

  rcases
      (table.mem_acceptedCostBudgets_iff
        maxBudget
        budget).mp
        hBudget with
    ⟨_, hDecision⟩

  exact
    (table.mem_acceptedCostBudgets_iff
      maxBudget
      budget').mpr
      ⟨hUpper,
        table.costFeasibleDecision_mono
          hLe
          hDecision⟩

/-- Under a full-product target witness, bounded-search membership is exactly
membership in the interval from the semantic minimum selection cost to the
search bound. -/
theorem mem_acceptedCostBudgets_iff_minimumCost_interval
    (hTarget :
      language ∈
        StartRootedCorrectedConcreteTargetClass
          (v := z)
          α
          (↥U → M)
          (selectedObservationProduct obsFamily U)
          f)
    (maxBudget budget : Nat) :
    budget ∈ table.acceptedCostBudgets maxBudget ↔
      ambientTargetObservationSelectionMinimumCost
            (z := z)
            obsFamily
            f
            selectionCost
            U
            hTarget <=
          budget ∧
        budget <= maxBudget := by

  rw [table.mem_acceptedCostBudgets_iff]

  change
    (budget <= maxBudget ∧
      table.minimumRankAtMostDecision budget = true) ↔ _

  rw [table.minimumRankAtMostDecision_eq_true_iff
      hTarget
      budget]

  constructor

  · rintro ⟨hUpper, hLower⟩
    exact ⟨hLower, hUpper⟩

  · rintro ⟨hLower, hUpper⟩
    exact ⟨hUpper, hLower⟩

/-- The complete bounded accepted-cost search is exactly a finite natural
interval. -/
theorem acceptedCostBudgets_eq_Icc_minimumCost
    (hTarget :
      language ∈
        StartRootedCorrectedConcreteTargetClass
          (v := z)
          α
          (↥U → M)
          (selectedObservationProduct obsFamily U)
          f)
    (maxBudget : Nat) :
    table.acceptedCostBudgets maxBudget =
      Finset.Icc
        (ambientTargetObservationSelectionMinimumCost
          (z := z)
          obsFamily
          f
          selectionCost
          U
          hTarget)
        maxBudget := by

  ext budget

  rw [table.mem_acceptedCostBudgets_iff_minimumCost_interval
      hTarget]

  simp only [Finset.mem_Icc]

/-- Consequently, the bounded cost search is nonempty exactly when the true
minimum cost lies below the search ceiling. -/
theorem acceptedCostBudgets_nonempty_iff_minimumCost_le
    (hTarget :
      language ∈
        StartRootedCorrectedConcreteTargetClass
          (v := z)
          α
          (↥U → M)
          (selectedObservationProduct obsFamily U)
          f)
    (maxBudget : Nat) :
    (table.acceptedCostBudgets maxBudget).Nonempty ↔
      ambientTargetObservationSelectionMinimumCost
            (z := z)
            obsFamily
            f
            selectionCost
            U
            hTarget <=
          maxBudget := by

  rw [table.acceptedCostBudgets_nonempty_iff_terminalDecision]

  change
    table.minimumRankAtMostDecision maxBudget = true ↔ _

  exact
    table.minimumRankAtMostDecision_eq_true_iff
      hTarget
      maxBudget

end CostBudgetSearch


section ParetoScalarBudgetSearch

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

/-- Explicit bounded search through Pareto scalar budgets. -/
def acceptedParetoScalarBudgets
    (maxBudget : Nat) :
    Finset Nat :=
  (Finset.range (maxBudget + 1)).filter
    (fun budget =>
      table.paretoScalarFeasibleDecision budget = true)

/-- Exact membership theorem for the bounded Pareto-scalar search. -/
theorem mem_acceptedParetoScalarBudgets_iff
    (maxBudget budget : Nat) :
    budget ∈ table.acceptedParetoScalarBudgets maxBudget ↔
      budget <= maxBudget ∧
        table.paretoScalarFeasibleDecision budget = true := by

  simp [acceptedParetoScalarBudgets, Nat.lt_succ_iff]

/-- The Pareto-scalar Boolean decision is monotone in its scalar budget. -/
theorem paretoScalarFeasibleDecision_mono
    {scalarBudget scalarBudget' : Nat}
    (hBudget : scalarBudget <= scalarBudget')
    (hDecision :
      table.paretoScalarFeasibleDecision scalarBudget = true) :
    table.paretoScalarFeasibleDecision scalarBudget' = true := by

  apply
    (table.paretoScalarFeasibleDecision_eq_true_iff
      scalarBudget').mpr

  rcases
      (table.paretoScalarFeasibleDecision_eq_true_iff
        scalarBudget).mp
        hDecision with
    ⟨S, hPareto, hScalar⟩

  exact
    ⟨S,
      hPareto,
      hScalar.trans hBudget⟩

/-- At most `maxBudget + 1` Pareto scalar budgets are retained. -/
theorem acceptedParetoScalarBudgets_card_le
    (maxBudget : Nat) :
    (table.acceptedParetoScalarBudgets maxBudget).card <=
      maxBudget + 1 := by

  have hSubset :
      table.acceptedParetoScalarBudgets maxBudget ⊆
        Finset.range (maxBudget + 1) := by

    intro budget hBudget

    exact
      (Finset.mem_filter.mp hBudget).1

  calc
    (table.acceptedParetoScalarBudgets maxBudget).card <=
        (Finset.range (maxBudget + 1)).card :=
      Finset.card_le_card hSubset

    _ = maxBudget + 1 := by
      simp

/-- A bounded Pareto-scalar search is nonempty exactly when its largest budget
is accepted. -/
theorem acceptedParetoScalarBudgets_nonempty_iff_terminalDecision
    (maxBudget : Nat) :
    (table.acceptedParetoScalarBudgets maxBudget).Nonempty ↔
      table.paretoScalarFeasibleDecision maxBudget = true := by

  constructor

  · intro hNonempty

    rcases hNonempty with
      ⟨budget, hBudget⟩

    rcases
        (table.mem_acceptedParetoScalarBudgets_iff
          maxBudget
          budget).mp
          hBudget with
      ⟨hBudgetLe, hDecision⟩

    exact
      table.paretoScalarFeasibleDecision_mono
        hBudgetLe
        hDecision

  · intro hDecision

    exact
      ⟨maxBudget,
        (table.mem_acceptedParetoScalarBudgets_iff
          maxBudget
          maxBudget).mpr
          ⟨Nat.le_refl maxBudget,
            hDecision⟩⟩

end ParetoScalarBudgetSearch


section PositiveAdditiveThresholdSearch

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

/-- Under the additive table convention, cost-budget bounded-search membership
is exactly the interval above the positive-additive minimum rank.  The bridge is
the already verified additive/Pareto decision-equivalence theorem. -/
theorem mem_acceptedPositiveAdditiveCostBudgets_iff_minimum_interval
    (maxBudget budget : Nat) :
    budget ∈ table.acceptedCostBudgets maxBudget ↔
      ambientTargetObservationSelectionPositiveAdditiveMinimumCost
            (z := z)
            obsFamily
            f
            coordinateWeight
            U
            hTarget <=
          budget ∧
        budget <= maxBudget := by

  rw [table.mem_acceptedCostBudgets_iff]

  rw [(table.positiveAdditiveDecision_equivalence_package
      hTarget
      budget).2.2]

  constructor

  · rintro ⟨hUpper, hLower⟩
    exact ⟨hLower, hUpper⟩

  · rintro ⟨hLower, hUpper⟩
    exact ⟨hUpper, hLower⟩

/-- Under positive additive cost, Pareto-scalar bounded-search membership is
exactly the interval above the positive-additive minimum rank. -/
theorem mem_acceptedParetoScalarBudgets_iff_positiveAdditiveMinimum_interval
    (maxBudget budget : Nat) :
    budget ∈ table.acceptedParetoScalarBudgets maxBudget ↔
      ambientTargetObservationSelectionPositiveAdditiveMinimumCost
            (z := z)
            obsFamily
            f
            coordinateWeight
            U
            hTarget <=
          budget ∧
        budget <= maxBudget := by

  rw [table.mem_acceptedParetoScalarBudgets_iff]

  rw [table.positiveAdditiveParetoScalarDecision_eq_true_iff_minimumRank_le
      hTarget
      budget]

  constructor

  · rintro ⟨hUpper, hLower⟩
    exact ⟨hLower, hUpper⟩

  · rintro ⟨hLower, hUpper⟩
    exact ⟨hUpper, hLower⟩

/-- The additive-table cost search is exactly the finite threshold interval
determined by the minimum positive-additive rank. -/
theorem acceptedPositiveAdditiveCostBudgets_eq_Icc_minimum
    (maxBudget : Nat) :
    table.acceptedCostBudgets maxBudget =
      Finset.Icc
        (ambientTargetObservationSelectionPositiveAdditiveMinimumCost
          (z := z)
          obsFamily
          f
          coordinateWeight
          U
          hTarget)
        maxBudget := by

  ext budget

  rw [table.mem_acceptedPositiveAdditiveCostBudgets_iff_minimum_interval
      hTarget]

  simp only [Finset.mem_Icc]

/-- The positive-additive Pareto-scalar bounded search is exactly the same
finite threshold interval determined by the minimum positive-additive rank. -/
theorem acceptedParetoScalarBudgets_eq_Icc_positiveAdditiveMinimum
    (maxBudget : Nat) :
    table.acceptedParetoScalarBudgets maxBudget =
      Finset.Icc
        (ambientTargetObservationSelectionPositiveAdditiveMinimumCost
          (z := z)
          obsFamily
          f
          coordinateWeight
          U
          hTarget)
        maxBudget := by

  ext budget

  rw [table.mem_acceptedParetoScalarBudgets_iff_positiveAdditiveMinimum_interval
      hTarget]

  simp only [Finset.mem_Icc]

/-- The ordinary cost search and the Pareto-scalar search have exactly the same
accepted budgets under positive additive observation cost. -/
theorem acceptedPositiveAdditiveCostBudgets_eq_acceptedParetoScalarBudgets
    (maxBudget : Nat) :
    table.acceptedCostBudgets maxBudget =
      table.acceptedParetoScalarBudgets maxBudget := by

  rw [table.acceptedPositiveAdditiveCostBudgets_eq_Icc_minimum
      hTarget]
  rw [table.acceptedParetoScalarBudgets_eq_Icc_positiveAdditiveMinimum
      hTarget]

/-- The positive-additive Pareto-scalar search is nonempty exactly when the
minimum positive-additive rank lies below its search ceiling. -/
theorem acceptedParetoScalarBudgets_nonempty_iff_positiveAdditiveMinimum_le
    (maxBudget : Nat) :
    (table.acceptedParetoScalarBudgets maxBudget).Nonempty ↔
      ambientTargetObservationSelectionPositiveAdditiveMinimumCost
            (z := z)
            obsFamily
            f
            coordinateWeight
            U
            hTarget <=
          maxBudget := by

  rw [table.acceptedParetoScalarBudgets_nonempty_iff_terminalDecision]

  exact
    table.positiveAdditiveParetoScalarDecision_eq_true_iff_minimumRank_le
      hTarget
      maxBudget

end PositiveAdditiveThresholdSearch

end CorrectedConcreteObservationSelectionDecisionTable


section BoundedDecisionSearchFinalPackage

variable {α : Type u}
variable {ι : Type v}
variable {M : Type w}
variable [DecidableEq ι]
variable [Monoid M]
variable (obsFamily : ι → α → M)
variable (f : Nat)
variable (coordinateWeight : ι → Nat)
variable (U : Finset ι)

/-- Final bounded-search package for the canonical semantic decision table. -/
theorem
    correctedConcreteWorkingGrammar_observationSelectionBoundedDecisionSearch_package
    (language : Set (Word α))
    (hTarget :
      language ∈
        StartRootedCorrectedConcreteTargetClass
          (v := z)
          α
          (↥U → M)
          (selectedObservationProduct obsFamily U)
          f)
    (maxBudget : Nat) :
    let table :=
      correctedConcreteObservationSelectionSemanticDecisionTable
        (z := z)
        obsFamily
        f
        (correctedConcreteObservationSelectionAdditiveCost
          coordinateWeight)
        U
        language
    table.acceptedCostBudgets maxBudget =
        Finset.Icc
          (ambientTargetObservationSelectionPositiveAdditiveMinimumCost
            (z := z)
            obsFamily
            f
            coordinateWeight
            U
            hTarget)
          maxBudget ∧
      table.acceptedParetoScalarBudgets maxBudget =
        Finset.Icc
          (ambientTargetObservationSelectionPositiveAdditiveMinimumCost
            (z := z)
            obsFamily
            f
            coordinateWeight
            U
            hTarget)
          maxBudget ∧
      table.acceptedCostBudgets maxBudget =
        table.acceptedParetoScalarBudgets maxBudget ∧
      (table.acceptedCostBudgets maxBudget).card <=
        maxBudget + 1 ∧
      (table.acceptedParetoScalarBudgets maxBudget).card <=
        maxBudget + 1 ∧
      ((table.acceptedCostBudgets maxBudget).Nonempty ↔
        ambientTargetObservationSelectionPositiveAdditiveMinimumCost
              (z := z)
              obsFamily
              f
              coordinateWeight
              U
              hTarget <=
            maxBudget) := by

  let table :=
    correctedConcreteObservationSelectionSemanticDecisionTable
      (z := z)
      obsFamily
      f
      (correctedConcreteObservationSelectionAdditiveCost
        coordinateWeight)
      U
      language

  exact
    ⟨table.acceptedPositiveAdditiveCostBudgets_eq_Icc_minimum
        hTarget
        maxBudget,
      table.acceptedParetoScalarBudgets_eq_Icc_positiveAdditiveMinimum
        hTarget
        maxBudget,
      table.acceptedPositiveAdditiveCostBudgets_eq_acceptedParetoScalarBudgets
        hTarget
        maxBudget,
      table.acceptedCostBudgets_card_le maxBudget,
      table.acceptedParetoScalarBudgets_card_le maxBudget,
      by
        rw [table.acceptedCostBudgets_nonempty_iff_terminalDecision]
        exact
          (table.positiveAdditiveDecision_equivalence_package
            hTarget
            maxBudget).2.2⟩

end BoundedDecisionSearchFinalPackage

end MCFG
