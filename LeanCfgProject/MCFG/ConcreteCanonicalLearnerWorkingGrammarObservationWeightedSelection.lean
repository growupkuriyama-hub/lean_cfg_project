/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG.ConcreteCanonicalLearnerWorkingGrammarObservationSelectionIrredundancy

/-!
# ConcreteCanonicalLearnerWorkingGrammarObservationWeightedSelection.lean

The preceding files define finite observation selections, minimum selection
cardinality, proper-subset obstructions, and coordinatewise essentiality.

This file replaces cardinality by an arbitrary natural-number cost assigned to
each finite selected set.

## General finite selection cost

Let

```lean
selectionCost : Finset ι → Nat
```

be any cost model for selected observation coordinates.

A language is selectable within cost budget `b` when there exists

```text
S ⊆ U
```

such that

```text
selectionCost S ≤ b
```

and the selected-product observation for `S` represents the language.

The least feasible cost is

```lean
correctedConcreteObservationSelectionMinimumCost.
```

It is defined by `Nat.find`, is attained by an actual selected subset, and has
the exact threshold property

```text
selection possible within cost b
  ↔
minimum cost ≤ b.
```

For every language represented by the full ambient product, the minimum cost is
at most `selectionCost U`.

## Strictly monotone costs

A cost model is strictly monotone when

```text
R ⊂ S
⇒
selectionCost R < selectionCost S.
```

Under this assumption, every minimum-cost selection is inclusion-irredundant:
no proper subset can still represent the target.

Consequently every coordinate in a minimum-cost selection is essential.  If one
coordinate is deleted, restoring it gives a strict observation refinement whose
gain class contains the target language.

The ordinary cardinality cost

```lean
selectionCost S = S.card
```

is strictly monotone, so the general weighted theory includes the preceding
minimum-cardinality irredundancy theorem as a special cost model.

## Cost lower bounds

The minimum cost has the exact obstruction form

```text
selection impossible within budget b
  ↔
b < minimum cost.
```

Equivalently, if every representing ambient subset has cost larger than `b`,
then the minimum cost is larger than `b`.

This is the weighted interface intended for future observation-design
reductions: one may assign costs to candidate interfaces and prove lower bounds
by excluding all selections within a total budget.

## Certified learner at a minimum-cost selection

When the terminal alphabet and observation monoid are finite and decidable, an
ambient-product target admits an attained minimum-cost selected product.  Its
own certified learner

* identifies the target;
* gives it a minimum certified-description rank relative to that selected
  product; and
* returns one exact checked output satisfying both the bit and finite-search
  budgets at that rank.

Under strict cost monotonicity, this minimum-cost selected product is also
inclusion-irredundant and every selected coordinate is essential.

No algorithm for computing the minimum-cost selection is asserted.
No target grammar is supplied to any learner.
No `sorry`, `admit`, or `axiom` is used.
-/

namespace MCFG

universe u v w z


section ObservationSelectionCostDefinitions

variable {ι : Type v}

/-- A finite selection cost is strictly monotone under proper subset. -/
def CorrectedConcreteObservationSelectionCostStrictlyMonotone
    (selectionCost : Finset ι → Nat) :
    Prop :=
  ∀ ⦃R S : Finset ι⦄,
    R ⊂ S →
      selectionCost R < selectionCost S

/-- The ordinary cardinality cost. -/
def correctedConcreteObservationSelectionCardinalityCost
    (S : Finset ι) :
    Nat :=
  S.card

/-- Cardinality is a strictly monotone finite selection cost. -/
theorem
    correctedConcreteObservationSelectionCardinalityCost_strictlyMonotone :
    CorrectedConcreteObservationSelectionCostStrictlyMonotone
      (correctedConcreteObservationSelectionCardinalityCost :
        Finset ι → Nat) := by

  intro R S hRS

  exact
    Finset.card_lt_card hRS

end ObservationSelectionCostDefinitions


section GenericWeightedObservationSelection

variable {α : Type u}
variable {ι : Type v}
variable {M : Type w}
variable [Monoid M]
variable {obsFamily : ι → α → M}
variable {f : Nat}
variable (selectionCost : Finset ι → Nat)

/-- A target language is representable from ambient candidates `U` by a
selection whose cost is at most `costBudget`. -/
def CorrectedConcreteObservationSelectionAtCost
    (U : Finset ι)
    (language : Set (Word α))
    (costBudget : Nat) :
    Prop :=
  ∃ S : Finset ι,
    S ⊆ U ∧
      selectionCost S <= costBudget ∧
      language ∈
        StartRootedCorrectedConcreteTargetClass
          (v := z)
          α
          (↥S → M)
          (selectedObservationProduct obsFamily S)
          f

/-- Existence of some finite selected observation product representing the
language with finite cost. -/
def HasCorrectedConcreteObservationSelectionCost
    (U : Finset ι)
    (language : Set (Word α)) :
    Prop :=
  ∃ costBudget : Nat,
    CorrectedConcreteObservationSelectionAtCost
      (obsFamily := obsFamily)
      (f := f)
      selectionCost
      U language costBudget

/-- Feasibility is upward closed in the cost budget. -/
theorem correctedConcreteObservationSelectionAtCost_mono
    {U : Finset ι}
    {language : Set (Word α)}
    {costBudget costBudget' : Nat}
    (hcost :
      costBudget <= costBudget')
    (hselection :
      CorrectedConcreteObservationSelectionAtCost
        (obsFamily := obsFamily)
        (f := f)
        selectionCost
        U language costBudget) :
    CorrectedConcreteObservationSelectionAtCost
      (obsFamily := obsFamily)
      (f := f)
      selectionCost
      U language costBudget' := by

  rcases hselection with
    ⟨S, hSU, hbound, hTarget⟩

  exact
    ⟨S,
      hSU,
      hbound.trans hcost,
      hTarget⟩

/-- Membership in the full ambient product supplies a finite-cost selection. -/
theorem
    hasCorrectedConcreteObservationSelectionCost_of_fullProductTarget
    {U : Finset ι}
    {language : Set (Word α)}
    (hTarget :
      language ∈
        StartRootedCorrectedConcreteTargetClass
          (v := z)
          α
          (↥U → M)
          (selectedObservationProduct obsFamily U)
          f) :
    HasCorrectedConcreteObservationSelectionCost
      (obsFamily := obsFamily)
      (f := f)
      selectionCost
      U language := by

  exact
    ⟨selectionCost U,
      U,
      by
        intro index hindex
        exact hindex,
      Nat.le_refl _,
      hTarget⟩

/-- Least feasible observation-selection cost. -/
noncomputable def correctedConcreteObservationSelectionMinimumCost
    {U : Finset ι}
    {language : Set (Word α)}
    (hSelection :
      HasCorrectedConcreteObservationSelectionCost
        (obsFamily := obsFamily)
        (f := f)
        selectionCost
        U language) :
    Nat :=
  Nat.find hSelection

namespace HasCorrectedConcreteObservationSelectionCost

variable {selectionCost}
variable {U : Finset ι}
variable {language : Set (Word α)}

/-- The minimum cost budget is feasible. -/
theorem minimumCost_spec
    (hSelection :
      HasCorrectedConcreteObservationSelectionCost
        (obsFamily := obsFamily)
        (f := f)
        selectionCost
        U language) :
    CorrectedConcreteObservationSelectionAtCost
      (obsFamily := obsFamily)
      (f := f)
      selectionCost
      U language
      (correctedConcreteObservationSelectionMinimumCost
        selectionCost hSelection) := by

  exact
    Nat.find_spec hSelection

/-- Minimality of the selected observation cost. -/
theorem minimumCost_le_of_selection
    (hSelection :
      HasCorrectedConcreteObservationSelectionCost
        (obsFamily := obsFamily)
        (f := f)
        selectionCost
        U language)
    {costBudget : Nat}
    (hbudget :
      CorrectedConcreteObservationSelectionAtCost
        (obsFamily := obsFamily)
        (f := f)
        selectionCost
        U language costBudget) :
    correctedConcreteObservationSelectionMinimumCost
        selectionCost hSelection <=
      costBudget := by

  exact
    Nat.find_min' hSelection hbudget

/-- Exact threshold theorem for weighted observation selection. -/
theorem selectionAtCost_iff_minimumCost_le
    (hSelection :
      HasCorrectedConcreteObservationSelectionCost
        (obsFamily := obsFamily)
        (f := f)
        selectionCost
        U language)
    (costBudget : Nat) :
    CorrectedConcreteObservationSelectionAtCost
        (obsFamily := obsFamily)
        (f := f)
        selectionCost
        U language costBudget ↔
      correctedConcreteObservationSelectionMinimumCost
          selectionCost hSelection <=
        costBudget := by

  constructor

  · exact
      hSelection.minimumCost_le_of_selection

  · intro hminimum

    exact
      correctedConcreteObservationSelectionAtCost_mono
        selectionCost
        hminimum
        hSelection.minimumCost_spec

/-- The minimum cost is attained by an actual selected subset with exactly that
cost. -/
theorem exists_selection_exact_minimumCost
    (hSelection :
      HasCorrectedConcreteObservationSelectionCost
        (obsFamily := obsFamily)
        (f := f)
        selectionCost
        U language) :
    ∃ S : Finset ι,
      S ⊆ U ∧
        selectionCost S =
          correctedConcreteObservationSelectionMinimumCost
            selectionCost hSelection ∧
        language ∈
          StartRootedCorrectedConcreteTargetClass
            (v := z)
            α
            (↥S → M)
            (selectedObservationProduct obsFamily S)
            f := by

  rcases hSelection.minimumCost_spec with
    ⟨S, hSU, hcost, hTarget⟩

  have hminimum :
      correctedConcreteObservationSelectionMinimumCost
          selectionCost hSelection <=
        selectionCost S := by

    apply
      hSelection.minimumCost_le_of_selection

    exact
      ⟨S,
        hSU,
        Nat.le_refl _,
        hTarget⟩

  exact
    ⟨S,
      hSU,
      Nat.le_antisymm
        hcost
        hminimum,
      hTarget⟩

end HasCorrectedConcreteObservationSelectionCost

end GenericWeightedObservationSelection


section CardinalityCostCompatibility

variable {α : Type u}
variable {ι : Type v}
variable {M : Type w}
variable [Monoid M]
variable {obsFamily : ι → α → M}
variable {f : Nat}
variable {U : Finset ι}
variable {language : Set (Word α)}
variable {costBudget : Nat}

/-- Weighted feasibility for the cardinality cost is exactly the preceding
cardinality-budget feasibility notion. -/
theorem observationSelectionAtCardinalityCost_iff :
    CorrectedConcreteObservationSelectionAtCost
        (obsFamily := obsFamily)
        (f := f)
        correctedConcreteObservationSelectionCardinalityCost
        U language costBudget ↔
      CorrectedConcreteObservationSelectionAtCardinality
        (obsFamily := obsFamily)
        (f := f)
        U language costBudget := by

  rfl

/-- Existence of a finite cardinality-cost selection is exactly the preceding
selection-existence notion. -/
theorem hasObservationSelectionCardinalityCost_iff :
    HasCorrectedConcreteObservationSelectionCost
        (obsFamily := obsFamily)
        (f := f)
        correctedConcreteObservationSelectionCardinalityCost
        U language ↔
      HasCorrectedConcreteObservationSelection
        (obsFamily := obsFamily)
        (f := f)
        U language := by

  rfl

end CardinalityCostCompatibility


section StrictCostMinimumIrredundancy

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

/-- An exact minimum-cost selected subset is inclusion-irredundant whenever the
cost is strictly monotone under proper subsets. -/
theorem observationSelection_exactMinimumCost_irredundant
    (hStrict :
      CorrectedConcreteObservationSelectionCostStrictlyMonotone
        selectionCost)
    (hSelection :
      HasCorrectedConcreteObservationSelectionCost
        (obsFamily := obsFamily)
        (f := f)
        selectionCost
        U language)
    {S : Finset ι}
    (hSU : S ⊆ U)
    (hcost :
      selectionCost S =
        correctedConcreteObservationSelectionMinimumCost
          selectionCost hSelection)
    (hTarget :
      language ∈
        StartRootedCorrectedConcreteTargetClass
          (v := z)
          α
          (↥S → M)
          (selectedObservationProduct obsFamily S)
          f) :
    CorrectedConcreteObservationSelectionIrredundant
      (z := z)
      α ι M obsFamily f language S := by

  refine
    ⟨hTarget,
      ?_⟩

  intro R hRS hRTarget

  have hSubsetNe :
      R ⊆ S ∧
        R ≠ S :=
    Finset.ssubset_iff_subset_ne.mp
      hRS

  have hRU :
      R ⊆ U := by

    intro index hindex

    exact
      hSU
        (hSubsetNe.1 hindex)

  have hMinimum :
      correctedConcreteObservationSelectionMinimumCost
          selectionCost hSelection <=
        selectionCost R := by

    apply
      hSelection.minimumCost_le_of_selection

    exact
      ⟨R,
        hRU,
        Nat.le_refl _,
        hRTarget⟩

  have hStrictCost :
      selectionCost R <
        selectionCost S :=
    hStrict hRS

  rw [hcost] at hStrictCost

  omega

/-- Every attained minimum-cost selection is irredundant under strict cost
monotonicity. -/
theorem
    observationSelection_exists_minimumCost_irredundant
    (hStrict :
      CorrectedConcreteObservationSelectionCostStrictlyMonotone
        selectionCost)
    (hSelection :
      HasCorrectedConcreteObservationSelectionCost
        (obsFamily := obsFamily)
        (f := f)
        selectionCost
        U language) :
    ∃ S : Finset ι,
      S ⊆ U ∧
        selectionCost S =
          correctedConcreteObservationSelectionMinimumCost
            selectionCost hSelection ∧
        CorrectedConcreteObservationSelectionIrredundant
          (z := z)
          α ι M obsFamily f language S := by

  rcases hSelection.exists_selection_exact_minimumCost with
    ⟨S, hSU, hcost, hTarget⟩

  exact
    ⟨S,
      hSU,
      hcost,
      observationSelection_exactMinimumCost_irredundant
        (z := z)
        hStrict hSelection hSU hcost hTarget⟩

/-- Every coordinate of an attained minimum-cost selection is essential under
strict cost monotonicity. -/
theorem
    observationSelection_minimumCost_coordinateEssential
    (hStrict :
      CorrectedConcreteObservationSelectionCostStrictlyMonotone
        selectionCost)
    (hSelection :
      HasCorrectedConcreteObservationSelectionCost
        (obsFamily := obsFamily)
        (f := f)
        selectionCost
        U language)
    {S : Finset ι}
    (hSU : S ⊆ U)
    (hcost :
      selectionCost S =
        correctedConcreteObservationSelectionMinimumCost
          selectionCost hSelection)
    (hTarget :
      language ∈
        StartRootedCorrectedConcreteTargetClass
          (v := z)
          α
          (↥S → M)
          (selectedObservationProduct obsFamily S)
          f)
    {index : ι}
    (hindex : index ∈ S) :
    CorrectedConcreteSelectedObservationCoordinateEssential
      (z := z)
      α ι M obsFamily f language S index := by

  exact
    observationSelection_irredundant_coordinateEssential
      (z := z)
      (observationSelection_exactMinimumCost_irredundant
        (z := z)
        hStrict hSelection hSU hcost hTarget)
      hindex

/-- Restoring any deleted coordinate of an attained minimum-cost selection is
an essential observation refinement. -/
theorem
    observationSelection_minimumCost_coordinateRefinementEssential
    (hStrict :
      CorrectedConcreteObservationSelectionCostStrictlyMonotone
        selectionCost)
    (hSelection :
      HasCorrectedConcreteObservationSelectionCost
        (obsFamily := obsFamily)
        (f := f)
        selectionCost
        U language)
    {S : Finset ι}
    (hSU : S ⊆ U)
    (hcost :
      selectionCost S =
        correctedConcreteObservationSelectionMinimumCost
          selectionCost hSelection)
    (hTarget :
      language ∈
        StartRootedCorrectedConcreteTargetClass
          (v := z)
          α
          (↥S → M)
          (selectedObservationProduct obsFamily S)
          f)
    {index : ι}
    (hindex : index ∈ S) :
    CorrectedConcreteObservationRefinementEssential
      (z := z)
      α
      (↥(S.erase index) → M)
      (↥S → M)
      (selectedObservationProduct obsFamily (S.erase index))
      (selectedObservationProduct obsFamily S)
      f := by

  exact
    observationSelection_irredundant_coordinateRefinementEssential
      (z := z)
      (observationSelection_exactMinimumCost_irredundant
        (z := z)
        hStrict hSelection hSU hcost hTarget)
      hindex

end StrictCostMinimumIrredundancy


section WeightedSelectionCostObstructions

variable {α : Type u}
variable {ι : Type v}
variable {M : Type w}
variable [Monoid M]
variable {obsFamily : ι → α → M}
variable {f : Nat}
variable {selectionCost : Finset ι → Nat}
variable {U : Finset ι}
variable {language : Set (Word α)}

/-- Exact obstruction form of the minimum observation-selection cost. -/
theorem observationSelection_not_atCost_iff_lt_minimumCost
    (hSelection :
      HasCorrectedConcreteObservationSelectionCost
        (obsFamily := obsFamily)
        (f := f)
        selectionCost
        U language)
    (costBudget : Nat) :
    ¬
        CorrectedConcreteObservationSelectionAtCost
          (obsFamily := obsFamily)
          (f := f)
          selectionCost
          U language costBudget ↔
      costBudget <
        correctedConcreteObservationSelectionMinimumCost
          selectionCost hSelection := by

  constructor

  · intro hNot

    by_contra hNotLt

    have hMinimum :
        correctedConcreteObservationSelectionMinimumCost
            selectionCost hSelection <=
          costBudget := by
      omega

    exact
      hNot
        ((hSelection.selectionAtCost_iff_minimumCost_le
          costBudget).mpr
          hMinimum)

  · intro hLt hAtCost

    have hMinimum :
        correctedConcreteObservationSelectionMinimumCost
            selectionCost hSelection <=
          costBudget :=
      (hSelection.selectionAtCost_iff_minimumCost_le
        costBudget).mp
        hAtCost

    omega

/-- Excluding every ambient selection within a cost budget gives a strict lower
bound on the minimum cost. -/
theorem
    observationSelection_minimumCost_gt_of_all_boundedCost_selections_fail
    (hSelection :
      HasCorrectedConcreteObservationSelectionCost
        (obsFamily := obsFamily)
        (f := f)
        selectionCost
        U language)
    (costBudget : Nat)
    (hFail :
      ∀ S : Finset ι,
        S ⊆ U →
        selectionCost S <= costBudget →
        language ∉
          StartRootedCorrectedConcreteTargetClass
            (v := z)
            α
            (↥S → M)
            (selectedObservationProduct obsFamily S)
            f) :
    costBudget <
      correctedConcreteObservationSelectionMinimumCost
        selectionCost hSelection := by

  apply
    (observationSelection_not_atCost_iff_lt_minimumCost
      hSelection costBudget).mp

  intro hAtCost

  rcases hAtCost with
    ⟨S, hSU, hcost, hTarget⟩

  exact
    hFail S hSU hcost hTarget

/-- Exact weighted lower-bound criterion. -/
theorem
    observationSelection_minimumCost_gt_iff_all_boundedCost_selections_fail
    (hSelection :
      HasCorrectedConcreteObservationSelectionCost
        (obsFamily := obsFamily)
        (f := f)
        selectionCost
        U language)
    (costBudget : Nat) :
    costBudget <
        correctedConcreteObservationSelectionMinimumCost
          selectionCost hSelection ↔
      ∀ S : Finset ι,
        S ⊆ U →
        selectionCost S <= costBudget →
        language ∉
          StartRootedCorrectedConcreteTargetClass
            (v := z)
            α
            (↥S → M)
            (selectedObservationProduct obsFamily S)
            f := by

  constructor

  · intro hLower S hSU hcost hTarget

    have hAtCost :
        CorrectedConcreteObservationSelectionAtCost
          (obsFamily := obsFamily)
          (f := f)
          selectionCost
          U language costBudget :=
      ⟨S,
        hSU,
        hcost,
        hTarget⟩

    exact
      (observationSelection_not_atCost_iff_lt_minimumCost
        hSelection costBudget).mpr
        hLower
        hAtCost

  · intro hFail

    exact
      observationSelection_minimumCost_gt_of_all_boundedCost_selections_fail
        hSelection costBudget hFail

/-- Compact weighted selection obstruction package. -/
theorem observationSelectionMinimumCost_obstruction_package
    (hSelection :
      HasCorrectedConcreteObservationSelectionCost
        (obsFamily := obsFamily)
        (f := f)
        selectionCost
        U language) :
    (∀ costBudget : Nat,
      (¬
        CorrectedConcreteObservationSelectionAtCost
          (obsFamily := obsFamily)
          (f := f)
          selectionCost
          U language costBudget ↔
        costBudget <
          correctedConcreteObservationSelectionMinimumCost
            selectionCost hSelection)) ∧
      (∀ costBudget : Nat,
        (costBudget <
            correctedConcreteObservationSelectionMinimumCost
              selectionCost hSelection ↔
          ∀ S : Finset ι,
            S ⊆ U →
            selectionCost S <= costBudget →
            language ∉
              StartRootedCorrectedConcreteTargetClass
                (v := z)
                α
                (↥S → M)
                (selectedObservationProduct obsFamily S)
                f)) := by

  exact
    ⟨fun costBudget =>
        observationSelection_not_atCost_iff_lt_minimumCost
          hSelection costBudget,
      fun costBudget =>
        observationSelection_minimumCost_gt_iff_all_boundedCost_selections_fail
          hSelection costBudget⟩

end WeightedSelectionCostObstructions


section AmbientWeightedObservationSelection

variable {α : Type u}
variable {ι : Type v}
variable {M : Type w}
variable [Monoid M]
variable (obsFamily : ι → α → M)
variable (f : Nat)
variable (selectionCost : Finset ι → Nat)
variable (U : Finset ι)

/-- Minimum selected-observation cost for a language represented by the full
ambient product. -/
noncomputable def ambientTargetObservationSelectionMinimumCost
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
  correctedConcreteObservationSelectionMinimumCost
    selectionCost
    (hasCorrectedConcreteObservationSelectionCost_of_fullProductTarget
      (obsFamily := obsFamily)
      (f := f)
      selectionCost
      hTarget)

/-- The minimum selected-observation cost is no greater than the cost of the
complete ambient candidate set. -/
theorem ambientTargetObservationSelectionMinimumCost_le
    {language : Set (Word α)}
    (hTarget :
      language ∈
        StartRootedCorrectedConcreteTargetClass
          (v := z)
          α
          (↥U → M)
          (selectedObservationProduct obsFamily U)
          f) :
    ambientTargetObservationSelectionMinimumCost
        (z := z)
        obsFamily f selectionCost U hTarget <=
      selectionCost U := by

  unfold
    ambientTargetObservationSelectionMinimumCost

  let hSelection :=
    hasCorrectedConcreteObservationSelectionCost_of_fullProductTarget
      (obsFamily := obsFamily)
      (f := f)
      selectionCost
      hTarget

  apply
    hSelection.minimumCost_le_of_selection

  exact
    ⟨U,
      by
        intro index hindex
        exact hindex,
      Nat.le_refl _,
      hTarget⟩

/-- An ambient-product target has an actual minimum-cost selected subset. -/
theorem ambientTarget_exists_minimumCostObservationSelection
    {language : Set (Word α)}
    (hTarget :
      language ∈
        StartRootedCorrectedConcreteTargetClass
          (v := z)
          α
          (↥U → M)
          (selectedObservationProduct obsFamily U)
          f) :
    ∃ S : Finset ι,
      S ⊆ U ∧
        selectionCost S =
          ambientTargetObservationSelectionMinimumCost
            (z := z)
            obsFamily f selectionCost U hTarget ∧
        language ∈
          StartRootedCorrectedConcreteTargetClass
            (v := z)
            α
            (↥S → M)
            (selectedObservationProduct obsFamily S)
            f := by

  unfold
    ambientTargetObservationSelectionMinimumCost

  exact
    (hasCorrectedConcreteObservationSelectionCost_of_fullProductTarget
      (obsFamily := obsFamily)
      (f := f)
      selectionCost
      hTarget).exists_selection_exact_minimumCost

end AmbientWeightedObservationSelection


section AmbientStrictWeightedIrredundancy

variable {α : Type u}
variable {ι : Type v}
variable {M : Type w}
variable [DecidableEq ι]
variable [Monoid M]
variable (obsFamily : ι → α → M)
variable (f : Nat)
variable (selectionCost : Finset ι → Nat)
variable (U : Finset ι)
variable (hStrict :
  CorrectedConcreteObservationSelectionCostStrictlyMonotone
    selectionCost)

/-- Under strict cost monotonicity, every ambient-product target has an actual
minimum-cost selected subset that is irredundant and coordinatewise essential. -/
theorem
    ambientTarget_exists_minimumCostIrredundantObservationSelection
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
        selectionCost S =
          ambientTargetObservationSelectionMinimumCost
            (z := z)
            obsFamily f selectionCost U hTarget ∧
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

  let hSelection :=
    hasCorrectedConcreteObservationSelectionCost_of_fullProductTarget
      (obsFamily := obsFamily)
      (f := f)
      selectionCost
      hTarget

  rcases hSelection.exists_selection_exact_minimumCost with
    ⟨S, hSU, hcost, hSelected⟩

  have hIrredundant :
      CorrectedConcreteObservationSelectionIrredundant
        (z := z)
        α ι M obsFamily f language S := by

    apply
      observationSelection_exactMinimumCost_irredundant
        (z := z)
        hStrict hSelection hSU

    · simpa [
        ambientTargetObservationSelectionMinimumCost,
        hSelection
      ] using hcost

    · exact hSelected

  exact
    ⟨S,
      hSU,
      by
        simpa [
          ambientTargetObservationSelectionMinimumCost,
          hSelection
        ] using hcost,
      hIrredundant,
      fun index hindex =>
        observationSelection_irredundant_coordinateRefinementEssential
          (z := z)
          hIrredundant hindex⟩

end AmbientStrictWeightedIrredundancy


section MinimumCostCertifiedLearner

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
variable (selectionCost : Finset ι → Nat)
variable (U : Finset ι)

/-- An ambient-product target admits a minimum-cost selected product whose own
certified learner identifies the target and returns an exact minimum-rank
checked description. -/
theorem ambientTarget_exists_minimumCostCertifiedObservationSelection
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
      selectionCost S =
          ambientTargetObservationSelectionMinimumCost
            (z := z)
            obsFamily f selectionCost U hTarget ∧
        IdentifiesLanguageFromPositiveData
          (correctedConcreteCertifiedWorkingGrammarHypLanguage
            (selectedObservationProduct obsFamily S)
            f)
          (correctedConcreteCertifiedWorkingGrammarLearner
            hα
            (selectedObservationProduct obsFamily S)
            f)
          language ∧
        language ∈
          CorrectedConcreteCertifiedRankProfileClass
            (α := α)
            (M := ↥S → M)
            (selectedObservationProduct obsFamily S)
            f
            (startRootedTargetCertifiedDescriptionRank
              (v := z)
              hα
              (selectedObservationProduct obsFamily S)
              f
              hSelected) ∧
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
      ambientTarget_exists_minimumCostObservationSelection
        (z := z)
        obsFamily f selectionCost U hTarget with
    ⟨S, hSU, hcost, hSelected⟩

  exact
    ⟨S,
      hSU,
      hSelected,
      hcost,
      selectedProductCertifiedLearner_identifies_targetClass
        (z := z)
        hα obsFamily f S
        language hSelected,
      startRootedTarget_mem_minimumCertifiedDescriptionRankProfile
        (v := z)
        hα
        (selectedObservationProduct obsFamily S)
        f
        hSelected,
      startRootedTarget_exists_output_at_minimumCertifiedDescriptionRank
        (v := z)
        hα
        (selectedObservationProduct obsFamily S)
        f
        hSelected⟩

end MinimumCostCertifiedLearner


section StrictMinimumCostCertifiedLearner

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
variable (selectionCost : Finset ι → Nat)
variable (U : Finset ι)
variable (hStrict :
  CorrectedConcreteObservationSelectionCostStrictlyMonotone
    selectionCost)

/-- Under strict cost monotonicity, an ambient-product target admits an
irredundant minimum-cost selected product whose own certified learner identifies
the target. -/
theorem
    ambientTarget_exists_minimumCostIrredundantCertifiedObservationSelection
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
      selectionCost S =
          ambientTargetObservationSelectionMinimumCost
            (z := z)
            obsFamily f selectionCost U hTarget ∧
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
      ambientTarget_exists_minimumCostCertifiedObservationSelection
        (z := z)
        hα obsFamily f selectionCost U hTarget with
    ⟨S,
      hSU,
      hSelected,
      hcost,
      hIdentifies,
      hProfile,
      C,
      hLanguage,
      hBits,
      hSearch⟩

  let hSelection :=
    hasCorrectedConcreteObservationSelectionCost_of_fullProductTarget
      (obsFamily := obsFamily)
      (f := f)
      selectionCost
      hTarget

  have hIrredundant :
      CorrectedConcreteObservationSelectionIrredundant
        (z := z)
        α ι M obsFamily f language S := by

    apply
      observationSelection_exactMinimumCost_irredundant
        (z := z)
        hStrict hSelection hSU

    · simpa [
        ambientTargetObservationSelectionMinimumCost,
        hSelection
      ] using hcost

    · exact hSelected

  exact
    ⟨S,
      hSU,
      hSelected,
      hcost,
      hIrredundant,
      fun index hindex =>
        observationSelection_irredundant_coordinateRefinementEssential
          (z := z)
          hIrredundant hindex,
      hIdentifies,
      C,
      hLanguage,
      hBits,
      hSearch⟩

end StrictMinimumCostCertifiedLearner


section ObservationWeightedSelectionFinalPackage

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
variable (selectionCost : Finset ι → Nat)
variable (U : Finset ι)

/-- Final weighted observation-selection, obstruction, and certified-learning
package. -/
theorem
    correctedConcreteCertifiedWorkingGrammar_observationWeightedSelection_package :
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
      ambientTargetObservationSelectionMinimumCost
          (z := z)
          obsFamily f selectionCost U hTarget <=
        selectionCost U) ∧
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
              ambientTargetObservationSelectionMinimumCost
                (z := z)
                obsFamily f selectionCost U hTarget ↔
            ∀ S : Finset ι,
              S ⊆ U →
              selectionCost S <= costBudget →
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
          selectionCost S =
              ambientTargetObservationSelectionMinimumCost
                (z := z)
                obsFamily f selectionCost U hTarget ∧
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
                    f) := by

  refine
    ⟨?_,
      ?_,
      ?_⟩

  · intro language hTarget

    exact
      ambientTargetObservationSelectionMinimumCost_le
        (z := z)
        obsFamily f selectionCost U hTarget

  · intro language hTarget costBudget

    let hSelection :=
      hasCorrectedConcreteObservationSelectionCost_of_fullProductTarget
        (obsFamily := obsFamily)
        (f := f)
        selectionCost
        hTarget

    simpa [
      ambientTargetObservationSelectionMinimumCost,
      hSelection
    ] using
      observationSelection_minimumCost_gt_iff_all_boundedCost_selections_fail
        hSelection costBudget

  · intro language hTarget

    rcases
        ambientTarget_exists_minimumCostCertifiedObservationSelection
          (z := z)
          hα obsFamily f selectionCost U hTarget with
      ⟨S,
        hSU,
        hSelected,
        hcost,
        hIdentifies,
        hProfile,
        C,
        hLanguage,
        hBits,
        hSearch⟩

    exact
      ⟨S,
        hSU,
        hSelected,
        hcost,
        hIdentifies,
        C,
        hLanguage,
        hBits,
        hSearch⟩

/-- Final strict-cost minimum irredundancy and certified-learning package. -/
theorem
    correctedConcreteCertifiedWorkingGrammar_observationStrictWeightedSelection_package
    (hStrict :
      CorrectedConcreteObservationSelectionCostStrictlyMonotone
        selectionCost) :
    ∀
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
        selectionCost S =
            ambientTargetObservationSelectionMinimumCost
              (z := z)
              obsFamily f selectionCost U hTarget ∧
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

  intro language hTarget

  exact
    ambientTarget_exists_minimumCostIrredundantCertifiedObservationSelection
      (z := z)
      hα obsFamily f selectionCost U hStrict hTarget

end ObservationWeightedSelectionFinalPackage

end MCFG
