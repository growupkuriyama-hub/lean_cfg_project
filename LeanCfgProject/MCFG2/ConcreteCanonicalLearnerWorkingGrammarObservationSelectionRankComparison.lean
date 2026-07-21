/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG2.ConcreteCanonicalLearnerWorkingGrammarObservationSelectionRank

/-!
# ConcreteCanonicalLearnerWorkingGrammarObservationSelectionRankComparison.lean

The preceding file defines cumulative observation-selection cost profiles,
exact cost-rank shells, and the unique semantic selection rank of every target
represented by a finite ambient product.

This file compares those hierarchies when the cost model changes.

## Pointwise comparison of costs

For two costs

```lean
selectionCost₀ selectionCost₁ : Finset ι → Nat
```

write

```lean
selectionCost₀ ≤ₚ selectionCost₁
```

when

```text
selectionCost₀ S ≤ selectionCost₁ S
```

for every finite selected set `S`.

A selection feasible within budget `b` for the more expensive cost
`selectionCost₁` is also feasible within budget `b` for the cheaper cost
`selectionCost₀`.

Consequently:

```text
Profile(cost₁,b) ⊆ Profile(cost₀,b),

BudgetLayer(cost₁,b) ⊆ BudgetLayer(cost₀,b),

minimumCost(cost₀,L) ≤ minimumCost(cost₁,L).
```

Thus cheaper cost models give larger cumulative profile classes and no larger
selection ranks.

## Exact-shell comparison

An exact rank-`r` target for the more expensive cost need not have exact rank
`r` for the cheaper cost: its rank may decrease.

We prove the precise replacement:

```text
L ∈ ExactRank(cost₁,r)
⇒
∃ r₀ ≤ r, L ∈ ExactRank(cost₀,r₀).
```

If the two costs are pointwise equal, then all cumulative profiles, budget
filtrations, exact-rank shells, and target ranks are equal.

## Rank obstructions

Because the more expensive profile is contained in the cheaper profile,

```text
L ∉ Profile(cost₀,b)
⇒
L ∉ Profile(cost₁,b).
```

A lower bound proved even for a cheaper cost model therefore transports to every
more expensive model.

## Additive-weight consequences

For every coordinate-weight function,

```text
cardinalityCost(S)
  ≤
positiveAdditiveCost(weight,S),

additiveCost(weight,S)
  ≤
positiveAdditiveCost(weight,S).
```

Hence the cardinality selection rank and the unshifted additive-weight rank are
both bounded above by the positive-additive selection rank.

Coordinatewise larger weights produce pointwise larger additive and positive
additive costs, and therefore no smaller selection ranks.

With zero extra coordinate weights, positive additive cost is pointwise
equivalent to cardinality cost, so the two rank hierarchies coincide exactly.

## Certified comparison

For a full ambient-product target and two pointwise ordered costs, the minimum
selectors for both costs carry their own certified learners.  Their observation
selection ranks satisfy the expected inequality, while both selected-product
learners identify the same target language and return exact checked outputs at
their respective minimum certified-description ranks.

No comparison between the two grammar-description ranks is asserted.

No target grammar is supplied to any learner.
No `sorry`, `admit`, or `axiom` is used.
-/

namespace MCFG

universe u v w z


section ObservationSelectionCostComparisonDefinitions

variable {ι : Type v}

/-- Pointwise order on finite observation-selection costs. -/
def CorrectedConcreteObservationSelectionCostPointwiseLe
    (selectionCost₀ selectionCost₁ : Finset ι → Nat) :
    Prop :=
  ∀ S : Finset ι,
    selectionCost₀ S <= selectionCost₁ S

/-- Pointwise equivalence of finite observation-selection costs. -/
def CorrectedConcreteObservationSelectionCostPointwiseEquivalent
    (selectionCost₀ selectionCost₁ : Finset ι → Nat) :
    Prop :=
  CorrectedConcreteObservationSelectionCostPointwiseLe
      selectionCost₀ selectionCost₁ ∧
    CorrectedConcreteObservationSelectionCostPointwiseLe
      selectionCost₁ selectionCost₀

/-- Pointwise cost order is reflexive. -/
theorem observationSelectionCostPointwiseLe_refl
    (selectionCost : Finset ι → Nat) :
    CorrectedConcreteObservationSelectionCostPointwiseLe
      selectionCost selectionCost := by

  intro S
  exact Nat.le_refl _

/-- Pointwise cost order is transitive. -/
theorem observationSelectionCostPointwiseLe_trans
    {selectionCost₀ selectionCost₁ selectionCost₂ :
      Finset ι → Nat}
    (h₀₁ :
      CorrectedConcreteObservationSelectionCostPointwiseLe
        selectionCost₀ selectionCost₁)
    (h₁₂ :
      CorrectedConcreteObservationSelectionCostPointwiseLe
        selectionCost₁ selectionCost₂) :
    CorrectedConcreteObservationSelectionCostPointwiseLe
      selectionCost₀ selectionCost₂ := by

  intro S

  exact
    (h₀₁ S).trans
      (h₁₂ S)

/-- Pointwise equivalent natural-number costs are equal as functions. -/
theorem observationSelectionCost_eq_of_pointwiseEquivalent
    {selectionCost₀ selectionCost₁ : Finset ι → Nat}
    (hEquivalent :
      CorrectedConcreteObservationSelectionCostPointwiseEquivalent
        selectionCost₀ selectionCost₁) :
    selectionCost₀ =
      selectionCost₁ := by

  funext S

  exact
    Nat.le_antisymm
      (hEquivalent.1 S)
      (hEquivalent.2 S)

end ObservationSelectionCostComparisonDefinitions


section ObservationSelectionFeasibilityComparison

variable {α : Type u}
variable {ι : Type v}
variable {M : Type w}
variable [Monoid M]
variable {obsFamily : ι → α → M}
variable {f : Nat}
variable {selectionCost₀ selectionCost₁ : Finset ι → Nat}
variable {U : Finset ι}
variable {language : Set (Word α)}

/-- Feasibility for a more expensive cost implies feasibility for a cheaper
pointwise cost at the same budget. -/
theorem observationSelectionAtCost_of_pointwiseLe
    (hCost :
      CorrectedConcreteObservationSelectionCostPointwiseLe
        selectionCost₀ selectionCost₁)
    {costBudget : Nat}
    (hSelection :
      CorrectedConcreteObservationSelectionAtCost
        (obsFamily := obsFamily)
        (f := f)
        selectionCost₁
        U
        language
        costBudget) :
    CorrectedConcreteObservationSelectionAtCost
      (obsFamily := obsFamily)
      (f := f)
      selectionCost₀
      U
      language
      costBudget := by

  rcases hSelection with
    ⟨S, hSU, hCost₁, hTarget⟩

  exact
    ⟨S,
      hSU,
      (hCost S).trans hCost₁,
      hTarget⟩

/-- Existence of a selection for a more expensive cost implies existence for a
cheaper pointwise cost. -/
theorem hasObservationSelectionCost_of_pointwiseLe
    (hCost :
      CorrectedConcreteObservationSelectionCostPointwiseLe
        selectionCost₀ selectionCost₁)
    (hSelection :
      HasCorrectedConcreteObservationSelectionCost
        (obsFamily := obsFamily)
        (f := f)
        selectionCost₁
        U
        language) :
    HasCorrectedConcreteObservationSelectionCost
      (obsFamily := obsFamily)
      (f := f)
      selectionCost₀
      U
      language := by

  rcases hSelection with
    ⟨costBudget, hAtCost⟩

  exact
    ⟨costBudget,
      observationSelectionAtCost_of_pointwiseLe
        hCost hAtCost⟩

/-- A more expensive cumulative profile is contained in the corresponding
cheaper cumulative profile. -/
theorem observationSelectionCostProfileClass_subset_of_pointwiseLe
    (hCost :
      CorrectedConcreteObservationSelectionCostPointwiseLe
        selectionCost₀ selectionCost₁)
    (costBudget : Nat) :
    CorrectedConcreteObservationSelectionCostProfileClass
        (z := z)
        α
        ι
        M
        obsFamily
        f
        selectionCost₁
        U
        costBudget ⊆
      CorrectedConcreteObservationSelectionCostProfileClass
        (z := z)
        α
        ι
        M
        obsFamily
        f
        selectionCost₀
        U
        costBudget := by

  intro target hTarget

  exact
    observationSelectionAtCost_of_pointwiseLe
      hCost hTarget

/-- A lower-bound obstruction for the cheaper cost transports to the more
expensive cost. -/
theorem observationSelection_not_mem_expensiveProfile_of_not_mem_cheaperProfile
    (hCost :
      CorrectedConcreteObservationSelectionCostPointwiseLe
        selectionCost₀ selectionCost₁)
    {costBudget : Nat}
    (hNot :
      language ∉
        CorrectedConcreteObservationSelectionCostProfileClass
          (z := z)
          α
          ι
          M
          obsFamily
          f
          selectionCost₀
          U
          costBudget) :
    language ∉
      CorrectedConcreteObservationSelectionCostProfileClass
        (z := z)
        α
        ι
        M
        obsFamily
        f
        selectionCost₁
        U
        costBudget := by

  intro hExpensive

  exact
    hNot
      (observationSelectionCostProfileClass_subset_of_pointwiseLe
        (z := z)
        hCost
        costBudget
        hExpensive)

end ObservationSelectionFeasibilityComparison


section ObservationBudgetFiltrationComparison

variable {α : Type u}
variable {ι : Type v}
variable {M : Type w}
variable [DecidableEq ι]
variable [Monoid M]
variable {obsFamily : ι → α → M}
variable {f : Nat}
variable {selectionCost₀ selectionCost₁ : Finset ι → Nat}
variable {U : Finset ι}
variable {language : Set (Word α)}

/-- Every budget layer for a more expensive cost is contained in the same
budget layer for a cheaper pointwise cost. -/
theorem observationCostBudgetFiltration_subset_of_pointwiseLe
    (hCost :
      CorrectedConcreteObservationSelectionCostPointwiseLe
        selectionCost₀ selectionCost₁)
    (costBudget : Nat) :
    correctedConcreteObservationCostBudgetFiltration
        (z := z)
        obsFamily
        f
        selectionCost₁
        U
        language
        costBudget ⊆
      correctedConcreteObservationCostBudgetFiltration
        (z := z)
        obsFamily
        f
        selectionCost₀
        U
        language
        costBudget := by

  intro S hS

  rcases
      (mem_correctedConcreteObservationCostBudgetFiltration_iff
        (z := z)).mp
        hS with
    ⟨hSU, hCost₁, hTarget⟩

  exact
    (mem_correctedConcreteObservationCostBudgetFiltration_iff
      (z := z)).mpr
      ⟨hSU,
        (hCost S).trans hCost₁,
        hTarget⟩

/-- Pointwise equivalent costs give identical budget filtrations. -/
theorem observationCostBudgetFiltration_eq_of_pointwiseEquivalent
    (hEquivalent :
      CorrectedConcreteObservationSelectionCostPointwiseEquivalent
        selectionCost₀ selectionCost₁)
    (costBudget : Nat) :
    correctedConcreteObservationCostBudgetFiltration
        (z := z)
        obsFamily
        f
        selectionCost₀
        U
        language
        costBudget =
      correctedConcreteObservationCostBudgetFiltration
        (z := z)
        obsFamily
        f
        selectionCost₁
        U
        language
        costBudget := by

  apply Finset.Subset.antisymm

  · exact
      observationCostBudgetFiltration_subset_of_pointwiseLe
        (z := z)
        hEquivalent.2
        costBudget

  · exact
      observationCostBudgetFiltration_subset_of_pointwiseLe
        (z := z)
        hEquivalent.1
        costBudget

end ObservationBudgetFiltrationComparison


section ObservationSelectionMinimumCostComparison

variable {α : Type u}
variable {ι : Type v}
variable {M : Type w}
variable [Monoid M]
variable {obsFamily : ι → α → M}
variable {f : Nat}
variable {selectionCost₀ selectionCost₁ : Finset ι → Nat}
variable {U : Finset ι}
variable {language : Set (Word α)}

/-- Pointwise cheaper selection cost has no larger semantic minimum. -/
theorem observationSelectionMinimumCost_le_of_pointwiseLe
    (hCost :
      CorrectedConcreteObservationSelectionCostPointwiseLe
        selectionCost₀ selectionCost₁)
    (hSelection₀ :
      HasCorrectedConcreteObservationSelectionCost
        (obsFamily := obsFamily)
        (f := f)
        selectionCost₀
        U
        language)
    (hSelection₁ :
      HasCorrectedConcreteObservationSelectionCost
        (obsFamily := obsFamily)
        (f := f)
        selectionCost₁
        U
        language) :
    correctedConcreteObservationSelectionMinimumCost
        selectionCost₀
        hSelection₀ <=
      correctedConcreteObservationSelectionMinimumCost
        selectionCost₁
        hSelection₁ := by

  rcases hSelection₁.exists_selection_exact_minimumCost with
    ⟨S, hSU, hCost₁, hTarget⟩

  have hMinimum₀ :
      correctedConcreteObservationSelectionMinimumCost
          selectionCost₀
          hSelection₀ <=
        selectionCost₀ S := by

    apply
      hSelection₀.minimumCost_le_of_selection

    exact
      ⟨S,
        hSU,
        Nat.le_refl _,
        hTarget⟩

  have hPointwise :
      selectionCost₀ S <=
        selectionCost₁ S :=
    hCost S

  rw [hCost₁] at hPointwise

  exact
    hMinimum₀.trans
      hPointwise

/-- Pointwise equivalent costs have equal semantic minima. -/
theorem observationSelectionMinimumCost_eq_of_pointwiseEquivalent
    (hEquivalent :
      CorrectedConcreteObservationSelectionCostPointwiseEquivalent
        selectionCost₀ selectionCost₁)
    (hSelection₀ :
      HasCorrectedConcreteObservationSelectionCost
        (obsFamily := obsFamily)
        (f := f)
        selectionCost₀
        U
        language)
    (hSelection₁ :
      HasCorrectedConcreteObservationSelectionCost
        (obsFamily := obsFamily)
        (f := f)
        selectionCost₁
        U
        language) :
    correctedConcreteObservationSelectionMinimumCost
        selectionCost₀
        hSelection₀ =
      correctedConcreteObservationSelectionMinimumCost
        selectionCost₁
        hSelection₁ := by

  apply Nat.le_antisymm

  · exact
      observationSelectionMinimumCost_le_of_pointwiseLe
        hEquivalent.1
        hSelection₀
        hSelection₁

  · exact
      observationSelectionMinimumCost_le_of_pointwiseLe
        hEquivalent.2
        hSelection₁
        hSelection₀

end ObservationSelectionMinimumCostComparison


section ExactRankShellComparison

variable {α : Type u}
variable {ι : Type v}
variable {M : Type w}
variable [Monoid M]
variable {obsFamily : ι → α → M}
variable {f : Nat}
variable {selectionCost₀ selectionCost₁ : Finset ι → Nat}
variable {U : Finset ι}
variable {language : Set (Word α)}

/-- An exact rank under a more expensive cost becomes some no-larger exact rank
under a cheaper pointwise cost. -/
theorem
    observationSelection_exactExpensiveRank_exists_cheaperRank_le
    (hCost :
      CorrectedConcreteObservationSelectionCostPointwiseLe
        selectionCost₀ selectionCost₁)
    {rank₁ : Nat}
    (hRank₁ :
      language ∈
        CorrectedConcreteObservationSelectionExactCostRankClass
          (z := z)
          α
          ι
          M
          obsFamily
          f
          selectionCost₁
          U
          rank₁) :
    ∃ rank₀ : Nat,
      rank₀ <= rank₁ ∧
        language ∈
          CorrectedConcreteObservationSelectionExactCostRankClass
            (z := z)
            α
            ι
            M
            obsFamily
            f
            selectionCost₀
            U
            rank₀ := by

  let hSelection₀ :
      HasCorrectedConcreteObservationSelectionCost
        (obsFamily := obsFamily)
        (f := f)
        selectionCost₀
        U
        language :=
    ⟨rank₁,
      observationSelectionAtCost_of_pointwiseLe
        hCost
        hRank₁.1⟩

  let rank₀ :=
    correctedConcreteObservationSelectionMinimumCost
      selectionCost₀
      hSelection₀

  have hRank₀Le :
      rank₀ <= rank₁ := by

    exact
      hSelection₀.minimumCost_le_of_selection
        (observationSelectionAtCost_of_pointwiseLe
          hCost
          hRank₁.1)

  exact
    ⟨rank₀,
      hRank₀Le,
      observationSelection_mem_exactMinimumCostRankClass
        (z := z)
        hSelection₀⟩

/-- Pointwise equivalent costs give identical cumulative profile classes. -/
theorem observationSelectionCostProfileClass_eq_of_pointwiseEquivalent
    (hEquivalent :
      CorrectedConcreteObservationSelectionCostPointwiseEquivalent
        selectionCost₀ selectionCost₁)
    (costBudget : Nat) :
    CorrectedConcreteObservationSelectionCostProfileClass
        (z := z)
        α
        ι
        M
        obsFamily
        f
        selectionCost₀
        U
        costBudget =
      CorrectedConcreteObservationSelectionCostProfileClass
        (z := z)
        α
        ι
        M
        obsFamily
        f
        selectionCost₁
        U
        costBudget := by

  apply Set.Subset.antisymm

  · exact
      observationSelectionCostProfileClass_subset_of_pointwiseLe
        (z := z)
        hEquivalent.2
        costBudget

  · exact
      observationSelectionCostProfileClass_subset_of_pointwiseLe
        (z := z)
        hEquivalent.1
        costBudget

/-- Pointwise equivalent costs give identical exact-rank shells. -/
theorem observationSelectionExactCostRankClass_eq_of_pointwiseEquivalent
    (hEquivalent :
      CorrectedConcreteObservationSelectionCostPointwiseEquivalent
        selectionCost₀ selectionCost₁)
    (rank : Nat) :
    CorrectedConcreteObservationSelectionExactCostRankClass
        (z := z)
        α
        ι
        M
        obsFamily
        f
        selectionCost₀
        U
        rank =
      CorrectedConcreteObservationSelectionExactCostRankClass
        (z := z)
        α
        ι
        M
        obsFamily
        f
        selectionCost₁
        U
        rank := by

  ext target

  constructor

  · intro hRank₀

    refine
      ⟨observationSelectionAtCost_of_pointwiseLe
          hEquivalent.2
          hRank₀.1,
        ?_⟩

    intro costBudget hBudget hAtCost₁

    exact
      hRank₀.2
        costBudget
        hBudget
        (observationSelectionAtCost_of_pointwiseLe
          hEquivalent.1
          hAtCost₁)

  · intro hRank₁

    refine
      ⟨observationSelectionAtCost_of_pointwiseLe
          hEquivalent.1
          hRank₁.1,
        ?_⟩

    intro costBudget hBudget hAtCost₀

    exact
      hRank₁.2
        costBudget
        hBudget
        (observationSelectionAtCost_of_pointwiseLe
          hEquivalent.2
          hAtCost₀)

end ExactRankShellComparison


section AmbientTargetRankComparison

variable {α : Type u}
variable {ι : Type v}
variable {M : Type w}
variable [Monoid M]
variable (obsFamily : ι → α → M)
variable (f : Nat)
variable (selectionCost₀ selectionCost₁ : Finset ι → Nat)
variable (U : Finset ι)

/-- Pointwise cheaper cost gives no larger paper-facing observation-selection
rank for every full ambient-product target. -/
theorem ambientTargetObservationSelectionCostRank_le_of_pointwiseLe
    (hCost :
      CorrectedConcreteObservationSelectionCostPointwiseLe
        selectionCost₀ selectionCost₁)
    {language : Set (Word α)}
    (hTarget :
      language ∈
        StartRootedCorrectedConcreteTargetClass
          (v := z)
          α
          (↥U → M)
          (selectedObservationProduct obsFamily U)
          f) :
    ambientTargetObservationSelectionCostRank
        (z := z)
        obsFamily
        f
        selectionCost₀
        U
        hTarget <=
      ambientTargetObservationSelectionCostRank
        (z := z)
        obsFamily
        f
        selectionCost₁
        U
        hTarget := by

  let hSelection₀ :=
    hasCorrectedConcreteObservationSelectionCost_of_fullProductTarget
      (obsFamily := obsFamily)
      (f := f)
      selectionCost₀
      hTarget

  let hSelection₁ :=
    hasCorrectedConcreteObservationSelectionCost_of_fullProductTarget
      (obsFamily := obsFamily)
      (f := f)
      selectionCost₁
      hTarget

  simpa [
    ambientTargetObservationSelectionCostRank,
    ambientTargetObservationSelectionMinimumCost,
    hSelection₀,
    hSelection₁
  ] using
    observationSelectionMinimumCost_le_of_pointwiseLe
      hCost
      hSelection₀
      hSelection₁

/-- Pointwise equivalent costs give equal paper-facing target ranks. -/
theorem ambientTargetObservationSelectionCostRank_eq_of_pointwiseEquivalent
    (hEquivalent :
      CorrectedConcreteObservationSelectionCostPointwiseEquivalent
        selectionCost₀ selectionCost₁)
    {language : Set (Word α)}
    (hTarget :
      language ∈
        StartRootedCorrectedConcreteTargetClass
          (v := z)
          α
          (↥U → M)
          (selectedObservationProduct obsFamily U)
          f) :
    ambientTargetObservationSelectionCostRank
        (z := z)
        obsFamily
        f
        selectionCost₀
        U
        hTarget =
      ambientTargetObservationSelectionCostRank
        (z := z)
        obsFamily
        f
        selectionCost₁
        U
        hTarget := by

  apply Nat.le_antisymm

  · exact
      ambientTargetObservationSelectionCostRank_le_of_pointwiseLe
        (z := z)
        obsFamily
        f
        selectionCost₀
        selectionCost₁
        U
        hEquivalent.1
        hTarget

  · exact
      ambientTargetObservationSelectionCostRank_le_of_pointwiseLe
        (z := z)
        obsFamily
        f
        selectionCost₁
        selectionCost₀
        U
        hEquivalent.2
        hTarget

end AmbientTargetRankComparison


section CoordinateWeightCostComparison

variable {ι : Type v}

/-- Ordinary cardinality cost is pointwise no greater than positive additive
coordinate cost. -/
theorem observationSelectionCardinalityCost_le_positiveAdditiveCost
    (coordinateWeight : ι → Nat) :
    CorrectedConcreteObservationSelectionCostPointwiseLe
      correctedConcreteObservationSelectionCardinalityCost
      (correctedConcreteObservationSelectionPositiveAdditiveCost
        coordinateWeight) := by

  intro S

  unfold
    correctedConcreteObservationSelectionCardinalityCost
    correctedConcreteObservationSelectionPositiveAdditiveCost

  omega

/-- Unshifted additive coordinate cost is pointwise no greater than positive
additive coordinate cost. -/
theorem observationSelectionAdditiveCost_le_positiveAdditiveCost
    (coordinateWeight : ι → Nat) :
    CorrectedConcreteObservationSelectionCostPointwiseLe
      (correctedConcreteObservationSelectionAdditiveCost
        coordinateWeight)
      (correctedConcreteObservationSelectionPositiveAdditiveCost
        coordinateWeight) := by

  intro S

  unfold
    correctedConcreteObservationSelectionPositiveAdditiveCost

  omega

/-- Coordinatewise larger weights give pointwise larger additive costs. -/
theorem observationSelectionAdditiveCost_pointwiseLe_of_weights_le
    {coordinateWeight₀ coordinateWeight₁ : ι → Nat}
    (hWeight :
      ∀ index : ι,
        coordinateWeight₀ index <=
          coordinateWeight₁ index) :
    CorrectedConcreteObservationSelectionCostPointwiseLe
      (correctedConcreteObservationSelectionAdditiveCost
        coordinateWeight₀)
      (correctedConcreteObservationSelectionAdditiveCost
        coordinateWeight₁) := by

  intro S

  classical

  unfold
    correctedConcreteObservationSelectionAdditiveCost

  exact
    Finset.sum_le_sum
      (fun index hindex =>
        hWeight index)

/-- Coordinatewise larger weights give pointwise larger positive additive
costs. -/
theorem
    observationSelectionPositiveAdditiveCost_pointwiseLe_of_weights_le
    {coordinateWeight₀ coordinateWeight₁ : ι → Nat}
    (hWeight :
      ∀ index : ι,
        coordinateWeight₀ index <=
          coordinateWeight₁ index) :
    CorrectedConcreteObservationSelectionCostPointwiseLe
      (correctedConcreteObservationSelectionPositiveAdditiveCost
        coordinateWeight₀)
      (correctedConcreteObservationSelectionPositiveAdditiveCost
        coordinateWeight₁) := by

  intro S

  have hAdditive :
      correctedConcreteObservationSelectionAdditiveCost
          coordinateWeight₀ S <=
        correctedConcreteObservationSelectionAdditiveCost
          coordinateWeight₁ S :=
    observationSelectionAdditiveCost_pointwiseLe_of_weights_le
      hWeight
      S

  unfold
    correctedConcreteObservationSelectionPositiveAdditiveCost

  omega

/-- Zero-extra-weight positive additive cost is pointwise equivalent to
cardinality cost. -/
theorem
    observationSelectionZeroPositiveAdditiveCost_equivalent_cardinality :
    CorrectedConcreteObservationSelectionCostPointwiseEquivalent
      (correctedConcreteObservationSelectionPositiveAdditiveCost
        (fun _ : ι => 0))
      correctedConcreteObservationSelectionCardinalityCost := by

  constructor

  · intro S

    simp

  · intro S

    simp

end CoordinateWeightCostComparison


section CoordinateWeightRankConsequences

variable {α : Type u}
variable {ι : Type v}
variable {M : Type w}
variable [Monoid M]
variable (obsFamily : ι → α → M)
variable (f : Nat)
variable (U : Finset ι)

/-- Cardinality-based observation-selection rank is bounded above by every
positive-additive observation-selection rank. -/
theorem ambientTarget_cardinalityCostRank_le_positiveAdditiveCostRank
    (coordinateWeight : ι → Nat)
    {language : Set (Word α)}
    (hTarget :
      language ∈
        StartRootedCorrectedConcreteTargetClass
          (v := z)
          α
          (↥U → M)
          (selectedObservationProduct obsFamily U)
          f) :
    ambientTargetObservationSelectionCostRank
        (z := z)
        obsFamily
        f
        correctedConcreteObservationSelectionCardinalityCost
        U
        hTarget <=
      ambientTargetObservationSelectionCostRank
        (z := z)
        obsFamily
        f
        (correctedConcreteObservationSelectionPositiveAdditiveCost
          coordinateWeight)
        U
        hTarget := by

  exact
    ambientTargetObservationSelectionCostRank_le_of_pointwiseLe
      (z := z)
      obsFamily
      f
      correctedConcreteObservationSelectionCardinalityCost
      (correctedConcreteObservationSelectionPositiveAdditiveCost
        coordinateWeight)
      U
      (observationSelectionCardinalityCost_le_positiveAdditiveCost
        coordinateWeight)
      hTarget

/-- Unshifted additive-weight rank is bounded above by positive-additive rank. -/
theorem ambientTarget_additiveCostRank_le_positiveAdditiveCostRank
    (coordinateWeight : ι → Nat)
    {language : Set (Word α)}
    (hTarget :
      language ∈
        StartRootedCorrectedConcreteTargetClass
          (v := z)
          α
          (↥U → M)
          (selectedObservationProduct obsFamily U)
          f) :
    ambientTargetObservationSelectionCostRank
        (z := z)
        obsFamily
        f
        (correctedConcreteObservationSelectionAdditiveCost
          coordinateWeight)
        U
        hTarget <=
      ambientTargetObservationSelectionCostRank
        (z := z)
        obsFamily
        f
        (correctedConcreteObservationSelectionPositiveAdditiveCost
          coordinateWeight)
        U
        hTarget := by

  exact
    ambientTargetObservationSelectionCostRank_le_of_pointwiseLe
      (z := z)
      obsFamily
      f
      (correctedConcreteObservationSelectionAdditiveCost
        coordinateWeight)
      (correctedConcreteObservationSelectionPositiveAdditiveCost
        coordinateWeight)
      U
      (observationSelectionAdditiveCost_le_positiveAdditiveCost
        coordinateWeight)
      hTarget

/-- Increasing every coordinate weight cannot decrease the positive-additive
observation-selection rank. -/
theorem ambientTarget_positiveAdditiveCostRank_mono_weights
    {coordinateWeight₀ coordinateWeight₁ : ι → Nat}
    (hWeight :
      ∀ index : ι,
        coordinateWeight₀ index <=
          coordinateWeight₁ index)
    {language : Set (Word α)}
    (hTarget :
      language ∈
        StartRootedCorrectedConcreteTargetClass
          (v := z)
          α
          (↥U → M)
          (selectedObservationProduct obsFamily U)
          f) :
    ambientTargetObservationSelectionCostRank
        (z := z)
        obsFamily
        f
        (correctedConcreteObservationSelectionPositiveAdditiveCost
          coordinateWeight₀)
        U
        hTarget <=
      ambientTargetObservationSelectionCostRank
        (z := z)
        obsFamily
        f
        (correctedConcreteObservationSelectionPositiveAdditiveCost
          coordinateWeight₁)
        U
        hTarget := by

  exact
    ambientTargetObservationSelectionCostRank_le_of_pointwiseLe
      (z := z)
      obsFamily
      f
      (correctedConcreteObservationSelectionPositiveAdditiveCost
        coordinateWeight₀)
      (correctedConcreteObservationSelectionPositiveAdditiveCost
        coordinateWeight₁)
      U
      (observationSelectionPositiveAdditiveCost_pointwiseLe_of_weights_le
        hWeight)
      hTarget

/-- With zero extra coordinate weights, positive-additive and cardinality rank
hierarchies coincide. -/
theorem
    ambientTarget_zeroPositiveAdditiveCostRank_eq_cardinalityCostRank
    {language : Set (Word α)}
    (hTarget :
      language ∈
        StartRootedCorrectedConcreteTargetClass
          (v := z)
          α
          (↥U → M)
          (selectedObservationProduct obsFamily U)
          f) :
    ambientTargetObservationSelectionCostRank
        (z := z)
        obsFamily
        f
        (correctedConcreteObservationSelectionPositiveAdditiveCost
          (fun _ : ι => 0))
        U
        hTarget =
      ambientTargetObservationSelectionCostRank
        (z := z)
        obsFamily
        f
        correctedConcreteObservationSelectionCardinalityCost
        U
        hTarget := by

  exact
    ambientTargetObservationSelectionCostRank_eq_of_pointwiseEquivalent
      (z := z)
      obsFamily
      f
      (correctedConcreteObservationSelectionPositiveAdditiveCost
        (fun _ : ι => 0))
      correctedConcreteObservationSelectionCardinalityCost
      U
      observationSelectionZeroPositiveAdditiveCost_equivalent_cardinality
      hTarget

end CoordinateWeightRankConsequences


section CertifiedTwoCostComparison

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
variable (selectionCost₀ selectionCost₁ : Finset ι → Nat)
variable (U : Finset ι)

/-- Two pointwise ordered cost models admit certified minimum selections whose
observation-selection ranks satisfy the same order. -/
theorem ambientTarget_twoCostRank_certifiedComparison_package
    (hCost :
      CorrectedConcreteObservationSelectionCostPointwiseLe
        selectionCost₀ selectionCost₁)
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
      (rank₀ rank₁ : Nat)
      (S₀ S₁ : Finset ι)
      (hSelected₀ :
        language ∈
          StartRootedCorrectedConcreteTargetClass
            (v := z)
            α
            (↥S₀ → M)
            (selectedObservationProduct obsFamily S₀)
            f)
      (hSelected₁ :
        language ∈
          StartRootedCorrectedConcreteTargetClass
            (v := z)
            α
            (↥S₁ → M)
            (selectedObservationProduct obsFamily S₁)
            f),
      rank₀ <= rank₁ ∧
        selectionCost₀ S₀ = rank₀ ∧
        selectionCost₁ S₁ = rank₁ ∧
        IdentifiesLanguageFromPositiveData
          (correctedConcreteCertifiedWorkingGrammarHypLanguage
            (selectedObservationProduct obsFamily S₀)
            f)
          (correctedConcreteCertifiedWorkingGrammarLearner
            hα
            (selectedObservationProduct obsFamily S₀)
            f)
          language ∧
        IdentifiesLanguageFromPositiveData
          (correctedConcreteCertifiedWorkingGrammarHypLanguage
            (selectedObservationProduct obsFamily S₁)
            f)
          (correctedConcreteCertifiedWorkingGrammarLearner
            hα
            (selectedObservationProduct obsFamily S₁)
            f)
          language ∧
        (∃
          C₀ :
            CorrectedConcreteCertifiedWorkingGrammarHypothesis
              α
              (↥S₀ → M)
              (selectedObservationProduct obsFamily S₀)
              f,
          C₀.output.grammar.StringLanguage =
              language ∧
            C₀.bits.length <=
              correctedConcreteCertifiedRankBitBudget
                (startRootedTargetCertifiedDescriptionRank
                  (v := z)
                  hα
                  (selectedObservationProduct obsFamily S₀)
                  f
                  hSelected₀)
                f ∧
            C₀.canonicalSearch.length <=
              correctedConcreteCertifiedRankSearchBudget
                (startRootedTargetCertifiedDescriptionRank
                  (v := z)
                  hα
                  (selectedObservationProduct obsFamily S₀)
                  f
                  hSelected₀)
                f) ∧
        (∃
          C₁ :
            CorrectedConcreteCertifiedWorkingGrammarHypothesis
              α
              (↥S₁ → M)
              (selectedObservationProduct obsFamily S₁)
              f,
          C₁.output.grammar.StringLanguage =
              language ∧
            C₁.bits.length <=
              correctedConcreteCertifiedRankBitBudget
                (startRootedTargetCertifiedDescriptionRank
                  (v := z)
                  hα
                  (selectedObservationProduct obsFamily S₁)
                  f
                  hSelected₁)
                f ∧
            C₁.canonicalSearch.length <=
              correctedConcreteCertifiedRankSearchBudget
                (startRootedTargetCertifiedDescriptionRank
                  (v := z)
                  hα
                  (selectedObservationProduct obsFamily S₁)
                  f
                  hSelected₁)
                f) := by

  rcases
      ambientTarget_observationSelectionCostRank_certified_package
        (z := z)
        hα
        obsFamily
        f
        selectionCost₀
        U
        hTarget with
    ⟨rank₀,
      S₀,
      hSelected₀,
      hRank₀,
      hCost₀,
      hShell₀,
      hIdentifies₀,
      C₀,
      hLanguage₀,
      hBits₀,
      hSearch₀⟩

  rcases
      ambientTarget_observationSelectionCostRank_certified_package
        (z := z)
        hα
        obsFamily
        f
        selectionCost₁
        U
        hTarget with
    ⟨rank₁,
      S₁,
      hSelected₁,
      hRank₁,
      hCost₁,
      hShell₁,
      hIdentifies₁,
      C₁,
      hLanguage₁,
      hBits₁,
      hSearch₁⟩

  have hRankLe :
      rank₀ <= rank₁ := by

    rw [hRank₀, hRank₁]

    exact
      ambientTargetObservationSelectionCostRank_le_of_pointwiseLe
        (z := z)
        obsFamily
        f
        selectionCost₀
        selectionCost₁
        U
        hCost
        hTarget

  exact
    ⟨rank₀,
      rank₁,
      S₀,
      S₁,
      hSelected₀,
      hSelected₁,
      hRankLe,
      hCost₀,
      hCost₁,
      hIdentifies₀,
      hIdentifies₁,
      ⟨C₀,
        hLanguage₀,
        hBits₀,
        hSearch₀⟩,
      ⟨C₁,
        hLanguage₁,
        hBits₁,
        hSearch₁⟩⟩

end CertifiedTwoCostComparison


section ObservationSelectionRankComparisonFinalPackage

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
variable (selectionCost₀ selectionCost₁ : Finset ι → Nat)
variable (U : Finset ι)

/-- Final profile, filtration, exact-shell, rank, and certified comparison
package for pointwise ordered observation-selection costs. -/
theorem
    correctedConcreteCertifiedWorkingGrammar_observationSelectionRankComparison_package
    (hCost :
      CorrectedConcreteObservationSelectionCostPointwiseLe
        selectionCost₀ selectionCost₁) :
    (∀ costBudget : Nat,
      CorrectedConcreteObservationSelectionCostProfileClass
          (z := z)
          α
          ι
          M
          obsFamily
          f
          selectionCost₁
          U
          costBudget ⊆
        CorrectedConcreteObservationSelectionCostProfileClass
          (z := z)
          α
          ι
          M
          obsFamily
          f
          selectionCost₀
          U
          costBudget) ∧
      (∀
        language : Set (Word α),
        ∀ costBudget : Nat,
          correctedConcreteObservationCostBudgetFiltration
              (z := z)
              obsFamily
              f
              selectionCost₁
              U
              language
              costBudget ⊆
            correctedConcreteObservationCostBudgetFiltration
              (z := z)
              obsFamily
              f
              selectionCost₀
              U
              language
              costBudget) ∧
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
          ambientTargetObservationSelectionCostRank
              (z := z)
              obsFamily
              f
              selectionCost₀
              U
              hTarget <=
            ambientTargetObservationSelectionCostRank
              (z := z)
              obsFamily
              f
              selectionCost₁
              U
              hTarget) ∧
      (∀
        language : Set (Word α),
        ∀ rank₁ : Nat,
          language ∈
              CorrectedConcreteObservationSelectionExactCostRankClass
                (z := z)
                α
                ι
                M
                obsFamily
                f
                selectionCost₁
                U
                rank₁ →
            ∃ rank₀ : Nat,
              rank₀ <= rank₁ ∧
                language ∈
                  CorrectedConcreteObservationSelectionExactCostRankClass
                    (z := z)
                    α
                    ι
                    M
                    obsFamily
                    f
                    selectionCost₀
                    U
                    rank₀) ∧
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
            (rank₀ rank₁ : Nat)
            (S₀ S₁ : Finset ι)
            (hSelected₀ :
              language ∈
                StartRootedCorrectedConcreteTargetClass
                  (v := z)
                  α
                  (↥S₀ → M)
                  (selectedObservationProduct obsFamily S₀)
                  f)
            (hSelected₁ :
              language ∈
                StartRootedCorrectedConcreteTargetClass
                  (v := z)
                  α
                  (↥S₁ → M)
                  (selectedObservationProduct obsFamily S₁)
                  f),
            rank₀ <= rank₁ ∧
              selectionCost₀ S₀ = rank₀ ∧
              selectionCost₁ S₁ = rank₁ ∧
              IdentifiesLanguageFromPositiveData
                (correctedConcreteCertifiedWorkingGrammarHypLanguage
                  (selectedObservationProduct obsFamily S₀)
                  f)
                (correctedConcreteCertifiedWorkingGrammarLearner
                  hα
                  (selectedObservationProduct obsFamily S₀)
                  f)
                language ∧
              IdentifiesLanguageFromPositiveData
                (correctedConcreteCertifiedWorkingGrammarHypLanguage
                  (selectedObservationProduct obsFamily S₁)
                  f)
                (correctedConcreteCertifiedWorkingGrammarLearner
                  hα
                  (selectedObservationProduct obsFamily S₁)
                  f)
                language) := by

  refine
    ⟨?_,
      ?_,
      ?_,
      ?_,
      ?_⟩

  · intro costBudget

    exact
      observationSelectionCostProfileClass_subset_of_pointwiseLe
        (z := z)
        hCost
        costBudget

  · intro language costBudget

    exact
      observationCostBudgetFiltration_subset_of_pointwiseLe
        (z := z)
        hCost
        costBudget

  · intro language hTarget

    exact
      ambientTargetObservationSelectionCostRank_le_of_pointwiseLe
        (z := z)
        obsFamily
        f
        selectionCost₀
        selectionCost₁
        U
        hCost
        hTarget

  · intro language rank₁ hRank₁

    exact
      observationSelection_exactExpensiveRank_exists_cheaperRank_le
        (z := z)
        hCost
        hRank₁

  · intro language hTarget

    rcases
        ambientTarget_twoCostRank_certifiedComparison_package
          (z := z)
          hα
          obsFamily
          f
          selectionCost₀
          selectionCost₁
          U
          hCost
          hTarget with
      ⟨rank₀,
        rank₁,
        S₀,
        S₁,
        hSelected₀,
        hSelected₁,
        hRankLe,
        hCost₀,
        hCost₁,
        hIdentifies₀,
        hIdentifies₁,
        hCertificate₀,
        hCertificate₁⟩

    exact
      ⟨rank₀,
        rank₁,
        S₀,
        S₁,
        hSelected₀,
        hSelected₁,
        hRankLe,
        hCost₀,
        hCost₁,
        hIdentifies₀,
        hIdentifies₁⟩

end ObservationSelectionRankComparisonFinalPackage

end MCFG
