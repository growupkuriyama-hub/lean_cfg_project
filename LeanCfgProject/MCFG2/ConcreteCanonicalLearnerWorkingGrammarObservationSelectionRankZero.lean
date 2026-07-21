/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG.ConcreteCanonicalLearnerWorkingGrammarObservationSelectionCostOverhead

/-!
# ConcreteCanonicalLearnerWorkingGrammarObservationSelectionRankZero.lean

The preceding files develop observation-selection cost ranks, compare cost
models, prove perturbation bounds, and analyze fixed-overhead normalization.

This file identifies the bottom rank of the hierarchy.

## General zero-cost class

For an arbitrary finite selection cost, define the zero-cost target class to
contain exactly the languages represented by some ambient selected subset `S`
with

```text
selectionCost S = 0.
```

For every selectable language,

```text
minimum selection cost = 0
  ↔
language belongs to the zero-cost class.
```

Consequently, the exact cost-rank-zero shell is precisely the zero-cost class.

## Positive additive and cardinality costs

For positive additive coordinate cost,

```text
PositiveAdditiveCost(S)
  =
S.card + ∑ i ∈ S, coordinateWeight i,
```

cost zero is possible exactly for `S = ∅`.

The same is true for ordinary cardinality cost.

Therefore, for both cost models,

```text
selection rank = 0
  ↔
the empty selected observation product represents the target.
```

The exact rank-zero shell is exactly the target class of the empty selected
product.

Failure under the empty selected product forces strictly positive observation-
selection rank.

## Rank-zero selector

For positive additive cost, every selected subset attaining rank zero is empty.
In particular, the minimum-cost selector constructed earlier returns the empty
subset whenever the target has rank zero.

The certified learner for the empty selected product then identifies every
rank-zero target and returns one exact checked grammar output at the empty
product's minimum certified-description rank.

## Interpretation

Rank zero means that none of the candidate observation coordinates is needed.
This is stronger than saying that a particular coordinate is redundant:
the entire finite observation interface can be removed.

No target grammar is supplied to any learner.
No `sorry`, `admit`, or `axiom` is used.
-/

namespace MCFG

universe u v w z


section ObservationSelectionZeroCostClassDefinition

variable (α : Type u)
variable (ι : Type v)
variable (M : Type w)
variable [Monoid M]
variable (obsFamily : ι → α → M)
variable (f : Nat)
variable (selectionCost : Finset ι → Nat)
variable (U : Finset ι)

/-- Languages represented by some ambient selected observation product of
exactly zero selection cost. -/
def CorrectedConcreteObservationSelectionZeroCostClass :
    Set (Set (Word α)) :=
  {language |
    ∃ S : Finset ι,
      S ⊆ U ∧
        selectionCost S = 0 ∧
        language ∈
          StartRootedCorrectedConcreteTargetClass
            (v := z)
            α
            (↥S → M)
            (selectedObservationProduct obsFamily S)
            f}

end ObservationSelectionZeroCostClassDefinition


section ObservationSelectionZeroCostClassMembership

variable {α : Type u}
variable {ι : Type v}
variable {M : Type w}
variable [Monoid M]
variable {obsFamily : ι → α → M}
variable {f : Nat}
variable {selectionCost : Finset ι → Nat}
variable {U : Finset ι}
variable {language : Set (Word α)}

/-- Exact membership theorem for the zero-cost target class. -/
theorem mem_observationSelectionZeroCostClass_iff :
    language ∈
        CorrectedConcreteObservationSelectionZeroCostClass
          (z := z)
          α
          ι
          M
          obsFamily
          f
          selectionCost
          U ↔
      ∃ S : Finset ι,
        S ⊆ U ∧
          selectionCost S = 0 ∧
          language ∈
            StartRootedCorrectedConcreteTargetClass
              (v := z)
              α
              (↥S → M)
              (selectedObservationProduct obsFamily S)
              f := by

  rfl

/-- A selectable language has minimum cost zero exactly when some feasible
ambient selection has exact cost zero. -/
theorem observationSelectionMinimumCost_eq_zero_iff_mem_zeroCostClass
    (hSelection :
      HasCorrectedConcreteObservationSelectionCost
        (obsFamily := obsFamily)
        (f := f)
        selectionCost
        U
        language) :
    correctedConcreteObservationSelectionMinimumCost
          selectionCost
          hSelection =
        0 ↔
      language ∈
        CorrectedConcreteObservationSelectionZeroCostClass
          (z := z)
          α
          ι
          M
          obsFamily
          f
          selectionCost
          U := by

  constructor

  · intro hZero

    rcases hSelection.exists_selection_exact_minimumCost with
      ⟨S, hSU, hCost, hTarget⟩

    exact
      ⟨S,
        hSU,
        by
          simpa [hZero] using hCost,
        hTarget⟩

  · intro hZeroCost

    rcases hZeroCost with
      ⟨S, hSU, hCost, hTarget⟩

    have hMinimum :
        correctedConcreteObservationSelectionMinimumCost
            selectionCost
            hSelection <=
          0 := by

      apply
        hSelection.minimumCost_le_of_selection

      exact
        ⟨S,
          hSU,
          by
            omega,
          hTarget⟩

    omega

/-- Strictly positive minimum selection cost is equivalent to exclusion from
the zero-cost target class. -/
theorem observationSelectionMinimumCost_pos_iff_not_mem_zeroCostClass
    (hSelection :
      HasCorrectedConcreteObservationSelectionCost
        (obsFamily := obsFamily)
        (f := f)
        selectionCost
        U
        language) :
    0 <
        correctedConcreteObservationSelectionMinimumCost
          selectionCost
          hSelection ↔
      language ∉
        CorrectedConcreteObservationSelectionZeroCostClass
          (z := z)
          α
          ι
          M
          obsFamily
          f
          selectionCost
          U := by

  constructor

  · intro hPositive hZeroCost

    have hZero :
        correctedConcreteObservationSelectionMinimumCost
            selectionCost
            hSelection =
          0 :=
      (observationSelectionMinimumCost_eq_zero_iff_mem_zeroCostClass
        (z := z)
        hSelection).mpr
        hZeroCost

    omega

  · intro hNotZeroCost

    by_contra hNotPositive

    have hZero :
        correctedConcreteObservationSelectionMinimumCost
            selectionCost
            hSelection =
          0 := by
      omega

    exact
      hNotZeroCost
        ((observationSelectionMinimumCost_eq_zero_iff_mem_zeroCostClass
          (z := z)
          hSelection).mp
          hZero)

end ObservationSelectionZeroCostClassMembership


section ExactRankZeroClass

variable {α : Type u}
variable {ι : Type v}
variable {M : Type w}
variable [Monoid M]
variable {obsFamily : ι → α → M}
variable {f : Nat}
variable {selectionCost : Finset ι → Nat}
variable {U : Finset ι}

/-- The exact rank-zero shell is exactly the zero-cost target class. -/
theorem observationSelectionExactCostRankZeroClass_eq_zeroCostClass :
    CorrectedConcreteObservationSelectionExactCostRankClass
        (z := z)
        α
        ι
        M
        obsFamily
        f
        selectionCost
        U
        0 =
      CorrectedConcreteObservationSelectionZeroCostClass
        (z := z)
        α
        ι
        M
        obsFamily
        f
        selectionCost
        U := by

  ext language

  constructor

  · intro hRankZero

    rcases hRankZero.1 with
      ⟨S, hSU, hCost, hTarget⟩

    have hCostZero :
        selectionCost S = 0 := by
      omega

    exact
      ⟨S,
        hSU,
        hCostZero,
        hTarget⟩

  · intro hZeroCost

    rcases hZeroCost with
      ⟨S, hSU, hCost, hTarget⟩

    refine
      ⟨⟨S,
          hSU,
          by
            omega,
          hTarget⟩,
        ?_⟩

    intro costBudget hBudget

    omega

end ExactRankZeroClass


section AmbientTargetZeroRank

variable {α : Type u}
variable {ι : Type v}
variable {M : Type w}
variable [Monoid M]
variable (obsFamily : ι → α → M)
variable (f : Nat)
variable (selectionCost : Finset ι → Nat)
variable (U : Finset ι)

/-- The paper-facing target rank is zero exactly when the target belongs to the
zero-cost selection class. -/
theorem ambientTargetObservationSelectionCostRank_eq_zero_iff_zeroCostClass
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
          selectionCost
          U
          hTarget =
        0 ↔
      language ∈
        CorrectedConcreteObservationSelectionZeroCostClass
          (z := z)
          α
          ι
          M
          obsFamily
          f
          selectionCost
          U := by

  let hSelection :=
    hasCorrectedConcreteObservationSelectionCost_of_fullProductTarget
      (obsFamily := obsFamily)
      (f := f)
      selectionCost
      hTarget

  simpa [
    ambientTargetObservationSelectionCostRank,
    ambientTargetObservationSelectionMinimumCost,
    hSelection
  ] using
    observationSelectionMinimumCost_eq_zero_iff_mem_zeroCostClass
      (z := z)
      hSelection

/-- The paper-facing target rank is positive exactly when the target is outside
the zero-cost selection class. -/
theorem ambientTargetObservationSelectionCostRank_pos_iff_not_zeroCostClass
    {language : Set (Word α)}
    (hTarget :
      language ∈
        StartRootedCorrectedConcreteTargetClass
          (v := z)
          α
          (↥U → M)
          (selectedObservationProduct obsFamily U)
          f) :
    0 <
        ambientTargetObservationSelectionCostRank
          (z := z)
          obsFamily
          f
          selectionCost
          U
          hTarget ↔
      language ∉
        CorrectedConcreteObservationSelectionZeroCostClass
          (z := z)
          α
          ι
          M
          obsFamily
          f
          selectionCost
          U := by

  let hSelection :=
    hasCorrectedConcreteObservationSelectionCost_of_fullProductTarget
      (obsFamily := obsFamily)
      (f := f)
      selectionCost
      hTarget

  simpa [
    ambientTargetObservationSelectionCostRank,
    ambientTargetObservationSelectionMinimumCost,
    hSelection
  ] using
    observationSelectionMinimumCost_pos_iff_not_mem_zeroCostClass
      (z := z)
      hSelection

end AmbientTargetZeroRank


section PositiveAdditiveCostZero

variable {ι : Type v}

/-- Positive additive coordinate cost is zero exactly for the empty selected
set. -/
theorem observationSelectionPositiveAdditiveCost_eq_zero_iff
    (coordinateWeight : ι → Nat)
    (S : Finset ι) :
    correctedConcreteObservationSelectionPositiveAdditiveCost
          coordinateWeight
          S =
        0 ↔
      S = ∅ := by

  constructor

  · intro hZero

    have hCardZero :
        S.card = 0 := by

      unfold
        correctedConcreteObservationSelectionPositiveAdditiveCost
        at hZero

      omega

    exact
      Finset.card_eq_zero.mp
        hCardZero

  · intro hEmpty

    subst S

    simp [
      correctedConcreteObservationSelectionPositiveAdditiveCost,
      correctedConcreteObservationSelectionAdditiveCost
    ]

/-- Ordinary cardinality cost is zero exactly for the empty selected set. -/
theorem observationSelectionCardinalityCost_eq_zero_iff
    (S : Finset ι) :
    correctedConcreteObservationSelectionCardinalityCost S =
        0 ↔
      S = ∅ := by

  unfold
    correctedConcreteObservationSelectionCardinalityCost

  exact
    Finset.card_eq_zero

end PositiveAdditiveCostZero


section PositiveAdditiveZeroCostClass

variable {α : Type u}
variable {ι : Type v}
variable {M : Type w}
variable [Monoid M]
variable (obsFamily : ι → α → M)
variable (f : Nat)
variable (coordinateWeight : ι → Nat)
variable (U : Finset ι)

/-- For positive additive cost, the zero-cost target class is exactly the
target class of the empty selected observation product. -/
theorem positiveAdditiveObservationSelectionZeroCostClass_eq_emptyProductTargetClass :
    CorrectedConcreteObservationSelectionZeroCostClass
        (z := z)
        α
        ι
        M
        obsFamily
        f
        (correctedConcreteObservationSelectionPositiveAdditiveCost
          coordinateWeight)
        U =
      StartRootedCorrectedConcreteTargetClass
        (v := z)
        α
        (↥(∅ : Finset ι) → M)
        (selectedObservationProduct obsFamily ∅)
        f := by

  ext language

  constructor

  · intro hZeroCost

    rcases hZeroCost with
      ⟨S, hSU, hCost, hTarget⟩

    have hEmpty :
        S = ∅ :=
      (observationSelectionPositiveAdditiveCost_eq_zero_iff
        coordinateWeight
        S).mp
        hCost

    simpa [hEmpty] using hTarget

  · intro hEmptyTarget

    exact
      ⟨∅,
        by
          intro index hindex
          simp at hindex,
        by
          simp,
        hEmptyTarget⟩

/-- The positive-additive exact rank-zero shell is exactly the target class of
the empty selected observation product. -/
theorem
    positiveAdditiveObservationSelectionExactRankZeroClass_eq_emptyProductTargetClass :
    CorrectedConcreteObservationSelectionExactCostRankClass
        (z := z)
        α
        ι
        M
        obsFamily
        f
        (correctedConcreteObservationSelectionPositiveAdditiveCost
          coordinateWeight)
        U
        0 =
      StartRootedCorrectedConcreteTargetClass
        (v := z)
        α
        (↥(∅ : Finset ι) → M)
        (selectedObservationProduct obsFamily ∅)
        f := by

  calc
    CorrectedConcreteObservationSelectionExactCostRankClass
        (z := z)
        α
        ι
        M
        obsFamily
        f
        (correctedConcreteObservationSelectionPositiveAdditiveCost
          coordinateWeight)
        U
        0 =
      CorrectedConcreteObservationSelectionZeroCostClass
        (z := z)
        α
        ι
        M
        obsFamily
        f
        (correctedConcreteObservationSelectionPositiveAdditiveCost
          coordinateWeight)
        U :=
          observationSelectionExactCostRankZeroClass_eq_zeroCostClass
            (z := z)

    _ =
      StartRootedCorrectedConcreteTargetClass
        (v := z)
        α
        (↥(∅ : Finset ι) → M)
        (selectedObservationProduct obsFamily ∅)
        f :=
          positiveAdditiveObservationSelectionZeroCostClass_eq_emptyProductTargetClass
            (z := z)
            obsFamily
            f
            coordinateWeight
            U

end PositiveAdditiveZeroCostClass


section CardinalityZeroCostClass

variable {α : Type u}
variable {ι : Type v}
variable {M : Type w}
variable [Monoid M]
variable (obsFamily : ι → α → M)
variable (f : Nat)
variable (U : Finset ι)

/-- For cardinality cost, the zero-cost target class is exactly the target
class of the empty selected observation product. -/
theorem cardinalityObservationSelectionZeroCostClass_eq_emptyProductTargetClass :
    CorrectedConcreteObservationSelectionZeroCostClass
        (z := z)
        α
        ι
        M
        obsFamily
        f
        correctedConcreteObservationSelectionCardinalityCost
        U =
      StartRootedCorrectedConcreteTargetClass
        (v := z)
        α
        (↥(∅ : Finset ι) → M)
        (selectedObservationProduct obsFamily ∅)
        f := by

  ext language

  constructor

  · intro hZeroCost

    rcases hZeroCost with
      ⟨S, hSU, hCost, hTarget⟩

    have hEmpty :
        S = ∅ :=
      (observationSelectionCardinalityCost_eq_zero_iff
        S).mp
        hCost

    simpa [hEmpty] using hTarget

  · intro hEmptyTarget

    exact
      ⟨∅,
        by
          intro index hindex
          simp at hindex,
        by
          simp [
            correctedConcreteObservationSelectionCardinalityCost
          ],
        hEmptyTarget⟩

/-- The cardinality exact rank-zero shell is exactly the target class of the
empty selected observation product. -/
theorem
    cardinalityObservationSelectionExactRankZeroClass_eq_emptyProductTargetClass :
    CorrectedConcreteObservationSelectionExactCostRankClass
        (z := z)
        α
        ι
        M
        obsFamily
        f
        correctedConcreteObservationSelectionCardinalityCost
        U
        0 =
      StartRootedCorrectedConcreteTargetClass
        (v := z)
        α
        (↥(∅ : Finset ι) → M)
        (selectedObservationProduct obsFamily ∅)
        f := by

  calc
    CorrectedConcreteObservationSelectionExactCostRankClass
        (z := z)
        α
        ι
        M
        obsFamily
        f
        correctedConcreteObservationSelectionCardinalityCost
        U
        0 =
      CorrectedConcreteObservationSelectionZeroCostClass
        (z := z)
        α
        ι
        M
        obsFamily
        f
        correctedConcreteObservationSelectionCardinalityCost
        U :=
          observationSelectionExactCostRankZeroClass_eq_zeroCostClass
            (z := z)

    _ =
      StartRootedCorrectedConcreteTargetClass
        (v := z)
        α
        (↥(∅ : Finset ι) → M)
        (selectedObservationProduct obsFamily ∅)
        f :=
          cardinalityObservationSelectionZeroCostClass_eq_emptyProductTargetClass
            (z := z)
            obsFamily
            f
            U

end CardinalityZeroCostClass


section AmbientPositiveAdditiveRankZero

variable {α : Type u}
variable {ι : Type v}
variable {M : Type w}
variable [Monoid M]
variable (obsFamily : ι → α → M)
variable (f : Nat)
variable (coordinateWeight : ι → Nat)
variable (U : Finset ι)

/-- Positive-additive target rank is zero exactly when the empty selected
product represents the target. -/
theorem ambientTarget_positiveAdditiveCostRank_eq_zero_iff_emptyProductTarget
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
            coordinateWeight)
          U
          hTarget =
        0 ↔
      language ∈
        StartRootedCorrectedConcreteTargetClass
          (v := z)
          α
          (↥(∅ : Finset ι) → M)
          (selectedObservationProduct obsFamily ∅)
          f := by

  rw [
    ambientTargetObservationSelectionCostRank_eq_zero_iff_zeroCostClass
      (z := z)
      obsFamily
      f
      (correctedConcreteObservationSelectionPositiveAdditiveCost
        coordinateWeight)
      U
      hTarget,
    positiveAdditiveObservationSelectionZeroCostClass_eq_emptyProductTargetClass
      (z := z)
      obsFamily
      f
      coordinateWeight
      U
  ]

/-- Failure under the empty selected product is equivalent to strictly positive
positive-additive observation-selection rank. -/
theorem ambientTarget_positiveAdditiveCostRank_pos_iff_not_emptyProductTarget
    {language : Set (Word α)}
    (hTarget :
      language ∈
        StartRootedCorrectedConcreteTargetClass
          (v := z)
          α
          (↥U → M)
          (selectedObservationProduct obsFamily U)
          f) :
    0 <
        ambientTargetObservationSelectionCostRank
          (z := z)
          obsFamily
          f
          (correctedConcreteObservationSelectionPositiveAdditiveCost
            coordinateWeight)
          U
          hTarget ↔
      language ∉
        StartRootedCorrectedConcreteTargetClass
          (v := z)
          α
          (↥(∅ : Finset ι) → M)
          (selectedObservationProduct obsFamily ∅)
          f := by

  rw [
    ambientTargetObservationSelectionCostRank_pos_iff_not_zeroCostClass
      (z := z)
      obsFamily
      f
      (correctedConcreteObservationSelectionPositiveAdditiveCost
        coordinateWeight)
      U
      hTarget,
    positiveAdditiveObservationSelectionZeroCostClass_eq_emptyProductTargetClass
      (z := z)
      obsFamily
      f
      coordinateWeight
      U
  ]

end AmbientPositiveAdditiveRankZero


section AmbientCardinalityRankZero

variable {α : Type u}
variable {ι : Type v}
variable {M : Type w}
variable [Monoid M]
variable (obsFamily : ι → α → M)
variable (f : Nat)
variable (U : Finset ι)

/-- Cardinality target rank is zero exactly when the empty selected product
represents the target. -/
theorem ambientTarget_cardinalityCostRank_eq_zero_iff_emptyProductTarget
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
          hTarget =
        0 ↔
      language ∈
        StartRootedCorrectedConcreteTargetClass
          (v := z)
          α
          (↥(∅ : Finset ι) → M)
          (selectedObservationProduct obsFamily ∅)
          f := by

  rw [
    ambientTargetObservationSelectionCostRank_eq_zero_iff_zeroCostClass
      (z := z)
      obsFamily
      f
      correctedConcreteObservationSelectionCardinalityCost
      U
      hTarget,
    cardinalityObservationSelectionZeroCostClass_eq_emptyProductTargetClass
      (z := z)
      obsFamily
      f
      U
  ]

/-- Failure under the empty selected product is equivalent to strictly positive
cardinality observation-selection rank. -/
theorem ambientTarget_cardinalityCostRank_pos_iff_not_emptyProductTarget
    {language : Set (Word α)}
    (hTarget :
      language ∈
        StartRootedCorrectedConcreteTargetClass
          (v := z)
          α
          (↥U → M)
          (selectedObservationProduct obsFamily U)
          f) :
    0 <
        ambientTargetObservationSelectionCostRank
          (z := z)
          obsFamily
          f
          correctedConcreteObservationSelectionCardinalityCost
          U
          hTarget ↔
      language ∉
        StartRootedCorrectedConcreteTargetClass
          (v := z)
          α
          (↥(∅ : Finset ι) → M)
          (selectedObservationProduct obsFamily ∅)
          f := by

  rw [
    ambientTargetObservationSelectionCostRank_pos_iff_not_zeroCostClass
      (z := z)
      obsFamily
      f
      correctedConcreteObservationSelectionCardinalityCost
      U
      hTarget,
    cardinalityObservationSelectionZeroCostClass_eq_emptyProductTargetClass
      (z := z)
      obsFamily
      f
      U
  ]

end AmbientCardinalityRankZero


section PositiveAdditiveRankZeroSelector

variable {α : Type u}
variable {ι : Type v}
variable {M : Type w}
variable [DecidableEq ι]
variable [Monoid M]
variable (obsFamily : ι → α → M)
variable (f : Nat)
variable (coordinateWeight : ι → Nat)
variable (U : Finset ι)
variable (language : Set (Word α))
variable
  (hTarget :
    language ∈
      StartRootedCorrectedConcreteTargetClass
        (v := z)
        α
        (↥U → M)
        (selectedObservationProduct obsFamily U)
        f)

/-- If the positive-additive observation-selection rank is zero, the selected
minimum-cost result is literally the empty selected set. -/
theorem
    correctedConcreteObservationPositiveAdditiveMinimumSelectionResult_eq_empty_of_rank_zero
    (hRankZero :
      ambientTargetObservationSelectionCostRank
          (z := z)
          obsFamily
          f
          (correctedConcreteObservationSelectionPositiveAdditiveCost
            coordinateWeight)
          U
          hTarget =
        0) :
    (correctedConcreteObservationPositiveAdditiveMinimumSelectionResult
        (z := z)
        obsFamily
        f
        coordinateWeight
        U
        language
        hTarget).selected =
      ∅ := by

  let hSelection :=
    positiveAdditiveSelectionExists
      (z := z)
      obsFamily
      f
      coordinateWeight
      U
      language
      hTarget

  let result :=
    correctedConcreteObservationPositiveAdditiveMinimumSelectionResult
      (z := z)
      obsFamily
      f
      coordinateWeight
      U
      language
      hTarget

  have hMinimumZero :
      correctedConcreteObservationSelectionMinimumCost
          (correctedConcreteObservationSelectionPositiveAdditiveCost
            coordinateWeight)
          hSelection =
        0 := by

    simpa [
      ambientTargetObservationSelectionCostRank,
      ambientTargetObservationSelectionMinimumCost,
      hSelection
    ] using
      hRankZero

  have hSelectedCostZero :
      correctedConcreteObservationSelectionPositiveAdditiveCost
          coordinateWeight
          result.selected =
        0 := by

    rw [
      CorrectedConcreteObservationMinimumCostSelectionResult.selected_cost_eq_minimum
        result,
      hMinimumZero
    ]

  exact
    (observationSelectionPositiveAdditiveCost_eq_zero_iff
      coordinateWeight
      result.selected).mp
      hSelectedCostZero

end PositiveAdditiveRankZeroSelector


section RankZeroCertifiedLearner

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
variable (coordinateWeight : ι → Nat)
variable (U : Finset ι)

/-- Every positive-additive rank-zero target is identified by the certified
learner for the empty selected observation product. -/
theorem ambientTarget_positiveAdditiveRankZero_emptyProductCertified_package
    {language : Set (Word α)}
    (hTarget :
      language ∈
        StartRootedCorrectedConcreteTargetClass
          (v := z)
          α
          (↥U → M)
          (selectedObservationProduct obsFamily U)
          f)
    (hRankZero :
      ambientTargetObservationSelectionCostRank
          (z := z)
          obsFamily
          f
          (correctedConcreteObservationSelectionPositiveAdditiveCost
            coordinateWeight)
          U
          hTarget =
        0) :
    let hEmpty :
      language ∈
        StartRootedCorrectedConcreteTargetClass
          (v := z)
          α
          (↥(∅ : Finset ι) → M)
          (selectedObservationProduct obsFamily ∅)
          f :=
      (ambientTarget_positiveAdditiveCostRank_eq_zero_iff_emptyProductTarget
        (z := z)
        obsFamily
        f
        coordinateWeight
        U
        hTarget).mp
        hRankZero
    IdentifiesLanguageFromPositiveData
        (correctedConcreteCertifiedWorkingGrammarHypLanguage
          (selectedObservationProduct obsFamily ∅)
          f)
        (correctedConcreteCertifiedWorkingGrammarLearner
          hα
          (selectedObservationProduct obsFamily ∅)
          f)
        language ∧
      language ∈
        CorrectedConcreteCertifiedRankProfileClass
          (α := α)
          (M := ↥(∅ : Finset ι) → M)
          (selectedObservationProduct obsFamily ∅)
          f
          (startRootedTargetCertifiedDescriptionRank
            (v := z)
            hα
            (selectedObservationProduct obsFamily ∅)
            f
            hEmpty) ∧
      ∃
        C :
          CorrectedConcreteCertifiedWorkingGrammarHypothesis
            α
            (↥(∅ : Finset ι) → M)
            (selectedObservationProduct obsFamily ∅)
            f,
        C.output.grammar.StringLanguage =
            language ∧
          C.bits.length <=
            correctedConcreteCertifiedRankBitBudget
              (startRootedTargetCertifiedDescriptionRank
                (v := z)
                hα
                (selectedObservationProduct obsFamily ∅)
                f
                hEmpty)
              f ∧
          C.canonicalSearch.length <=
            correctedConcreteCertifiedRankSearchBudget
              (startRootedTargetCertifiedDescriptionRank
                (v := z)
                hα
                (selectedObservationProduct obsFamily ∅)
                f
                hEmpty)
              f := by

  let hEmpty :
      language ∈
        StartRootedCorrectedConcreteTargetClass
          (v := z)
          α
          (↥(∅ : Finset ι) → M)
          (selectedObservationProduct obsFamily ∅)
          f :=
    (ambientTarget_positiveAdditiveCostRank_eq_zero_iff_emptyProductTarget
      (z := z)
      obsFamily
      f
      coordinateWeight
      U
      hTarget).mp
      hRankZero

  exact
    ⟨selectedProductCertifiedLearner_identifies_targetClass
        (z := z)
        hα
        obsFamily
        f
        ∅
        language
        hEmpty,
      startRootedTarget_mem_minimumCertifiedDescriptionRankProfile
        (v := z)
        hα
        (selectedObservationProduct obsFamily ∅)
        f
        hEmpty,
      startRootedTarget_exists_output_at_minimumCertifiedDescriptionRank
        (v := z)
        hα
        (selectedObservationProduct obsFamily ∅)
        f
        hEmpty⟩

end RankZeroCertifiedLearner


section ObservationSelectionRankZeroFinalPackage

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
variable (coordinateWeight : ι → Nat)
variable (U : Finset ι)

/-- Final zero-cost class, exact rank-zero shell, empty-interface
characterization, selector, and certified-learning package. -/
theorem
    correctedConcreteCertifiedWorkingGrammar_observationSelectionRankZero_package :
    (CorrectedConcreteObservationSelectionExactCostRankClass
        (z := z)
        α
        ι
        M
        obsFamily
        f
        (correctedConcreteObservationSelectionPositiveAdditiveCost
          coordinateWeight)
        U
        0 =
      StartRootedCorrectedConcreteTargetClass
        (v := z)
        α
        (↥(∅ : Finset ι) → M)
        (selectedObservationProduct obsFamily ∅)
        f) ∧
      (CorrectedConcreteObservationSelectionExactCostRankClass
        (z := z)
        α
        ι
        M
        obsFamily
        f
        correctedConcreteObservationSelectionCardinalityCost
        U
        0 =
      StartRootedCorrectedConcreteTargetClass
        (v := z)
        α
        (↥(∅ : Finset ι) → M)
        (selectedObservationProduct obsFamily ∅)
        f) ∧
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
          (ambientTargetObservationSelectionCostRank
              (z := z)
              obsFamily
              f
              (correctedConcreteObservationSelectionPositiveAdditiveCost
                coordinateWeight)
              U
              hTarget =
            0 ↔
            language ∈
              StartRootedCorrectedConcreteTargetClass
                (v := z)
                α
                (↥(∅ : Finset ι) → M)
                (selectedObservationProduct obsFamily ∅)
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
        ∀ hRankZero :
          ambientTargetObservationSelectionCostRank
              (z := z)
              obsFamily
              f
              (correctedConcreteObservationSelectionPositiveAdditiveCost
                coordinateWeight)
              U
              hTarget =
            0,
          (correctedConcreteObservationPositiveAdditiveMinimumSelectionResult
              (z := z)
              obsFamily
              f
              coordinateWeight
              U
              language
              hTarget).selected =
            ∅) ∧
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
        ∀ hRankZero :
          ambientTargetObservationSelectionCostRank
              (z := z)
              obsFamily
              f
              (correctedConcreteObservationSelectionPositiveAdditiveCost
                coordinateWeight)
              U
              hTarget =
            0,
          IdentifiesLanguageFromPositiveData
            (correctedConcreteCertifiedWorkingGrammarHypLanguage
              (selectedObservationProduct obsFamily ∅)
              f)
            (correctedConcreteCertifiedWorkingGrammarLearner
              hα
              (selectedObservationProduct obsFamily ∅)
              f)
            language) := by

  refine
    ⟨positiveAdditiveObservationSelectionExactRankZeroClass_eq_emptyProductTargetClass
        (z := z)
        obsFamily
        f
        coordinateWeight
        U,
      cardinalityObservationSelectionExactRankZeroClass_eq_emptyProductTargetClass
        (z := z)
        obsFamily
        f
        U,
      ?_,
      ?_,
      ?_⟩

  · intro language hTarget

    exact
      ambientTarget_positiveAdditiveCostRank_eq_zero_iff_emptyProductTarget
        (z := z)
        obsFamily
        f
        coordinateWeight
        U
        hTarget

  · intro language hTarget hRankZero

    exact
      correctedConcreteObservationPositiveAdditiveMinimumSelectionResult_eq_empty_of_rank_zero
        (z := z)
        obsFamily
        f
        coordinateWeight
        U
        language
        hTarget
        hRankZero

  · intro language hTarget hRankZero

    exact
      (ambientTarget_positiveAdditiveRankZero_emptyProductCertified_package
        (z := z)
        hα
        obsFamily
        f
        coordinateWeight
        U
        hTarget
        hRankZero).1

end ObservationSelectionRankZeroFinalPackage

end MCFG
