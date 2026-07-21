/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG.ConcreteCanonicalLearnerWorkingGrammarObservationSelectionRankComparison

/-!
# ConcreteCanonicalLearnerWorkingGrammarObservationSelectionRankSensitivity.lean

The preceding file compares observation-selection rank hierarchies under an
exact pointwise order between two cost models.

This file develops a quantitative perturbation theory.

## Cost perturbation within a finite ambient set

For a finite ambient candidate set `U`, say that `selectionCost₁` is bounded by
`selectionCost₀` up to additive error `delta` when

```text
S ⊆ U
⇒
selectionCost₁ S ≤ selectionCost₀ S + delta.
```

Then every cost-`selectionCost₀` selection feasible at budget `b` is feasible
for `selectionCost₁` at budget `b + delta`.

Consequently:

```text
Profile(cost₀,b)
  ⊆
Profile(cost₁,b+delta),

Layer(cost₀,b)
  ⊆
Layer(cost₁,b+delta),

minimumRank(cost₁,L)
  ≤
minimumRank(cost₀,L)+delta.
```

An exact rank-`r₀` language for `selectionCost₀` therefore has some exact
`selectionCost₁` rank at most `r₀ + delta`.

## Two-sided sensitivity

If both directional perturbation bounds hold,

```text
cost₁(S) ≤ cost₀(S)+delta₀₁,
cost₀(S) ≤ cost₁(S)+delta₁₀,
```

then the two ranks satisfy

```text
rank₁ ≤ rank₀ + delta₀₁,
rank₀ ≤ rank₁ + delta₁₀.
```

No integer subtraction or absolute-value convention is required.

## Coordinate-weight perturbations

For coordinate weights `weight₀` and `weight₁`, assume

```text
weight₁ i ≤ weight₀ i + d
```

for every candidate coordinate.  For every selected subset `S`,

```text
AdditiveCost(weight₁,S)
  ≤
AdditiveCost(weight₀,S) + d * |S|.
```

Inside `U`, this yields the uniform perturbation bound

```text
AdditiveCost(weight₁,S)
  ≤
AdditiveCost(weight₀,S) + d * |U|.
```

The same bound holds for positive additive cost

```text
|S| + AdditiveCost(weight,S).
```

Hence both additive and positive-additive observation-selection ranks can
increase by at most `d * |U|` when every coordinate weight increases by at most
`d`.

This complements the monotonicity theorem from the preceding file: coordinate
weights may change non-monotonically, yet a uniform perturbation still gives a
quantitative rank bound.

## Certified selectors

For every full ambient-product target, the minimum selectors for the two cost
models carry their own certified learners.  Their observation-selection ranks
satisfy the perturbation inequality, and both selected-product learners
identify the same target language.

No relation between the two grammar-description ranks is asserted.

## Boundary

All optimization remains semantic and finite.  The perturbation results are
exact theorems about the rank hierarchy, not an executable sensitivity
algorithm.

No target grammar is supplied to any learner.
No `sorry`, `admit`, or `axiom` is used.
-/

namespace MCFG

universe u v w z


section CostPerturbationDefinitions

variable {ι : Type v}

/-- `selectionCost₁` is at most `selectionCost₀` plus `delta` on every selected
subset of the fixed ambient candidate set `U`. -/
def CorrectedConcreteObservationSelectionCostLeUpToWithin
    (U : Finset ι)
    (selectionCost₀ selectionCost₁ : Finset ι → Nat)
    (delta : Nat) :
    Prop :=
  ∀ S : Finset ι,
    S ⊆ U →
      selectionCost₁ S <=
        selectionCost₀ S + delta

/-- Two-sided additive perturbation bounds between finite selection costs. -/
def CorrectedConcreteObservationSelectionCostsWithin
    (U : Finset ι)
    (selectionCost₀ selectionCost₁ : Finset ι → Nat)
    (delta₀₁ delta₁₀ : Nat) :
    Prop :=
  CorrectedConcreteObservationSelectionCostLeUpToWithin
      U selectionCost₀ selectionCost₁ delta₀₁ ∧
    CorrectedConcreteObservationSelectionCostLeUpToWithin
      U selectionCost₁ selectionCost₀ delta₁₀

/-- Zero-error ambient comparison is induced by global pointwise cost order. -/
theorem observationSelectionCostLeUpToWithin_zero_of_pointwiseLe
    {U : Finset ι}
    {selectionCost₀ selectionCost₁ : Finset ι → Nat}
    (hCost :
      CorrectedConcreteObservationSelectionCostPointwiseLe
        selectionCost₁ selectionCost₀) :
    CorrectedConcreteObservationSelectionCostLeUpToWithin
      U selectionCost₀ selectionCost₁ 0 := by

  intro S hSU

  simpa using
    hCost S

/-- Ambient additive perturbation bounds compose. -/
theorem observationSelectionCostLeUpToWithin_trans
    {U : Finset ι}
    {selectionCost₀ selectionCost₁ selectionCost₂ :
      Finset ι → Nat}
    {delta₀₁ delta₁₂ : Nat}
    (h₀₁ :
      CorrectedConcreteObservationSelectionCostLeUpToWithin
        U selectionCost₀ selectionCost₁ delta₀₁)
    (h₁₂ :
      CorrectedConcreteObservationSelectionCostLeUpToWithin
        U selectionCost₁ selectionCost₂ delta₁₂) :
    CorrectedConcreteObservationSelectionCostLeUpToWithin
      U
      selectionCost₀
      selectionCost₂
      (delta₀₁ + delta₁₂) := by

  intro S hSU

  have hFirst :
      selectionCost₁ S <=
        selectionCost₀ S + delta₀₁ :=
    h₀₁ S hSU

  have hSecond :
      selectionCost₂ S <=
        selectionCost₁ S + delta₁₂ :=
    h₁₂ S hSU

  omega

end CostPerturbationDefinitions


section CostPerturbationFeasibility

variable {α : Type u}
variable {ι : Type v}
variable {M : Type w}
variable [Monoid M]
variable {obsFamily : ι → α → M}
variable {f : Nat}
variable {selectionCost₀ selectionCost₁ : Finset ι → Nat}
variable {U : Finset ι}
variable {language : Set (Word α)}
variable {delta : Nat}

/-- A feasible selection under `selectionCost₀` at budget `b` remains feasible
under `selectionCost₁` at shifted budget `b + delta`. -/
theorem observationSelectionAtCost_shift_of_leUpToWithin
    (hCost :
      CorrectedConcreteObservationSelectionCostLeUpToWithin
        U selectionCost₀ selectionCost₁ delta)
    {costBudget : Nat}
    (hSelection :
      CorrectedConcreteObservationSelectionAtCost
        (obsFamily := obsFamily)
        (f := f)
        selectionCost₀
        U
        language
        costBudget) :
    CorrectedConcreteObservationSelectionAtCost
      (obsFamily := obsFamily)
      (f := f)
      selectionCost₁
      U
      language
      (costBudget + delta) := by

  rcases hSelection with
    ⟨S, hSU, hCost₀, hTarget⟩

  have hPerturb :
      selectionCost₁ S <=
        selectionCost₀ S + delta :=
    hCost S hSU

  exact
    ⟨S,
      hSU,
      hPerturb.trans
        (Nat.add_le_add_right
          hCost₀
          delta),
      hTarget⟩

/-- Selection existence transports across a finite ambient perturbation. -/
theorem hasObservationSelectionCost_of_leUpToWithin
    (hCost :
      CorrectedConcreteObservationSelectionCostLeUpToWithin
        U selectionCost₀ selectionCost₁ delta)
    (hSelection :
      HasCorrectedConcreteObservationSelectionCost
        (obsFamily := obsFamily)
        (f := f)
        selectionCost₀
        U
        language) :
    HasCorrectedConcreteObservationSelectionCost
      (obsFamily := obsFamily)
      (f := f)
      selectionCost₁
      U
      language := by

  rcases hSelection with
    ⟨costBudget, hAtCost⟩

  exact
    ⟨costBudget + delta,
      observationSelectionAtCost_shift_of_leUpToWithin
        hCost hAtCost⟩

/-- Cumulative profile inclusion with an additive budget shift. -/
theorem observationSelectionCostProfileClass_subset_shifted_of_leUpToWithin
    (hCost :
      CorrectedConcreteObservationSelectionCostLeUpToWithin
        U selectionCost₀ selectionCost₁ delta)
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
        costBudget ⊆
      CorrectedConcreteObservationSelectionCostProfileClass
        (z := z)
        α
        ι
        M
        obsFamily
        f
        selectionCost₁
        U
        (costBudget + delta) := by

  intro target hTarget

  exact
    observationSelectionAtCost_shift_of_leUpToWithin
      hCost hTarget

/-- A shifted obstruction for `selectionCost₁` transports backward to an
obstruction for `selectionCost₀`. -/
theorem
    observationSelection_not_mem_cheaperProfile_of_not_mem_shiftedPerturbedProfile
    (hCost :
      CorrectedConcreteObservationSelectionCostLeUpToWithin
        U selectionCost₀ selectionCost₁ delta)
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
          selectionCost₁
          U
          (costBudget + delta)) :
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
        costBudget := by

  intro hProfile₀

  exact
    hNot
      (observationSelectionCostProfileClass_subset_shifted_of_leUpToWithin
        (z := z)
        hCost
        costBudget
        hProfile₀)

end CostPerturbationFeasibility


section CostPerturbationFiltration

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
variable {delta : Nat}

/-- Budget filtration inclusion with an additive shift. -/
theorem observationCostBudgetFiltration_subset_shifted_of_leUpToWithin
    (hCost :
      CorrectedConcreteObservationSelectionCostLeUpToWithin
        U selectionCost₀ selectionCost₁ delta)
    (costBudget : Nat) :
    correctedConcreteObservationCostBudgetFiltration
        (z := z)
        obsFamily
        f
        selectionCost₀
        U
        language
        costBudget ⊆
      correctedConcreteObservationCostBudgetFiltration
        (z := z)
        obsFamily
        f
        selectionCost₁
        U
        language
        (costBudget + delta) := by

  intro S hS

  rcases
      (mem_correctedConcreteObservationCostBudgetFiltration_iff
        (z := z)).mp
        hS with
    ⟨hSU, hCost₀, hTarget⟩

  have hPerturb :
      selectionCost₁ S <=
        selectionCost₀ S + delta :=
    hCost S hSU

  exact
    (mem_correctedConcreteObservationCostBudgetFiltration_iff
      (z := z)).mpr
      ⟨hSU,
        hPerturb.trans
          (Nat.add_le_add_right
            hCost₀
            delta),
        hTarget⟩

end CostPerturbationFiltration


section MinimumCostSensitivity

variable {α : Type u}
variable {ι : Type v}
variable {M : Type w}
variable [Monoid M]
variable {obsFamily : ι → α → M}
variable {f : Nat}
variable {selectionCost₀ selectionCost₁ : Finset ι → Nat}
variable {U : Finset ι}
variable {language : Set (Word α)}
variable {delta : Nat}

/-- Minimum observation-selection cost changes by at most the ambient
perturbation bound in the controlled direction. -/
theorem observationSelectionMinimumCost_le_add_of_leUpToWithin
    (hCost :
      CorrectedConcreteObservationSelectionCostLeUpToWithin
        U selectionCost₀ selectionCost₁ delta)
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
        selectionCost₁
        hSelection₁ <=
      correctedConcreteObservationSelectionMinimumCost
          selectionCost₀
          hSelection₀ +
        delta := by

  rcases hSelection₀.exists_selection_exact_minimumCost with
    ⟨S, hSU, hCost₀, hTarget⟩

  apply
    hSelection₁.minimumCost_le_of_selection

  have hPerturb :
      selectionCost₁ S <=
        selectionCost₀ S + delta :=
    hCost S hSU

  rw [hCost₀] at hPerturb

  exact
    ⟨S,
      hSU,
      hPerturb,
      hTarget⟩

/-- Two-sided perturbation gives two directional minimum-rank bounds. -/
theorem observationSelectionMinimumCosts_twoSidedBounds
    {delta₀₁ delta₁₀ : Nat}
    (hCosts :
      CorrectedConcreteObservationSelectionCostsWithin
        U
        selectionCost₀
        selectionCost₁
        delta₀₁
        delta₁₀)
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
          selectionCost₁
          hSelection₁ <=
        correctedConcreteObservationSelectionMinimumCost
            selectionCost₀
            hSelection₀ +
          delta₀₁ ∧
      correctedConcreteObservationSelectionMinimumCost
          selectionCost₀
          hSelection₀ <=
        correctedConcreteObservationSelectionMinimumCost
            selectionCost₁
            hSelection₁ +
          delta₁₀ := by

  exact
    ⟨observationSelectionMinimumCost_le_add_of_leUpToWithin
        hCosts.1
        hSelection₀
        hSelection₁,
      observationSelectionMinimumCost_le_add_of_leUpToWithin
        hCosts.2
        hSelection₁
        hSelection₀⟩

end MinimumCostSensitivity


section ExactRankSensitivity

variable {α : Type u}
variable {ι : Type v}
variable {M : Type w}
variable [Monoid M]
variable {obsFamily : ι → α → M}
variable {f : Nat}
variable {selectionCost₀ selectionCost₁ : Finset ι → Nat}
variable {U : Finset ι}
variable {language : Set (Word α)}
variable {delta : Nat}

/-- An exact `selectionCost₀` rank transfers to some exact `selectionCost₁`
rank no greater than the original rank plus the perturbation. -/
theorem observationSelection_exactRank_exists_perturbedRank_le_add
    (hCost :
      CorrectedConcreteObservationSelectionCostLeUpToWithin
        U selectionCost₀ selectionCost₁ delta)
    {rank₀ : Nat}
    (hRank₀ :
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
          rank₀) :
    ∃ rank₁ : Nat,
      rank₁ <= rank₀ + delta ∧
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
            rank₁ := by

  let hSelection₁ :
      HasCorrectedConcreteObservationSelectionCost
        (obsFamily := obsFamily)
        (f := f)
        selectionCost₁
        U
        language :=
    ⟨rank₀ + delta,
      observationSelectionAtCost_shift_of_leUpToWithin
        hCost
        hRank₀.1⟩

  let rank₁ :=
    correctedConcreteObservationSelectionMinimumCost
      selectionCost₁
      hSelection₁

  have hRankBound :
      rank₁ <= rank₀ + delta :=
    hSelection₁.minimumCost_le_of_selection
      (observationSelectionAtCost_shift_of_leUpToWithin
        hCost
        hRank₀.1)

  exact
    ⟨rank₁,
      hRankBound,
      observationSelection_mem_exactMinimumCostRankClass
        (z := z)
        hSelection₁⟩

end ExactRankSensitivity


section AmbientTargetRankSensitivity

variable {α : Type u}
variable {ι : Type v}
variable {M : Type w}
variable [Monoid M]
variable (obsFamily : ι → α → M)
variable (f : Nat)
variable (selectionCost₀ selectionCost₁ : Finset ι → Nat)
variable (U : Finset ι)

/-- Paper-facing target rank sensitivity under an ambient additive cost
perturbation. -/
theorem ambientTargetObservationSelectionCostRank_le_add_of_leUpToWithin
    {delta : Nat}
    (hCost :
      CorrectedConcreteObservationSelectionCostLeUpToWithin
        U selectionCost₀ selectionCost₁ delta)
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
        selectionCost₁
        U
        hTarget <=
      ambientTargetObservationSelectionCostRank
          (z := z)
          obsFamily
          f
          selectionCost₀
          U
          hTarget +
        delta := by

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
    observationSelectionMinimumCost_le_add_of_leUpToWithin
      hCost
      hSelection₀
      hSelection₁

/-- Two-sided paper-facing rank sensitivity. -/
theorem ambientTargetObservationSelectionCostRanks_twoSidedBounds
    {delta₀₁ delta₁₀ : Nat}
    (hCosts :
      CorrectedConcreteObservationSelectionCostsWithin
        U
        selectionCost₀
        selectionCost₁
        delta₀₁
        delta₁₀)
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
          selectionCost₁
          U
          hTarget <=
        ambientTargetObservationSelectionCostRank
            (z := z)
            obsFamily
            f
            selectionCost₀
            U
            hTarget +
          delta₀₁ ∧
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
            hTarget +
          delta₁₀ := by

  exact
    ⟨ambientTargetObservationSelectionCostRank_le_add_of_leUpToWithin
        (z := z)
        obsFamily
        f
        selectionCost₀
        selectionCost₁
        U
        hCosts.1
        hTarget,
      ambientTargetObservationSelectionCostRank_le_add_of_leUpToWithin
        (z := z)
        obsFamily
        f
        selectionCost₁
        selectionCost₀
        U
        hCosts.2
        hTarget⟩

end AmbientTargetRankSensitivity


section CoordinateWeightPerturbationDefinitions

variable {ι : Type v}

/-- Coordinatewise additive weight perturbation. -/
def CorrectedConcreteObservationCoordinateWeightsLeUpTo
    (coordinateWeight₀ coordinateWeight₁ : ι → Nat)
    (coordinateDelta : Nat) :
    Prop :=
  ∀ index : ι,
    coordinateWeight₁ index <=
      coordinateWeight₀ index + coordinateDelta

/-- Two-sided coordinatewise additive weight perturbation. -/
def CorrectedConcreteObservationCoordinateWeightsWithin
    (coordinateWeight₀ coordinateWeight₁ : ι → Nat)
    (delta₀₁ delta₁₀ : Nat) :
    Prop :=
  CorrectedConcreteObservationCoordinateWeightsLeUpTo
      coordinateWeight₀ coordinateWeight₁ delta₀₁ ∧
    CorrectedConcreteObservationCoordinateWeightsLeUpTo
      coordinateWeight₁ coordinateWeight₀ delta₁₀

end CoordinateWeightPerturbationDefinitions


section FiniteWeightedSumPerturbation

variable {ι : Type v}

/-- Coordinatewise additive perturbation accumulates by at most
`coordinateDelta * |S|` over one finite selected set. -/
theorem finsetNatWeightedSum_le_add_delta_mul_card
    {coordinateWeight₀ coordinateWeight₁ : ι → Nat}
    {coordinateDelta : Nat}
    (hWeight :
      CorrectedConcreteObservationCoordinateWeightsLeUpTo
        coordinateWeight₀
        coordinateWeight₁
        coordinateDelta)
    (S : Finset ι) :
    (∑ index in S, coordinateWeight₁ index) <=
      (∑ index in S, coordinateWeight₀ index) +
        coordinateDelta * S.card := by

  classical

  induction S using Finset.induction_on with

  | empty =>

      simp

  | @insert selectedIndex S hNotMem ih =>

      have hSelected :
          coordinateWeight₁ selectedIndex <=
            coordinateWeight₀ selectedIndex +
              coordinateDelta :=
        hWeight selectedIndex

      calc
        (∑ index in insert selectedIndex S,
            coordinateWeight₁ index) =
            coordinateWeight₁ selectedIndex +
              ∑ index in S,
                coordinateWeight₁ index := by
                  rw [
                    Finset.sum_insert hNotMem
                  ]

        _ <=
            (coordinateWeight₀ selectedIndex +
                coordinateDelta) +
              ((∑ index in S,
                  coordinateWeight₀ index) +
                coordinateDelta * S.card) :=
          Nat.add_le_add
            hSelected
            ih

        _ =
            (∑ index in insert selectedIndex S,
                coordinateWeight₀ index) +
              coordinateDelta *
                (insert selectedIndex S).card := by
          rw [
            Finset.sum_insert hNotMem,
            Finset.card_insert_of_not_mem hNotMem,
            Nat.mul_add,
            Nat.mul_one
          ]
          omega

end FiniteWeightedSumPerturbation


section AdditiveCostPerturbation

variable {ι : Type v}

/-- Additive coordinate cost perturbation on one selected set. -/
theorem observationSelectionAdditiveCost_le_add_delta_mul_card
    {coordinateWeight₀ coordinateWeight₁ : ι → Nat}
    {coordinateDelta : Nat}
    (hWeight :
      CorrectedConcreteObservationCoordinateWeightsLeUpTo
        coordinateWeight₀
        coordinateWeight₁
        coordinateDelta)
    (S : Finset ι) :
    correctedConcreteObservationSelectionAdditiveCost
        coordinateWeight₁ S <=
      correctedConcreteObservationSelectionAdditiveCost
          coordinateWeight₀ S +
        coordinateDelta * S.card := by

  exact
    finsetNatWeightedSum_le_add_delta_mul_card
      hWeight S

/-- Positive additive coordinate cost obeys the same perturbation estimate. -/
theorem observationSelectionPositiveAdditiveCost_le_add_delta_mul_card
    {coordinateWeight₀ coordinateWeight₁ : ι → Nat}
    {coordinateDelta : Nat}
    (hWeight :
      CorrectedConcreteObservationCoordinateWeightsLeUpTo
        coordinateWeight₀
        coordinateWeight₁
        coordinateDelta)
    (S : Finset ι) :
    correctedConcreteObservationSelectionPositiveAdditiveCost
        coordinateWeight₁ S <=
      correctedConcreteObservationSelectionPositiveAdditiveCost
          coordinateWeight₀ S +
        coordinateDelta * S.card := by

  have hAdditive :
      correctedConcreteObservationSelectionAdditiveCost
          coordinateWeight₁ S <=
        correctedConcreteObservationSelectionAdditiveCost
            coordinateWeight₀ S +
          coordinateDelta * S.card :=
    observationSelectionAdditiveCost_le_add_delta_mul_card
      hWeight S

  unfold
    correctedConcreteObservationSelectionPositiveAdditiveCost

  omega

/-- Inside one finite ambient candidate set, additive costs differ by at most
`coordinateDelta * |U|`. -/
theorem observationSelectionAdditiveCost_leUpToWithin_of_weightsLeUpTo
    {U : Finset ι}
    {coordinateWeight₀ coordinateWeight₁ : ι → Nat}
    {coordinateDelta : Nat}
    (hWeight :
      CorrectedConcreteObservationCoordinateWeightsLeUpTo
        coordinateWeight₀
        coordinateWeight₁
        coordinateDelta) :
    CorrectedConcreteObservationSelectionCostLeUpToWithin
      U
      (correctedConcreteObservationSelectionAdditiveCost
        coordinateWeight₀)
      (correctedConcreteObservationSelectionAdditiveCost
        coordinateWeight₁)
      (coordinateDelta * U.card) := by

  intro S hSU

  have hLocal :
      correctedConcreteObservationSelectionAdditiveCost
          coordinateWeight₁ S <=
        correctedConcreteObservationSelectionAdditiveCost
            coordinateWeight₀ S +
          coordinateDelta * S.card :=
    observationSelectionAdditiveCost_le_add_delta_mul_card
      hWeight S

  have hCard :
      S.card <= U.card :=
    Finset.card_le_card hSU

  have hDelta :
      coordinateDelta * S.card <=
        coordinateDelta * U.card :=
    Nat.mul_le_mul_left
      coordinateDelta
      hCard

  omega

/-- Inside one finite ambient candidate set, positive additive costs differ by
at most `coordinateDelta * |U|`. -/
theorem
    observationSelectionPositiveAdditiveCost_leUpToWithin_of_weightsLeUpTo
    {U : Finset ι}
    {coordinateWeight₀ coordinateWeight₁ : ι → Nat}
    {coordinateDelta : Nat}
    (hWeight :
      CorrectedConcreteObservationCoordinateWeightsLeUpTo
        coordinateWeight₀
        coordinateWeight₁
        coordinateDelta) :
    CorrectedConcreteObservationSelectionCostLeUpToWithin
      U
      (correctedConcreteObservationSelectionPositiveAdditiveCost
        coordinateWeight₀)
      (correctedConcreteObservationSelectionPositiveAdditiveCost
        coordinateWeight₁)
      (coordinateDelta * U.card) := by

  intro S hSU

  have hLocal :
      correctedConcreteObservationSelectionPositiveAdditiveCost
          coordinateWeight₁ S <=
        correctedConcreteObservationSelectionPositiveAdditiveCost
            coordinateWeight₀ S +
          coordinateDelta * S.card :=
    observationSelectionPositiveAdditiveCost_le_add_delta_mul_card
      hWeight S

  have hCard :
      S.card <= U.card :=
    Finset.card_le_card hSU

  have hDelta :
      coordinateDelta * S.card <=
        coordinateDelta * U.card :=
    Nat.mul_le_mul_left
      coordinateDelta
      hCard

  omega

end AdditiveCostPerturbation


section CoordinateWeightRankSensitivity

variable {α : Type u}
variable {ι : Type v}
variable {M : Type w}
variable [Monoid M]
variable (obsFamily : ι → α → M)
variable (f : Nat)
variable (U : Finset ι)

/-- Additive observation-selection rank sensitivity under coordinatewise weight
perturbation. -/
theorem ambientTarget_additiveCostRank_le_add_weightPerturbation
    {coordinateWeight₀ coordinateWeight₁ : ι → Nat}
    {coordinateDelta : Nat}
    (hWeight :
      CorrectedConcreteObservationCoordinateWeightsLeUpTo
        coordinateWeight₀
        coordinateWeight₁
        coordinateDelta)
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
          coordinateWeight₁)
        U
        hTarget <=
      ambientTargetObservationSelectionCostRank
          (z := z)
          obsFamily
          f
          (correctedConcreteObservationSelectionAdditiveCost
            coordinateWeight₀)
          U
          hTarget +
        coordinateDelta * U.card := by

  exact
    ambientTargetObservationSelectionCostRank_le_add_of_leUpToWithin
      (z := z)
      obsFamily
      f
      (correctedConcreteObservationSelectionAdditiveCost
        coordinateWeight₀)
      (correctedConcreteObservationSelectionAdditiveCost
        coordinateWeight₁)
      U
      (observationSelectionAdditiveCost_leUpToWithin_of_weightsLeUpTo
        hWeight)
      hTarget

/-- Positive-additive observation-selection rank sensitivity under
coordinatewise weight perturbation. -/
theorem ambientTarget_positiveAdditiveCostRank_le_add_weightPerturbation
    {coordinateWeight₀ coordinateWeight₁ : ι → Nat}
    {coordinateDelta : Nat}
    (hWeight :
      CorrectedConcreteObservationCoordinateWeightsLeUpTo
        coordinateWeight₀
        coordinateWeight₁
        coordinateDelta)
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
          coordinateWeight₁)
        U
        hTarget <=
      ambientTargetObservationSelectionCostRank
          (z := z)
          obsFamily
          f
          (correctedConcreteObservationSelectionPositiveAdditiveCost
            coordinateWeight₀)
          U
          hTarget +
        coordinateDelta * U.card := by

  exact
    ambientTargetObservationSelectionCostRank_le_add_of_leUpToWithin
      (z := z)
      obsFamily
      f
      (correctedConcreteObservationSelectionPositiveAdditiveCost
        coordinateWeight₀)
      (correctedConcreteObservationSelectionPositiveAdditiveCost
        coordinateWeight₁)
      U
      (observationSelectionPositiveAdditiveCost_leUpToWithin_of_weightsLeUpTo
        hWeight)
      hTarget

/-- Two-sided positive-additive rank sensitivity under two-sided coordinate
weight perturbations. -/
theorem ambientTarget_positiveAdditiveCostRanks_twoSidedWeightBounds
    {coordinateWeight₀ coordinateWeight₁ : ι → Nat}
    {delta₀₁ delta₁₀ : Nat}
    (hWeights :
      CorrectedConcreteObservationCoordinateWeightsWithin
        coordinateWeight₀
        coordinateWeight₁
        delta₀₁
        delta₁₀)
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
            coordinateWeight₁)
          U
          hTarget <=
        ambientTargetObservationSelectionCostRank
            (z := z)
            obsFamily
            f
            (correctedConcreteObservationSelectionPositiveAdditiveCost
              coordinateWeight₀)
            U
            hTarget +
          delta₀₁ * U.card ∧
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
            hTarget +
          delta₁₀ * U.card := by

  exact
    ⟨ambientTarget_positiveAdditiveCostRank_le_add_weightPerturbation
        (z := z)
        obsFamily
        f
        U
        hWeights.1
        hTarget,
      ambientTarget_positiveAdditiveCostRank_le_add_weightPerturbation
        (z := z)
        obsFamily
        f
        U
        hWeights.2
        hTarget⟩

end CoordinateWeightRankSensitivity


section CertifiedCostSensitivity

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

/-- Two perturbed cost models admit certified minimum selections whose
observation-selection ranks satisfy the additive sensitivity bound. -/
theorem ambientTarget_costRankSensitivity_certified_package
    {delta : Nat}
    (hCost :
      CorrectedConcreteObservationSelectionCostLeUpToWithin
        U selectionCost₀ selectionCost₁ delta)
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
      rank₁ <= rank₀ + delta ∧
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
          language := by

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

  have hRankBound :
      rank₁ <= rank₀ + delta := by

    rw [hRank₀, hRank₁]

    exact
      ambientTargetObservationSelectionCostRank_le_add_of_leUpToWithin
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
      hRankBound,
      hCost₀,
      hCost₁,
      hIdentifies₀,
      hIdentifies₁⟩

end CertifiedCostSensitivity


section ObservationSelectionRankSensitivityFinalPackage

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

/-- Final shifted-profile, shifted-filtration, exact-shell, rank-sensitivity,
and certified-selector package. -/
theorem
    correctedConcreteCertifiedWorkingGrammar_observationSelectionRankSensitivity_package
    {delta : Nat}
    (hCost :
      CorrectedConcreteObservationSelectionCostLeUpToWithin
        U selectionCost₀ selectionCost₁ delta) :
    (∀ costBudget : Nat,
      CorrectedConcreteObservationSelectionCostProfileClass
          (z := z)
          α
          ι
          M
          obsFamily
          f
          selectionCost₀
          U
          costBudget ⊆
        CorrectedConcreteObservationSelectionCostProfileClass
          (z := z)
          α
          ι
          M
          obsFamily
          f
          selectionCost₁
          U
          (costBudget + delta)) ∧
      (∀
        language : Set (Word α),
        ∀ costBudget : Nat,
          correctedConcreteObservationCostBudgetFiltration
              (z := z)
              obsFamily
              f
              selectionCost₀
              U
              language
              costBudget ⊆
            correctedConcreteObservationCostBudgetFiltration
              (z := z)
              obsFamily
              f
              selectionCost₁
              U
              language
              (costBudget + delta)) ∧
      (∀
        language : Set (Word α),
        ∀ rank₀ : Nat,
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
                rank₀ →
            ∃ rank₁ : Nat,
              rank₁ <= rank₀ + delta ∧
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
                    rank₁) ∧
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
              selectionCost₁
              U
              hTarget <=
            ambientTargetObservationSelectionCostRank
                (z := z)
                obsFamily
                f
                selectionCost₀
                U
                hTarget +
              delta) ∧
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
            rank₁ <= rank₀ + delta ∧
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
      observationSelectionCostProfileClass_subset_shifted_of_leUpToWithin
        (z := z)
        hCost
        costBudget

  · intro language costBudget

    exact
      observationCostBudgetFiltration_subset_shifted_of_leUpToWithin
        (z := z)
        hCost
        costBudget

  · intro language rank₀ hRank₀

    exact
      observationSelection_exactRank_exists_perturbedRank_le_add
        (z := z)
        hCost
        hRank₀

  · intro language hTarget

    exact
      ambientTargetObservationSelectionCostRank_le_add_of_leUpToWithin
        (z := z)
        obsFamily
        f
        selectionCost₀
        selectionCost₁
        U
        hCost
        hTarget

  · intro language hTarget

    exact
      ambientTarget_costRankSensitivity_certified_package
        (z := z)
        hα
        obsFamily
        f
        selectionCost₀
        selectionCost₁
        U
        hCost
        hTarget

end ObservationSelectionRankSensitivityFinalPackage

end MCFG
