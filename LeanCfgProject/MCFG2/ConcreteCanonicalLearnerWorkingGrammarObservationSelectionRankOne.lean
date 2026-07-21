/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG.ConcreteCanonicalLearnerWorkingGrammarObservationSelectionRankZero

/-!
# ConcreteCanonicalLearnerWorkingGrammarObservationSelectionRankOne.lean

The preceding file identifies observation-selection rank zero with complete
removability of the finite observation interface.

This file identifies rank one.

## One-coordinate target class

A language belongs to the one-coordinate target class when some selected
subset `S ⊆ U` with

```text
S.card = 1
```

already represents the target.

For ordinary cardinality cost, exact rank one means precisely:

```text
some one-coordinate selected product represents the target,
but the empty selected product does not.
```

Thus cardinality rank one is the first genuinely observation-dependent layer.

## Positive additive rank one

For positive additive cost

```text
PositiveAdditiveCost(S)
  =
S.card + AdditiveCost(weight,S),
```

cost one forces

```text
S.card = 1
and
AdditiveCost(weight,S) = 0.
```

Therefore exact positive-additive rank one means:

```text
some one-coordinate selected product represents the target,
the selected coordinate has zero total extra weight,
and the empty selected product does not represent the target.
```

No singleton-coordinate extraction lemma is needed: the selected finite set
itself carries the exact cardinality-one certificate.

## Target-rank characterizations

For every target represented by the full ambient product,

```text
cardinality rank = 1
```

is equivalent to the one-coordinate/nonempty-interface characterization above.

The analogous theorem holds for positive additive rank.

## Certified rank-one witnesses

Every exact rank-one target comes with an actual cardinality-one selected subset.
The certified learner for that selected product identifies the target and
returns one exact checked grammar output at the selected product's minimum
certified-description rank.

For positive additive rank one, the witness additionally has zero additive
coordinate cost.

## Interpretation

Rank zero says that all observation coordinates can be removed.
Rank one says that the whole interface can be compressed to one selected
coordinate, but not to zero coordinates.

No target grammar is supplied to any learner.
No `sorry`, `admit`, or `axiom` is used.
-/

namespace MCFG

universe u v w z


section OneCoordinateTargetClassDefinitions

variable (α : Type u)
variable (ι : Type v)
variable (M : Type w)
variable [Monoid M]
variable (obsFamily : ι → α → M)
variable (f : Nat)
variable (U : Finset ι)

/-- Languages represented by some ambient selected product using exactly one
observation coordinate. -/
def CorrectedConcreteObservationSelectionOneCoordinateTargetClass :
    Set (Set (Word α)) :=
  {language |
    ∃ S : Finset ι,
      S ⊆ U ∧
        S.card = 1 ∧
        language ∈
          StartRootedCorrectedConcreteTargetClass
            (v := z)
            α
            (↥S → M)
            (selectedObservationProduct obsFamily S)
            f}

/-- Cardinality-rank-one candidate class: one coordinate suffices, but the
empty selected product does not. -/
def CorrectedConcreteCardinalityObservationSelectionRankOneClass :
    Set (Set (Word α)) :=
  {language |
    language ∈
        CorrectedConcreteObservationSelectionOneCoordinateTargetClass
          (z := z)
          α
          ι
          M
          obsFamily
          f
          U ∧
      language ∉
        StartRootedCorrectedConcreteTargetClass
          (v := z)
          α
          (↥(∅ : Finset ι) → M)
          (selectedObservationProduct obsFamily ∅)
          f}

end OneCoordinateTargetClassDefinitions


section PositiveAdditiveRankOneClassDefinition

variable (α : Type u)
variable (ι : Type v)
variable (M : Type w)
variable [Monoid M]
variable (obsFamily : ι → α → M)
variable (f : Nat)
variable (coordinateWeight : ι → Nat)
variable (U : Finset ι)

/-- Positive-additive unit-cost witness class: one coordinate is selected, its
total extra additive weight is zero, and the selected product represents the
target. -/
def CorrectedConcretePositiveAdditiveObservationSelectionUnitTargetClass :
    Set (Set (Word α)) :=
  {language |
    ∃ S : Finset ι,
      S ⊆ U ∧
        S.card = 1 ∧
        correctedConcreteObservationSelectionAdditiveCost
            coordinateWeight S =
          0 ∧
        language ∈
          StartRootedCorrectedConcreteTargetClass
            (v := z)
            α
            (↥S → M)
            (selectedObservationProduct obsFamily S)
            f}

/-- Positive-additive-rank-one candidate class: a zero-extra-weight
one-coordinate product suffices, but the empty product does not. -/
def CorrectedConcretePositiveAdditiveObservationSelectionRankOneClass :
    Set (Set (Word α)) :=
  {language |
    language ∈
        CorrectedConcretePositiveAdditiveObservationSelectionUnitTargetClass
          (z := z)
          α
          ι
          M
          obsFamily
          f
          coordinateWeight
          U ∧
      language ∉
        StartRootedCorrectedConcreteTargetClass
          (v := z)
          α
          (↥(∅ : Finset ι) → M)
          (selectedObservationProduct obsFamily ∅)
          f}

end PositiveAdditiveRankOneClassDefinition


section RankOneClassMembership

variable {α : Type u}
variable {ι : Type v}
variable {M : Type w}
variable [Monoid M]
variable {obsFamily : ι → α → M}
variable {f : Nat}
variable {coordinateWeight : ι → Nat}
variable {U : Finset ι}
variable {language : Set (Word α)}

/-- Exact membership theorem for the one-coordinate target class. -/
theorem mem_observationSelectionOneCoordinateTargetClass_iff :
    language ∈
        CorrectedConcreteObservationSelectionOneCoordinateTargetClass
          (z := z)
          α
          ι
          M
          obsFamily
          f
          U ↔
      ∃ S : Finset ι,
        S ⊆ U ∧
          S.card = 1 ∧
          language ∈
            StartRootedCorrectedConcreteTargetClass
              (v := z)
              α
              (↥S → M)
              (selectedObservationProduct obsFamily S)
              f := by

  rfl

/-- Exact membership theorem for the cardinality-rank-one candidate class. -/
theorem mem_cardinalityObservationSelectionRankOneClass_iff :
    language ∈
        CorrectedConcreteCardinalityObservationSelectionRankOneClass
          (z := z)
          α
          ι
          M
          obsFamily
          f
          U ↔
      (∃ S : Finset ι,
        S ⊆ U ∧
          S.card = 1 ∧
          language ∈
            StartRootedCorrectedConcreteTargetClass
              (v := z)
              α
              (↥S → M)
              (selectedObservationProduct obsFamily S)
              f) ∧
        language ∉
          StartRootedCorrectedConcreteTargetClass
            (v := z)
            α
            (↥(∅ : Finset ι) → M)
            (selectedObservationProduct obsFamily ∅)
            f := by

  rfl

/-- Exact membership theorem for the positive-additive unit-target class. -/
theorem mem_positiveAdditiveObservationSelectionUnitTargetClass_iff :
    language ∈
        CorrectedConcretePositiveAdditiveObservationSelectionUnitTargetClass
          (z := z)
          α
          ι
          M
          obsFamily
          f
          coordinateWeight
          U ↔
      ∃ S : Finset ι,
        S ⊆ U ∧
          S.card = 1 ∧
          correctedConcreteObservationSelectionAdditiveCost
              coordinateWeight S =
            0 ∧
          language ∈
            StartRootedCorrectedConcreteTargetClass
              (v := z)
              α
              (↥S → M)
              (selectedObservationProduct obsFamily S)
              f := by

  rfl

/-- Exact membership theorem for the positive-additive-rank-one candidate
class. -/
theorem mem_positiveAdditiveObservationSelectionRankOneClass_iff :
    language ∈
        CorrectedConcretePositiveAdditiveObservationSelectionRankOneClass
          (z := z)
          α
          ι
          M
          obsFamily
          f
          coordinateWeight
          U ↔
      (∃ S : Finset ι,
        S ⊆ U ∧
          S.card = 1 ∧
          correctedConcreteObservationSelectionAdditiveCost
              coordinateWeight S =
            0 ∧
          language ∈
            StartRootedCorrectedConcreteTargetClass
              (v := z)
              α
              (↥S → M)
              (selectedObservationProduct obsFamily S)
              f) ∧
        language ∉
          StartRootedCorrectedConcreteTargetClass
            (v := z)
            α
            (↥(∅ : Finset ι) → M)
            (selectedObservationProduct obsFamily ∅)
            f := by

  rfl

end RankOneClassMembership


section PositiveAdditiveCostOne

variable {ι : Type v}

/-- Positive additive cost is exactly one precisely when one coordinate is
selected and the total extra additive weight is zero. -/
theorem observationSelectionPositiveAdditiveCost_eq_one_iff
    (coordinateWeight : ι → Nat)
    (S : Finset ι) :
    correctedConcreteObservationSelectionPositiveAdditiveCost
          coordinateWeight S =
        1 ↔
      S.card = 1 ∧
        correctedConcreteObservationSelectionAdditiveCost
            coordinateWeight S =
          0 := by

  constructor

  · intro hCost

    have hCardNe :
        S.card ≠ 0 := by

      intro hCardZero

      have hEmpty :
          S = ∅ :=
        Finset.card_eq_zero.mp
          hCardZero

      subst S

      simp [
        correctedConcreteObservationSelectionPositiveAdditiveCost,
        correctedConcreteObservationSelectionAdditiveCost
      ] at hCost

    unfold
      correctedConcreteObservationSelectionPositiveAdditiveCost
      at hCost

    constructor <;> omega

  · intro hData

    rcases hData with
      ⟨hCard, hAdditive⟩

    unfold
      correctedConcreteObservationSelectionPositiveAdditiveCost

    omega

end PositiveAdditiveCostOne


section CardinalityExactRankOne

variable {α : Type u}
variable {ι : Type v}
variable {M : Type w}
variable [Monoid M]
variable {obsFamily : ι → α → M}
variable {f : Nat}
variable {U : Finset ι}

/-- The exact cardinality-rank-one shell is exactly the class of targets
represented by one coordinate but not by the empty selected product. -/
theorem
    cardinalityObservationSelectionExactRankOneClass_eq_rankOneClass :
    CorrectedConcreteObservationSelectionExactCostRankClass
        (z := z)
        α
        ι
        M
        obsFamily
        f
        correctedConcreteObservationSelectionCardinalityCost
        U
        1 =
      CorrectedConcreteCardinalityObservationSelectionRankOneClass
        (z := z)
        α
        ι
        M
        obsFamily
        f
        U := by

  ext language

  constructor

  · intro hRankOne

    rcases hRankOne.1 with
      ⟨S, hSU, hCardLe, hTarget⟩

    have hCardNeZero :
        S.card ≠ 0 := by

      intro hCardZero

      have hAtZero :
          CorrectedConcreteObservationSelectionAtCost
            (obsFamily := obsFamily)
            (f := f)
            correctedConcreteObservationSelectionCardinalityCost
            U
            language
            0 := by

        exact
          ⟨S,
            hSU,
            by
              unfold
                correctedConcreteObservationSelectionCardinalityCost
              omega,
            hTarget⟩

      exact
        hRankOne.2
          0
          (by omega)
          hAtZero

    have hCardOne :
        S.card = 1 := by

      unfold
        correctedConcreteObservationSelectionCardinalityCost
        at hCardLe

      omega

    refine
      ⟨⟨S,
          hSU,
          hCardOne,
          hTarget⟩,
        ?_⟩

    intro hEmptyTarget

    have hAtZero :
        CorrectedConcreteObservationSelectionAtCost
          (obsFamily := obsFamily)
          (f := f)
          correctedConcreteObservationSelectionCardinalityCost
          U
          language
          0 := by

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

    exact
      hRankOne.2
        0
        (by omega)
        hAtZero

  · intro hClass

    rcases hClass with
      ⟨⟨S, hSU, hCardOne, hTarget⟩,
        hNotEmptyTarget⟩

    refine
      ⟨⟨S,
          hSU,
          by
            unfold
              correctedConcreteObservationSelectionCardinalityCost
            omega,
          hTarget⟩,
        ?_⟩

    intro costBudget hBudget hAtCost

    have hBudgetZero :
        costBudget = 0 := by
      omega

    subst costBudget

    rcases hAtCost with
      ⟨R, hRU, hRCard, hRTarget⟩

    have hRCardZero :
        R.card = 0 := by

      unfold
        correctedConcreteObservationSelectionCardinalityCost
        at hRCard

      omega

    have hREmpty :
        R = ∅ :=
      Finset.card_eq_zero.mp
        hRCardZero

    subst R

    exact
      hNotEmptyTarget
        hRTarget

end CardinalityExactRankOne


section PositiveAdditiveExactRankOne

variable {α : Type u}
variable {ι : Type v}
variable {M : Type w}
variable [Monoid M]
variable {obsFamily : ι → α → M}
variable {f : Nat}
variable {coordinateWeight : ι → Nat}
variable {U : Finset ι}

/-- The exact positive-additive-rank-one shell is exactly the class of targets
represented by a zero-extra-weight one-coordinate product but not by the empty
selected product. -/
theorem
    positiveAdditiveObservationSelectionExactRankOneClass_eq_rankOneClass :
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
        1 =
      CorrectedConcretePositiveAdditiveObservationSelectionRankOneClass
        (z := z)
        α
        ι
        M
        obsFamily
        f
        coordinateWeight
        U := by

  ext language

  constructor

  · intro hRankOne

    rcases hRankOne.1 with
      ⟨S, hSU, hCostLe, hTarget⟩

    have hCostNeZero :
        correctedConcreteObservationSelectionPositiveAdditiveCost
            coordinateWeight S ≠
          0 := by

      intro hCostZero

      have hAtZero :
          CorrectedConcreteObservationSelectionAtCost
            (obsFamily := obsFamily)
            (f := f)
            (correctedConcreteObservationSelectionPositiveAdditiveCost
              coordinateWeight)
            U
            language
            0 := by

        exact
          ⟨S,
            hSU,
            by
              omega,
            hTarget⟩

      exact
        hRankOne.2
          0
          (by omega)
          hAtZero

    have hCostOne :
        correctedConcreteObservationSelectionPositiveAdditiveCost
            coordinateWeight S =
          1 := by
      omega

    rcases
        (observationSelectionPositiveAdditiveCost_eq_one_iff
          coordinateWeight
          S).mp
          hCostOne with
      ⟨hCardOne, hAdditiveZero⟩

    refine
      ⟨⟨S,
          hSU,
          hCardOne,
          hAdditiveZero,
          hTarget⟩,
        ?_⟩

    intro hEmptyTarget

    have hAtZero :
        CorrectedConcreteObservationSelectionAtCost
          (obsFamily := obsFamily)
          (f := f)
          (correctedConcreteObservationSelectionPositiveAdditiveCost
            coordinateWeight)
          U
          language
          0 := by

      exact
        ⟨∅,
          by
            intro index hindex
            simp at hindex,
          by
            simp [
              correctedConcreteObservationSelectionPositiveAdditiveCost,
              correctedConcreteObservationSelectionAdditiveCost
            ],
          hEmptyTarget⟩

    exact
      hRankOne.2
        0
        (by omega)
        hAtZero

  · intro hClass

    rcases hClass with
      ⟨⟨S,
          hSU,
          hCardOne,
          hAdditiveZero,
          hTarget⟩,
        hNotEmptyTarget⟩

    have hCostOne :
        correctedConcreteObservationSelectionPositiveAdditiveCost
            coordinateWeight S =
          1 :=
      (observationSelectionPositiveAdditiveCost_eq_one_iff
        coordinateWeight
        S).mpr
        ⟨hCardOne, hAdditiveZero⟩

    refine
      ⟨⟨S,
          hSU,
          by
            omega,
          hTarget⟩,
        ?_⟩

    intro costBudget hBudget hAtCost

    have hBudgetZero :
        costBudget = 0 := by
      omega

    subst costBudget

    rcases hAtCost with
      ⟨R, hRU, hRCost, hRTarget⟩

    have hRCostZero :
        correctedConcreteObservationSelectionPositiveAdditiveCost
            coordinateWeight R =
          0 := by
      omega

    have hREmpty :
        R = ∅ :=
      (observationSelectionPositiveAdditiveCost_eq_zero_iff
        coordinateWeight
        R).mp
        hRCostZero

    subst R

    exact
      hNotEmptyTarget
        hRTarget

end PositiveAdditiveExactRankOne


section ZeroWeightCompatibilityAtRankOne

variable {α : Type u}
variable {ι : Type v}
variable {M : Type w}
variable [Monoid M]
variable {obsFamily : ι → α → M}
variable {f : Nat}
variable {U : Finset ι}

/-- With zero extra weights, the positive-additive and cardinality exact
rank-one shells coincide. -/
theorem
    zeroPositiveAdditiveExactRankOneClass_eq_cardinalityExactRankOneClass :
    CorrectedConcreteObservationSelectionExactCostRankClass
        (z := z)
        α
        ι
        M
        obsFamily
        f
        (correctedConcreteObservationSelectionPositiveAdditiveCost
          (fun _ : ι => 0))
        U
        1 =
      CorrectedConcreteObservationSelectionExactCostRankClass
        (z := z)
        α
        ι
        M
        obsFamily
        f
        correctedConcreteObservationSelectionCardinalityCost
        U
        1 := by

  exact
    observationSelectionExactCostRankClass_eq_of_pointwiseEquivalent
      (z := z)
      observationSelectionZeroPositiveAdditiveCost_equivalent_cardinality
      1

end ZeroWeightCompatibilityAtRankOne


section AmbientCardinalityRankOne

variable {α : Type u}
variable {ι : Type v}
variable {M : Type w}
variable [Monoid M]
variable (obsFamily : ι → α → M)
variable (f : Nat)
variable (U : Finset ι)

/-- A full-product target has cardinality observation-selection rank one
exactly when one selected coordinate suffices but the empty product does not. -/
theorem ambientTarget_cardinalityCostRank_eq_one_iff_rankOneClass
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
        1 ↔
      language ∈
        CorrectedConcreteCardinalityObservationSelectionRankOneClass
          (z := z)
          α
          ι
          M
          obsFamily
          f
          U := by

  constructor

  · intro hRank

    have hShell :=
      ambientTarget_mem_exactObservationSelectionCostRankClass
        (z := z)
        obsFamily
        f
        correctedConcreteObservationSelectionCardinalityCost
        U
        hTarget

    rw [hRank] at hShell

    rw [
      cardinalityObservationSelectionExactRankOneClass_eq_rankOneClass
        (z := z)
    ] at hShell

    exact hShell

  · intro hClass

    have hShell :
        language ∈
          CorrectedConcreteObservationSelectionExactCostRankClass
            (z := z)
            α
            ι
            M
            obsFamily
            f
            correctedConcreteObservationSelectionCardinalityCost
            U
            1 := by

      rw [
        cardinalityObservationSelectionExactRankOneClass_eq_rankOneClass
          (z := z)
      ]

      exact hClass

    let hSelection :=
      hasCorrectedConcreteObservationSelectionCost_of_fullProductTarget
        (obsFamily := obsFamily)
        (f := f)
        correctedConcreteObservationSelectionCardinalityCost
        hTarget

    have hOneEqMinimum :
        1 =
          correctedConcreteObservationSelectionMinimumCost
            correctedConcreteObservationSelectionCardinalityCost
            hSelection :=
      (observationSelection_mem_exactCostRankClass_iff_rank_eq_minimum
        (z := z)
        hSelection
        1).mp
        hShell

    simpa [
      ambientTargetObservationSelectionCostRank,
      ambientTargetObservationSelectionMinimumCost,
      hSelection
    ] using
      hOneEqMinimum.symm

end AmbientCardinalityRankOne


section AmbientPositiveAdditiveRankOne

variable {α : Type u}
variable {ι : Type v}
variable {M : Type w}
variable [Monoid M]
variable (obsFamily : ι → α → M)
variable (f : Nat)
variable (coordinateWeight : ι → Nat)
variable (U : Finset ι)

/-- A full-product target has positive-additive observation-selection rank one
exactly when a zero-extra-weight one-coordinate product suffices but the empty
product does not. -/
theorem ambientTarget_positiveAdditiveCostRank_eq_one_iff_rankOneClass
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
        1 ↔
      language ∈
        CorrectedConcretePositiveAdditiveObservationSelectionRankOneClass
          (z := z)
          α
          ι
          M
          obsFamily
          f
          coordinateWeight
          U := by

  constructor

  · intro hRank

    have hShell :=
      ambientTarget_mem_exactObservationSelectionCostRankClass
        (z := z)
        obsFamily
        f
        (correctedConcreteObservationSelectionPositiveAdditiveCost
          coordinateWeight)
        U
        hTarget

    rw [hRank] at hShell

    rw [
      positiveAdditiveObservationSelectionExactRankOneClass_eq_rankOneClass
        (z := z)
    ] at hShell

    exact hShell

  · intro hClass

    have hShell :
        language ∈
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
            1 := by

      rw [
        positiveAdditiveObservationSelectionExactRankOneClass_eq_rankOneClass
          (z := z)
      ]

      exact hClass

    let hSelection :=
      hasCorrectedConcreteObservationSelectionCost_of_fullProductTarget
        (obsFamily := obsFamily)
        (f := f)
        (correctedConcreteObservationSelectionPositiveAdditiveCost
          coordinateWeight)
        hTarget

    have hOneEqMinimum :
        1 =
          correctedConcreteObservationSelectionMinimumCost
            (correctedConcreteObservationSelectionPositiveAdditiveCost
              coordinateWeight)
            hSelection :=
      (observationSelection_mem_exactCostRankClass_iff_rank_eq_minimum
        (z := z)
        hSelection
        1).mp
        hShell

    simpa [
      ambientTargetObservationSelectionCostRank,
      ambientTargetObservationSelectionMinimumCost,
      hSelection
    ] using
      hOneEqMinimum.symm

end AmbientPositiveAdditiveRankOne


section CardinalityRankOneCertifiedWitness

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
variable (U : Finset ι)

/-- Every exact cardinality-rank-one target has an actual one-coordinate
selected product whose certified learner identifies the target. -/
theorem cardinalityExactRankOne_exists_oneCoordinateCertifiedWitness
    {language : Set (Word α)}
    (hRankOne :
      language ∈
        CorrectedConcreteObservationSelectionExactCostRankClass
          (z := z)
          α
          ι
          M
          obsFamily
          f
          correctedConcreteObservationSelectionCardinalityCost
          U
          1) :
    ∃
      (S : Finset ι)
      (hSelected :
        language ∈
          StartRootedCorrectedConcreteTargetClass
            (v := z)
            α
            (↥S → M)
            (selectedObservationProduct obsFamily S)
            f),
      S ⊆ U ∧
        S.card = 1 ∧
        language ∉
          StartRootedCorrectedConcreteTargetClass
            (v := z)
            α
            (↥(∅ : Finset ι) → M)
            (selectedObservationProduct obsFamily ∅)
            f ∧
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

  have hClass :
      language ∈
        CorrectedConcreteCardinalityObservationSelectionRankOneClass
          (z := z)
          α
          ι
          M
          obsFamily
          f
          U := by

    rw [
      ← cardinalityObservationSelectionExactRankOneClass_eq_rankOneClass
          (z := z)
    ]

    exact hRankOne

  rcases hClass with
    ⟨⟨S, hSU, hCardOne, hSelected⟩,
      hNotEmpty⟩

  exact
    ⟨S,
      hSelected,
      hSU,
      hCardOne,
      hNotEmpty,
      selectedProductCertifiedLearner_identifies_targetClass
        (z := z)
        hα
        obsFamily
        f
        S
        language
        hSelected,
      startRootedTarget_exists_output_at_minimumCertifiedDescriptionRank
        (v := z)
        hα
        (selectedObservationProduct obsFamily S)
        f
        hSelected⟩

end CardinalityRankOneCertifiedWitness


section PositiveAdditiveRankOneCertifiedWitness

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

/-- Every exact positive-additive-rank-one target has an actual
zero-extra-weight one-coordinate selected product whose certified learner
identifies the target. -/
theorem positiveAdditiveExactRankOne_exists_unitCostCertifiedWitness
    {language : Set (Word α)}
    (hRankOne :
      language ∈
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
          1) :
    ∃
      (S : Finset ι)
      (hSelected :
        language ∈
          StartRootedCorrectedConcreteTargetClass
            (v := z)
            α
            (↥S → M)
            (selectedObservationProduct obsFamily S)
            f),
      S ⊆ U ∧
        S.card = 1 ∧
        correctedConcreteObservationSelectionAdditiveCost
            coordinateWeight S =
          0 ∧
        language ∉
          StartRootedCorrectedConcreteTargetClass
            (v := z)
            α
            (↥(∅ : Finset ι) → M)
            (selectedObservationProduct obsFamily ∅)
            f ∧
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

  have hClass :
      language ∈
        CorrectedConcretePositiveAdditiveObservationSelectionRankOneClass
          (z := z)
          α
          ι
          M
          obsFamily
          f
          coordinateWeight
          U := by

    rw [
      ← positiveAdditiveObservationSelectionExactRankOneClass_eq_rankOneClass
          (z := z)
    ]

    exact hRankOne

  rcases hClass with
    ⟨⟨S,
        hSU,
        hCardOne,
        hAdditiveZero,
        hSelected⟩,
      hNotEmpty⟩

  exact
    ⟨S,
      hSelected,
      hSU,
      hCardOne,
      hAdditiveZero,
      hNotEmpty,
      selectedProductCertifiedLearner_identifies_targetClass
        (z := z)
        hα
        obsFamily
        f
        S
        language
        hSelected,
      startRootedTarget_exists_output_at_minimumCertifiedDescriptionRank
        (v := z)
        hα
        (selectedObservationProduct obsFamily S)
        f
        hSelected⟩

end PositiveAdditiveRankOneCertifiedWitness


section ObservationSelectionRankOneFinalPackage

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

/-- Final exact rank-one shell, target-rank characterization, and certified
one-coordinate witness package. -/
theorem
    correctedConcreteCertifiedWorkingGrammar_observationSelectionRankOne_package :
    (CorrectedConcreteObservationSelectionExactCostRankClass
        (z := z)
        α
        ι
        M
        obsFamily
        f
        correctedConcreteObservationSelectionCardinalityCost
        U
        1 =
      CorrectedConcreteCardinalityObservationSelectionRankOneClass
        (z := z)
        α
        ι
        M
        obsFamily
        f
        U) ∧
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
        1 =
      CorrectedConcretePositiveAdditiveObservationSelectionRankOneClass
        (z := z)
        α
        ι
        M
        obsFamily
        f
        coordinateWeight
        U) ∧
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
              correctedConcreteObservationSelectionCardinalityCost
              U
              hTarget =
            1 ↔
            language ∈
              CorrectedConcreteCardinalityObservationSelectionRankOneClass
                (z := z)
                α
                ι
                M
                obsFamily
                f
                U)) ∧
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
            1 ↔
            language ∈
              CorrectedConcretePositiveAdditiveObservationSelectionRankOneClass
                (z := z)
                α
                ι
                M
                obsFamily
                f
                coordinateWeight
                U)) ∧
      (∀
        language : Set (Word α),
        language ∈
            CorrectedConcreteObservationSelectionExactCostRankClass
              (z := z)
              α
              ι
              M
              obsFamily
              f
              correctedConcreteObservationSelectionCardinalityCost
              U
              1 →
          ∃
            (S : Finset ι)
            (hSelected :
              language ∈
                StartRootedCorrectedConcreteTargetClass
                  (v := z)
                  α
                  (↥S → M)
                  (selectedObservationProduct obsFamily S)
                  f),
            S ⊆ U ∧
              S.card = 1 ∧
              IdentifiesLanguageFromPositiveData
                (correctedConcreteCertifiedWorkingGrammarHypLanguage
                  (selectedObservationProduct obsFamily S)
                  f)
                (correctedConcreteCertifiedWorkingGrammarLearner
                  hα
                  (selectedObservationProduct obsFamily S)
                  f)
                language) ∧
      (∀
        language : Set (Word α),
        language ∈
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
              1 →
          ∃
            (S : Finset ι)
            (hSelected :
              language ∈
                StartRootedCorrectedConcreteTargetClass
                  (v := z)
                  α
                  (↥S → M)
                  (selectedObservationProduct obsFamily S)
                  f),
            S ⊆ U ∧
              S.card = 1 ∧
              correctedConcreteObservationSelectionAdditiveCost
                  coordinateWeight S =
                0 ∧
              IdentifiesLanguageFromPositiveData
                (correctedConcreteCertifiedWorkingGrammarHypLanguage
                  (selectedObservationProduct obsFamily S)
                  f)
                (correctedConcreteCertifiedWorkingGrammarLearner
                  hα
                  (selectedObservationProduct obsFamily S)
                  f)
                language) := by

  refine
    ⟨cardinalityObservationSelectionExactRankOneClass_eq_rankOneClass
        (z := z),
      positiveAdditiveObservationSelectionExactRankOneClass_eq_rankOneClass
        (z := z),
      ?_,
      ?_,
      ?_,
      ?_⟩

  · intro language hTarget

    exact
      ambientTarget_cardinalityCostRank_eq_one_iff_rankOneClass
        (z := z)
        obsFamily
        f
        U
        hTarget

  · intro language hTarget

    exact
      ambientTarget_positiveAdditiveCostRank_eq_one_iff_rankOneClass
        (z := z)
        obsFamily
        f
        coordinateWeight
        U
        hTarget

  · intro language hRankOne

    rcases
        cardinalityExactRankOne_exists_oneCoordinateCertifiedWitness
          (z := z)
          hα
          obsFamily
          f
          U
          hRankOne with
      ⟨S,
        hSelected,
        hSU,
        hCardOne,
        hNotEmpty,
        hIdentifies,
        C,
        hLanguage,
        hBits,
        hSearch⟩

    exact
      ⟨S,
        hSelected,
        hSU,
        hCardOne,
        hIdentifies⟩

  · intro language hRankOne

    rcases
        positiveAdditiveExactRankOne_exists_unitCostCertifiedWitness
          (z := z)
          hα
          obsFamily
          f
          coordinateWeight
          U
          hRankOne with
      ⟨S,
        hSelected,
        hSU,
        hCardOne,
        hAdditiveZero,
        hNotEmpty,
        hIdentifies,
        C,
        hLanguage,
        hBits,
        hSearch⟩

    exact
      ⟨S,
        hSelected,
        hSU,
        hCardOne,
        hAdditiveZero,
        hIdentifies⟩

end ObservationSelectionRankOneFinalPackage

end MCFG
