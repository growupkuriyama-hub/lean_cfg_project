/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG.ConcreteCanonicalLearnerWorkingGrammarObservationSelectionRankOne

/-!
# ConcreteCanonicalLearnerWorkingGrammarObservationSelectionCardinalityRank.lean

The preceding files identify the observation-selection rank-zero and rank-one
layers.

This file gives the uniform theorem for every cardinality rank.

## Exact cardinality-rank witness class

For a natural number `rank`, define the exact cardinality-rank witness class to
contain exactly the languages for which there is some selected set `S` such
that

```text
S ⊆ U,
S.card = rank,
Product(S) represents the target,
```

and every other ambient selected product representing the target has at least
`rank` coordinates.

This witness class is proved equal to the generic exact cost-rank shell for the
cardinality cost.

Thus the exact shell at arbitrary rank has the direct form

```text
there is a representing selection of cardinality exactly rank,
and no representing selection has smaller cardinality.
```

## Compatibility of the two cardinality minima

Earlier files introduced two equivalent minimum notions:

```text
correctedConcreteObservationSelectionCardinality
```

from the direct cardinality-budget theory, and

```text
correctedConcreteObservationSelectionMinimumCost
```

specialized to the cardinality cost.

They are proved equal.  Consequently the paper-facing generic cost rank under
cardinality cost is exactly

```text
ambientTargetObservationSelectionCardinality.
```

## Bounded shell decomposition

Every language represented by the full ambient product belongs to a unique
exact cardinality-rank shell, and its rank is at most `U.card`.

Therefore

```text
Target(Product(U))
```

is exactly the union of the exact cardinality shells with rank at most
`U.card`.

The rank-zero and rank-one characterizations from the preceding files become
the first two instances of this general decomposition.

## Certified minimum-cardinality witness

Every full ambient-product target has an actual selected subset `S` such that

```text
S.card = its cardinality observation-selection rank.
```

The subset is inclusion-irredundant, every selected coordinate is essential,
and the selected-product certified learner identifies the target and returns an
exact checked grammar output at the selected product's minimum certified-
description rank.

## Boundary

The cardinality minimum and selected witness remain semantic.  This file does
not claim an executable minimum-interface algorithm.

No target grammar is supplied to any learner.
No `sorry`, `admit`, or `axiom` is used.
-/

namespace MCFG

universe u v w z


section ExactCardinalityRankWitnessClassDefinition

variable (α : Type u)
variable (ι : Type v)
variable (M : Type w)
variable [Monoid M]
variable (obsFamily : ι → α → M)
variable (f : Nat)
variable (U : Finset ι)

/-- Languages having a representing ambient selection of cardinality exactly
`rank`, with no smaller representing ambient selection. -/
def CorrectedConcreteObservationSelectionExactCardinalityRankWitnessClass
    (rank : Nat) :
    Set (Set (Word α)) :=
  {language |
    ∃ S : Finset ι,
      S ⊆ U ∧
        S.card = rank ∧
        language ∈
          StartRootedCorrectedConcreteTargetClass
            (v := z)
            α
            (↥S → M)
            (selectedObservationProduct obsFamily S)
            f ∧
        ∀ R : Finset ι,
          R ⊆ U →
          language ∈
            StartRootedCorrectedConcreteTargetClass
              (v := z)
              α
              (↥R → M)
              (selectedObservationProduct obsFamily R)
              f →
          rank <= R.card}

end ExactCardinalityRankWitnessClassDefinition


section ExactCardinalityRankWitnessMembership

variable {α : Type u}
variable {ι : Type v}
variable {M : Type w}
variable [Monoid M]
variable {obsFamily : ι → α → M}
variable {f : Nat}
variable {U : Finset ι}
variable {language : Set (Word α)}
variable {rank : Nat}

/-- Exact membership theorem for the direct cardinality-rank witness class. -/
theorem
    mem_observationSelectionExactCardinalityRankWitnessClass_iff :
    language ∈
        CorrectedConcreteObservationSelectionExactCardinalityRankWitnessClass
          (z := z)
          α
          ι
          M
          obsFamily
          f
          U
          rank ↔
      ∃ S : Finset ι,
        S ⊆ U ∧
          S.card = rank ∧
          language ∈
            StartRootedCorrectedConcreteTargetClass
              (v := z)
              α
              (↥S → M)
              (selectedObservationProduct obsFamily S)
              f ∧
          ∀ R : Finset ι,
            R ⊆ U →
            language ∈
              StartRootedCorrectedConcreteTargetClass
                (v := z)
                α
                (↥R → M)
                (selectedObservationProduct obsFamily R)
                f →
            rank <= R.card := by

  rfl

end ExactCardinalityRankWitnessMembership


section ExactCardinalityRankShellEquality

variable {α : Type u}
variable {ι : Type v}
variable {M : Type w}
variable [Monoid M]
variable {obsFamily : ι → α → M}
variable {f : Nat}
variable {U : Finset ι}

/-- The generic exact cost-rank shell for cardinality cost is exactly the
direct minimum-cardinality witness class. -/
theorem
    cardinalityObservationSelectionExactRankClass_eq_witnessClass
    (rank : Nat) :
    CorrectedConcreteObservationSelectionExactCostRankClass
        (z := z)
        α
        ι
        M
        obsFamily
        f
        correctedConcreteObservationSelectionCardinalityCost
        U
        rank =
      CorrectedConcreteObservationSelectionExactCardinalityRankWitnessClass
        (z := z)
        α
        ι
        M
        obsFamily
        f
        U
        rank := by

  ext language

  constructor

  · intro hRank

    rcases hRank.1 with
      ⟨S, hSU, hCardLe, hTarget⟩

    have hRankLeCard :
        rank <= S.card := by

      by_contra hNotLe

      have hCardLt :
          S.card < rank := by
        omega

      have hAtSmaller :
          CorrectedConcreteObservationSelectionAtCost
            (obsFamily := obsFamily)
            (f := f)
            correctedConcreteObservationSelectionCardinalityCost
            U
            language
            S.card := by

        exact
          ⟨S,
            hSU,
            by
              unfold
                correctedConcreteObservationSelectionCardinalityCost
              exact Nat.le_refl _,
            hTarget⟩

      exact
        hRank.2
          S.card
          hCardLt
          hAtSmaller

    have hCardEq :
        S.card = rank := by

      unfold
        correctedConcreteObservationSelectionCardinalityCost
        at hCardLe

      exact
        Nat.le_antisymm
          hCardLe
          hRankLeCard

    refine
      ⟨S,
        hSU,
        hCardEq,
        hTarget,
        ?_⟩

    intro R hRU hRTarget

    by_contra hNotLe

    have hRCardLt :
        R.card < rank := by
      omega

    have hAtSmaller :
        CorrectedConcreteObservationSelectionAtCost
          (obsFamily := obsFamily)
          (f := f)
          correctedConcreteObservationSelectionCardinalityCost
          U
          language
          R.card := by

      exact
        ⟨R,
          hRU,
          by
            unfold
              correctedConcreteObservationSelectionCardinalityCost
            exact Nat.le_refl _,
          hRTarget⟩

    exact
      hRank.2
        R.card
        hRCardLt
        hAtSmaller

  · intro hWitness

    rcases hWitness with
      ⟨S,
        hSU,
        hCardEq,
        hTarget,
        hMinimum⟩

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

    rcases hAtCost with
      ⟨R, hRU, hRCard, hRTarget⟩

    have hRankLe :
        rank <= R.card :=
      hMinimum
        R
        hRU
        hRTarget

    unfold
      correctedConcreteObservationSelectionCardinalityCost
      at hRCard

    omega

end ExactCardinalityRankShellEquality


section CardinalityMinimumCompatibility

variable {α : Type u}
variable {ι : Type v}
variable {M : Type w}
variable [Monoid M]
variable {obsFamily : ι → α → M}
variable {f : Nat}
variable {U : Finset ι}
variable {language : Set (Word α)}

/-- The generic minimum-cost value specialized to cardinality cost equals the
direct minimum-cardinality value. -/
theorem observationSelectionCardinalityCostMinimum_eq_cardinality
    (hCostSelection :
      HasCorrectedConcreteObservationSelectionCost
        (obsFamily := obsFamily)
        (f := f)
        correctedConcreteObservationSelectionCardinalityCost
        U
        language)
    (hCardSelection :
      HasCorrectedConcreteObservationSelection
        (obsFamily := obsFamily)
        (f := f)
        U
        language) :
    correctedConcreteObservationSelectionMinimumCost
        correctedConcreteObservationSelectionCardinalityCost
        hCostSelection =
      correctedConcreteObservationSelectionCardinality
        hCardSelection := by

  apply Nat.le_antisymm

  · rcases hCardSelection.exists_selection_exact_cardinality with
      ⟨S, hSU, hCard, hTarget⟩

    have hMinimum :
        correctedConcreteObservationSelectionMinimumCost
            correctedConcreteObservationSelectionCardinalityCost
            hCostSelection <=
          correctedConcreteObservationSelectionCardinalityCost S := by

      apply
        hCostSelection.minimumCost_le_of_selection

      exact
        ⟨S,
          hSU,
          Nat.le_refl _,
          hTarget⟩

    unfold
      correctedConcreteObservationSelectionCardinalityCost
      at hMinimum

    simpa [hCard] using hMinimum

  · rcases hCostSelection.exists_selection_exact_minimumCost with
      ⟨S, hSU, hCost, hTarget⟩

    have hMinimum :
        correctedConcreteObservationSelectionCardinality
            hCardSelection <=
          S.card := by

      apply
        hCardSelection.cardinality_le_of_selection

      exact
        ⟨S,
          hSU,
          Nat.le_refl _,
          hTarget⟩

    unfold
      correctedConcreteObservationSelectionCardinalityCost
      at hCost

    rw [hCost] at hMinimum

    exact hMinimum

end CardinalityMinimumCompatibility


section AmbientCardinalityRankCompatibility

variable {α : Type u}
variable {ι : Type v}
variable {M : Type w}
variable [Monoid M]
variable (obsFamily : ι → α → M)
variable (f : Nat)
variable (U : Finset ι)

/-- The paper-facing generic selection cost rank under cardinality cost is
exactly the earlier minimum observation-selection cardinality. -/
theorem ambientTarget_cardinalityCostRank_eq_selectionCardinality
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
      ambientTargetObservationSelectionCardinality
        (z := z)
        obsFamily
        f
        U
        hTarget := by

  let hCostSelection :=
    hasCorrectedConcreteObservationSelectionCost_of_fullProductTarget
      (obsFamily := obsFamily)
      (f := f)
      correctedConcreteObservationSelectionCardinalityCost
      hTarget

  let hCardSelection :=
    hasCorrectedConcreteObservationSelection_of_fullProductTarget
      (obsFamily := obsFamily)
      (f := f)
      hTarget

  simpa [
    ambientTargetObservationSelectionCostRank,
    ambientTargetObservationSelectionMinimumCost,
    ambientTargetObservationSelectionCardinality,
    hCostSelection,
    hCardSelection
  ] using
    observationSelectionCardinalityCostMinimum_eq_cardinality
      hCostSelection
      hCardSelection

/-- A full-product target belongs to the exact cardinality-rank witness class
at its minimum observation-selection cardinality. -/
theorem ambientTarget_mem_exactCardinalityRankWitnessClass
    {language : Set (Word α)}
    (hTarget :
      language ∈
        StartRootedCorrectedConcreteTargetClass
          (v := z)
          α
          (↥U → M)
          (selectedObservationProduct obsFamily U)
          f) :
    language ∈
      CorrectedConcreteObservationSelectionExactCardinalityRankWitnessClass
        (z := z)
        α
        ι
        M
        obsFamily
        f
        U
        (ambientTargetObservationSelectionCardinality
          (z := z)
          obsFamily
          f
          U
          hTarget) := by

  have hShell :=
    ambientTarget_mem_exactObservationSelectionCostRankClass
      (z := z)
      obsFamily
      f
      correctedConcreteObservationSelectionCardinalityCost
      U
      hTarget

  rw [
    ambientTarget_cardinalityCostRank_eq_selectionCardinality
      (z := z)
      obsFamily
      f
      U
      hTarget,
    cardinalityObservationSelectionExactRankClass_eq_witnessClass
      (z := z)
  ] at hShell

  exact hShell

end AmbientCardinalityRankCompatibility


section BoundedCardinalityRankDecomposition

variable {α : Type u}
variable {ι : Type v}
variable {M : Type w}
variable [Monoid M]
variable (obsFamily : ι → α → M)
variable (f : Nat)
variable (U : Finset ι)

/-- The full ambient target class is exactly the union of exact cardinality
shells bounded by the ambient candidate count. -/
theorem
    fullProductTargetClass_eq_exists_boundedExactCardinalityRank :
    StartRootedCorrectedConcreteTargetClass
        (v := z)
        α
        (↥U → M)
        (selectedObservationProduct obsFamily U)
        f =
      {language : Set (Word α) |
        ∃ rank : Nat,
          rank <= U.card ∧
            language ∈
              CorrectedConcreteObservationSelectionExactCardinalityRankWitnessClass
                (z := z)
                α
                ι
                M
                obsFamily
                f
                U
                rank} := by

  ext language

  constructor

  · intro hTarget

    let rank :=
      ambientTargetObservationSelectionCardinality
        (z := z)
        obsFamily
        f
        U
        hTarget

    exact
      ⟨rank,
        ambientTargetObservationSelectionCardinality_le
          (z := z)
          obsFamily
          f
          U
          hTarget,
        ambientTarget_mem_exactCardinalityRankWitnessClass
          (z := z)
          obsFamily
          f
          U
          hTarget⟩

  · intro hRank

    rcases hRank with
      ⟨rank, hRankBound, hWitness⟩

    rcases hWitness with
      ⟨S, hSU, hCard, hTarget, hMinimum⟩

    exact
      selectedObservationProductTargetClass_mono
        (z := z)
        obsFamily
        f
        hSU
        hTarget

/-- Every full-product target belongs to a unique bounded exact cardinality
shell. -/
theorem
    fullProductTarget_existsUnique_boundedExactCardinalityRank
    {language : Set (Word α)}
    (hTarget :
      language ∈
        StartRootedCorrectedConcreteTargetClass
          (v := z)
          α
          (↥U → M)
          (selectedObservationProduct obsFamily U)
          f) :
    ∃! rank : Nat,
      rank <= U.card ∧
        language ∈
          CorrectedConcreteObservationSelectionExactCardinalityRankWitnessClass
            (z := z)
            α
            ι
            M
            obsFamily
            f
            U
            rank := by

  let rank :=
    ambientTargetObservationSelectionCardinality
      (z := z)
      obsFamily
      f
      U
      hTarget

  refine
    ⟨rank,
      ⟨ambientTargetObservationSelectionCardinality_le
          (z := z)
          obsFamily
          f
          U
          hTarget,
        ambientTarget_mem_exactCardinalityRankWitnessClass
          (z := z)
          obsFamily
          f
          U
          hTarget⟩,
      ?_⟩

  intro rank' hRank'

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
          rank' := by

    rw [
      cardinalityObservationSelectionExactRankClass_eq_witnessClass
        (z := z)
    ]

    exact hRank'.2

  let hCostSelection :=
    hasCorrectedConcreteObservationSelectionCost_of_fullProductTarget
      (obsFamily := obsFamily)
      (f := f)
      correctedConcreteObservationSelectionCardinalityCost
      hTarget

  have hRankEqCostMinimum :
      rank' =
        correctedConcreteObservationSelectionMinimumCost
          correctedConcreteObservationSelectionCardinalityCost
          hCostSelection :=
    (observationSelection_mem_exactCostRankClass_iff_rank_eq_minimum
      (z := z)
      hCostSelection
      rank').mp
      hShell

  have hCompatibility :
      correctedConcreteObservationSelectionMinimumCost
          correctedConcreteObservationSelectionCardinalityCost
          hCostSelection =
        rank := by

    unfold rank

    rw [
      ← ambientTarget_cardinalityCostRank_eq_selectionCardinality
          (z := z)
          obsFamily
          f
          U
          hTarget
    ]

    simp [
      ambientTargetObservationSelectionCostRank,
      ambientTargetObservationSelectionMinimumCost,
      hCostSelection
    ]

  omega

end BoundedCardinalityRankDecomposition


section CardinalityRankLowerBoundCriterion

variable {α : Type u}
variable {ι : Type v}
variable {M : Type w}
variable [Monoid M]
variable (obsFamily : ι → α → M)
variable (f : Nat)
variable (U : Finset ι)

/-- A strict lower bound on minimum selected-coordinate count is exactly
failure of every ambient selection of at most that size. -/
theorem ambientTarget_cardinalityRank_gt_iff_all_boundedSelections_fail
    {language : Set (Word α)}
    (hTarget :
      language ∈
        StartRootedCorrectedConcreteTargetClass
          (v := z)
          α
          (↥U → M)
          (selectedObservationProduct obsFamily U)
          f)
    (cardinalityBudget : Nat) :
    cardinalityBudget <
        ambientTargetObservationSelectionCardinality
          (z := z)
          obsFamily
          f
          U
          hTarget ↔
      ∀ S : Finset ι,
        S ⊆ U →
        S.card <= cardinalityBudget →
        language ∉
          StartRootedCorrectedConcreteTargetClass
            (v := z)
            α
            (↥S → M)
            (selectedObservationProduct obsFamily S)
            f := by

  let hSelection :=
    hasCorrectedConcreteObservationSelection_of_fullProductTarget
      (obsFamily := obsFamily)
      (f := f)
      hTarget

  constructor

  · intro hLower S hSU hCard hSelected

    have hMinimum :
        correctedConcreteObservationSelectionCardinality
            hSelection <=
          S.card := by

      apply
        hSelection.cardinality_le_of_selection

      exact
        ⟨S,
          hSU,
          Nat.le_refl _,
          hSelected⟩

    have hRankEq :
        ambientTargetObservationSelectionCardinality
            (z := z)
            obsFamily
            f
            U
            hTarget =
          correctedConcreteObservationSelectionCardinality
            hSelection := by

      simp [
        ambientTargetObservationSelectionCardinality,
        hSelection
      ]

    rw [hRankEq] at hLower

    omega

  · intro hFailure

    by_contra hNotLt

    have hRankLe :
        ambientTargetObservationSelectionCardinality
            (z := z)
            obsFamily
            f
            U
            hTarget <=
          cardinalityBudget := by
      omega

    rcases
        ambientTarget_exists_minimumObservationSelection
          (z := z)
          obsFamily
          f
          U
          hTarget with
      ⟨S, hSU, hCard, hSelected⟩

    exact
      hFailure
        S
        hSU
        (by omega)
        hSelected

end CardinalityRankLowerBoundCriterion


section CardinalityRankCertifiedSelection

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

/-- Every full-product target has an actual irredundant selected subset whose
cardinality is exactly its cardinality observation-selection rank, together
with the selected-product certified learner. -/
theorem ambientTarget_exists_cardinalityRankCertifiedSelection
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
      (rank : Nat)
      (S : Finset ι)
      (hSelected :
        language ∈
          StartRootedCorrectedConcreteTargetClass
            (v := z)
            α
            (↥S → M)
            (selectedObservationProduct obsFamily S)
            f),
      rank =
          ambientTargetObservationSelectionCardinality
            (z := z)
            obsFamily
            f
            U
            hTarget ∧
        S ⊆ U ∧
        S.card = rank ∧
        language ∈
          CorrectedConcreteObservationSelectionExactCardinalityRankWitnessClass
            (z := z)
            α
            ι
            M
            obsFamily
            f
            U
            rank ∧
        CorrectedConcreteObservationSelectionIrredundant
          (z := z)
          α
          ι
          M
          obsFamily
          f
          language
          S ∧
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
      ambientTarget_exists_minimumIrredundantCertifiedObservationSelection
        (z := z)
        hα
        obsFamily
        f
        U
        hTarget with
    ⟨S,
      hSU,
      hSelected,
      hCard,
      hIrredundant,
      hEssential,
      hIdentifies,
      C,
      hLanguage,
      hBits,
      hSearch⟩

  let rank :=
    ambientTargetObservationSelectionCardinality
      (z := z)
      obsFamily
      f
      U
      hTarget

  have hRankWitness :
      language ∈
        CorrectedConcreteObservationSelectionExactCardinalityRankWitnessClass
          (z := z)
          α
          ι
          M
          obsFamily
          f
          U
          rank :=
    ambientTarget_mem_exactCardinalityRankWitnessClass
      (z := z)
      obsFamily
      f
      U
      hTarget

  exact
    ⟨rank,
      S,
      hSelected,
      rfl,
      hSU,
      by
        simpa [rank] using hCard,
      hRankWitness,
      hIrredundant,
      hEssential,
      hIdentifies,
      C,
      hLanguage,
      hBits,
      hSearch⟩

end CardinalityRankCertifiedSelection


section CardinalityRankZeroOneCompatibility

variable {α : Type u}
variable {ι : Type v}
variable {M : Type w}
variable [Monoid M]
variable (obsFamily : ι → α → M)
variable (f : Nat)
variable (U : Finset ι)

/-- The general exact cardinality-rank witness theorem specializes at rank zero
to the empty selected product target class. -/
theorem exactCardinalityRankWitnessClass_zero_eq_emptyProductTargetClass :
    CorrectedConcreteObservationSelectionExactCardinalityRankWitnessClass
        (z := z)
        α
        ι
        M
        obsFamily
        f
        U
        0 =
      StartRootedCorrectedConcreteTargetClass
        (v := z)
        α
        (↥(∅ : Finset ι) → M)
        (selectedObservationProduct obsFamily ∅)
        f := by

  calc
    CorrectedConcreteObservationSelectionExactCardinalityRankWitnessClass
        (z := z)
        α
        ι
        M
        obsFamily
        f
        U
        0 =
      CorrectedConcreteObservationSelectionExactCostRankClass
        (z := z)
        α
        ι
        M
        obsFamily
        f
        correctedConcreteObservationSelectionCardinalityCost
        U
        0 := by
          symm
          exact
            cardinalityObservationSelectionExactRankClass_eq_witnessClass
              (z := z)
              0

    _ =
      StartRootedCorrectedConcreteTargetClass
        (v := z)
        α
        (↥(∅ : Finset ι) → M)
        (selectedObservationProduct obsFamily ∅)
        f :=
          cardinalityObservationSelectionExactRankZeroClass_eq_emptyProductTargetClass
            (z := z)
            obsFamily
            f
            U

/-- The general exact cardinality-rank witness theorem specializes at rank one
to the one-coordinate/nonempty-interface class from the preceding file. -/
theorem exactCardinalityRankWitnessClass_one_eq_rankOneClass :
    CorrectedConcreteObservationSelectionExactCardinalityRankWitnessClass
        (z := z)
        α
        ι
        M
        obsFamily
        f
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

  calc
    CorrectedConcreteObservationSelectionExactCardinalityRankWitnessClass
        (z := z)
        α
        ι
        M
        obsFamily
        f
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
          symm
          exact
            cardinalityObservationSelectionExactRankClass_eq_witnessClass
              (z := z)
              1

    _ =
      CorrectedConcreteCardinalityObservationSelectionRankOneClass
        (z := z)
        α
        ι
        M
        obsFamily
        f
        U :=
          cardinalityObservationSelectionExactRankOneClass_eq_rankOneClass
            (z := z)

end CardinalityRankZeroOneCompatibility


section ObservationSelectionCardinalityRankFinalPackage

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

/-- Final arbitrary-rank witness characterization, bounded shell decomposition,
lower-bound obstruction, and certified minimum-cardinality selection package. -/
theorem
    correctedConcreteCertifiedWorkingGrammar_observationSelectionCardinalityRank_package :
    (∀ rank : Nat,
      CorrectedConcreteObservationSelectionExactCostRankClass
          (z := z)
          α
          ι
          M
          obsFamily
          f
          correctedConcreteObservationSelectionCardinalityCost
          U
          rank =
        CorrectedConcreteObservationSelectionExactCardinalityRankWitnessClass
          (z := z)
          α
          ι
          M
          obsFamily
          f
          U
          rank) ∧
      (StartRootedCorrectedConcreteTargetClass
          (v := z)
          α
          (↥U → M)
          (selectedObservationProduct obsFamily U)
          f =
        {language : Set (Word α) |
          ∃ rank : Nat,
            rank <= U.card ∧
              language ∈
                CorrectedConcreteObservationSelectionExactCardinalityRankWitnessClass
                  (z := z)
                  α
                  ι
                  M
                  obsFamily
                  f
                  U
                  rank}) ∧
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
        ∀ cardinalityBudget : Nat,
          (cardinalityBudget <
              ambientTargetObservationSelectionCardinality
                (z := z)
                obsFamily
                f
                U
                hTarget ↔
            ∀ S : Finset ι,
              S ⊆ U →
              S.card <= cardinalityBudget →
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
          (rank : Nat)
          (S : Finset ι)
          (hSelected :
            language ∈
              StartRootedCorrectedConcreteTargetClass
                (v := z)
                α
                (↥S → M)
                (selectedObservationProduct obsFamily S)
                f),
          rank =
              ambientTargetObservationSelectionCardinality
                (z := z)
                obsFamily
                f
                U
                hTarget ∧
            S ⊆ U ∧
            S.card = rank ∧
            CorrectedConcreteObservationSelectionIrredundant
              (z := z)
              α
              ι
              M
              obsFamily
              f
              language
              S ∧
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
    ⟨?_,
      fullProductTargetClass_eq_exists_boundedExactCardinalityRank
        (z := z)
        obsFamily
        f
        U,
      ?_,
      ?_⟩

  · intro rank

    exact
      cardinalityObservationSelectionExactRankClass_eq_witnessClass
        (z := z)
        rank

  · intro language hTarget cardinalityBudget

    exact
      ambientTarget_cardinalityRank_gt_iff_all_boundedSelections_fail
        (z := z)
        obsFamily
        f
        U
        hTarget
        cardinalityBudget

  · intro language hTarget

    rcases
        ambientTarget_exists_cardinalityRankCertifiedSelection
          (z := z)
          hα
          obsFamily
          f
          U
          hTarget with
      ⟨rank,
        S,
        hSelected,
        hRank,
        hSU,
        hCard,
        hRankWitness,
        hIrredundant,
        hEssential,
        hIdentifies,
        C,
        hLanguage,
        hBits,
        hSearch⟩

    exact
      ⟨rank,
        S,
        hSelected,
        hRank,
        hSU,
        hCard,
        hIrredundant,
        hIdentifies⟩

end ObservationSelectionCardinalityRankFinalPackage

end MCFG
