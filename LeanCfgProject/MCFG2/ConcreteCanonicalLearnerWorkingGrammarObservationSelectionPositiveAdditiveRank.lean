/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG2.ConcreteCanonicalLearnerWorkingGrammarObservationSelectionCardinalityRank

/-!
# ConcreteCanonicalLearnerWorkingGrammarObservationSelectionPositiveAdditiveRank.lean

The preceding file gives the arbitrary-rank characterization for ordinary
cardinality observation-selection cost.

This file develops the corresponding arbitrary-rank theory for positive
additive coordinate cost.

## Exact positive-additive-rank witness class

For a coordinate-weight function

```lean
coordinateWeight : ι → Nat
```

and rank `r`, define the exact positive-additive-rank witness class by the
existence of an ambient selected subset `S` satisfying

```text
S.card + AdditiveCost(weight,S) = r,
Product(S) represents the target,
```

and such that every other representing ambient subset has positive additive
cost at least `r`.

This direct witness class is proved equal to the generic exact cost-rank shell
for

```text
PositiveAdditiveCost(weight,S)
  =
S.card + AdditiveCost(weight,S).
```

Hence every exact rank has a concrete decomposition into

```text
number of selected coordinates
+
total extra coordinate weight.
```

## Bounded shell decomposition

Every target represented by the full ambient product belongs to a unique exact
positive-additive-rank shell.  Its rank is bounded by

```text
U.card + AdditiveCost(weight,U),
```

the cost of selecting the complete ambient interface.

Thus the full ambient target class is exactly the union of the bounded exact
positive-additive shells.

## Lower-bound obstruction

For a full-product target,

```text
budget < positive-additive rank
```

is equivalent to failure of every ambient selected product whose combined
cardinality-and-weight cost is at most `budget`.

This gives a direct observation-interface lower-bound principle.

## Certified exact-rank selection

Every full-product target has an actual selected subset `S` whose positive
additive cost is exactly its rank.

Because positive additive cost is strictly monotone under proper inclusion,
the selected subset is inclusion-irredundant and every selected coordinate is
an essential observation refinement.

The selected-product certified learner identifies the target and returns one
exact checked grammar output at the selected product's minimum certified-
description rank.

## Compatibility with ranks zero and one

At rank zero, the general witness class is exactly the target class of the empty
selected product.

At rank one, it is exactly the zero-extra-weight one-coordinate/nonempty-
interface class established in the preceding rank-one file.

## Boundary

The rank and selected witness remain semantic and noncomputable.
No executable target-class decision procedure or optimization algorithm is
asserted.

No target grammar is supplied to any learner.
No `sorry`, `admit`, or `axiom` is used.
-/

namespace MCFG

universe u v w z


section ExactPositiveAdditiveRankWitnessClassDefinition

variable (α : Type u)
variable (ι : Type v)
variable (M : Type w)
variable [Monoid M]
variable (obsFamily : ι → α → M)
variable (f : Nat)
variable (coordinateWeight : ι → Nat)
variable (U : Finset ι)

/-- Languages having a representing ambient selection whose cardinality plus
total extra coordinate weight is exactly `rank`, with no cheaper representing
ambient selection. -/
def CorrectedConcreteObservationSelectionExactPositiveAdditiveRankWitnessClass
    (rank : Nat) :
    Set (Set (Word α)) :=
  {language |
    ∃ S : Finset ι,
      S ⊆ U ∧
        S.card +
            correctedConcreteObservationSelectionAdditiveCost
              coordinateWeight S =
          rank ∧
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
          rank <=
            R.card +
              correctedConcreteObservationSelectionAdditiveCost
                coordinateWeight R}

end ExactPositiveAdditiveRankWitnessClassDefinition


section ExactPositiveAdditiveRankWitnessMembership

variable {α : Type u}
variable {ι : Type v}
variable {M : Type w}
variable [Monoid M]
variable {obsFamily : ι → α → M}
variable {f : Nat}
variable {coordinateWeight : ι → Nat}
variable {U : Finset ι}
variable {language : Set (Word α)}
variable {rank : Nat}

/-- Exact membership theorem for the direct positive-additive-rank witness
class. -/
theorem
    mem_observationSelectionExactPositiveAdditiveRankWitnessClass_iff :
    language ∈
        CorrectedConcreteObservationSelectionExactPositiveAdditiveRankWitnessClass
          (z := z)
          α
          ι
          M
          obsFamily
          f
          coordinateWeight
          U
          rank ↔
      ∃ S : Finset ι,
        S ⊆ U ∧
          S.card +
              correctedConcreteObservationSelectionAdditiveCost
                coordinateWeight S =
            rank ∧
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
            rank <=
              R.card +
                correctedConcreteObservationSelectionAdditiveCost
                  coordinateWeight R := by

  rfl

end ExactPositiveAdditiveRankWitnessMembership


section ExactPositiveAdditiveRankShellEquality

variable {α : Type u}
variable {ι : Type v}
variable {M : Type w}
variable [Monoid M]
variable {obsFamily : ι → α → M}
variable {f : Nat}
variable {coordinateWeight : ι → Nat}
variable {U : Finset ι}

/-- The generic exact cost-rank shell for positive additive cost is exactly the
direct cardinality-plus-weight witness class. -/
theorem
    positiveAdditiveObservationSelectionExactRankClass_eq_witnessClass
    (rank : Nat) :
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
        rank =
      CorrectedConcreteObservationSelectionExactPositiveAdditiveRankWitnessClass
        (z := z)
        α
        ι
        M
        obsFamily
        f
        coordinateWeight
        U
        rank := by

  ext language

  constructor

  · intro hRank

    rcases hRank.1 with
      ⟨S, hSU, hCostLe, hTarget⟩

    have hRankLeCost :
        rank <=
          correctedConcreteObservationSelectionPositiveAdditiveCost
            coordinateWeight S := by

      by_contra hNotLe

      have hCostLt :
          correctedConcreteObservationSelectionPositiveAdditiveCost
              coordinateWeight S <
            rank := by
        omega

      have hAtSmaller :
          CorrectedConcreteObservationSelectionAtCost
            (obsFamily := obsFamily)
            (f := f)
            (correctedConcreteObservationSelectionPositiveAdditiveCost
              coordinateWeight)
            U
            language
            (correctedConcreteObservationSelectionPositiveAdditiveCost
              coordinateWeight S) := by

        exact
          ⟨S,
            hSU,
            Nat.le_refl _,
            hTarget⟩

      exact
        hRank.2
          (correctedConcreteObservationSelectionPositiveAdditiveCost
            coordinateWeight S)
          hCostLt
          hAtSmaller

    have hCostEq :
        correctedConcreteObservationSelectionPositiveAdditiveCost
            coordinateWeight S =
          rank :=
      Nat.le_antisymm
        hCostLe
        hRankLeCost

    refine
      ⟨S,
        hSU,
        by
          simpa [
            correctedConcreteObservationSelectionPositiveAdditiveCost
          ] using hCostEq,
        hTarget,
        ?_⟩

    intro R hRU hRTarget

    have hRankLeR :
        rank <=
          correctedConcreteObservationSelectionPositiveAdditiveCost
            coordinateWeight R := by

      by_contra hNotLe

      have hRCostLt :
          correctedConcreteObservationSelectionPositiveAdditiveCost
              coordinateWeight R <
            rank := by
        omega

      have hAtSmaller :
          CorrectedConcreteObservationSelectionAtCost
            (obsFamily := obsFamily)
            (f := f)
            (correctedConcreteObservationSelectionPositiveAdditiveCost
              coordinateWeight)
            U
            language
            (correctedConcreteObservationSelectionPositiveAdditiveCost
              coordinateWeight R) := by

        exact
          ⟨R,
            hRU,
            Nat.le_refl _,
            hRTarget⟩

      exact
        hRank.2
          (correctedConcreteObservationSelectionPositiveAdditiveCost
            coordinateWeight R)
          hRCostLt
          hAtSmaller

    simpa [
      correctedConcreteObservationSelectionPositiveAdditiveCost
    ] using hRankLeR

  · intro hWitness

    rcases hWitness with
      ⟨S,
        hSU,
        hCostEq,
        hTarget,
        hMinimum⟩

    have hPositiveCostEq :
        correctedConcreteObservationSelectionPositiveAdditiveCost
            coordinateWeight S =
          rank := by

      simpa [
        correctedConcreteObservationSelectionPositiveAdditiveCost
      ] using hCostEq

    refine
      ⟨⟨S,
          hSU,
          by
            rw [hPositiveCostEq],
          hTarget⟩,
        ?_⟩

    intro costBudget hBudget hAtCost

    rcases hAtCost with
      ⟨R, hRU, hRCost, hRTarget⟩

    have hRankLe :
        rank <=
          R.card +
            correctedConcreteObservationSelectionAdditiveCost
              coordinateWeight R :=
      hMinimum
        R
        hRU
        hRTarget

    unfold
      correctedConcreteObservationSelectionPositiveAdditiveCost
      at hRCost

    omega

end ExactPositiveAdditiveRankShellEquality


section PositiveAdditiveRankWitnessBounds

variable {α : Type u}
variable {ι : Type v}
variable {M : Type w}
variable [Monoid M]
variable {obsFamily : ι → α → M}
variable {f : Nat}
variable {coordinateWeight : ι → Nat}
variable {U : Finset ι}
variable {language : Set (Word α)}
variable {rank : Nat}

/-- Every direct positive-additive rank witness uses at most `rank`
coordinates. -/
theorem positiveAdditiveRankWitness_card_le
    (hWitness :
      language ∈
        CorrectedConcreteObservationSelectionExactPositiveAdditiveRankWitnessClass
          (z := z)
          α
          ι
          M
          obsFamily
          f
          coordinateWeight
          U
          rank) :
    ∃ S : Finset ι,
      S ⊆ U ∧
        S.card <= rank ∧
        language ∈
          StartRootedCorrectedConcreteTargetClass
            (v := z)
            α
            (↥S → M)
            (selectedObservationProduct obsFamily S)
            f := by

  rcases hWitness with
    ⟨S, hSU, hCostEq, hTarget, hMinimum⟩

  refine
    ⟨S,
      hSU,
      ?_,
      hTarget⟩

  omega

/-- Every direct positive-additive rank witness has total extra coordinate
weight at most `rank`. -/
theorem positiveAdditiveRankWitness_additiveCost_le
    (hWitness :
      language ∈
        CorrectedConcreteObservationSelectionExactPositiveAdditiveRankWitnessClass
          (z := z)
          α
          ι
          M
          obsFamily
          f
          coordinateWeight
          U
          rank) :
    ∃ S : Finset ι,
      S ⊆ U ∧
        correctedConcreteObservationSelectionAdditiveCost
            coordinateWeight S <=
          rank ∧
        language ∈
          StartRootedCorrectedConcreteTargetClass
            (v := z)
            α
            (↥S → M)
            (selectedObservationProduct obsFamily S)
            f := by

  rcases hWitness with
    ⟨S, hSU, hCostEq, hTarget, hMinimum⟩

  refine
    ⟨S,
      hSU,
      ?_,
      hTarget⟩

  omega

end PositiveAdditiveRankWitnessBounds


section PositiveAdditiveRankCompatibility

variable {α : Type u}
variable {ι : Type v}
variable {M : Type w}
variable [Monoid M]
variable (obsFamily : ι → α → M)
variable (f : Nat)
variable (coordinateWeight : ι → Nat)
variable (U : Finset ι)

/-- The paper-facing generic target rank under positive additive cost is
definitionally the earlier positive-additive minimum cost. -/
theorem
    ambientTarget_positiveAdditiveCostRank_eq_positiveAdditiveMinimumCost
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
      ambientTargetObservationSelectionPositiveAdditiveMinimumCost
        (z := z)
        obsFamily
        f
        coordinateWeight
        U
        hTarget := by

  rfl

/-- A full-product target belongs to the direct exact witness class at its
minimum positive additive rank. -/
theorem ambientTarget_mem_exactPositiveAdditiveRankWitnessClass
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
      CorrectedConcreteObservationSelectionExactPositiveAdditiveRankWitnessClass
        (z := z)
        α
        ι
        M
        obsFamily
        f
        coordinateWeight
        U
        (ambientTargetObservationSelectionPositiveAdditiveMinimumCost
          (z := z)
          obsFamily
          f
          coordinateWeight
          U
          hTarget) := by

  have hShell :=
    ambientTarget_mem_exactObservationSelectionCostRankClass
      (z := z)
      obsFamily
      f
      (correctedConcreteObservationSelectionPositiveAdditiveCost
        coordinateWeight)
      U
      hTarget

  rw [
    ambientTarget_positiveAdditiveCostRank_eq_positiveAdditiveMinimumCost
      (z := z)
      obsFamily
      f
      coordinateWeight
      U
      hTarget,
    positiveAdditiveObservationSelectionExactRankClass_eq_witnessClass
      (z := z)
  ] at hShell

  exact hShell

end PositiveAdditiveRankCompatibility


section BoundedPositiveAdditiveRankDecomposition

variable {α : Type u}
variable {ι : Type v}
variable {M : Type w}
variable [Monoid M]
variable (obsFamily : ι → α → M)
variable (f : Nat)
variable (coordinateWeight : ι → Nat)
variable (U : Finset ι)

/-- The full ambient target class is exactly the union of exact positive
additive shells bounded by the cost of the complete ambient interface. -/
theorem
    fullProductTargetClass_eq_exists_boundedExactPositiveAdditiveRank :
    StartRootedCorrectedConcreteTargetClass
        (v := z)
        α
        (↥U → M)
        (selectedObservationProduct obsFamily U)
        f =
      {language : Set (Word α) |
        ∃ rank : Nat,
          rank <=
              U.card +
                correctedConcreteObservationSelectionAdditiveCost
                  coordinateWeight U ∧
            language ∈
              CorrectedConcreteObservationSelectionExactPositiveAdditiveRankWitnessClass
                (z := z)
                α
                ι
                M
                obsFamily
                f
                coordinateWeight
                U
                rank} := by

  ext language

  constructor

  · intro hTarget

    let rank :=
      ambientTargetObservationSelectionPositiveAdditiveMinimumCost
        (z := z)
        obsFamily
        f
        coordinateWeight
        U
        hTarget

    have hRankBound :
        rank <=
          U.card +
            correctedConcreteObservationSelectionAdditiveCost
              coordinateWeight U := by

      have hBound :=
        ambientTargetObservationSelectionPositiveAdditiveMinimumCost_le
          (z := z)
          obsFamily
          f
          coordinateWeight
          U
          hTarget

      simpa [
        rank,
        correctedConcreteObservationSelectionPositiveAdditiveCost
      ] using hBound

    exact
      ⟨rank,
        hRankBound,
        ambientTarget_mem_exactPositiveAdditiveRankWitnessClass
          (z := z)
          obsFamily
          f
          coordinateWeight
          U
          hTarget⟩

  · intro hRank

    rcases hRank with
      ⟨rank, hRankBound, hWitness⟩

    rcases hWitness with
      ⟨S,
        hSU,
        hCostEq,
        hSelected,
        hMinimum⟩

    exact
      selectedObservationProductTargetClass_mono
        (z := z)
        obsFamily
        f
        hSU
        hSelected

/-- Every full-product target belongs to a unique bounded exact positive
additive rank shell. -/
theorem
    fullProductTarget_existsUnique_boundedExactPositiveAdditiveRank
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
      rank <=
          U.card +
            correctedConcreteObservationSelectionAdditiveCost
              coordinateWeight U ∧
        language ∈
          CorrectedConcreteObservationSelectionExactPositiveAdditiveRankWitnessClass
            (z := z)
            α
            ι
            M
            obsFamily
            f
            coordinateWeight
            U
            rank := by

  let rank :=
    ambientTargetObservationSelectionPositiveAdditiveMinimumCost
      (z := z)
      obsFamily
      f
      coordinateWeight
      U
      hTarget

  have hRankBound :
      rank <=
        U.card +
          correctedConcreteObservationSelectionAdditiveCost
            coordinateWeight U := by

    have hBound :=
      ambientTargetObservationSelectionPositiveAdditiveMinimumCost_le
        (z := z)
        obsFamily
        f
        coordinateWeight
        U
        hTarget

    simpa [
      rank,
      correctedConcreteObservationSelectionPositiveAdditiveCost
    ] using hBound

  refine
    ⟨rank,
      ⟨hRankBound,
        ambientTarget_mem_exactPositiveAdditiveRankWitnessClass
          (z := z)
          obsFamily
          f
          coordinateWeight
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
          (correctedConcreteObservationSelectionPositiveAdditiveCost
            coordinateWeight)
          U
          rank' := by

    rw [
      positiveAdditiveObservationSelectionExactRankClass_eq_witnessClass
        (z := z)
    ]

    exact hRank'.2

  let hSelection :=
    hasCorrectedConcreteObservationSelectionCost_of_fullProductTarget
      (obsFamily := obsFamily)
      (f := f)
      (correctedConcreteObservationSelectionPositiveAdditiveCost
        coordinateWeight)
      hTarget

  have hRankEqMinimum :
      rank' =
        correctedConcreteObservationSelectionMinimumCost
          (correctedConcreteObservationSelectionPositiveAdditiveCost
            coordinateWeight)
          hSelection :=
    (observationSelection_mem_exactCostRankClass_iff_rank_eq_minimum
      (z := z)
      hSelection
      rank').mp
      hShell

  have hMinimumEqRank :
      correctedConcreteObservationSelectionMinimumCost
          (correctedConcreteObservationSelectionPositiveAdditiveCost
            coordinateWeight)
          hSelection =
        rank := by

    simp [
      rank,
      ambientTargetObservationSelectionPositiveAdditiveMinimumCost,
      ambientTargetObservationSelectionMinimumCost,
      hSelection
    ]

  omega

end BoundedPositiveAdditiveRankDecomposition


section PositiveAdditiveRankLowerBoundCriterion

variable {α : Type u}
variable {ι : Type v}
variable {M : Type w}
variable [Monoid M]
variable (obsFamily : ι → α → M)
variable (f : Nat)
variable (coordinateWeight : ι → Nat)
variable (U : Finset ι)

/-- A strict lower bound on positive additive rank is exactly failure of every
ambient selection within the combined cardinality-and-weight budget. -/
theorem
    ambientTarget_positiveAdditiveRank_gt_iff_all_boundedSelections_fail
    {language : Set (Word α)}
    (hTarget :
      language ∈
        StartRootedCorrectedConcreteTargetClass
          (v := z)
          α
          (↥U → M)
          (selectedObservationProduct obsFamily U)
          f)
    (costBudget : Nat) :
    costBudget <
        ambientTargetObservationSelectionPositiveAdditiveMinimumCost
          (z := z)
          obsFamily
          f
          coordinateWeight
          U
          hTarget ↔
      ∀ S : Finset ι,
        S ⊆ U →
        S.card +
            correctedConcreteObservationSelectionAdditiveCost
              coordinateWeight S <=
          costBudget →
        language ∉
          StartRootedCorrectedConcreteTargetClass
            (v := z)
            α
            (↥S → M)
            (selectedObservationProduct obsFamily S)
            f := by

  simpa [
    correctedConcreteObservationSelectionPositiveAdditiveCost
  ] using
    ambientTargetPositiveAdditiveMinimumCost_gt_iff_all_bounded_selections_fail
      (z := z)
      obsFamily
      f
      coordinateWeight
      U
      hTarget
      costBudget

end PositiveAdditiveRankLowerBoundCriterion


section PositiveAdditiveRankCertifiedSelection

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

/-- Every full-product target has an actual irredundant selected subset whose
cardinality plus total extra coordinate weight is exactly its positive additive
rank, together with the selected-product certified learner. -/
theorem ambientTarget_exists_positiveAdditiveRankCertifiedSelection
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
          ambientTargetObservationSelectionPositiveAdditiveMinimumCost
            (z := z)
            obsFamily
            f
            coordinateWeight
            U
            hTarget ∧
        S ⊆ U ∧
        S.card +
            correctedConcreteObservationSelectionAdditiveCost
              coordinateWeight S =
          rank ∧
        S.card <= rank ∧
        correctedConcreteObservationSelectionAdditiveCost
            coordinateWeight S <=
          rank ∧
        language ∈
          CorrectedConcreteObservationSelectionExactPositiveAdditiveRankWitnessClass
            (z := z)
            α
            ι
            M
            obsFamily
            f
            coordinateWeight
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
      ambientTarget_exists_positiveAdditiveMinimumCertifiedSelection
        (z := z)
        hα
        obsFamily
        f
        coordinateWeight
        U
        hTarget with
    ⟨S,
      hSU,
      hSelected,
      hCost,
      hIrredundant,
      hEssential,
      hIdentifies,
      C,
      hLanguage,
      hBits,
      hSearch⟩

  let rank :=
    ambientTargetObservationSelectionPositiveAdditiveMinimumCost
      (z := z)
      obsFamily
      f
      coordinateWeight
      U
      hTarget

  have hCostDecomposition :
      S.card +
          correctedConcreteObservationSelectionAdditiveCost
            coordinateWeight S =
        rank := by

    simpa [
      rank,
      correctedConcreteObservationSelectionPositiveAdditiveCost
    ] using hCost

  have hRankWitness :
      language ∈
        CorrectedConcreteObservationSelectionExactPositiveAdditiveRankWitnessClass
          (z := z)
          α
          ι
          M
          obsFamily
          f
          coordinateWeight
          U
          rank :=
    ambientTarget_mem_exactPositiveAdditiveRankWitnessClass
      (z := z)
      obsFamily
      f
      coordinateWeight
      U
      hTarget

  exact
    ⟨rank,
      S,
      hSelected,
      rfl,
      hSU,
      hCostDecomposition,
      by omega,
      by omega,
      hRankWitness,
      hIrredundant,
      hEssential,
      hIdentifies,
      C,
      hLanguage,
      hBits,
      hSearch⟩

end PositiveAdditiveRankCertifiedSelection


section PositiveAdditiveRankZeroOneCompatibility

variable {α : Type u}
variable {ι : Type v}
variable {M : Type w}
variable [Monoid M]
variable (obsFamily : ι → α → M)
variable (f : Nat)
variable (coordinateWeight : ι → Nat)
variable (U : Finset ι)

/-- The general exact positive-additive-rank witness theorem specializes at
rank zero to the empty selected product target class. -/
theorem
    exactPositiveAdditiveRankWitnessClass_zero_eq_emptyProductTargetClass :
    CorrectedConcreteObservationSelectionExactPositiveAdditiveRankWitnessClass
        (z := z)
        α
        ι
        M
        obsFamily
        f
        coordinateWeight
        U
        0 =
      StartRootedCorrectedConcreteTargetClass
        (v := z)
        α
        (↥(∅ : Finset ι) → M)
        (selectedObservationProduct obsFamily ∅)
        f := by

  calc
    CorrectedConcreteObservationSelectionExactPositiveAdditiveRankWitnessClass
        (z := z)
        α
        ι
        M
        obsFamily
        f
        coordinateWeight
        U
        0 =
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
        0 := by
          symm
          exact
            positiveAdditiveObservationSelectionExactRankClass_eq_witnessClass
              (z := z)
              0

    _ =
      StartRootedCorrectedConcreteTargetClass
        (v := z)
        α
        (↥(∅ : Finset ι) → M)
        (selectedObservationProduct obsFamily ∅)
        f :=
          positiveAdditiveObservationSelectionExactRankZeroClass_eq_emptyProductTargetClass
            (z := z)
            obsFamily
            f
            coordinateWeight
            U

/-- The general exact positive-additive-rank witness theorem specializes at
rank one to the zero-extra-weight one-coordinate class. -/
theorem
    exactPositiveAdditiveRankWitnessClass_one_eq_rankOneClass :
    CorrectedConcreteObservationSelectionExactPositiveAdditiveRankWitnessClass
        (z := z)
        α
        ι
        M
        obsFamily
        f
        coordinateWeight
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

  calc
    CorrectedConcreteObservationSelectionExactPositiveAdditiveRankWitnessClass
        (z := z)
        α
        ι
        M
        obsFamily
        f
        coordinateWeight
        U
        1 =
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
          symm
          exact
            positiveAdditiveObservationSelectionExactRankClass_eq_witnessClass
              (z := z)
              1

    _ =
      CorrectedConcretePositiveAdditiveObservationSelectionRankOneClass
        (z := z)
        α
        ι
        M
        obsFamily
        f
        coordinateWeight
        U :=
          positiveAdditiveObservationSelectionExactRankOneClass_eq_rankOneClass
            (z := z)

end PositiveAdditiveRankZeroOneCompatibility


section ObservationSelectionPositiveAdditiveRankFinalPackage

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

/-- Final arbitrary-rank positive-additive witness characterization, bounded
shell decomposition, lower-bound obstruction, and certified exact-rank
selection package. -/
theorem
    correctedConcreteCertifiedWorkingGrammar_observationSelectionPositiveAdditiveRank_package :
    (∀ rank : Nat,
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
          rank =
        CorrectedConcreteObservationSelectionExactPositiveAdditiveRankWitnessClass
          (z := z)
          α
          ι
          M
          obsFamily
          f
          coordinateWeight
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
            rank <=
                U.card +
                  correctedConcreteObservationSelectionAdditiveCost
                    coordinateWeight U ∧
              language ∈
                CorrectedConcreteObservationSelectionExactPositiveAdditiveRankWitnessClass
                  (z := z)
                  α
                  ι
                  M
                  obsFamily
                  f
                  coordinateWeight
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
        ∀ costBudget : Nat,
          (costBudget <
              ambientTargetObservationSelectionPositiveAdditiveMinimumCost
                (z := z)
                obsFamily
                f
                coordinateWeight
                U
                hTarget ↔
            ∀ S : Finset ι,
              S ⊆ U →
              S.card +
                  correctedConcreteObservationSelectionAdditiveCost
                    coordinateWeight S <=
                costBudget →
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
              ambientTargetObservationSelectionPositiveAdditiveMinimumCost
                (z := z)
                obsFamily
                f
                coordinateWeight
                U
                hTarget ∧
            S ⊆ U ∧
            S.card +
                correctedConcreteObservationSelectionAdditiveCost
                  coordinateWeight S =
              rank ∧
            S.card <= rank ∧
            correctedConcreteObservationSelectionAdditiveCost
                coordinateWeight S <=
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
      fullProductTargetClass_eq_exists_boundedExactPositiveAdditiveRank
        (z := z)
        obsFamily
        f
        coordinateWeight
        U,
      ?_,
      ?_⟩

  · intro rank

    exact
      positiveAdditiveObservationSelectionExactRankClass_eq_witnessClass
        (z := z)
        rank

  · intro language hTarget costBudget

    exact
      ambientTarget_positiveAdditiveRank_gt_iff_all_boundedSelections_fail
        (z := z)
        obsFamily
        f
        coordinateWeight
        U
        hTarget
        costBudget

  · intro language hTarget

    rcases
        ambientTarget_exists_positiveAdditiveRankCertifiedSelection
          (z := z)
          hα
          obsFamily
          f
          coordinateWeight
          U
          hTarget with
      ⟨rank,
        S,
        hSelected,
        hRank,
        hSU,
        hCostDecomposition,
        hCardLe,
        hAdditiveLe,
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
        hCostDecomposition,
        hCardLe,
        hAdditiveLe,
        hIrredundant,
        hIdentifies⟩

end ObservationSelectionPositiveAdditiveRankFinalPackage

end MCFG
