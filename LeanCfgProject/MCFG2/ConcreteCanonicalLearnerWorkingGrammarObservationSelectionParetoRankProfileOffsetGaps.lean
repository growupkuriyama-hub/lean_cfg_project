/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG2.ConcreteCanonicalLearnerWorkingGrammarObservationSelectionParetoRankProfileOffsetGapFree

/-!
# ConcreteCanonicalLearnerWorkingGrammarObservationSelectionParetoRankProfileOffsetGaps.lean

The preceding file isolates the gap-free case of the finite realized
Pareto-profile offset spectrum.

This file formalizes the complementary finite gap structure.

## Offset gaps

The finite gap set is

```text
range (width + 1) \ realizedOffsets.
```

Thus an offset belongs to the gap set exactly when

```text
offset ≤ width
```

but no rank-minimizing Pareto profile realizes it.

Gap-freeness is equivalent to the gap set being empty.

## Exact defect formula

Because the realized offset set is always contained in the complete finite
width interval, the interval splits into realized offsets and gaps.

Using the previously proved finite offset/profile bijection:

```text
number of profiles + number of gaps = width + 1.
```

Equivalently,

```text
number of gaps = width + 1 - number of profiles.
```

Thus the gap count is the exact defect in the sharp profile-count bound.

## First gap

When the spectrum is not gap-free, select the least missing offset by
`Nat.find`.

Every smaller offset is realized, while the first gap itself has no
rank-minimizing Pareto profile and therefore no offset-indexed selected
interface.

The realized prefix before the first gap remains fully available: every
smaller offset has an actual Pareto-optimal, exact-rank, irredundant selected
product and its own certified learner identifying the target.

## Boundary

A gap means absence of a profile at one point of the affine rank line.
It does not imply nonlearnability of the target.  The endpoint products and all
realized offset products remain certifiably learnable.

No target grammar is supplied to any learner.
No `sorry`, `admit`, or `axiom` is used.
-/

namespace MCFG

universe u v w z


section ParetoRankProfileOffsetGapDefinition

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
  {hTarget :
    language ∈
      StartRootedCorrectedConcreteTargetClass
        (v := z)
        α
        (↥U → M)
        (selectedObservationProduct obsFamily U)
        f}

/-- Finite set of missing normalized offsets inside the complete width
interval. -/
def correctedConcreteObservationPositiveAdditiveParetoRankProfileOffsetGaps
    (minimumCardinalityResult :
      CorrectedConcreteObservationPositiveAdditiveParetoMinimumCardinalityProfileResult
        (z := z)
        obsFamily
        f
        coordinateWeight
        U
        language
        hTarget)
    (minimumAdditiveResult :
      CorrectedConcreteObservationPositiveAdditiveParetoMinimumAdditiveProfileResult
        (z := z)
        obsFamily
        f
        coordinateWeight
        U
        language
        hTarget) :
    Finset Nat :=
  Finset.range
      (correctedConcreteObservationPositiveAdditiveParetoProfileTradeoffWidth
          minimumCardinalityResult
          minimumAdditiveResult +
        1) \
    correctedConcreteObservationPositiveAdditiveParetoRankProfileOffsets
      minimumCardinalityResult

/-- Number of missing normalized offsets. -/
def correctedConcreteObservationPositiveAdditiveParetoRankProfileOffsetGapCount
    (minimumCardinalityResult :
      CorrectedConcreteObservationPositiveAdditiveParetoMinimumCardinalityProfileResult
        (z := z)
        obsFamily
        f
        coordinateWeight
        U
        language
        hTarget)
    (minimumAdditiveResult :
      CorrectedConcreteObservationPositiveAdditiveParetoMinimumAdditiveProfileResult
        (z := z)
        obsFamily
        f
        coordinateWeight
        U
        language
        hTarget) :
    Nat :=
  (correctedConcreteObservationPositiveAdditiveParetoRankProfileOffsetGaps
    minimumCardinalityResult
    minimumAdditiveResult).card

end ParetoRankProfileOffsetGapDefinition


section ParetoRankProfileOffsetGapMembership

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
  {hTarget :
    language ∈
      StartRootedCorrectedConcreteTargetClass
        (v := z)
        α
        (↥U → M)
        (selectedObservationProduct obsFamily U)
        f}
variable
  (minimumCardinalityResult :
    CorrectedConcreteObservationPositiveAdditiveParetoMinimumCardinalityProfileResult
      (z := z)
      obsFamily
      f
      coordinateWeight
      U
      language
      hTarget)
variable
  (minimumAdditiveResult :
    CorrectedConcreteObservationPositiveAdditiveParetoMinimumAdditiveProfileResult
      (z := z)
      obsFamily
      f
      coordinateWeight
      U
      language
      hTarget)

/-- Exact membership theorem for the finite gap set. -/
theorem
    mem_correctedConcreteObservationPositiveAdditiveParetoRankProfileOffsetGaps_iff
    {offset : Nat} :
    offset ∈
        correctedConcreteObservationPositiveAdditiveParetoRankProfileOffsetGaps
          minimumCardinalityResult
          minimumAdditiveResult ↔
      offset <=
          correctedConcreteObservationPositiveAdditiveParetoProfileTradeoffWidth
            minimumCardinalityResult
            minimumAdditiveResult ∧
        offset ∉
          correctedConcreteObservationPositiveAdditiveParetoRankProfileOffsets
            minimumCardinalityResult := by

  unfold
    correctedConcreteObservationPositiveAdditiveParetoRankProfileOffsetGaps

  simp only [
    Finset.mem_sdiff,
    Finset.mem_range
  ]

  constructor

  · intro hOffset

    exact
      ⟨by omega,
        hOffset.2⟩

  · intro hOffset

    exact
      ⟨by omega,
        hOffset.2⟩

/-- Every gap lies in the complete finite width interval. -/
theorem
    correctedConcreteObservationPositiveAdditiveParetoRankProfileOffsetGaps_subset_range :
    correctedConcreteObservationPositiveAdditiveParetoRankProfileOffsetGaps
        minimumCardinalityResult
        minimumAdditiveResult ⊆
      Finset.range
        (correctedConcreteObservationPositiveAdditiveParetoProfileTradeoffWidth
            minimumCardinalityResult
            minimumAdditiveResult +
          1) := by

  intro offset hGap

  exact
    Finset.mem_range.mpr
      (by
        have hLe :=
          ((mem_correctedConcreteObservationPositiveAdditiveParetoRankProfileOffsetGaps_iff
            minimumCardinalityResult
            minimumAdditiveResult).mp
            hGap).1

        omega)

/-- The realized offset set and gap set are disjoint. -/
theorem
    correctedConcreteObservationPositiveAdditiveParetoRankProfileOffsets_disjoint_gaps :
    Disjoint
      (correctedConcreteObservationPositiveAdditiveParetoRankProfileOffsets
        minimumCardinalityResult)
      (correctedConcreteObservationPositiveAdditiveParetoRankProfileOffsetGaps
        minimumCardinalityResult
        minimumAdditiveResult) := by

  refine Finset.disjoint_left.mpr ?_

  intro offset hOffset hGap

  exact
    ((mem_correctedConcreteObservationPositiveAdditiveParetoRankProfileOffsetGaps_iff
      minimumCardinalityResult
      minimumAdditiveResult).mp
      hGap).2
      hOffset

/-- Realized offsets together with gaps cover the complete width interval. -/
theorem
    correctedConcreteObservationPositiveAdditiveParetoRankProfileOffsets_union_gaps_eq_range :
    correctedConcreteObservationPositiveAdditiveParetoRankProfileOffsets
          minimumCardinalityResult ∪
        correctedConcreteObservationPositiveAdditiveParetoRankProfileOffsetGaps
          minimumCardinalityResult
          minimumAdditiveResult =
      Finset.range
        (correctedConcreteObservationPositiveAdditiveParetoProfileTradeoffWidth
            minimumCardinalityResult
            minimumAdditiveResult +
          1) := by

  ext offset

  constructor

  · intro hOffset

    rcases Finset.mem_union.mp hOffset with
      hRealized | hGap

    · exact
        correctedConcreteObservationPositiveAdditiveParetoRankProfileOffsets_subset_range
          minimumCardinalityResult
          minimumAdditiveResult
          hRealized

    · exact
        correctedConcreteObservationPositiveAdditiveParetoRankProfileOffsetGaps_subset_range
          minimumCardinalityResult
          minimumAdditiveResult
          hGap

  · intro hRange

    by_cases hRealized :
      offset ∈
        correctedConcreteObservationPositiveAdditiveParetoRankProfileOffsets
          minimumCardinalityResult

    · exact
        Finset.mem_union_left
          _
          hRealized

    · apply
        Finset.mem_union_right

      apply
        (mem_correctedConcreteObservationPositiveAdditiveParetoRankProfileOffsetGaps_iff
          minimumCardinalityResult
          minimumAdditiveResult).mpr

      exact
        ⟨by
          have hLt :=
            Finset.mem_range.mp
              hRange

          omega,
          hRealized⟩

end ParetoRankProfileOffsetGapMembership


section ParetoRankProfileOffsetGapFreeEquivalences

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
  {hTarget :
    language ∈
      StartRootedCorrectedConcreteTargetClass
        (v := z)
        α
        (↥U → M)
        (selectedObservationProduct obsFamily U)
        f}
variable
  (minimumCardinalityResult :
    CorrectedConcreteObservationPositiveAdditiveParetoMinimumCardinalityProfileResult
      (z := z)
      obsFamily
      f
      coordinateWeight
      U
      language
      hTarget)
variable
  (minimumAdditiveResult :
    CorrectedConcreteObservationPositiveAdditiveParetoMinimumAdditiveProfileResult
      (z := z)
      obsFamily
      f
      coordinateWeight
      U
      language
      hTarget)

/-- Gap-freeness is equivalent to the finite gap set being empty. -/
theorem
    positiveAdditiveParetoRankProfileOffsetsGapFree_iff_gaps_eq_empty :
    CorrectedConcreteObservationPositiveAdditiveParetoRankProfileOffsetsGapFree
          minimumCardinalityResult
          minimumAdditiveResult ↔
      correctedConcreteObservationPositiveAdditiveParetoRankProfileOffsetGaps
          minimumCardinalityResult
          minimumAdditiveResult =
        ∅ := by

  constructor

  · intro hGapFree

    ext offset

    constructor

    · intro hGap

      have hGapData :=
        (mem_correctedConcreteObservationPositiveAdditiveParetoRankProfileOffsetGaps_iff
          minimumCardinalityResult
          minimumAdditiveResult).mp
          hGap

      exact
        False.elim
          (hGapData.2
            (hGapFree
              offset
              hGapData.1))

    · intro hEmpty

      simp at hEmpty

  · intro hGapsEmpty offset hOffsetLe

    by_contra hOffsetMissing

    have hGap :
        offset ∈
          correctedConcreteObservationPositiveAdditiveParetoRankProfileOffsetGaps
            minimumCardinalityResult
            minimumAdditiveResult :=
      (mem_correctedConcreteObservationPositiveAdditiveParetoRankProfileOffsetGaps_iff
        minimumCardinalityResult
        minimumAdditiveResult).mpr
        ⟨hOffsetLe,
          hOffsetMissing⟩

    rw [hGapsEmpty] at hGap

    simpa using hGap

/-- Non-gap-freeness is equivalent to the finite gap set being nonempty. -/
theorem
    not_positiveAdditiveParetoRankProfileOffsetsGapFree_iff_gaps_nonempty :
    ¬
        CorrectedConcreteObservationPositiveAdditiveParetoRankProfileOffsetsGapFree
          minimumCardinalityResult
          minimumAdditiveResult ↔
      (correctedConcreteObservationPositiveAdditiveParetoRankProfileOffsetGaps
        minimumCardinalityResult
        minimumAdditiveResult).Nonempty := by

  constructor

  · intro hNotGapFree

    by_contra hNotNonempty

    have hGapsEmpty :
        correctedConcreteObservationPositiveAdditiveParetoRankProfileOffsetGaps
            minimumCardinalityResult
            minimumAdditiveResult =
          ∅ := by

      ext offset

      constructor

      · intro hGap

        exact
          False.elim
            (hNotNonempty
              ⟨offset,
                hGap⟩)

      · intro hEmpty

        simp at hEmpty

    exact
      hNotGapFree
        ((positiveAdditiveParetoRankProfileOffsetsGapFree_iff_gaps_eq_empty
          minimumCardinalityResult
          minimumAdditiveResult).mpr
          hGapsEmpty)

  · intro hGapsNonempty hGapFree

    rcases hGapsNonempty with
      ⟨offset, hGap⟩

    have hGapsEmpty :=
      (positiveAdditiveParetoRankProfileOffsetsGapFree_iff_gaps_eq_empty
        minimumCardinalityResult
        minimumAdditiveResult).mp
        hGapFree

    rw [hGapsEmpty] at hGap

    simpa using hGap

/-- Gap-freeness is equivalent to zero finite gap count. -/
theorem
    positiveAdditiveParetoRankProfileOffsetsGapFree_iff_gapCount_eq_zero :
    CorrectedConcreteObservationPositiveAdditiveParetoRankProfileOffsetsGapFree
          minimumCardinalityResult
          minimumAdditiveResult ↔
      correctedConcreteObservationPositiveAdditiveParetoRankProfileOffsetGapCount
          minimumCardinalityResult
          minimumAdditiveResult =
        0 := by

  rw [
    positiveAdditiveParetoRankProfileOffsetsGapFree_iff_gaps_eq_empty
      minimumCardinalityResult
      minimumAdditiveResult
  ]

  unfold
    correctedConcreteObservationPositiveAdditiveParetoRankProfileOffsetGapCount

  exact
    Finset.card_eq_zero

/-- Non-gap-freeness is equivalent to positive finite gap count. -/
theorem
    not_positiveAdditiveParetoRankProfileOffsetsGapFree_iff_gapCount_pos :
    ¬
        CorrectedConcreteObservationPositiveAdditiveParetoRankProfileOffsetsGapFree
          minimumCardinalityResult
          minimumAdditiveResult ↔
      0 <
        correctedConcreteObservationPositiveAdditiveParetoRankProfileOffsetGapCount
          minimumCardinalityResult
          minimumAdditiveResult := by

  rw [
    not_positiveAdditiveParetoRankProfileOffsetsGapFree_iff_gaps_nonempty
      minimumCardinalityResult
      minimumAdditiveResult
  ]

  unfold
    correctedConcreteObservationPositiveAdditiveParetoRankProfileOffsetGapCount

  exact
    Finset.card_pos

end ParetoRankProfileOffsetGapFreeEquivalences


section ParetoRankProfileOffsetGapCountFormula

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
  {hTarget :
    language ∈
      StartRootedCorrectedConcreteTargetClass
        (v := z)
        α
        (↥U → M)
        (selectedObservationProduct obsFamily U)
        f}
variable
  (minimumCardinalityResult :
    CorrectedConcreteObservationPositiveAdditiveParetoMinimumCardinalityProfileResult
      (z := z)
      obsFamily
      f
      coordinateWeight
      U
      language
      hTarget)
variable
  (minimumAdditiveResult :
    CorrectedConcreteObservationPositiveAdditiveParetoMinimumAdditiveProfileResult
      (z := z)
      obsFamily
      f
      coordinateWeight
      U
      language
      hTarget)

/-- The finite gap count is the exact cardinality defect of the realized
offset set inside the complete width interval. -/
theorem
    positiveAdditiveParetoRankProfileOffsetGapCount_eq_width_add_one_sub_offsets_card :
    correctedConcreteObservationPositiveAdditiveParetoRankProfileOffsetGapCount
          minimumCardinalityResult
          minimumAdditiveResult =
      correctedConcreteObservationPositiveAdditiveParetoProfileTradeoffWidth
            minimumCardinalityResult
            minimumAdditiveResult +
          1 -
        (correctedConcreteObservationPositiveAdditiveParetoRankProfileOffsets
          minimumCardinalityResult).card := by

  have hSubset :=
    correctedConcreteObservationPositiveAdditiveParetoRankProfileOffsets_subset_range
      minimumCardinalityResult
      minimumAdditiveResult

  have hCardSdiff :
      (Finset.range
          (correctedConcreteObservationPositiveAdditiveParetoProfileTradeoffWidth
              minimumCardinalityResult
              minimumAdditiveResult +
            1) \
        correctedConcreteObservationPositiveAdditiveParetoRankProfileOffsets
          minimumCardinalityResult).card =
        (Finset.range
          (correctedConcreteObservationPositiveAdditiveParetoProfileTradeoffWidth
              minimumCardinalityResult
              minimumAdditiveResult +
            1)).card -
          (correctedConcreteObservationPositiveAdditiveParetoRankProfileOffsets
            minimumCardinalityResult).card :=
    Finset.card_sdiff
      hSubset

  simpa [
    correctedConcreteObservationPositiveAdditiveParetoRankProfileOffsetGapCount,
    correctedConcreteObservationPositiveAdditiveParetoRankProfileOffsetGaps
  ] using
    hCardSdiff

/-- Exact defect formula:
`profiles.card + gaps.card = width + 1`. -/
theorem
    positiveAdditiveParetoRankProfiles_card_add_gapCount_eq_width_add_one :
    (correctedConcreteObservationPositiveAdditiveRankMinimizingParetoProfiles
          (z := z)
          obsFamily
          f
          coordinateWeight
          U
          language
          hTarget).card +
        correctedConcreteObservationPositiveAdditiveParetoRankProfileOffsetGapCount
          minimumCardinalityResult
          minimumAdditiveResult =
      correctedConcreteObservationPositiveAdditiveParetoProfileTradeoffWidth
          minimumCardinalityResult
          minimumAdditiveResult +
        1 := by

  have hOffsetProfileCard :=
    correctedConcreteObservationPositiveAdditiveParetoRankProfileOffsets_card_eq_profiles_card
      minimumCardinalityResult
      minimumAdditiveResult

  have hOffsetsLe :=
    correctedConcreteObservationPositiveAdditiveParetoRankProfileOffsets_card_le_width_add_one
      minimumCardinalityResult
      minimumAdditiveResult

  rw [
    positiveAdditiveParetoRankProfileOffsetGapCount_eq_width_add_one_sub_offsets_card
      minimumCardinalityResult
      minimumAdditiveResult,
    ← hOffsetProfileCard
  ]

  omega

/-- Equivalent profile-cardinality defect formula. -/
theorem
    positiveAdditiveParetoRankProfiles_card_eq_width_add_one_sub_gapCount :
    (correctedConcreteObservationPositiveAdditiveRankMinimizingParetoProfiles
          (z := z)
          obsFamily
          f
          coordinateWeight
          U
          language
          hTarget).card =
      correctedConcreteObservationPositiveAdditiveParetoProfileTradeoffWidth
            minimumCardinalityResult
            minimumAdditiveResult +
          1 -
        correctedConcreteObservationPositiveAdditiveParetoRankProfileOffsetGapCount
          minimumCardinalityResult
          minimumAdditiveResult := by

  have hFormula :=
    positiveAdditiveParetoRankProfiles_card_add_gapCount_eq_width_add_one
      minimumCardinalityResult
      minimumAdditiveResult

  omega

/-- The finite gap count is at most `width + 1`. -/
theorem
    positiveAdditiveParetoRankProfileOffsetGapCount_le_width_add_one :
    correctedConcreteObservationPositiveAdditiveParetoRankProfileOffsetGapCount
          minimumCardinalityResult
          minimumAdditiveResult <=
      correctedConcreteObservationPositiveAdditiveParetoProfileTradeoffWidth
          minimumCardinalityResult
          minimumAdditiveResult +
        1 := by

  have hFormula :=
    positiveAdditiveParetoRankProfiles_card_add_gapCount_eq_width_add_one
      minimumCardinalityResult
      minimumAdditiveResult

  omega

end ParetoRankProfileOffsetGapCountFormula


section FirstParetoRankProfileOffsetGap

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
  {hTarget :
    language ∈
      StartRootedCorrectedConcreteTargetClass
        (v := z)
        α
        (↥U → M)
        (selectedObservationProduct obsFamily U)
        f}
variable
  (minimumCardinalityResult :
    CorrectedConcreteObservationPositiveAdditiveParetoMinimumCardinalityProfileResult
      (z := z)
      obsFamily
      f
      coordinateWeight
      U
      language
      hTarget)
variable
  (minimumAdditiveResult :
    CorrectedConcreteObservationPositiveAdditiveParetoMinimumAdditiveProfileResult
      (z := z)
      obsFamily
      f
      coordinateWeight
      U
      language
      hTarget)
variable
  (hNotGapFree :
    ¬
      CorrectedConcreteObservationPositiveAdditiveParetoRankProfileOffsetsGapFree
        minimumCardinalityResult
        minimumAdditiveResult)

/-- Least missing normalized offset. -/
noncomputable def
    correctedConcreteObservationPositiveAdditiveParetoRankProfileFirstGap :
    Nat :=
  Nat.find
    ((not_positiveAdditiveParetoRankProfileOffsetsGapFree_iff_gaps_nonempty
      minimumCardinalityResult
      minimumAdditiveResult).mp
      hNotGapFree)

/-- The selected first gap belongs to the finite gap set. -/
theorem positiveAdditiveParetoRankProfileFirstGap_mem :
    correctedConcreteObservationPositiveAdditiveParetoRankProfileFirstGap
          minimumCardinalityResult
          minimumAdditiveResult
          hNotGapFree ∈
      correctedConcreteObservationPositiveAdditiveParetoRankProfileOffsetGaps
        minimumCardinalityResult
        minimumAdditiveResult := by

  exact
    Nat.find_spec
      ((not_positiveAdditiveParetoRankProfileOffsetsGapFree_iff_gaps_nonempty
        minimumCardinalityResult
        minimumAdditiveResult).mp
        hNotGapFree)

/-- The first gap is no greater than any other gap. -/
theorem positiveAdditiveParetoRankProfileFirstGap_le
    {offset : Nat}
    (hGap :
      offset ∈
        correctedConcreteObservationPositiveAdditiveParetoRankProfileOffsetGaps
          minimumCardinalityResult
          minimumAdditiveResult) :
    correctedConcreteObservationPositiveAdditiveParetoRankProfileFirstGap
          minimumCardinalityResult
          minimumAdditiveResult
          hNotGapFree <=
      offset := by

  apply
    Nat.find_min'
      ((not_positiveAdditiveParetoRankProfileOffsetsGapFree_iff_gaps_nonempty
        minimumCardinalityResult
        minimumAdditiveResult).mp
        hNotGapFree)

  exact
    hGap

/-- The first gap lies inside the width interval. -/
theorem positiveAdditiveParetoRankProfileFirstGap_le_width :
    correctedConcreteObservationPositiveAdditiveParetoRankProfileFirstGap
          minimumCardinalityResult
          minimumAdditiveResult
          hNotGapFree <=
      correctedConcreteObservationPositiveAdditiveParetoProfileTradeoffWidth
        minimumCardinalityResult
        minimumAdditiveResult := by

  exact
    ((mem_correctedConcreteObservationPositiveAdditiveParetoRankProfileOffsetGaps_iff
      minimumCardinalityResult
      minimumAdditiveResult).mp
      (positiveAdditiveParetoRankProfileFirstGap_mem
        minimumCardinalityResult
        minimumAdditiveResult
        hNotGapFree)).1

/-- The first gap itself is not realized. -/
theorem positiveAdditiveParetoRankProfileFirstGap_not_mem_offsets :
    correctedConcreteObservationPositiveAdditiveParetoRankProfileFirstGap
          minimumCardinalityResult
          minimumAdditiveResult
          hNotGapFree ∉
      correctedConcreteObservationPositiveAdditiveParetoRankProfileOffsets
        minimumCardinalityResult := by

  exact
    ((mem_correctedConcreteObservationPositiveAdditiveParetoRankProfileOffsetGaps_iff
      minimumCardinalityResult
      minimumAdditiveResult).mp
      (positiveAdditiveParetoRankProfileFirstGap_mem
        minimumCardinalityResult
        minimumAdditiveResult
        hNotGapFree)).2

/-- Every smaller offset is realized. -/
theorem positiveAdditiveParetoRankProfileOffset_mem_of_lt_firstGap
    {offset : Nat}
    (hOffsetLt :
      offset <
        correctedConcreteObservationPositiveAdditiveParetoRankProfileFirstGap
          minimumCardinalityResult
          minimumAdditiveResult
          hNotGapFree) :
    offset ∈
      correctedConcreteObservationPositiveAdditiveParetoRankProfileOffsets
        minimumCardinalityResult := by

  by_contra hOffsetMissing

  have hFirstGapLeWidth :=
    positiveAdditiveParetoRankProfileFirstGap_le_width
      minimumCardinalityResult
      minimumAdditiveResult
      hNotGapFree

  have hGap :
      offset ∈
        correctedConcreteObservationPositiveAdditiveParetoRankProfileOffsetGaps
          minimumCardinalityResult
          minimumAdditiveResult :=
    (mem_correctedConcreteObservationPositiveAdditiveParetoRankProfileOffsetGaps_iff
      minimumCardinalityResult
      minimumAdditiveResult).mpr
      ⟨by omega,
        hOffsetMissing⟩

  have hFirstLe :=
    positiveAdditiveParetoRankProfileFirstGap_le
      minimumCardinalityResult
      minimumAdditiveResult
      hNotGapFree
      hGap

  omega

/-- The affine profile located at the first gap is not a rank-minimizing
Pareto profile. -/
theorem positiveAdditiveParetoProfileOfFirstGap_not_mem_profiles :
    correctedConcreteObservationPositiveAdditiveParetoProfileOfOffset
          minimumCardinalityResult
          (correctedConcreteObservationPositiveAdditiveParetoRankProfileFirstGap
            minimumCardinalityResult
            minimumAdditiveResult
            hNotGapFree) ∉
      correctedConcreteObservationPositiveAdditiveRankMinimizingParetoProfiles
        (z := z)
        obsFamily
        f
        coordinateWeight
        U
        language
        hTarget := by

  intro hProfile

  have hOffsetMem :
      correctedConcreteObservationPositiveAdditiveParetoRankProfileFirstGap
            minimumCardinalityResult
            minimumAdditiveResult
            hNotGapFree ∈
        correctedConcreteObservationPositiveAdditiveParetoRankProfileOffsets
          minimumCardinalityResult := by

    apply
      (mem_correctedConcreteObservationPositiveAdditiveParetoRankProfileOffsets_iff
        minimumCardinalityResult).mpr

    exact
      ⟨correctedConcreteObservationPositiveAdditiveParetoProfileOfOffset
          minimumCardinalityResult
          (correctedConcreteObservationPositiveAdditiveParetoRankProfileFirstGap
            minimumCardinalityResult
            minimumAdditiveResult
            hNotGapFree),
        hProfile,
        positiveAdditiveParetoProfileOfOffset_offset_eq
          minimumCardinalityResult
          (correctedConcreteObservationPositiveAdditiveParetoRankProfileFirstGap
            minimumCardinalityResult
            minimumAdditiveResult
            hNotGapFree)⟩

  exact
    positiveAdditiveParetoRankProfileFirstGap_not_mem_offsets
      minimumCardinalityResult
      minimumAdditiveResult
      hNotGapFree
      hOffsetMem

end FirstParetoRankProfileOffsetGap


section CertifiedSelectionBeforeFirstGap

variable {α : Type u}
variable {ι : Type v}
variable {M : Type w}
variable [Fintype M]
variable [DecidableEq α]
variable [DecidableEq ι]
variable [DecidableEq M]
variable [Monoid M]
variable (hα : Nonempty α)
variable {obsFamily : ι → α → M}
variable {f : Nat}
variable {coordinateWeight : ι → Nat}
variable {U : Finset ι}
variable {language : Set (Word α)}
variable
  {hTarget :
    language ∈
      StartRootedCorrectedConcreteTargetClass
        (v := z)
        α
        (↥U → M)
        (selectedObservationProduct obsFamily U)
        f}
variable
  (minimumCardinalityResult :
    CorrectedConcreteObservationPositiveAdditiveParetoMinimumCardinalityProfileResult
      (z := z)
      obsFamily
      f
      coordinateWeight
      U
      language
      hTarget)
variable
  (minimumAdditiveResult :
    CorrectedConcreteObservationPositiveAdditiveParetoMinimumAdditiveProfileResult
      (z := z)
      obsFamily
      f
      coordinateWeight
      U
      language
      hTarget)
variable
  (hNotGapFree :
    ¬
      CorrectedConcreteObservationPositiveAdditiveParetoRankProfileOffsetsGapFree
        minimumCardinalityResult
        minimumAdditiveResult)

/-- Every offset before the first gap has an actual Pareto-optimal,
exact-rank, irredundant selected product with a certified learner. -/
theorem
    positiveAdditiveParetoRankProfileOffset_beforeFirstGap_exists_certifiedSelection
    {offset : Nat}
    (hOffsetLt :
      offset <
        correctedConcreteObservationPositiveAdditiveParetoRankProfileFirstGap
          minimumCardinalityResult
          minimumAdditiveResult
          hNotGapFree) :
    ∃
      (hOffset :
        offset ∈
          correctedConcreteObservationPositiveAdditiveParetoRankProfileOffsets
            minimumCardinalityResult)
      (result :
        CorrectedConcreteObservationPositiveAdditiveParetoRankProfileOffsetSelectionResult
          (z := z)
          obsFamily
          f
          coordinateWeight
          U
          language
          hTarget
          minimumCardinalityResult
          minimumAdditiveResult
          offset
          hOffset),
      result.selected.card =
          minimumCardinalityResult.profile.1 + offset ∧
        correctedConcreteObservationSelectionAdditiveCost
            coordinateWeight result.selected =
          minimumCardinalityResult.profile.2 - offset ∧
        correctedConcreteObservationSelectionPositiveAdditiveCost
            coordinateWeight result.selected =
          ambientTargetObservationSelectionPositiveAdditiveMinimumCost
            (z := z)
            obsFamily
            f
            coordinateWeight
            U
            hTarget ∧
        CorrectedConcreteObservationSelectionParetoOptimal
          (z := z)
          obsFamily
          f
          (correctedConcreteObservationSelectionAdditiveCost
            coordinateWeight)
          U
          language
          result.selected ∧
        CorrectedConcreteObservationSelectionIrredundant
          (z := z)
          α
          ι
          M
          obsFamily
          f
          language
          result.selected ∧
        IdentifiesLanguageFromPositiveData
          (correctedConcreteCertifiedWorkingGrammarHypLanguage
            (selectedObservationProduct obsFamily result.selected)
            f)
          (correctedConcreteCertifiedWorkingGrammarLearner
            hα
            (selectedObservationProduct obsFamily result.selected)
            f)
          language := by

  let hOffset :=
    positiveAdditiveParetoRankProfileOffset_mem_of_lt_firstGap
      minimumCardinalityResult
      minimumAdditiveResult
      hNotGapFree
      hOffsetLt

  let result :=
    correctedConcreteObservationPositiveAdditiveParetoRankProfileOffsetSelectionResult
      (z := z)
      obsFamily
      f
      coordinateWeight
      U
      language
      hTarget
      minimumCardinalityResult
      minimumAdditiveResult
      offset
      hOffset

  have hCertified :=
    CorrectedConcreteObservationPositiveAdditiveParetoRankProfileOffsetSelectionResult.certified_package
      (z := z)
      hα
      result

  exact
    ⟨hOffset,
      result,
      result.selected_card_eq,
      result.selected_additiveCost_eq,
      result.selected_cost_eq_rank,
      result.selected_pareto,
      result.selected_irredundant,
      hCertified.1⟩

end CertifiedSelectionBeforeFirstGap


section ParetoRankProfileOffsetGapsFinalPackage

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

/-- Final finite gap-set, exact defect, first-gap, realized-prefix, and
certified-prefix-selection package. -/
theorem
    correctedConcreteCertifiedWorkingGrammar_observationSelectionParetoRankProfileOffsetGaps_package :
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
      let minimumCardinalityResult :=
        correctedConcreteObservationPositiveAdditiveParetoMinimumCardinalityProfileResult
          (z := z)
          obsFamily
          f
          coordinateWeight
          U
          language
          hTarget
      let minimumAdditiveResult :=
        correctedConcreteObservationPositiveAdditiveParetoMinimumAdditiveProfileResult
          (z := z)
          obsFamily
          f
          coordinateWeight
          U
          language
          hTarget
      let gaps :=
        correctedConcreteObservationPositiveAdditiveParetoRankProfileOffsetGaps
          minimumCardinalityResult
          minimumAdditiveResult
      (CorrectedConcreteObservationPositiveAdditiveParetoRankProfileOffsetsGapFree
            minimumCardinalityResult
            minimumAdditiveResult ↔
          gaps = ∅) ∧
        (correctedConcreteObservationPositiveAdditiveRankMinimizingParetoProfiles
              (z := z)
              obsFamily
              f
              coordinateWeight
              U
              language
              hTarget).card +
            gaps.card =
          correctedConcreteObservationPositiveAdditiveParetoProfileTradeoffWidth
              minimumCardinalityResult
              minimumAdditiveResult +
            1 ∧
        (∀ hNotGapFree :
          ¬
            CorrectedConcreteObservationPositiveAdditiveParetoRankProfileOffsetsGapFree
              minimumCardinalityResult
              minimumAdditiveResult,
          let firstGap :=
            correctedConcreteObservationPositiveAdditiveParetoRankProfileFirstGap
              minimumCardinalityResult
              minimumAdditiveResult
              hNotGapFree
          firstGap ∈ gaps ∧
            firstGap <=
              correctedConcreteObservationPositiveAdditiveParetoProfileTradeoffWidth
                minimumCardinalityResult
                minimumAdditiveResult ∧
            firstGap ∉
              correctedConcreteObservationPositiveAdditiveParetoRankProfileOffsets
                minimumCardinalityResult ∧
            (∀ offset : Nat,
              offset < firstGap →
                offset ∈
                  correctedConcreteObservationPositiveAdditiveParetoRankProfileOffsets
                    minimumCardinalityResult) ∧
            correctedConcreteObservationPositiveAdditiveParetoProfileOfOffset
                  minimumCardinalityResult
                  firstGap ∉
              correctedConcreteObservationPositiveAdditiveRankMinimizingParetoProfiles
                (z := z)
                obsFamily
                f
                coordinateWeight
                U
                language
                hTarget) := by

  intro language hTarget

  let minimumCardinalityResult :=
    correctedConcreteObservationPositiveAdditiveParetoMinimumCardinalityProfileResult
      (z := z)
      obsFamily
      f
      coordinateWeight
      U
      language
      hTarget

  let minimumAdditiveResult :=
    correctedConcreteObservationPositiveAdditiveParetoMinimumAdditiveProfileResult
      (z := z)
      obsFamily
      f
      coordinateWeight
      U
      language
      hTarget

  let gaps :=
    correctedConcreteObservationPositiveAdditiveParetoRankProfileOffsetGaps
      minimumCardinalityResult
      minimumAdditiveResult

  refine
    ⟨positiveAdditiveParetoRankProfileOffsetsGapFree_iff_gaps_eq_empty
        minimumCardinalityResult
        minimumAdditiveResult,
      ?_,
      ?_⟩

  · simpa [
      correctedConcreteObservationPositiveAdditiveParetoRankProfileOffsetGapCount
    ] using
      positiveAdditiveParetoRankProfiles_card_add_gapCount_eq_width_add_one
        minimumCardinalityResult
        minimumAdditiveResult

  · intro hNotGapFree

    let firstGap :=
      correctedConcreteObservationPositiveAdditiveParetoRankProfileFirstGap
        minimumCardinalityResult
        minimumAdditiveResult
        hNotGapFree

    exact
      ⟨positiveAdditiveParetoRankProfileFirstGap_mem
          minimumCardinalityResult
          minimumAdditiveResult
          hNotGapFree,
        positiveAdditiveParetoRankProfileFirstGap_le_width
          minimumCardinalityResult
          minimumAdditiveResult
          hNotGapFree,
        positiveAdditiveParetoRankProfileFirstGap_not_mem_offsets
          minimumCardinalityResult
          minimumAdditiveResult
          hNotGapFree,
        fun offset hOffsetLt =>
          positiveAdditiveParetoRankProfileOffset_mem_of_lt_firstGap
            minimumCardinalityResult
            minimumAdditiveResult
            hNotGapFree
            hOffsetLt,
        positiveAdditiveParetoProfileOfFirstGap_not_mem_profiles
          minimumCardinalityResult
          minimumAdditiveResult
          hNotGapFree⟩

end ParetoRankProfileOffsetGapsFinalPackage

end MCFG
