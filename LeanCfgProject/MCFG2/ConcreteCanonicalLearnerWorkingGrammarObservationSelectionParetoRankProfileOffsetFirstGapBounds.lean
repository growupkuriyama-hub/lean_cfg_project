/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG2.ConcreteCanonicalLearnerWorkingGrammarObservationSelectionParetoRankProfileOffsetGaps

/-!
# ConcreteCanonicalLearnerWorkingGrammarObservationSelectionParetoRankProfileOffsetFirstGapBounds.lean

The preceding file constructs the finite missing-offset set and, in the
non-gap-free case, selects its least element.

This file proves that the first gap is necessarily a strict interior point and
derives quantitative lower and upper bounds from its position.

## The first gap is interior

Offset zero is always realized by the minimum-cardinality endpoint.
Offset `width` is always realized by the minimum-additive endpoint.

Therefore, if a first gap `g` exists, then

```text
0 < g < width.
```

Consequently,

```text
2 ≤ width ≤ positiveAdditiveRank.
```

In particular, ranks zero and one cannot contain gaps, consistently with the
previous bottom-rank theorems.

## Certified realized prefix

Every offset strictly below `g` is realized.  Thus

```text
range g ⊆ realizedOffsets.
```

The endpoint `width` is also realized and lies outside `range g`.  Hence the
finite witness family

```text
insert width (range g)
```

contains exactly `g + 1` distinct realized offsets.

Using the finite offset/profile bijection:

```text
g + 1 ≤ number of rank-minimizing Pareto profiles.
```

## Gap-count bounds

Combining the preceding lower bound with the exact defect formula

```text
profiles.card + gaps.card = width + 1
```

gives

```text
1 ≤ gapCount ≤ width - g.
```

Thus the first gap position controls both the amount of certified tradeoff
already available before failure and the maximum possible number of missing
profiles after that point.

## Prefix selectors

Every offset `d < g` has an actual offset-indexed selected interface with

```text
cardinality = c_min + d,
additiveCost = a_max - d.
```

It is Pareto optimal, exact-rank, irredundant, and carries a certified learner
identifying the target.

The maximum endpoint at offset `width` has the same properties.

No target grammar is supplied to any learner.
No `sorry`, `admit`, or `axiom` is used.
-/

namespace MCFG

universe u v w z


section FirstGapInteriorBounds

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

/-- The first missing offset is strictly positive because offset zero is
always realized. -/
theorem positiveAdditiveParetoRankProfileFirstGap_pos :
    0 <
      correctedConcreteObservationPositiveAdditiveParetoRankProfileFirstGap
        minimumCardinalityResult
        minimumAdditiveResult
        hNotGapFree := by

  have hFirstMissing :=
    positiveAdditiveParetoRankProfileFirstGap_not_mem_offsets
      minimumCardinalityResult
      minimumAdditiveResult
      hNotGapFree

  have hZeroMem :=
    zero_mem_correctedConcreteObservationPositiveAdditiveParetoRankProfileOffsets
      minimumCardinalityResult

  by_contra hNotPositive

  have hFirstZero :
      correctedConcreteObservationPositiveAdditiveParetoRankProfileFirstGap
          minimumCardinalityResult
          minimumAdditiveResult
          hNotGapFree =
        0 := by
    omega

  exact
    hFirstMissing
      (by
        simpa [hFirstZero] using
          hZeroMem)

/-- The first missing offset is strictly below the tradeoff width because the
maximum endpoint offset is always realized. -/
theorem positiveAdditiveParetoRankProfileFirstGap_lt_width :
    correctedConcreteObservationPositiveAdditiveParetoRankProfileFirstGap
          minimumCardinalityResult
          minimumAdditiveResult
          hNotGapFree <
      correctedConcreteObservationPositiveAdditiveParetoProfileTradeoffWidth
        minimumCardinalityResult
        minimumAdditiveResult := by

  have hFirstLe :=
    positiveAdditiveParetoRankProfileFirstGap_le_width
      minimumCardinalityResult
      minimumAdditiveResult
      hNotGapFree

  have hFirstMissing :=
    positiveAdditiveParetoRankProfileFirstGap_not_mem_offsets
      minimumCardinalityResult
      minimumAdditiveResult
      hNotGapFree

  have hWidthMem :=
    width_mem_correctedConcreteObservationPositiveAdditiveParetoRankProfileOffsets
      minimumCardinalityResult
      minimumAdditiveResult

  by_contra hNotStrict

  have hFirstEq :
      correctedConcreteObservationPositiveAdditiveParetoRankProfileFirstGap
          minimumCardinalityResult
          minimumAdditiveResult
          hNotGapFree =
        correctedConcreteObservationPositiveAdditiveParetoProfileTradeoffWidth
          minimumCardinalityResult
          minimumAdditiveResult := by
    omega

  exact
    hFirstMissing
      (by
        simpa [hFirstEq] using
          hWidthMem)

/-- Non-gap-freeness forces tradeoff width at least two. -/
theorem two_le_positiveAdditiveParetoProfileTradeoffWidth :
    2 <=
      correctedConcreteObservationPositiveAdditiveParetoProfileTradeoffWidth
        minimumCardinalityResult
        minimumAdditiveResult := by

  have hFirstPos :=
    positiveAdditiveParetoRankProfileFirstGap_pos
      minimumCardinalityResult
      minimumAdditiveResult
      hNotGapFree

  have hFirstLt :=
    positiveAdditiveParetoRankProfileFirstGap_lt_width
      minimumCardinalityResult
      minimumAdditiveResult
      hNotGapFree

  omega

/-- Non-gap-freeness forces the positive additive observation-selection rank
to be at least two. -/
theorem two_le_ambientTargetPositiveAdditiveRank_of_not_gapFree :
    2 <=
      ambientTargetObservationSelectionPositiveAdditiveMinimumCost
        (z := z)
        obsFamily
        f
        coordinateWeight
        U
        hTarget := by

  calc
    2 <=
      correctedConcreteObservationPositiveAdditiveParetoProfileTradeoffWidth
        minimumCardinalityResult
        minimumAdditiveResult :=
          two_le_positiveAdditiveParetoProfileTradeoffWidth
            minimumCardinalityResult
            minimumAdditiveResult
            hNotGapFree

    _ <=
      ambientTargetObservationSelectionPositiveAdditiveMinimumCost
        (z := z)
        obsFamily
        f
        coordinateWeight
        U
        hTarget :=
          positiveAdditiveParetoProfile_tradeoffWidth_le_rank
            minimumCardinalityResult
            minimumAdditiveResult

end FirstGapInteriorBounds


section FirstGapRealizedPrefixDefinition

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

/-- Complete initial interval of realized offsets before the first gap. -/
def correctedConcreteObservationPositiveAdditiveParetoRankProfileFirstGapPrefix
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
        hTarget)
    (hNotGapFree :
      ¬
        CorrectedConcreteObservationPositiveAdditiveParetoRankProfileOffsetsGapFree
          minimumCardinalityResult
          minimumAdditiveResult) :
    Finset Nat :=
  Finset.range
    (correctedConcreteObservationPositiveAdditiveParetoRankProfileFirstGap
      minimumCardinalityResult
      minimumAdditiveResult
      hNotGapFree)

/-- Certified initial realized prefix together with the always-realized maximum
endpoint offset. -/
def
    correctedConcreteObservationPositiveAdditiveParetoRankProfileFirstGapPrefixWithMaximum
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
        hTarget)
    (hNotGapFree :
      ¬
        CorrectedConcreteObservationPositiveAdditiveParetoRankProfileOffsetsGapFree
          minimumCardinalityResult
          minimumAdditiveResult) :
    Finset Nat :=
  insert
    (correctedConcreteObservationPositiveAdditiveParetoProfileTradeoffWidth
      minimumCardinalityResult
      minimumAdditiveResult)
    (correctedConcreteObservationPositiveAdditiveParetoRankProfileFirstGapPrefix
      minimumCardinalityResult
      minimumAdditiveResult
      hNotGapFree)

end FirstGapRealizedPrefixDefinition


section FirstGapRealizedPrefixProperties

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

/-- Prefix membership is strict comparison with the first gap. -/
theorem
    mem_correctedConcreteObservationPositiveAdditiveParetoRankProfileFirstGapPrefix_iff
    {offset : Nat} :
    offset ∈
        correctedConcreteObservationPositiveAdditiveParetoRankProfileFirstGapPrefix
          minimumCardinalityResult
          minimumAdditiveResult
          hNotGapFree ↔
      offset <
        correctedConcreteObservationPositiveAdditiveParetoRankProfileFirstGap
          minimumCardinalityResult
          minimumAdditiveResult
          hNotGapFree := by

  unfold
    correctedConcreteObservationPositiveAdditiveParetoRankProfileFirstGapPrefix

  exact
    Finset.mem_range

/-- Every offset in the first-gap prefix is realized. -/
theorem
    correctedConcreteObservationPositiveAdditiveParetoRankProfileFirstGapPrefix_subset_offsets :
    correctedConcreteObservationPositiveAdditiveParetoRankProfileFirstGapPrefix
        minimumCardinalityResult
        minimumAdditiveResult
        hNotGapFree ⊆
      correctedConcreteObservationPositiveAdditiveParetoRankProfileOffsets
        minimumCardinalityResult := by

  intro offset hOffset

  exact
    positiveAdditiveParetoRankProfileOffset_mem_of_lt_firstGap
      minimumCardinalityResult
      minimumAdditiveResult
      hNotGapFree
      ((mem_correctedConcreteObservationPositiveAdditiveParetoRankProfileFirstGapPrefix_iff
        minimumCardinalityResult
        minimumAdditiveResult
        hNotGapFree).mp
        hOffset)

/-- The realized prefix has exactly `firstGap` members. -/
theorem
    correctedConcreteObservationPositiveAdditiveParetoRankProfileFirstGapPrefix_card :
    (correctedConcreteObservationPositiveAdditiveParetoRankProfileFirstGapPrefix
      minimumCardinalityResult
      minimumAdditiveResult
      hNotGapFree).card =
      correctedConcreteObservationPositiveAdditiveParetoRankProfileFirstGap
        minimumCardinalityResult
        minimumAdditiveResult
        hNotGapFree := by

  unfold
    correctedConcreteObservationPositiveAdditiveParetoRankProfileFirstGapPrefix

  simp

/-- The first gap itself is outside the realized prefix. -/
theorem
    positiveAdditiveParetoRankProfileFirstGap_not_mem_prefix :
    correctedConcreteObservationPositiveAdditiveParetoRankProfileFirstGap
          minimumCardinalityResult
          minimumAdditiveResult
          hNotGapFree ∉
      correctedConcreteObservationPositiveAdditiveParetoRankProfileFirstGapPrefix
        minimumCardinalityResult
        minimumAdditiveResult
        hNotGapFree := by

  unfold
    correctedConcreteObservationPositiveAdditiveParetoRankProfileFirstGapPrefix

  simp

/-- The maximum endpoint offset is outside the strict prefix. -/
theorem
    positiveAdditiveParetoProfileTradeoffWidth_not_mem_firstGapPrefix :
    correctedConcreteObservationPositiveAdditiveParetoProfileTradeoffWidth
          minimumCardinalityResult
          minimumAdditiveResult ∉
      correctedConcreteObservationPositiveAdditiveParetoRankProfileFirstGapPrefix
        minimumCardinalityResult
        minimumAdditiveResult
        hNotGapFree := by

  unfold
    correctedConcreteObservationPositiveAdditiveParetoRankProfileFirstGapPrefix

  simp only [Finset.mem_range]

  exact
    Nat.not_lt_of_ge
      (Nat.le_of_lt
        (positiveAdditiveParetoRankProfileFirstGap_lt_width
          minimumCardinalityResult
          minimumAdditiveResult
          hNotGapFree))

/-- Prefix plus maximum endpoint consists entirely of realized offsets. -/
theorem
    correctedConcreteObservationPositiveAdditiveParetoRankProfileFirstGapPrefixWithMaximum_subset_offsets :
    correctedConcreteObservationPositiveAdditiveParetoRankProfileFirstGapPrefixWithMaximum
        minimumCardinalityResult
        minimumAdditiveResult
        hNotGapFree ⊆
      correctedConcreteObservationPositiveAdditiveParetoRankProfileOffsets
        minimumCardinalityResult := by

  intro offset hOffset

  rcases Finset.mem_insert.mp hOffset with
    hMaximum | hPrefix

  · subst offset

    exact
      width_mem_correctedConcreteObservationPositiveAdditiveParetoRankProfileOffsets
        minimumCardinalityResult
        minimumAdditiveResult

  · exact
      correctedConcreteObservationPositiveAdditiveParetoRankProfileFirstGapPrefix_subset_offsets
        minimumCardinalityResult
        minimumAdditiveResult
        hNotGapFree
        hPrefix

/-- Prefix plus maximum endpoint has exactly `firstGap + 1` members. -/
theorem
    correctedConcreteObservationPositiveAdditiveParetoRankProfileFirstGapPrefixWithMaximum_card :
    (correctedConcreteObservationPositiveAdditiveParetoRankProfileFirstGapPrefixWithMaximum
      minimumCardinalityResult
      minimumAdditiveResult
      hNotGapFree).card =
      correctedConcreteObservationPositiveAdditiveParetoRankProfileFirstGap
          minimumCardinalityResult
          minimumAdditiveResult
          hNotGapFree +
        1 := by

  unfold
    correctedConcreteObservationPositiveAdditiveParetoRankProfileFirstGapPrefixWithMaximum

  rw [
    Finset.card_insert_of_not_mem
      (positiveAdditiveParetoProfileTradeoffWidth_not_mem_firstGapPrefix
        minimumCardinalityResult
        minimumAdditiveResult
        hNotGapFree),
    correctedConcreteObservationPositiveAdditiveParetoRankProfileFirstGapPrefix_card
      minimumCardinalityResult
      minimumAdditiveResult
      hNotGapFree
  ]

  omega

end FirstGapRealizedPrefixProperties


section FirstGapQuantitativeBounds

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

/-- The number of rank-minimizing Pareto profiles is at least
`firstGap + 1`. -/
theorem firstGap_add_one_le_positiveAdditiveParetoRankProfiles_card :
    correctedConcreteObservationPositiveAdditiveParetoRankProfileFirstGap
          minimumCardinalityResult
          minimumAdditiveResult
          hNotGapFree +
        1 <=
      (correctedConcreteObservationPositiveAdditiveRankMinimizingParetoProfiles
        (z := z)
        obsFamily
        f
        coordinateWeight
        U
        language
        hTarget).card := by

  have hWitnessCardLe :
      (correctedConcreteObservationPositiveAdditiveParetoRankProfileFirstGapPrefixWithMaximum
          minimumCardinalityResult
          minimumAdditiveResult
          hNotGapFree).card <=
        (correctedConcreteObservationPositiveAdditiveParetoRankProfileOffsets
          minimumCardinalityResult).card :=
    Finset.card_le_card
      (correctedConcreteObservationPositiveAdditiveParetoRankProfileFirstGapPrefixWithMaximum_subset_offsets
        minimumCardinalityResult
        minimumAdditiveResult
        hNotGapFree)

  have hCardEq :=
    correctedConcreteObservationPositiveAdditiveParetoRankProfileOffsets_card_eq_profiles_card
      minimumCardinalityResult
      minimumAdditiveResult

  rw [
    correctedConcreteObservationPositiveAdditiveParetoRankProfileFirstGapPrefixWithMaximum_card
      minimumCardinalityResult
      minimumAdditiveResult
      hNotGapFree,
    hCardEq
  ] at hWitnessCardLe

  exact
    hWitnessCardLe

/-- Non-gap-freeness gives at least one gap. -/
theorem one_le_positiveAdditiveParetoRankProfileOffsetGapCount :
    1 <=
      correctedConcreteObservationPositiveAdditiveParetoRankProfileOffsetGapCount
        minimumCardinalityResult
        minimumAdditiveResult := by

  have hPositive :=
    (not_positiveAdditiveParetoRankProfileOffsetsGapFree_iff_gapCount_pos
      minimumCardinalityResult
      minimumAdditiveResult).mp
      hNotGapFree

  omega

/-- The number of gaps is bounded by the remaining distance from the first gap
to the maximum endpoint. -/
theorem
    positiveAdditiveParetoRankProfileOffsetGapCount_le_width_sub_firstGap :
    correctedConcreteObservationPositiveAdditiveParetoRankProfileOffsetGapCount
          minimumCardinalityResult
          minimumAdditiveResult <=
      correctedConcreteObservationPositiveAdditiveParetoProfileTradeoffWidth
            minimumCardinalityResult
            minimumAdditiveResult -
        correctedConcreteObservationPositiveAdditiveParetoRankProfileFirstGap
          minimumCardinalityResult
          minimumAdditiveResult
          hNotGapFree := by

  have hDefect :=
    positiveAdditiveParetoRankProfiles_card_add_gapCount_eq_width_add_one
      minimumCardinalityResult
      minimumAdditiveResult

  have hProfilesLower :=
    firstGap_add_one_le_positiveAdditiveParetoRankProfiles_card
      minimumCardinalityResult
      minimumAdditiveResult
      hNotGapFree

  have hFirstLe :=
    Nat.le_of_lt
      (positiveAdditiveParetoRankProfileFirstGap_lt_width
        minimumCardinalityResult
        minimumAdditiveResult
        hNotGapFree)

  omega

/-- Combined exact first-gap quantitative interval. -/
theorem positiveAdditiveParetoRankProfileFirstGap_quantitative_package :
    0 <
        correctedConcreteObservationPositiveAdditiveParetoRankProfileFirstGap
          minimumCardinalityResult
          minimumAdditiveResult
          hNotGapFree ∧
      correctedConcreteObservationPositiveAdditiveParetoRankProfileFirstGap
          minimumCardinalityResult
          minimumAdditiveResult
          hNotGapFree <
        correctedConcreteObservationPositiveAdditiveParetoProfileTradeoffWidth
          minimumCardinalityResult
          minimumAdditiveResult ∧
      correctedConcreteObservationPositiveAdditiveParetoRankProfileFirstGap
            minimumCardinalityResult
            minimumAdditiveResult
            hNotGapFree +
          1 <=
        (correctedConcreteObservationPositiveAdditiveRankMinimizingParetoProfiles
          (z := z)
          obsFamily
          f
          coordinateWeight
          U
          language
          hTarget).card ∧
      1 <=
        correctedConcreteObservationPositiveAdditiveParetoRankProfileOffsetGapCount
          minimumCardinalityResult
          minimumAdditiveResult ∧
      correctedConcreteObservationPositiveAdditiveParetoRankProfileOffsetGapCount
          minimumCardinalityResult
          minimumAdditiveResult <=
        correctedConcreteObservationPositiveAdditiveParetoProfileTradeoffWidth
              minimumCardinalityResult
              minimumAdditiveResult -
          correctedConcreteObservationPositiveAdditiveParetoRankProfileFirstGap
            minimumCardinalityResult
            minimumAdditiveResult
            hNotGapFree := by

  exact
    ⟨positiveAdditiveParetoRankProfileFirstGap_pos
        minimumCardinalityResult
        minimumAdditiveResult
        hNotGapFree,
      positiveAdditiveParetoRankProfileFirstGap_lt_width
        minimumCardinalityResult
        minimumAdditiveResult
        hNotGapFree,
      firstGap_add_one_le_positiveAdditiveParetoRankProfiles_card
        minimumCardinalityResult
        minimumAdditiveResult
        hNotGapFree,
      one_le_positiveAdditiveParetoRankProfileOffsetGapCount
        minimumCardinalityResult
        minimumAdditiveResult
        hNotGapFree,
      positiveAdditiveParetoRankProfileOffsetGapCount_le_width_sub_firstGap
        minimumCardinalityResult
        minimumAdditiveResult
        hNotGapFree⟩

end FirstGapQuantitativeBounds


section FirstGapPrefixCertifiedSelectors

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

/-- Every offset in the strict first-gap prefix has an actual certified
selected interface. -/
theorem
    positiveAdditiveParetoRankProfileFirstGapPrefix_exists_certifiedSelection
    {offset : Nat}
    (hOffset :
      offset ∈
        correctedConcreteObservationPositiveAdditiveParetoRankProfileFirstGapPrefix
          minimumCardinalityResult
          minimumAdditiveResult
          hNotGapFree) :
    ∃
      (hRealized :
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
          hRealized),
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

  have hOffsetLt :=
    (mem_correctedConcreteObservationPositiveAdditiveParetoRankProfileFirstGapPrefix_iff
      minimumCardinalityResult
      minimumAdditiveResult
      hNotGapFree).mp
      hOffset

  exact
    positiveAdditiveParetoRankProfileOffset_beforeFirstGap_exists_certifiedSelection
      (z := z)
      hα
      minimumCardinalityResult
      minimumAdditiveResult
      hNotGapFree
      hOffsetLt

/-- The always-realized maximum endpoint also has an actual certified selected
interface. -/
theorem
    positiveAdditiveParetoRankProfileMaximumOffset_exists_certifiedSelection :
    let width :=
      correctedConcreteObservationPositiveAdditiveParetoProfileTradeoffWidth
        minimumCardinalityResult
        minimumAdditiveResult
    let hWidth :
        width ∈
          correctedConcreteObservationPositiveAdditiveParetoRankProfileOffsets
            minimumCardinalityResult :=
      width_mem_correctedConcreteObservationPositiveAdditiveParetoRankProfileOffsets
        minimumCardinalityResult
        minimumAdditiveResult
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
        width
        hWidth
    (result.selected.card,
        correctedConcreteObservationSelectionAdditiveCost
          coordinateWeight result.selected) =
      minimumAdditiveResult.profile ∧
      CorrectedConcreteObservationSelectionParetoOptimal
        (z := z)
        obsFamily
        f
        (correctedConcreteObservationSelectionAdditiveCost
          coordinateWeight)
        U
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

  let width :=
    correctedConcreteObservationPositiveAdditiveParetoProfileTradeoffWidth
      minimumCardinalityResult
      minimumAdditiveResult

  let hWidth :
      width ∈
        correctedConcreteObservationPositiveAdditiveParetoRankProfileOffsets
          minimumCardinalityResult :=
    width_mem_correctedConcreteObservationPositiveAdditiveParetoRankProfileOffsets
      minimumCardinalityResult
      minimumAdditiveResult

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
      width
      hWidth

  have hCertified :=
    CorrectedConcreteObservationPositiveAdditiveParetoRankProfileOffsetSelectionResult.certified_package
      (z := z)
      hα
      result

  exact
    ⟨result.selected_profile_eq_minimumAdditive_of_offset_width
        rfl,
      result.selected_pareto,
      hCertified.1⟩

end FirstGapPrefixCertifiedSelectors


section FirstGapBoundsFinalPackage

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

/-- Final strict-interior, rank lower bound, certified-prefix, profile-count,
and gap-count package for the first missing Pareto-profile offset. -/
theorem
    correctedConcreteCertifiedWorkingGrammar_observationSelectionParetoRankProfileOffsetFirstGapBounds_package :
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
      ∀ hNotGapFree :
        ¬
          CorrectedConcreteObservationPositiveAdditiveParetoRankProfileOffsetsGapFree
            minimumCardinalityResult
            minimumAdditiveResult,
        let firstGap :=
          correctedConcreteObservationPositiveAdditiveParetoRankProfileFirstGap
            minimumCardinalityResult
            minimumAdditiveResult
            hNotGapFree
        let width :=
          correctedConcreteObservationPositiveAdditiveParetoProfileTradeoffWidth
            minimumCardinalityResult
            minimumAdditiveResult
        0 < firstGap ∧
          firstGap < width ∧
          2 <= width ∧
          2 <=
            ambientTargetObservationSelectionPositiveAdditiveMinimumCost
              (z := z)
              obsFamily
              f
              coordinateWeight
              U
              hTarget ∧
          firstGap + 1 <=
            (correctedConcreteObservationPositiveAdditiveRankMinimizingParetoProfiles
              (z := z)
              obsFamily
              f
              coordinateWeight
              U
              language
              hTarget).card ∧
          1 <=
            correctedConcreteObservationPositiveAdditiveParetoRankProfileOffsetGapCount
              minimumCardinalityResult
              minimumAdditiveResult ∧
          correctedConcreteObservationPositiveAdditiveParetoRankProfileOffsetGapCount
              minimumCardinalityResult
              minimumAdditiveResult <=
            width - firstGap ∧
          correctedConcreteObservationPositiveAdditiveParetoRankProfileFirstGapPrefix
              minimumCardinalityResult
              minimumAdditiveResult
              hNotGapFree ⊆
            correctedConcreteObservationPositiveAdditiveParetoRankProfileOffsets
              minimumCardinalityResult := by

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

  intro hNotGapFree

  let firstGap :=
    correctedConcreteObservationPositiveAdditiveParetoRankProfileFirstGap
      minimumCardinalityResult
      minimumAdditiveResult
      hNotGapFree

  let width :=
    correctedConcreteObservationPositiveAdditiveParetoProfileTradeoffWidth
      minimumCardinalityResult
      minimumAdditiveResult

  exact
    ⟨positiveAdditiveParetoRankProfileFirstGap_pos
        minimumCardinalityResult
        minimumAdditiveResult
        hNotGapFree,
      positiveAdditiveParetoRankProfileFirstGap_lt_width
        minimumCardinalityResult
        minimumAdditiveResult
        hNotGapFree,
      two_le_positiveAdditiveParetoProfileTradeoffWidth
        minimumCardinalityResult
        minimumAdditiveResult
        hNotGapFree,
      two_le_ambientTargetPositiveAdditiveRank_of_not_gapFree
        minimumCardinalityResult
        minimumAdditiveResult
        hNotGapFree,
      firstGap_add_one_le_positiveAdditiveParetoRankProfiles_card
        minimumCardinalityResult
        minimumAdditiveResult
        hNotGapFree,
      one_le_positiveAdditiveParetoRankProfileOffsetGapCount
        minimumCardinalityResult
        minimumAdditiveResult
        hNotGapFree,
      positiveAdditiveParetoRankProfileOffsetGapCount_le_width_sub_firstGap
        minimumCardinalityResult
        minimumAdditiveResult
        hNotGapFree,
      correctedConcreteObservationPositiveAdditiveParetoRankProfileFirstGapPrefix_subset_offsets
        minimumCardinalityResult
        minimumAdditiveResult
        hNotGapFree⟩

end FirstGapBoundsFinalPackage

end MCFG
