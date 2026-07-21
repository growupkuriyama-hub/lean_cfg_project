/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG2.ConcreteCanonicalLearnerWorkingGrammarObservationSelectionParetoRankProfileOffsetBijection

/-!
# ConcreteCanonicalLearnerWorkingGrammarObservationSelectionParetoRankProfileOffsetGapFree.lean

The preceding file constructs an explicit finite equivalence between realized
normalized offsets and positive-additive-rank-minimizing Pareto profiles.

This file isolates the important special case in which the realized offset set
has no gaps.

## Gap-free offset spectrum

The offset spectrum is gap-free when every natural offset between zero and the
tradeoff width is realized:

```text
∀ d ≤ width, d ∈ offsets.
```

Equivalently,

```text
offsets = range (width + 1).
```

In that case the rank-minimizing Pareto profile set is exactly the complete
finite tradeoff interval

```text
{(c_min + d, a_max - d) | d = 0,...,width}.
```

No density statement is asserted without this explicit gap-free premise.

## Exact cardinalities

Under gap-freeness,

```text
offsets.card = width + 1
profiles.card = width + 1.
```

Conversely, because the realized offsets are always contained in
`range (width + 1)`, attaining cardinality `width + 1` forces gap-freeness.

Thus the finite profile-count upper bound is exact precisely when every
intermediate tradeoff offset is realized.

## One-step exchange

For every `d < width`, both `d` and `d+1` are realized.  The corresponding
actual offset selectors satisfy

```text
cardinality(d+1) = cardinality(d) + 1
additiveCost(d) = additiveCost(d+1) + 1.
```

Both selected products remain Pareto optimal, exact-rank, irredundant, and
certifiably learnable.

## Rigidity and bottom ranks

A gap-free spectrum is rigid exactly when `width = 0`; then the only offset is
zero and the only profile is the minimum-cardinality endpoint.

Ranks zero and one are automatically gap-free because their tradeoff width is
zero.

No target grammar is supplied to any learner.
No `sorry`, `admit`, or `axiom` is used.
-/

namespace MCFG

universe u v w z


section GapFreeDefinition

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

/-- Every natural offset from zero through the Pareto-profile tradeoff width
is realized. -/
def
    CorrectedConcreteObservationPositiveAdditiveParetoRankProfileOffsetsGapFree
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
    Prop :=
  ∀ offset : Nat,
    offset <=
        correctedConcreteObservationPositiveAdditiveParetoProfileTradeoffWidth
          minimumCardinalityResult
          minimumAdditiveResult →
      offset ∈
        correctedConcreteObservationPositiveAdditiveParetoRankProfileOffsets
          minimumCardinalityResult

end GapFreeDefinition


section GapFreeCharacterizations

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

/-- Gap-freeness is exactly equality with the complete finite offset range. -/
theorem positiveAdditiveParetoRankProfileOffsetsGapFree_iff_eq_range :
    CorrectedConcreteObservationPositiveAdditiveParetoRankProfileOffsetsGapFree
          minimumCardinalityResult
          minimumAdditiveResult ↔
      correctedConcreteObservationPositiveAdditiveParetoRankProfileOffsets
          minimumCardinalityResult =
        Finset.range
          (correctedConcreteObservationPositiveAdditiveParetoProfileTradeoffWidth
              minimumCardinalityResult
              minimumAdditiveResult +
            1) := by

  constructor

  · intro hGapFree

    ext offset

    constructor

    · intro hOffset

      have hLe :=
        positiveAdditiveParetoRankProfileOffset_le_width
          minimumCardinalityResult
          minimumAdditiveResult
          hOffset

      exact
        Finset.mem_range.mpr
          (by omega)

    · intro hOffset

      have hLt :=
        Finset.mem_range.mp
          hOffset

      exact
        hGapFree
          offset
          (by omega)

  · intro hOffsetsEq offset hOffsetLe

    rw [hOffsetsEq]

    exact
      Finset.mem_range.mpr
        (by omega)

/-- Gap-freeness is equivalent to the realized offset set attaining its
maximum possible cardinality. -/
theorem
    positiveAdditiveParetoRankProfileOffsetsGapFree_iff_card_eq_width_add_one :
    CorrectedConcreteObservationPositiveAdditiveParetoRankProfileOffsetsGapFree
          minimumCardinalityResult
          minimumAdditiveResult ↔
      (correctedConcreteObservationPositiveAdditiveParetoRankProfileOffsets
          minimumCardinalityResult).card =
        correctedConcreteObservationPositiveAdditiveParetoProfileTradeoffWidth
            minimumCardinalityResult
            minimumAdditiveResult +
          1 := by

  constructor

  · intro hGapFree

    have hOffsetsEq :=
      (positiveAdditiveParetoRankProfileOffsetsGapFree_iff_eq_range
        minimumCardinalityResult
        minimumAdditiveResult).mp
        hGapFree

    rw [hOffsetsEq]

    simp

  · intro hCard

    have hSubset :=
      correctedConcreteObservationPositiveAdditiveParetoRankProfileOffsets_subset_range
        minimumCardinalityResult
        minimumAdditiveResult

    have hOffsetsEq :
        correctedConcreteObservationPositiveAdditiveParetoRankProfileOffsets
            minimumCardinalityResult =
          Finset.range
            (correctedConcreteObservationPositiveAdditiveParetoProfileTradeoffWidth
                minimumCardinalityResult
                minimumAdditiveResult +
              1) := by

      apply
        Finset.eq_of_subset_of_card_le
          hSubset

      simpa [hCard]

    exact
      (positiveAdditiveParetoRankProfileOffsetsGapFree_iff_eq_range
        minimumCardinalityResult
        minimumAdditiveResult).mpr
        hOffsetsEq

/-- Under gap-freeness, the finite Pareto profile set is exactly the complete
endpoint tradeoff interval. -/
theorem
    positiveAdditiveParetoRankProfileOffsetsGapFree_profiles_eq_tradeoffInterval
    (hGapFree :
      CorrectedConcreteObservationPositiveAdditiveParetoRankProfileOffsetsGapFree
        minimumCardinalityResult
        minimumAdditiveResult) :
    correctedConcreteObservationPositiveAdditiveRankMinimizingParetoProfiles
        (z := z)
        obsFamily
        f
        coordinateWeight
        U
        language
        hTarget =
      correctedConcreteObservationPositiveAdditiveParetoProfileTradeoffInterval
        minimumCardinalityResult
        minimumAdditiveResult := by

  have hOffsetsEq :=
    (positiveAdditiveParetoRankProfileOffsetsGapFree_iff_eq_range
      minimumCardinalityResult
      minimumAdditiveResult).mp
      hGapFree

  calc
    correctedConcreteObservationPositiveAdditiveRankMinimizingParetoProfiles
        (z := z)
        obsFamily
        f
        coordinateWeight
        U
        language
        hTarget =
      (correctedConcreteObservationPositiveAdditiveParetoRankProfileOffsets
          minimumCardinalityResult).image
        (correctedConcreteObservationPositiveAdditiveParetoProfileOfOffset
          minimumCardinalityResult) :=
            (correctedConcreteObservationPositiveAdditiveParetoRankProfileOffsets_image_profileOfOffset_eq_profiles
              minimumCardinalityResult
              minimumAdditiveResult).symm

    _ =
      (Finset.range
        (correctedConcreteObservationPositiveAdditiveParetoProfileTradeoffWidth
            minimumCardinalityResult
            minimumAdditiveResult +
          1)).image
        (correctedConcreteObservationPositiveAdditiveParetoProfileOfOffset
          minimumCardinalityResult) := by
            rw [hOffsetsEq]

    _ =
      correctedConcreteObservationPositiveAdditiveParetoProfileTradeoffInterval
        minimumCardinalityResult
        minimumAdditiveResult := by
          rfl

/-- Under gap-freeness, the finite profile set has exactly `width + 1`
members. -/
theorem
    positiveAdditiveParetoRankProfileOffsetsGapFree_profiles_card_eq_width_add_one
    (hGapFree :
      CorrectedConcreteObservationPositiveAdditiveParetoRankProfileOffsetsGapFree
        minimumCardinalityResult
        minimumAdditiveResult) :
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
        1 := by

  calc
    (correctedConcreteObservationPositiveAdditiveRankMinimizingParetoProfiles
        (z := z)
        obsFamily
        f
        coordinateWeight
        U
        language
        hTarget).card =
      (correctedConcreteObservationPositiveAdditiveParetoRankProfileOffsets
        minimumCardinalityResult).card :=
          (correctedConcreteObservationPositiveAdditiveParetoRankProfileOffsets_card_eq_profiles_card
            minimumCardinalityResult
            minimumAdditiveResult).symm

    _ =
      correctedConcreteObservationPositiveAdditiveParetoProfileTradeoffWidth
          minimumCardinalityResult
          minimumAdditiveResult +
        1 :=
          (positiveAdditiveParetoRankProfileOffsetsGapFree_iff_card_eq_width_add_one
            minimumCardinalityResult
            minimumAdditiveResult).mp
            hGapFree

/-- Under gap-freeness, positive width is equivalent to the profile set having
more than one member. -/
theorem
    positiveAdditiveParetoRankProfileOffsetsGapFree_width_pos_iff_one_lt_profiles_card
    (hGapFree :
      CorrectedConcreteObservationPositiveAdditiveParetoRankProfileOffsetsGapFree
        minimumCardinalityResult
        minimumAdditiveResult) :
    0 <
        correctedConcreteObservationPositiveAdditiveParetoProfileTradeoffWidth
          minimumCardinalityResult
          minimumAdditiveResult ↔
      1 <
        (correctedConcreteObservationPositiveAdditiveRankMinimizingParetoProfiles
          (z := z)
          obsFamily
          f
          coordinateWeight
          U
          language
          hTarget).card := by

  have hCard :=
    positiveAdditiveParetoRankProfileOffsetsGapFree_profiles_card_eq_width_add_one
      minimumCardinalityResult
      minimumAdditiveResult
      hGapFree

  omega

end GapFreeCharacterizations


section GapFreeOffsetSelector

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
  (hGapFree :
    CorrectedConcreteObservationPositiveAdditiveParetoRankProfileOffsetsGapFree
      minimumCardinalityResult
      minimumAdditiveResult)

/-- Under gap-freeness, choose an actual Pareto-optimal selected interface at
every offset through the width. -/
noncomputable def
    correctedConcreteObservationPositiveAdditiveParetoRankProfileGapFreeOffsetSelectionResult
    (offset : Nat)
    (hOffsetLe :
      offset <=
        correctedConcreteObservationPositiveAdditiveParetoProfileTradeoffWidth
          minimumCardinalityResult
          minimumAdditiveResult) :
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
      (hGapFree offset hOffsetLe) :=
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
    (hGapFree offset hOffsetLe)

/-- The gap-free selector at offset `d` has profile
`(c_min+d, a_max-d)`. -/
theorem
    positiveAdditiveParetoRankProfileGapFreeOffsetSelectionResult_profile
    (offset : Nat)
    (hOffsetLe :
      offset <=
        correctedConcreteObservationPositiveAdditiveParetoProfileTradeoffWidth
          minimumCardinalityResult
          minimumAdditiveResult) :
    let result :=
      correctedConcreteObservationPositiveAdditiveParetoRankProfileGapFreeOffsetSelectionResult
        minimumCardinalityResult
        minimumAdditiveResult
        hGapFree
        offset
        hOffsetLe
    (result.selected.card,
        correctedConcreteObservationSelectionAdditiveCost
          coordinateWeight result.selected) =
      correctedConcreteObservationPositiveAdditiveParetoProfileOfOffset
        minimumCardinalityResult
        offset := by

  exact
    (correctedConcreteObservationPositiveAdditiveParetoRankProfileGapFreeOffsetSelectionResult
      minimumCardinalityResult
      minimumAdditiveResult
      hGapFree
      offset
      hOffsetLe).selected_profile_eq

/-- Every gap-free offset selector attains the exact positive additive rank and
is Pareto optimal and irredundant. -/
theorem
    positiveAdditiveParetoRankProfileGapFreeOffsetSelectionResult_semantic_package
    (offset : Nat)
    (hOffsetLe :
      offset <=
        correctedConcreteObservationPositiveAdditiveParetoProfileTradeoffWidth
          minimumCardinalityResult
          minimumAdditiveResult) :
    let result :=
      correctedConcreteObservationPositiveAdditiveParetoRankProfileGapFreeOffsetSelectionResult
        minimumCardinalityResult
        minimumAdditiveResult
        hGapFree
        offset
        hOffsetLe
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
        result.selected := by

  let result :=
    correctedConcreteObservationPositiveAdditiveParetoRankProfileGapFreeOffsetSelectionResult
      minimumCardinalityResult
      minimumAdditiveResult
      hGapFree
      offset
      hOffsetLe

  exact
    ⟨result.selected_card_eq,
      result.selected_additiveCost_eq,
      result.selected_cost_eq_rank,
      result.selected_pareto,
      result.selected_irredundant⟩

end GapFreeOffsetSelector


section GapFreeOneStepTradeoff

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
  (hGapFree :
    CorrectedConcreteObservationPositiveAdditiveParetoRankProfileOffsetsGapFree
      minimumCardinalityResult
      minimumAdditiveResult)

/-- Adjacent gap-free offsets exchange exactly one additive-cost unit for one
selected-coordinate unit, and both selected products have certified learners. -/
theorem
    positiveAdditiveParetoRankProfileGapFree_oneStepCertifiedTradeoff
    (offset : Nat)
    (hOffsetLt :
      offset <
        correctedConcreteObservationPositiveAdditiveParetoProfileTradeoffWidth
          minimumCardinalityResult
          minimumAdditiveResult) :
    let hOffsetLe :
        offset <=
          correctedConcreteObservationPositiveAdditiveParetoProfileTradeoffWidth
            minimumCardinalityResult
            minimumAdditiveResult :=
      Nat.le_of_lt hOffsetLt
    let hNextLe :
        offset + 1 <=
          correctedConcreteObservationPositiveAdditiveParetoProfileTradeoffWidth
            minimumCardinalityResult
            minimumAdditiveResult := by
      omega
    let result₀ :=
      correctedConcreteObservationPositiveAdditiveParetoRankProfileGapFreeOffsetSelectionResult
        minimumCardinalityResult
        minimumAdditiveResult
        hGapFree
        offset
        hOffsetLe
    let result₁ :=
      correctedConcreteObservationPositiveAdditiveParetoRankProfileGapFreeOffsetSelectionResult
        minimumCardinalityResult
        minimumAdditiveResult
        hGapFree
        (offset + 1)
        hNextLe
    result₁.selected.card =
        result₀.selected.card + 1 ∧
      correctedConcreteObservationSelectionAdditiveCost
          coordinateWeight result₀.selected =
        correctedConcreteObservationSelectionAdditiveCost
            coordinateWeight result₁.selected +
          1 ∧
      correctedConcreteObservationSelectionPositiveAdditiveCost
          coordinateWeight result₀.selected =
        correctedConcreteObservationSelectionPositiveAdditiveCost
          coordinateWeight result₁.selected ∧
      IdentifiesLanguageFromPositiveData
        (correctedConcreteCertifiedWorkingGrammarHypLanguage
          (selectedObservationProduct obsFamily result₀.selected)
          f)
        (correctedConcreteCertifiedWorkingGrammarLearner
          hα
          (selectedObservationProduct obsFamily result₀.selected)
          f)
        language ∧
      IdentifiesLanguageFromPositiveData
        (correctedConcreteCertifiedWorkingGrammarHypLanguage
          (selectedObservationProduct obsFamily result₁.selected)
          f)
        (correctedConcreteCertifiedWorkingGrammarLearner
          hα
          (selectedObservationProduct obsFamily result₁.selected)
          f)
        language := by

  let hOffsetLe :
      offset <=
        correctedConcreteObservationPositiveAdditiveParetoProfileTradeoffWidth
          minimumCardinalityResult
          minimumAdditiveResult :=
    Nat.le_of_lt hOffsetLt

  let hNextLe :
      offset + 1 <=
        correctedConcreteObservationPositiveAdditiveParetoProfileTradeoffWidth
          minimumCardinalityResult
          minimumAdditiveResult := by
    omega

  let result₀ :=
    correctedConcreteObservationPositiveAdditiveParetoRankProfileGapFreeOffsetSelectionResult
      minimumCardinalityResult
      minimumAdditiveResult
      hGapFree
      offset
      hOffsetLe

  let result₁ :=
    correctedConcreteObservationPositiveAdditiveParetoRankProfileGapFreeOffsetSelectionResult
      minimumCardinalityResult
      minimumAdditiveResult
      hGapFree
      (offset + 1)
      hNextLe

  have hTradeoff :=
    result₀.selected_exactTradeoff_package
      result₁
      (Nat.le_succ offset)

  have hCertified₀ :=
    CorrectedConcreteObservationPositiveAdditiveParetoRankProfileOffsetSelectionResult.certified_package
      (z := z)
      hα
      result₀

  have hCertified₁ :=
    CorrectedConcreteObservationPositiveAdditiveParetoRankProfileOffsetSelectionResult.certified_package
      (z := z)
      hα
      result₁

  have hCardStep :
      result₁.selected.card =
        result₀.selected.card + 1 := by

    have hDifference :=
      hTradeoff.2.2.1

    omega

  have hAdditiveStep :
      correctedConcreteObservationSelectionAdditiveCost
          coordinateWeight result₀.selected =
        correctedConcreteObservationSelectionAdditiveCost
            coordinateWeight result₁.selected +
          1 := by

    have hOrder :=
      hTradeoff.2.1

    have hDifference :=
      hTradeoff.2.2.2.1

    omega

  exact
    ⟨hCardStep,
      hAdditiveStep,
      hTradeoff.2.2.2.2,
      hCertified₀.1,
      hCertified₁.1⟩

end GapFreeOneStepTradeoff


section GapFreeBottomRanks

variable {α : Type u}
variable {ι : Type v}
variable {M : Type w}
variable [DecidableEq ι]
variable [Monoid M]
variable (obsFamily : ι → α → M)
variable (f : Nat)
variable (coordinateWeight : ι → Nat)
variable (U : Finset ι)

/-- Positive-additive rank zero has a gap-free offset spectrum. -/
theorem positiveAdditiveParetoRankProfileOffsetsGapFree_of_rank_zero
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
      ambientTargetObservationSelectionPositiveAdditiveMinimumCost
          (z := z)
          obsFamily
          f
          coordinateWeight
          U
          hTarget =
        0) :
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
    CorrectedConcreteObservationPositiveAdditiveParetoRankProfileOffsetsGapFree
      minimumCardinalityResult
      minimumAdditiveResult := by

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

  have hWidthZero :=
    positiveAdditiveParetoProfile_tradeoffWidth_eq_zero_of_rank_zero
      (z := z)
      obsFamily
      f
      coordinateWeight
      U
      hTarget
      hRankZero

  have hOffsetsSingleton :=
    (positiveAdditiveParetoProfile_tradeoffWidth_eq_zero_iff_offsets_singleton
      minimumCardinalityResult
      minimumAdditiveResult).mp
      hWidthZero

  apply
    (positiveAdditiveParetoRankProfileOffsetsGapFree_iff_eq_range
      minimumCardinalityResult
      minimumAdditiveResult).mpr

  rw [hOffsetsSingleton, hWidthZero]

  simp

/-- Positive-additive rank one has a gap-free offset spectrum. -/
theorem positiveAdditiveParetoRankProfileOffsetsGapFree_of_rank_one
    {language : Set (Word α)}
    (hTarget :
      language ∈
        StartRootedCorrectedConcreteTargetClass
          (v := z)
          α
          (↥U → M)
          (selectedObservationProduct obsFamily U)
          f)
    (hRankOne :
      ambientTargetObservationSelectionPositiveAdditiveMinimumCost
          (z := z)
          obsFamily
          f
          coordinateWeight
          U
          hTarget =
        1) :
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
    CorrectedConcreteObservationPositiveAdditiveParetoRankProfileOffsetsGapFree
      minimumCardinalityResult
      minimumAdditiveResult := by

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

  have hWidthZero :=
    positiveAdditiveParetoProfile_tradeoffWidth_eq_zero_of_rank_one
      (z := z)
      obsFamily
      f
      coordinateWeight
      U
      hTarget
      hRankOne

  have hOffsetsSingleton :=
    (positiveAdditiveParetoProfile_tradeoffWidth_eq_zero_iff_offsets_singleton
      minimumCardinalityResult
      minimumAdditiveResult).mp
      hWidthZero

  apply
    (positiveAdditiveParetoRankProfileOffsetsGapFree_iff_eq_range
      minimumCardinalityResult
      minimumAdditiveResult).mpr

  rw [hOffsetsSingleton, hWidthZero]

  simp

end GapFreeBottomRanks


section GapFreeFinalPackage

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

/-- Final gap-free characterization, exact profile count, full interval,
all-offset semantic selection, and one-step certified tradeoff package. -/
theorem
    correctedConcreteCertifiedWorkingGrammar_observationSelectionParetoRankProfileOffsetGapFree_package :
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
      CorrectedConcreteObservationPositiveAdditiveParetoRankProfileOffsetsGapFree
          minimumCardinalityResult
          minimumAdditiveResult →
        (correctedConcreteObservationPositiveAdditiveParetoRankProfileOffsets
            minimumCardinalityResult =
          Finset.range
            (correctedConcreteObservationPositiveAdditiveParetoProfileTradeoffWidth
                minimumCardinalityResult
                minimumAdditiveResult +
              1)) ∧
        (correctedConcreteObservationPositiveAdditiveRankMinimizingParetoProfiles
            (z := z)
            obsFamily
            f
            coordinateWeight
            U
            language
            hTarget =
          correctedConcreteObservationPositiveAdditiveParetoProfileTradeoffInterval
            minimumCardinalityResult
            minimumAdditiveResult) ∧
        ((correctedConcreteObservationPositiveAdditiveRankMinimizingParetoProfiles
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
            1) ∧
        (∀ offset : Nat,
          ∀ hOffsetLe :
            offset <=
              correctedConcreteObservationPositiveAdditiveParetoProfileTradeoffWidth
                minimumCardinalityResult
                minimumAdditiveResult,
            let result :=
              correctedConcreteObservationPositiveAdditiveParetoRankProfileGapFreeOffsetSelectionResult
                minimumCardinalityResult
                minimumAdditiveResult
                ‹CorrectedConcreteObservationPositiveAdditiveParetoRankProfileOffsetsGapFree
                    minimumCardinalityResult
                    minimumAdditiveResult›
                offset
                hOffsetLe
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
              IdentifiesLanguageFromPositiveData
                (correctedConcreteCertifiedWorkingGrammarHypLanguage
                  (selectedObservationProduct obsFamily result.selected)
                  f)
                (correctedConcreteCertifiedWorkingGrammarLearner
                  hα
                  (selectedObservationProduct obsFamily result.selected)
                  f)
                language) := by

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

  intro hGapFree

  refine
    ⟨(positiveAdditiveParetoRankProfileOffsetsGapFree_iff_eq_range
        minimumCardinalityResult
        minimumAdditiveResult).mp
        hGapFree,
      positiveAdditiveParetoRankProfileOffsetsGapFree_profiles_eq_tradeoffInterval
        minimumCardinalityResult
        minimumAdditiveResult
        hGapFree,
      positiveAdditiveParetoRankProfileOffsetsGapFree_profiles_card_eq_width_add_one
        minimumCardinalityResult
        minimumAdditiveResult
        hGapFree,
      ?_⟩

  intro offset hOffsetLe

  let result :=
    correctedConcreteObservationPositiveAdditiveParetoRankProfileGapFreeOffsetSelectionResult
      minimumCardinalityResult
      minimumAdditiveResult
      hGapFree
      offset
      hOffsetLe

  have hCertified :=
    CorrectedConcreteObservationPositiveAdditiveParetoRankProfileOffsetSelectionResult.certified_package
      (z := z)
      hα
      result

  exact
    ⟨result.selected_card_eq,
      result.selected_additiveCost_eq,
      result.selected_cost_eq_rank,
      hCertified.1⟩

end GapFreeFinalPackage

end MCFG
