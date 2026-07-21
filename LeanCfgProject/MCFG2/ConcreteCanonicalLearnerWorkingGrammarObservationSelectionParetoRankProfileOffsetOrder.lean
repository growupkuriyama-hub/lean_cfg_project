/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG.ConcreteCanonicalLearnerWorkingGrammarObservationSelectionParetoRankProfileOffsetSelector

/-!
# ConcreteCanonicalLearnerWorkingGrammarObservationSelectionParetoRankProfileOffsetOrder.lean

The preceding file constructs an actual selected observation interface for
every realized normalized Pareto-profile offset.

This file proves that the offset order is exactly the profile tradeoff order.

## Exact order correspondence

Fix the minimum-cardinality endpoint

```text
(c_min, a_max).
```

The profile reconstructed from offset `d` is

```text
(c_min + d, a_max - d).
```

For realized offsets `d₀,d₁`:

```text
d₀ ≤ d₁
  ↔ cardinality(d₀) ≤ cardinality(d₁)
  ↔ additiveCost(d₁) ≤ additiveCost(d₀).
```

The strict versions also hold.

Thus increasing the normalized offset moves monotonically along the finite
Pareto rank line:

```text
more selected coordinates,
less additional coordinate weight,
the same positive additive rank.
```

## Exact difference preservation

When `d₀ ≤ d₁`,

```text
cardinality(d₁) - cardinality(d₀)
  = d₁ - d₀
```

and

```text
additiveCost(d₀) - additiveCost(d₁)
  = d₁ - d₀.
```

Hence every one-step offset increase exchanges exactly one unit of additive
weight for one selected-coordinate unit.

## Actual offset selectors

The same order and difference theorems are transferred to the actual selected
subsets returned by the offset-indexed selector.

Different subsets may realize the same offset.  No subset equality is claimed.
However, equality of offsets is equivalent to equality of their
cardinality/additive-weight profiles.

Every selected product continues to carry its own certified learner
identifying the target.

No target grammar is supplied to any learner.
No `sorry`, `admit`, or `axiom` is used.
-/

namespace MCFG

universe u v w z


section ReconstructedOffsetProfileOrder

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

/-- First coordinate of the profile reconstructed from an offset. -/
theorem positiveAdditiveParetoProfileOfOffset_fst
    (offset : Nat) :
    (correctedConcreteObservationPositiveAdditiveParetoProfileOfOffset
        minimumCardinalityResult
        offset).1 =
      minimumCardinalityResult.profile.1 + offset := by

  rfl

/-- Second coordinate of the profile reconstructed from an offset. -/
theorem positiveAdditiveParetoProfileOfOffset_snd
    (offset : Nat) :
    (correctedConcreteObservationPositiveAdditiveParetoProfileOfOffset
        minimumCardinalityResult
        offset).2 =
      minimumCardinalityResult.profile.2 - offset := by

  rfl

/-- Reconstructed profiles are injective in their offset. -/
theorem positiveAdditiveParetoProfileOfOffset_injective :
    Function.Injective
      (correctedConcreteObservationPositiveAdditiveParetoProfileOfOffset
        minimumCardinalityResult) := by

  intro offset₀ offset₁ hProfile

  have hFirst :=
    congrArg Prod.fst
      hProfile

  simpa [
    correctedConcreteObservationPositiveAdditiveParetoProfileOfOffset
  ] using
    Nat.add_left_cancel
      hFirst

/-- Offset order is exactly first-coordinate order. -/
theorem positiveAdditiveParetoProfileOfOffset_fst_le_iff
    (offset₀ offset₁ : Nat) :
    (correctedConcreteObservationPositiveAdditiveParetoProfileOfOffset
        minimumCardinalityResult
        offset₀).1 <=
      (correctedConcreteObservationPositiveAdditiveParetoProfileOfOffset
        minimumCardinalityResult
        offset₁).1 ↔
      offset₀ <= offset₁ := by

  simp [
    correctedConcreteObservationPositiveAdditiveParetoProfileOfOffset
  ]

/-- Strict offset order is exactly strict first-coordinate order. -/
theorem positiveAdditiveParetoProfileOfOffset_fst_lt_iff
    (offset₀ offset₁ : Nat) :
    (correctedConcreteObservationPositiveAdditiveParetoProfileOfOffset
        minimumCardinalityResult
        offset₀).1 <
      (correctedConcreteObservationPositiveAdditiveParetoProfileOfOffset
        minimumCardinalityResult
        offset₁).1 ↔
      offset₀ < offset₁ := by

  simp [
    correctedConcreteObservationPositiveAdditiveParetoProfileOfOffset
  ]

/-- For realized offsets, increasing offset is exactly decreasing additive
coordinate cost. -/
theorem positiveAdditiveParetoProfileOfOffset_snd_reverse_le_iff
    {offset₀ offset₁ : Nat}
    (hOffset₀ :
      offset₀ ∈
        correctedConcreteObservationPositiveAdditiveParetoRankProfileOffsets
          minimumCardinalityResult)
    (hOffset₁ :
      offset₁ ∈
        correctedConcreteObservationPositiveAdditiveParetoRankProfileOffsets
          minimumCardinalityResult) :
    (correctedConcreteObservationPositiveAdditiveParetoProfileOfOffset
        minimumCardinalityResult
        offset₁).2 <=
      (correctedConcreteObservationPositiveAdditiveParetoProfileOfOffset
        minimumCardinalityResult
        offset₀).2 ↔
      offset₀ <= offset₁ := by

  have hOffset₀Le :=
    positiveAdditiveParetoRankProfileOffset_le_width
      minimumCardinalityResult
      minimumAdditiveResult
      hOffset₀

  have hOffset₁Le :=
    positiveAdditiveParetoRankProfileOffset_le_width
      minimumCardinalityResult
      minimumAdditiveResult
      hOffset₁

  have hMaximumAdditive :=
    positiveAdditiveParetoProfile_maxAdditive_eq_minAdditive_add_width
      minimumCardinalityResult
      minimumAdditiveResult

  unfold
    correctedConcreteObservationPositiveAdditiveParetoProfileOfOffset

  omega

/-- For realized offsets, strict offset increase is exactly strict additive
coordinate decrease. -/
theorem positiveAdditiveParetoProfileOfOffset_snd_reverse_lt_iff
    {offset₀ offset₁ : Nat}
    (hOffset₀ :
      offset₀ ∈
        correctedConcreteObservationPositiveAdditiveParetoRankProfileOffsets
          minimumCardinalityResult)
    (hOffset₁ :
      offset₁ ∈
        correctedConcreteObservationPositiveAdditiveParetoRankProfileOffsets
          minimumCardinalityResult) :
    (correctedConcreteObservationPositiveAdditiveParetoProfileOfOffset
        minimumCardinalityResult
        offset₁).2 <
      (correctedConcreteObservationPositiveAdditiveParetoProfileOfOffset
        minimumCardinalityResult
        offset₀).2 ↔
      offset₀ < offset₁ := by

  have hOffset₀Le :=
    positiveAdditiveParetoRankProfileOffset_le_width
      minimumCardinalityResult
      minimumAdditiveResult
      hOffset₀

  have hOffset₁Le :=
    positiveAdditiveParetoRankProfileOffset_le_width
      minimumCardinalityResult
      minimumAdditiveResult
      hOffset₁

  have hMaximumAdditive :=
    positiveAdditiveParetoProfile_maxAdditive_eq_minAdditive_add_width
      minimumCardinalityResult
      minimumAdditiveResult

  unfold
    correctedConcreteObservationPositiveAdditiveParetoProfileOfOffset

  omega

/-- Every reconstructed realized profile remains on the exact target-rank
line. -/
theorem positiveAdditiveParetoProfileOfOffset_sum_eq_rank
    {offset : Nat}
    (hOffset :
      offset ∈
        correctedConcreteObservationPositiveAdditiveParetoRankProfileOffsets
          minimumCardinalityResult) :
    (correctedConcreteObservationPositiveAdditiveParetoProfileOfOffset
          minimumCardinalityResult
          offset).1 +
        (correctedConcreteObservationPositiveAdditiveParetoProfileOfOffset
          minimumCardinalityResult
          offset).2 =
      ambientTargetObservationSelectionPositiveAdditiveMinimumCost
        (z := z)
        obsFamily
        f
        coordinateWeight
        U
        hTarget := by

  have hProfileMem :=
    positiveAdditiveParetoProfileOfOffset_mem
      minimumCardinalityResult
      minimumAdditiveResult
      hOffset

  exact
    correctedConcreteObservationPositiveAdditiveRankMinimizingParetoProfile_sum_eq_rank
      (z := z)
      hProfileMem

/-- First-coordinate difference is exactly offset difference. -/
theorem positiveAdditiveParetoProfileOfOffset_fst_sub_eq
    {offset₀ offset₁ : Nat}
    (hOrder : offset₀ <= offset₁) :
    (correctedConcreteObservationPositiveAdditiveParetoProfileOfOffset
          minimumCardinalityResult
          offset₁).1 -
        (correctedConcreteObservationPositiveAdditiveParetoProfileOfOffset
          minimumCardinalityResult
          offset₀).1 =
      offset₁ - offset₀ := by

  unfold
    correctedConcreteObservationPositiveAdditiveParetoProfileOfOffset

  omega

/-- For realized ordered offsets, additive-coordinate decrease is exactly
offset difference. -/
theorem positiveAdditiveParetoProfileOfOffset_snd_sub_eq
    {offset₀ offset₁ : Nat}
    (hOffset₀ :
      offset₀ ∈
        correctedConcreteObservationPositiveAdditiveParetoRankProfileOffsets
          minimumCardinalityResult)
    (hOffset₁ :
      offset₁ ∈
        correctedConcreteObservationPositiveAdditiveParetoRankProfileOffsets
          minimumCardinalityResult)
    (hOrder : offset₀ <= offset₁) :
    (correctedConcreteObservationPositiveAdditiveParetoProfileOfOffset
          minimumCardinalityResult
          offset₀).2 -
        (correctedConcreteObservationPositiveAdditiveParetoProfileOfOffset
          minimumCardinalityResult
          offset₁).2 =
      offset₁ - offset₀ := by

  have hOffset₀Le :=
    positiveAdditiveParetoRankProfileOffset_le_width
      minimumCardinalityResult
      minimumAdditiveResult
      hOffset₀

  have hOffset₁Le :=
    positiveAdditiveParetoRankProfileOffset_le_width
      minimumCardinalityResult
      minimumAdditiveResult
      hOffset₁

  have hMaximumAdditive :=
    positiveAdditiveParetoProfile_maxAdditive_eq_minAdditive_add_width
      minimumCardinalityResult
      minimumAdditiveResult

  unfold
    correctedConcreteObservationPositiveAdditiveParetoProfileOfOffset

  omega

/-- Exact profile tradeoff package for two ordered realized offsets. -/
theorem positiveAdditiveParetoProfileOfOffset_exactTradeoff_package
    {offset₀ offset₁ : Nat}
    (hOffset₀ :
      offset₀ ∈
        correctedConcreteObservationPositiveAdditiveParetoRankProfileOffsets
          minimumCardinalityResult)
    (hOffset₁ :
      offset₁ ∈
        correctedConcreteObservationPositiveAdditiveParetoRankProfileOffsets
          minimumCardinalityResult)
    (hOrder : offset₀ <= offset₁) :
    (correctedConcreteObservationPositiveAdditiveParetoProfileOfOffset
          minimumCardinalityResult
          offset₀).1 <=
        (correctedConcreteObservationPositiveAdditiveParetoProfileOfOffset
          minimumCardinalityResult
          offset₁).1 ∧
      (correctedConcreteObservationPositiveAdditiveParetoProfileOfOffset
          minimumCardinalityResult
          offset₁).2 <=
        (correctedConcreteObservationPositiveAdditiveParetoProfileOfOffset
          minimumCardinalityResult
          offset₀).2 ∧
      (correctedConcreteObservationPositiveAdditiveParetoProfileOfOffset
            minimumCardinalityResult
            offset₁).1 -
          (correctedConcreteObservationPositiveAdditiveParetoProfileOfOffset
            minimumCardinalityResult
            offset₀).1 =
        offset₁ - offset₀ ∧
      (correctedConcreteObservationPositiveAdditiveParetoProfileOfOffset
            minimumCardinalityResult
            offset₀).2 -
          (correctedConcreteObservationPositiveAdditiveParetoProfileOfOffset
            minimumCardinalityResult
            offset₁).2 =
        offset₁ - offset₀ := by

  exact
    ⟨(positiveAdditiveParetoProfileOfOffset_fst_le_iff
        minimumCardinalityResult
        offset₀
        offset₁).2
        hOrder,
      (positiveAdditiveParetoProfileOfOffset_snd_reverse_le_iff
        minimumCardinalityResult
        minimumAdditiveResult
        hOffset₀
        hOffset₁).2
        hOrder,
      positiveAdditiveParetoProfileOfOffset_fst_sub_eq
        minimumCardinalityResult
        hOrder,
      positiveAdditiveParetoProfileOfOffset_snd_sub_eq
        minimumCardinalityResult
        minimumAdditiveResult
        hOffset₀
        hOffset₁
        hOrder⟩

end ReconstructedOffsetProfileOrder


namespace CorrectedConcreteObservationPositiveAdditiveParetoRankProfileOffsetSelectionResult

section OffsetSelectorOrder

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
  {minimumCardinalityResult :
    CorrectedConcreteObservationPositiveAdditiveParetoMinimumCardinalityProfileResult
      (z := z)
      obsFamily
      f
      coordinateWeight
      U
      language
      hTarget}
variable
  {minimumAdditiveResult :
    CorrectedConcreteObservationPositiveAdditiveParetoMinimumAdditiveProfileResult
      (z := z)
      obsFamily
      f
      coordinateWeight
      U
      language
      hTarget}
variable
  {offset₀ offset₁ : Nat}
variable
  {hOffset₀ :
    offset₀ ∈
      correctedConcreteObservationPositiveAdditiveParetoRankProfileOffsets
        minimumCardinalityResult}
variable
  {hOffset₁ :
    offset₁ ∈
      correctedConcreteObservationPositiveAdditiveParetoRankProfileOffsets
        minimumCardinalityResult}
variable
  (result₀ :
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
      offset₀
      hOffset₀)
variable
  (result₁ :
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
      offset₁
      hOffset₁)

/-- Offset order is exactly selected-set cardinality order. -/
theorem selected_card_le_iff_offset_le :
    result₀.selected.card <= result₁.selected.card ↔
      offset₀ <= offset₁ := by

  rw [
    result₀.selected_card_eq,
    result₁.selected_card_eq
  ]

  simp

/-- Strict offset order is exactly strict selected-set cardinality order. -/
theorem selected_card_lt_iff_offset_lt :
    result₀.selected.card < result₁.selected.card ↔
      offset₀ < offset₁ := by

  rw [
    result₀.selected_card_eq,
    result₁.selected_card_eq
  ]

  simp

/-- Offset order is exactly reverse additive-cost order. -/
theorem selected_additiveCost_reverse_le_iff_offset_le :
    correctedConcreteObservationSelectionAdditiveCost
          coordinateWeight result₁.selected <=
        correctedConcreteObservationSelectionAdditiveCost
          coordinateWeight result₀.selected ↔
      offset₀ <= offset₁ := by

  rw [
    result₀.selected_additiveCost_eq,
    result₁.selected_additiveCost_eq
  ]

  have hOffset₀Le :=
    result₀.offset_le_width

  have hOffset₁Le :=
    result₁.offset_le_width

  have hMaximumAdditive :=
    positiveAdditiveParetoProfile_maxAdditive_eq_minAdditive_add_width
      minimumCardinalityResult
      minimumAdditiveResult

  omega

/-- Strict offset order is exactly strict reverse additive-cost order. -/
theorem selected_additiveCost_reverse_lt_iff_offset_lt :
    correctedConcreteObservationSelectionAdditiveCost
          coordinateWeight result₁.selected <
        correctedConcreteObservationSelectionAdditiveCost
          coordinateWeight result₀.selected ↔
      offset₀ < offset₁ := by

  rw [
    result₀.selected_additiveCost_eq,
    result₁.selected_additiveCost_eq
  ]

  have hOffset₀Le :=
    result₀.offset_le_width

  have hOffset₁Le :=
    result₁.offset_le_width

  have hMaximumAdditive :=
    positiveAdditiveParetoProfile_maxAdditive_eq_minAdditive_add_width
      minimumCardinalityResult
      minimumAdditiveResult

  omega

/-- Equality of offsets is equivalent to equality of selected profiles. -/
theorem selected_profile_eq_iff_offset_eq :
    (result₀.selected.card,
        correctedConcreteObservationSelectionAdditiveCost
          coordinateWeight result₀.selected) =
      (result₁.selected.card,
        correctedConcreteObservationSelectionAdditiveCost
          coordinateWeight result₁.selected) ↔
      offset₀ = offset₁ := by

  constructor

  · intro hProfile

    have hCard :=
      congrArg Prod.fst
        hProfile

    rw [
      result₀.selected_card_eq,
      result₁.selected_card_eq
    ] at hCard

    omega

  · intro hOffsetEq

    rw [
      result₀.selected_profile_eq,
      result₁.selected_profile_eq,
      hOffsetEq
    ]

/-- Selected cardinality difference is exactly offset difference. -/
theorem selected_card_sub_eq_offset_sub
    (hOrder : offset₀ <= offset₁) :
    result₁.selected.card - result₀.selected.card =
      offset₁ - offset₀ := by

  rw [
    result₀.selected_card_eq,
    result₁.selected_card_eq
  ]

  omega

/-- Selected additive-cost decrease is exactly offset difference. -/
theorem selected_additiveCost_sub_eq_offset_sub
    (hOrder : offset₀ <= offset₁) :
    correctedConcreteObservationSelectionAdditiveCost
          coordinateWeight result₀.selected -
        correctedConcreteObservationSelectionAdditiveCost
          coordinateWeight result₁.selected =
      offset₁ - offset₀ := by

  rw [
    result₀.selected_additiveCost_eq,
    result₁.selected_additiveCost_eq
  ]

  have hOffset₀Le :=
    result₀.offset_le_width

  have hOffset₁Le :=
    result₁.offset_le_width

  have hMaximumAdditive :=
    positiveAdditiveParetoProfile_maxAdditive_eq_minAdditive_add_width
      minimumCardinalityResult
      minimumAdditiveResult

  omega

/-- Two selected offset interfaces have the same exact positive additive
rank. -/
theorem selected_cost_eq_selected_cost :
    correctedConcreteObservationSelectionPositiveAdditiveCost
        coordinateWeight result₀.selected =
      correctedConcreteObservationSelectionPositiveAdditiveCost
        coordinateWeight result₁.selected := by

  rw [
    result₀.selected_cost_eq_rank,
    result₁.selected_cost_eq_rank
  ]

/-- Exact actual-selection tradeoff package for two ordered offsets. -/
theorem selected_exactTradeoff_package
    (hOrder : offset₀ <= offset₁) :
    result₀.selected.card <= result₁.selected.card ∧
      correctedConcreteObservationSelectionAdditiveCost
          coordinateWeight result₁.selected <=
        correctedConcreteObservationSelectionAdditiveCost
          coordinateWeight result₀.selected ∧
      result₁.selected.card - result₀.selected.card =
        offset₁ - offset₀ ∧
      correctedConcreteObservationSelectionAdditiveCost
            coordinateWeight result₀.selected -
          correctedConcreteObservationSelectionAdditiveCost
            coordinateWeight result₁.selected =
        offset₁ - offset₀ ∧
      correctedConcreteObservationSelectionPositiveAdditiveCost
          coordinateWeight result₀.selected =
        correctedConcreteObservationSelectionPositiveAdditiveCost
          coordinateWeight result₁.selected := by

  exact
    ⟨(result₀.selected_card_le_iff_offset_le result₁).2
        hOrder,
      (result₀.selected_additiveCost_reverse_le_iff_offset_le result₁).2
        hOrder,
      result₀.selected_card_sub_eq_offset_sub
        result₁
        hOrder,
      result₀.selected_additiveCost_sub_eq_offset_sub
        result₁
        hOrder,
      result₀.selected_cost_eq_selected_cost
        result₁⟩

end OffsetSelectorOrder

end CorrectedConcreteObservationPositiveAdditiveParetoRankProfileOffsetSelectionResult


section OffsetOrderCertifiedPair

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
  {minimumCardinalityResult :
    CorrectedConcreteObservationPositiveAdditiveParetoMinimumCardinalityProfileResult
      (z := z)
      obsFamily
      f
      coordinateWeight
      U
      language
      hTarget}
variable
  {minimumAdditiveResult :
    CorrectedConcreteObservationPositiveAdditiveParetoMinimumAdditiveProfileResult
      (z := z)
      obsFamily
      f
      coordinateWeight
      U
      language
      hTarget}
variable
  {offset₀ offset₁ : Nat}
variable
  {hOffset₀ :
    offset₀ ∈
      correctedConcreteObservationPositiveAdditiveParetoRankProfileOffsets
        minimumCardinalityResult}
variable
  {hOffset₁ :
    offset₁ ∈
      correctedConcreteObservationPositiveAdditiveParetoRankProfileOffsets
        minimumCardinalityResult}
variable
  (result₀ :
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
      offset₀
      hOffset₀)
variable
  (result₁ :
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
      offset₁
      hOffset₁)

/-- Both ordered-offset selected products have certified learners identifying
the same target. -/
theorem positiveAdditiveParetoRankProfileOffset_selectedPair_certified
    (hOrder : offset₀ <= offset₁) :
    result₀.selected.card <= result₁.selected.card ∧
      correctedConcreteObservationSelectionAdditiveCost
          coordinateWeight result₁.selected <=
        correctedConcreteObservationSelectionAdditiveCost
          coordinateWeight result₀.selected ∧
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

  have hTradeoff :=
    result₀.selected_exactTradeoff_package
      result₁
      hOrder

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

  exact
    ⟨hTradeoff.1,
      hTradeoff.2.1,
      hCertified₀.1,
      hCertified₁.1⟩

end OffsetOrderCertifiedPair


section ParetoRankProfileOffsetOrderFinalPackage

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

/-- Final offset/profile order equivalence, exact difference preservation, and
certified two-offset selection package. -/
theorem
    correctedConcreteCertifiedWorkingGrammar_observationSelectionParetoRankProfileOffsetOrder_package :
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
      ∀ offset₀ offset₁ : Nat,
        ∀ hOffset₀ :
          offset₀ ∈
            correctedConcreteObservationPositiveAdditiveParetoRankProfileOffsets
              minimumCardinalityResult,
        ∀ hOffset₁ :
          offset₁ ∈
            correctedConcreteObservationPositiveAdditiveParetoRankProfileOffsets
              minimumCardinalityResult,
          let result₀ :=
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
              offset₀
              hOffset₀
          let result₁ :=
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
              offset₁
              hOffset₁
          (result₀.selected.card <= result₁.selected.card ↔
              offset₀ <= offset₁) ∧
            (correctedConcreteObservationSelectionAdditiveCost
                  coordinateWeight result₁.selected <=
                correctedConcreteObservationSelectionAdditiveCost
                  coordinateWeight result₀.selected ↔
              offset₀ <= offset₁) ∧
            (offset₀ <= offset₁ →
              result₁.selected.card - result₀.selected.card =
                  offset₁ - offset₀ ∧
                correctedConcreteObservationSelectionAdditiveCost
                      coordinateWeight result₀.selected -
                    correctedConcreteObservationSelectionAdditiveCost
                      coordinateWeight result₁.selected =
                  offset₁ - offset₀) ∧
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

  intro offset₀ offset₁ hOffset₀ hOffset₁

  let result₀ :=
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
      offset₀
      hOffset₀

  let result₁ :=
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
      offset₁
      hOffset₁

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

  exact
    ⟨result₀.selected_card_le_iff_offset_le
        result₁,
      result₀.selected_additiveCost_reverse_le_iff_offset_le
        result₁,
      fun hOrder =>
        ⟨result₀.selected_card_sub_eq_offset_sub
            result₁
            hOrder,
          result₀.selected_additiveCost_sub_eq_offset_sub
            result₁
            hOrder⟩,
      hCertified₀.1,
      hCertified₁.1⟩

end ParetoRankProfileOffsetOrderFinalPackage

end MCFG
