/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG.ConcreteCanonicalLearnerWorkingGrammarObservationSelectionParetoRankProfileOffsets

/-!
# ConcreteCanonicalLearnerWorkingGrammarObservationSelectionParetoRankProfileOffsetSelector.lean

The preceding file normalizes the finite positive-additive-rank-minimizing
Pareto profile set to realized natural-number offsets.

This file turns every realized offset into an actual selected observation
interface.

## Offset-indexed selector

Fix the minimum-cardinality endpoint

```text
(c_min, a_max).
```

For every realized offset `d`, select an actual finite subset `S` satisfying

```text
S.card = c_min + d,
AdditiveCost(weight,S) = a_max - d.
```

The selected subset belongs to the finite rank-minimizing Pareto selection set.

Therefore it

* represents the target;
* is Pareto optimal for cardinality and additive coordinate weight;
* attains the exact positive additive observation-selection rank;
* is globally minimum among every feasible ambient selection;
* is inclusion-irredundant; and
* has every selected coordinate essential.

## Profile uniqueness, not subset uniqueness

Different selected subsets may realize the same offset.
No uniqueness of the selected subset is asserted.

However, every selector result for one fixed offset has exactly the same
two-dimensional profile.  Thus the normalized offset determines the
cardinality/additive-weight pair uniquely.

## Endpoint selectors

Offset zero produces the minimum-cardinality endpoint profile.
Offset `width` produces the minimum-additive-cost endpoint profile.

Hence the two endpoint optimization policies are instances of one uniform
offset-indexed selector.

## Certified learner

For every realized offset, the selected product has its own certified learner.
It identifies the target from positive data and has an exact checked grammar
output at the selected product's minimum certified-description rank.

The observation-interface offset remains separate from the grammar-description
rank.

No target grammar is supplied to any learner.
No `sorry`, `admit`, or `axiom` is used.
-/

namespace MCFG

universe u v w z


section ParetoRankProfileOffsetSelectionResultDefinition

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
  (offset : Nat)
variable
  (hOffset :
    offset ∈
      correctedConcreteObservationPositiveAdditiveParetoRankProfileOffsets
        minimumCardinalityResult)

/-- One actual rank-minimizing Pareto selection realizing a prescribed
normalized profile offset. -/
structure
    CorrectedConcreteObservationPositiveAdditiveParetoRankProfileOffsetSelectionResult where

  selected :
    Finset ι

  selected_mem :
    selected ∈
      correctedConcreteObservationPositiveAdditiveRankMinimizingParetoSelections
        (z := z)
        obsFamily
        f
        coordinateWeight
        U
        language
        hTarget

  selected_profile_eq :
    (selected.card,
        correctedConcreteObservationSelectionAdditiveCost
          coordinateWeight selected) =
      correctedConcreteObservationPositiveAdditiveParetoProfileOfOffset
        minimumCardinalityResult
        offset

/-- Select one actual observation interface for every realized normalized
profile offset. -/
noncomputable def
    correctedConcreteObservationPositiveAdditiveParetoRankProfileOffsetSelectionResult :
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
      hOffset := by

  classical

  have hProfileMem :
      correctedConcreteObservationPositiveAdditiveParetoProfileOfOffset
          minimumCardinalityResult
          offset ∈
        correctedConcreteObservationPositiveAdditiveRankMinimizingParetoProfiles
          (z := z)
          obsFamily
          f
          coordinateWeight
          U
          language
          hTarget :=
    positiveAdditiveParetoProfileOfOffset_mem
      minimumCardinalityResult
      minimumAdditiveResult
      hOffset

  rcases
      (mem_correctedConcreteObservationPositiveAdditiveRankMinimizingParetoProfiles_iff
        (z := z)).mp
        hProfileMem with
    ⟨S, hS, hProfileEq⟩

  exact
    ⟨S,
      hS,
      hProfileEq⟩

end ParetoRankProfileOffsetSelectionResultDefinition


namespace CorrectedConcreteObservationPositiveAdditiveParetoRankProfileOffsetSelectionResult

section OffsetSelectionSemanticProperties

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
  {offset : Nat}
variable
  {hOffset :
    offset ∈
      correctedConcreteObservationPositiveAdditiveParetoRankProfileOffsets
        minimumCardinalityResult}
variable
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
      hOffset)

/-- The selected subset is Pareto optimal for cardinality and additive
coordinate weight. -/
theorem selected_pareto :
    CorrectedConcreteObservationSelectionParetoOptimal
      (z := z)
      obsFamily
      f
      (correctedConcreteObservationSelectionAdditiveCost
        coordinateWeight)
      U
      language
      result.selected := by

  exact
    ((mem_correctedConcreteObservationPositiveAdditiveRankMinimizingParetoSelections_iff
      (z := z)).mp
      result.selected_mem).1

/-- The selected subset lies inside the ambient candidate set. -/
theorem selected_subset :
    result.selected ⊆ U := by

  exact
    result.selected_pareto.1

/-- The selected product represents the target language. -/
theorem selected_target :
    language ∈
      StartRootedCorrectedConcreteTargetClass
        (v := z)
        α
        (↥result.selected → M)
        (selectedObservationProduct obsFamily result.selected)
        f := by

  exact
    result.selected_pareto.2.1

/-- The selected subset attains the exact ambient positive-additive rank. -/
theorem selected_cost_eq_rank :
    correctedConcreteObservationSelectionPositiveAdditiveCost
        coordinateWeight result.selected =
      ambientTargetObservationSelectionPositiveAdditiveMinimumCost
        (z := z)
        obsFamily
        f
        coordinateWeight
        U
        hTarget := by

  exact
    ((mem_correctedConcreteObservationPositiveAdditiveRankMinimizingParetoSelections_iff
      (z := z)).mp
      result.selected_mem).2

/-- The selected-set cardinality is exactly the minimum endpoint cardinality
plus the prescribed offset. -/
theorem selected_card_eq :
    result.selected.card =
      minimumCardinalityResult.profile.1 + offset := by

  have hFirst :=
    congrArg Prod.fst
      result.selected_profile_eq

  simpa [
    correctedConcreteObservationPositiveAdditiveParetoProfileOfOffset
  ] using
    hFirst

/-- The selected additive coordinate cost is exactly the maximum endpoint
additive coordinate minus the prescribed offset. -/
theorem selected_additiveCost_eq :
    correctedConcreteObservationSelectionAdditiveCost
          coordinateWeight result.selected =
      minimumCardinalityResult.profile.2 - offset := by

  have hSecond :=
    congrArg Prod.snd
      result.selected_profile_eq

  simpa [
    correctedConcreteObservationPositiveAdditiveParetoProfileOfOffset
  ] using
    hSecond

/-- The selected profile has normalized offset exactly equal to the prescribed
offset. -/
theorem selected_profileOffset_eq :
    correctedConcreteObservationPositiveAdditiveParetoProfileCardinalityOffset
          minimumCardinalityResult
          (result.selected.card,
            correctedConcreteObservationSelectionAdditiveCost
              coordinateWeight result.selected) =
      offset := by

  unfold
    correctedConcreteObservationPositiveAdditiveParetoProfileCardinalityOffset

  rw [result.selected_card_eq]

  simp

/-- The prescribed offset is bounded by the global Pareto-profile width. -/
theorem offset_le_width :
    offset <=
      correctedConcreteObservationPositiveAdditiveParetoProfileTradeoffWidth
        minimumCardinalityResult
        minimumAdditiveResult := by

  exact
    positiveAdditiveParetoRankProfileOffset_le_width
      minimumCardinalityResult
      minimumAdditiveResult
      hOffset

/-- The selected cardinality is bounded by the maximum-cardinality endpoint. -/
theorem selected_card_le_maximum :
    result.selected.card <=
      minimumAdditiveResult.profile.1 := by

  have hWidth :=
    result.offset_le_width

  have hMaximumEq :=
    positiveAdditiveParetoProfile_maxCardinality_eq_minCardinality_add_width
      minimumCardinalityResult
      minimumAdditiveResult

  rw [result.selected_card_eq, hMaximumEq]

  omega

/-- The selected additive coordinate lies above the minimum-additive endpoint. -/
theorem minimum_additive_le_selected :
    minimumAdditiveResult.profile.2 <=
      correctedConcreteObservationSelectionAdditiveCost
        coordinateWeight result.selected := by

  have hProfileMem :
      (result.selected.card,
          correctedConcreteObservationSelectionAdditiveCost
            coordinateWeight result.selected) ∈
        correctedConcreteObservationPositiveAdditiveRankMinimizingParetoProfiles
          (z := z)
          obsFamily
          f
          coordinateWeight
          U
          language
          hTarget := by

    apply
      (mem_correctedConcreteObservationPositiveAdditiveRankMinimizingParetoProfiles_iff
        (z := z)).mpr

    exact
      ⟨result.selected,
        result.selected_mem,
        rfl⟩

  exact
    minimumAdditiveResult.profile_additive_le
      hProfileMem

/-- The selected result has no larger positive additive cost than any feasible
ambient selection. -/
theorem selected_cost_le_every_feasible
    {R : Finset ι}
    (hRU : R ⊆ U)
    (hRTarget :
      language ∈
        StartRootedCorrectedConcreteTargetClass
          (v := z)
          α
          (↥R → M)
          (selectedObservationProduct obsFamily R)
          f) :
    correctedConcreteObservationSelectionPositiveAdditiveCost
          coordinateWeight result.selected <=
      correctedConcreteObservationSelectionPositiveAdditiveCost
        coordinateWeight R := by

  let hSelection :=
    hasCorrectedConcreteObservationSelectionCost_of_fullProductTarget
      (obsFamily := obsFamily)
      (f := f)
      (correctedConcreteObservationSelectionPositiveAdditiveCost
        coordinateWeight)
      hTarget

  have hMinimum :
      correctedConcreteObservationSelectionMinimumCost
          (correctedConcreteObservationSelectionPositiveAdditiveCost
            coordinateWeight)
          hSelection <=
        correctedConcreteObservationSelectionPositiveAdditiveCost
          coordinateWeight R := by

    apply
      hSelection.minimumCost_le_of_selection

    exact
      ⟨R,
        hRU,
        Nat.le_refl _,
        hRTarget⟩

  rw [result.selected_cost_eq_rank]

  simpa [
    ambientTargetObservationSelectionPositiveAdditiveMinimumCost,
    ambientTargetObservationSelectionMinimumCost,
    hSelection
  ] using
    hMinimum

/-- The offset-indexed selected subset is inclusion-irredundant. -/
theorem selected_irredundant :
    CorrectedConcreteObservationSelectionIrredundant
      (z := z)
      α
      ι
      M
      obsFamily
      f
      language
      result.selected := by

  exact
    observationSelection_paretoOptimal_irredundant
      (z := z)
      (correctedConcreteObservationSelectionAdditiveCost_monotone
        coordinateWeight)
      result.selected_pareto

/-- Every selected coordinate is essential. -/
theorem selected_coordinateEssential
    {index : ι}
    (hindex : index ∈ result.selected) :
    CorrectedConcreteSelectedObservationCoordinateEssential
      (z := z)
      α
      ι
      M
      obsFamily
      f
      language
      result.selected
      index := by

  exact
    observationSelection_paretoOptimal_coordinateEssential
      (z := z)
      (correctedConcreteObservationSelectionAdditiveCost_monotone
        coordinateWeight)
      result.selected_pareto
      hindex

/-- Restoring any deleted selected coordinate is an essential refinement. -/
theorem selected_coordinateRefinementEssential
    {index : ι}
    (hindex : index ∈ result.selected) :
    CorrectedConcreteObservationRefinementEssential
      (z := z)
      α
      (↥(result.selected.erase index) → M)
      (↥result.selected → M)
      (selectedObservationProduct
        obsFamily
        (result.selected.erase index))
      (selectedObservationProduct
        obsFamily
        result.selected)
      f := by

  exact
    observationSelection_paretoOptimal_coordinateRefinementEssential
      (z := z)
      (correctedConcreteObservationSelectionAdditiveCost_monotone
        coordinateWeight)
      result.selected_pareto
      hindex

/-- Compact semantic package for one prescribed realized offset. -/
theorem semantic_package :
    result.selected ⊆ U ∧
      language ∈
        StartRootedCorrectedConcreteTargetClass
          (v := z)
          α
          (↥result.selected → M)
          (selectedObservationProduct obsFamily result.selected)
          f ∧
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

  exact
    ⟨result.selected_subset,
      result.selected_target,
      result.selected_card_eq,
      result.selected_additiveCost_eq,
      result.selected_cost_eq_rank,
      result.selected_pareto,
      result.selected_irredundant⟩

end OffsetSelectionSemanticProperties


section OffsetSelectionProfileUniqueness

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
  {offset : Nat}
variable
  {hOffset :
    offset ∈
      correctedConcreteObservationPositiveAdditiveParetoRankProfileOffsets
        minimumCardinalityResult}

/-- Any two selector results for the same offset have the same
cardinality/additive-weight profile. -/
theorem selected_profile_unique
    (result₀ result₁ :
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
        hOffset) :
    (result₀.selected.card,
        correctedConcreteObservationSelectionAdditiveCost
          coordinateWeight result₀.selected) =
      (result₁.selected.card,
        correctedConcreteObservationSelectionAdditiveCost
          coordinateWeight result₁.selected) := by

  rw [
    result₀.selected_profile_eq,
    result₁.selected_profile_eq
  ]

/-- Any two selector results for the same offset have equal selected-set
cardinalities. -/
theorem selected_card_unique
    (result₀ result₁ :
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
        hOffset) :
    result₀.selected.card =
      result₁.selected.card := by

  exact
    congrArg Prod.fst
      (selected_profile_unique
        result₀
        result₁)

/-- Any two selector results for the same offset have equal additive coordinate
costs. -/
theorem selected_additiveCost_unique
    (result₀ result₁ :
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
        hOffset) :
    correctedConcreteObservationSelectionAdditiveCost
        coordinateWeight result₀.selected =
      correctedConcreteObservationSelectionAdditiveCost
        coordinateWeight result₁.selected := by

  exact
    congrArg Prod.snd
      (selected_profile_unique
        result₀
        result₁)

end OffsetSelectionProfileUniqueness


section OffsetSelectionEndpointProfiles

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
  {offset : Nat}
variable
  {hOffset :
    offset ∈
      correctedConcreteObservationPositiveAdditiveParetoRankProfileOffsets
        minimumCardinalityResult}
variable
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
      hOffset)

/-- Offset zero realizes exactly the minimum-cardinality endpoint profile. -/
theorem selected_profile_eq_minimumCardinality_of_offset_zero
    (hOffsetZero : offset = 0) :
    (result.selected.card,
        correctedConcreteObservationSelectionAdditiveCost
          coordinateWeight result.selected) =
      minimumCardinalityResult.profile := by

  calc
    (result.selected.card,
        correctedConcreteObservationSelectionAdditiveCost
          coordinateWeight result.selected) =
      correctedConcreteObservationPositiveAdditiveParetoProfileOfOffset
        minimumCardinalityResult
        offset :=
          result.selected_profile_eq

    _ =
      correctedConcreteObservationPositiveAdditiveParetoProfileOfOffset
        minimumCardinalityResult
        0 := by
          rw [hOffsetZero]

    _ =
      minimumCardinalityResult.profile := by
          unfold
            correctedConcreteObservationPositiveAdditiveParetoProfileOfOffset

          apply Prod.ext <;> simp

/-- Offset `width` realizes exactly the minimum-additive-cost endpoint
profile. -/
theorem selected_profile_eq_minimumAdditive_of_offset_width
    (hOffsetWidth :
      offset =
        correctedConcreteObservationPositiveAdditiveParetoProfileTradeoffWidth
          minimumCardinalityResult
          minimumAdditiveResult) :
    (result.selected.card,
        correctedConcreteObservationSelectionAdditiveCost
          coordinateWeight result.selected) =
      minimumAdditiveResult.profile := by

  have hEndpointReconstruction :=
    positiveAdditiveParetoProfile_eq_profileOfOffset
      minimumCardinalityResult
      minimumAdditiveResult
      minimumAdditiveResult.profile_mem

  rw [
    positiveAdditiveParetoMinimumAdditiveProfile_offset_eq_width
      minimumCardinalityResult
      minimumAdditiveResult
  ] at hEndpointReconstruction

  calc
    (result.selected.card,
        correctedConcreteObservationSelectionAdditiveCost
          coordinateWeight result.selected) =
      correctedConcreteObservationPositiveAdditiveParetoProfileOfOffset
        minimumCardinalityResult
        offset :=
          result.selected_profile_eq

    _ =
      correctedConcreteObservationPositiveAdditiveParetoProfileOfOffset
        minimumCardinalityResult
        (correctedConcreteObservationPositiveAdditiveParetoProfileTradeoffWidth
          minimumCardinalityResult
          minimumAdditiveResult) := by
            rw [hOffsetWidth]

    _ =
      minimumAdditiveResult.profile :=
        hEndpointReconstruction.symm

end OffsetSelectionEndpointProfiles


section OffsetSelectionCertifiedLearner

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
  {offset : Nat}
variable
  {hOffset :
    offset ∈
      correctedConcreteObservationPositiveAdditiveParetoRankProfileOffsets
        minimumCardinalityResult}
variable
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
      hOffset)

/-- The offset-indexed selected product has its own certified learner and an
exact checked output at minimum certified-description rank. -/
theorem certified_package :
    IdentifiesLanguageFromPositiveData
        (correctedConcreteCertifiedWorkingGrammarHypLanguage
          (selectedObservationProduct obsFamily result.selected)
          f)
        (correctedConcreteCertifiedWorkingGrammarLearner
          hα
          (selectedObservationProduct obsFamily result.selected)
          f)
        language ∧
      language ∈
        CorrectedConcreteCertifiedRankProfileClass
          (α := α)
          (M := ↥result.selected → M)
          (selectedObservationProduct obsFamily result.selected)
          f
          (startRootedTargetCertifiedDescriptionRank
            (v := z)
            hα
            (selectedObservationProduct obsFamily result.selected)
            f
            result.selected_target) ∧
      ∃
        C :
          CorrectedConcreteCertifiedWorkingGrammarHypothesis
            α
            (↥result.selected → M)
            (selectedObservationProduct obsFamily result.selected)
            f,
        C.output.grammar.StringLanguage =
            language ∧
          C.bits.length <=
            correctedConcreteCertifiedRankBitBudget
              (startRootedTargetCertifiedDescriptionRank
                (v := z)
                hα
                (selectedObservationProduct obsFamily result.selected)
                f
                result.selected_target)
              f ∧
          C.canonicalSearch.length <=
            correctedConcreteCertifiedRankSearchBudget
              (startRootedTargetCertifiedDescriptionRank
                (v := z)
                hα
                (selectedObservationProduct obsFamily result.selected)
                f
                result.selected_target)
              f := by

  exact
    ⟨selectedProductCertifiedLearner_identifies_targetClass
        (z := z)
        hα
        obsFamily
        f
        result.selected
        language
        result.selected_target,
      startRootedTarget_mem_minimumCertifiedDescriptionRankProfile
        (v := z)
        hα
        (selectedObservationProduct obsFamily result.selected)
        f
        result.selected_target,
      startRootedTarget_exists_output_at_minimumCertifiedDescriptionRank
        (v := z)
        hα
        (selectedObservationProduct obsFamily result.selected)
        f
        result.selected_target⟩

end OffsetSelectionCertifiedLearner

end CorrectedConcreteObservationPositiveAdditiveParetoRankProfileOffsetSelectionResult


section ParetoRankProfileOffsetSelectorFinalPackage

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

/-- Final offset-indexed actual selector, exact profile, Pareto optimality,
irredundancy, and certified-learning package. -/
theorem
    correctedConcreteCertifiedWorkingGrammar_observationSelectionParetoRankProfileOffsetSelector_package :
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
      ∀ offset : Nat,
        ∀ hOffset :
          offset ∈
            correctedConcreteObservationPositiveAdditiveParetoRankProfileOffsets
              minimumCardinalityResult,
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
          result.selected ∈
              correctedConcreteObservationPositiveAdditiveRankMinimizingParetoSelections
                (z := z)
                obsFamily
                f
                coordinateWeight
                U
                language
                hTarget ∧
            (result.selected.card,
                correctedConcreteObservationSelectionAdditiveCost
                  coordinateWeight result.selected) =
              correctedConcreteObservationPositiveAdditiveParetoProfileOfOffset
                minimumCardinalityResult
                offset ∧
            result.selected ⊆ U ∧
            CorrectedConcreteObservationSelectionParetoOptimal
              (z := z)
              obsFamily
              f
              (correctedConcreteObservationSelectionAdditiveCost
                coordinateWeight)
              U
              language
              result.selected ∧
            correctedConcreteObservationSelectionPositiveAdditiveCost
                coordinateWeight result.selected =
              ambientTargetObservationSelectionPositiveAdditiveMinimumCost
                (z := z)
                obsFamily
                f
                coordinateWeight
                U
                hTarget ∧
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

  intro offset hOffset

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
    ⟨result.selected_mem,
      result.selected_profile_eq,
      result.selected_subset,
      result.selected_pareto,
      result.selected_cost_eq_rank,
      result.selected_irredundant,
      hCertified.1⟩

end ParetoRankProfileOffsetSelectorFinalPackage

end MCFG
