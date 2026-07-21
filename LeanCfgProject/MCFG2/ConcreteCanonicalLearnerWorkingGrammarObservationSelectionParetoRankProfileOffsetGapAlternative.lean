/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG2.ConcreteCanonicalLearnerWorkingGrammarObservationSelectionParetoRankProfileOffsetGapDecision

/-!
# ConcreteCanonicalLearnerWorkingGrammarObservationSelectionParetoRankProfileOffsetGapAlternative.lean

The preceding file adds a finite Boolean decision and a checked missing-offset
certificate to the normalized Pareto-profile spectrum.

This file packages the decision as a proof-carrying alternative.

## Positive branch

If the decision is `true`, the normalized offset spectrum is gap-free.
Every offset through the tradeoff width is realized.

For every such offset, the proof-carrying branch returns an actual selected
observation interface with profile

```text
(c_min + offset, a_max - offset).
```

The selected interface is Pareto optimal, attains the exact positive additive
rank, is inclusion-irredundant, and has its own certified learner identifying
the target.

## Negative branch

If the decision is `false`, the branch returns the canonical least missing
offset certificate.

The returned certificate is

* accepted by the finite Boolean verifier;
* strictly positive;
* strictly below the tradeoff width;
* no larger than every other valid gap certificate; and
* absent from the rank-minimizing Pareto profile set.

Every smaller offset is realized and has an actual certified selected
interface.

Non-gap-freeness also forces

```text
2 ≤ width ≤ positiveAdditiveRank.
```

## Boundary

The decision operates on the already constructed finite semantic offset table.
This is a proof-carrying finite alternative, not yet an effective complexity
classification for an externally presented target language.

No target grammar is supplied to any learner.
No `sorry`, `admit`, or `axiom` is used.
-/

namespace MCFG

universe u v w z


section GapAlternativeResultDefinition

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

/-- A proof-carrying Boolean result for the finite gap-free decision. -/
structure
    CorrectedConcreteObservationPositiveAdditiveParetoRankProfileGapAlternativeResult where

  decision :
    Bool

  decision_eq :
    decision =
      correctedConcreteObservationPositiveAdditiveParetoRankProfileGapFreeDecision
        minimumCardinalityResult
        minimumAdditiveResult

/-- Canonical proof-carrying result of the finite gap-free decision. -/
noncomputable def
    correctedConcreteObservationPositiveAdditiveParetoRankProfileGapAlternativeResult :
    CorrectedConcreteObservationPositiveAdditiveParetoRankProfileGapAlternativeResult
      (z := z)
      obsFamily
      f
      coordinateWeight
      U
      language
      hTarget
      minimumCardinalityResult
      minimumAdditiveResult :=
  ⟨correctedConcreteObservationPositiveAdditiveParetoRankProfileGapFreeDecision
      minimumCardinalityResult
      minimumAdditiveResult,
    rfl⟩

end GapAlternativeResultDefinition


namespace CorrectedConcreteObservationPositiveAdditiveParetoRankProfileGapAlternativeResult

section AlternativeLogicalProperties

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
  (result :
    CorrectedConcreteObservationPositiveAdditiveParetoRankProfileGapAlternativeResult
      (z := z)
      obsFamily
      f
      coordinateWeight
      U
      language
      hTarget
      minimumCardinalityResult
      minimumAdditiveResult)

/-- The positive branch is exactly gap-freeness. -/
theorem decision_eq_true_iff_gapFree :
    result.decision = true ↔
      CorrectedConcreteObservationPositiveAdditiveParetoRankProfileOffsetsGapFree
        minimumCardinalityResult
        minimumAdditiveResult := by

  rw [result.decision_eq]

  exact
    positiveAdditiveParetoRankProfileGapFreeDecision_eq_true_iff
      minimumCardinalityResult
      minimumAdditiveResult

/-- The negative branch is exactly non-gap-freeness. -/
theorem decision_eq_false_iff_not_gapFree :
    result.decision = false ↔
      ¬
        CorrectedConcreteObservationPositiveAdditiveParetoRankProfileOffsetsGapFree
          minimumCardinalityResult
          minimumAdditiveResult := by

  rw [result.decision_eq]

  exact
    positiveAdditiveParetoRankProfileGapFreeDecision_eq_false_iff
      minimumCardinalityResult
      minimumAdditiveResult

/-- The Boolean result always selects one of the two semantic branches. -/
theorem decision_dichotomy :
    (result.decision = true ∧
        CorrectedConcreteObservationPositiveAdditiveParetoRankProfileOffsetsGapFree
          minimumCardinalityResult
          minimumAdditiveResult) ∨
      (result.decision = false ∧
        ¬
          CorrectedConcreteObservationPositiveAdditiveParetoRankProfileOffsetsGapFree
            minimumCardinalityResult
            minimumAdditiveResult) := by

  cases hDecision : result.decision with

  | false =>
      exact
        Or.inr
          ⟨hDecision,
            (result.decision_eq_false_iff_not_gapFree).mp
              hDecision⟩

  | true =>
      exact
        Or.inl
          ⟨hDecision,
            (result.decision_eq_true_iff_gapFree).mp
              hDecision⟩

end AlternativeLogicalProperties


section NegativeBranchCertificate

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
  (result :
    CorrectedConcreteObservationPositiveAdditiveParetoRankProfileGapAlternativeResult
      (z := z)
      obsFamily
      f
      coordinateWeight
      U
      language
      hTarget
      minimumCardinalityResult
      minimumAdditiveResult)

/-- Canonical least gap certificate returned by the negative decision branch. -/
noncomputable def negativeCertificate
    (hDecisionFalse : result.decision = false) :
    CorrectedConcreteObservationPositiveAdditiveParetoRankProfileOffsetGapCertificate
      minimumCardinalityResult
      minimumAdditiveResult :=
  correctedConcreteObservationPositiveAdditiveParetoRankProfileFirstGapCertificate
    minimumCardinalityResult
    minimumAdditiveResult
    ((result.decision_eq_false_iff_not_gapFree).mp
      hDecisionFalse)

/-- The negative-branch certificate is accepted by the finite verifier. -/
theorem negativeCertificate_verifier_eq_true
    (hDecisionFalse : result.decision = false) :
    correctedConcreteObservationPositiveAdditiveParetoRankProfileOffsetGapVerifier
          minimumCardinalityResult
          minimumAdditiveResult
          (result.negativeCertificate hDecisionFalse).offset =
        true := by

  exact
    (result.negativeCertificate hDecisionFalse).verifier_eq_true

/-- The negative-branch certificate is strictly positive. -/
theorem negativeCertificate_pos
    (hDecisionFalse : result.decision = false) :
    0 <
      (result.negativeCertificate hDecisionFalse).offset := by

  exact
    positiveAdditiveParetoRankProfileFirstGapCertificate_pos
      minimumCardinalityResult
      minimumAdditiveResult
      ((result.decision_eq_false_iff_not_gapFree).mp
        hDecisionFalse)

/-- The negative-branch certificate is strictly below the tradeoff width. -/
theorem negativeCertificate_lt_width
    (hDecisionFalse : result.decision = false) :
    (result.negativeCertificate hDecisionFalse).offset <
      correctedConcreteObservationPositiveAdditiveParetoProfileTradeoffWidth
        minimumCardinalityResult
        minimumAdditiveResult := by

  exact
    positiveAdditiveParetoRankProfileFirstGapCertificate_lt_width
      minimumCardinalityResult
      minimumAdditiveResult
      ((result.decision_eq_false_iff_not_gapFree).mp
        hDecisionFalse)

/-- The negative-branch certificate is no larger than every valid gap
certificate. -/
theorem negativeCertificate_le
    (hDecisionFalse : result.decision = false)
    (other :
      CorrectedConcreteObservationPositiveAdditiveParetoRankProfileOffsetGapCertificate
        minimumCardinalityResult
        minimumAdditiveResult) :
    (result.negativeCertificate hDecisionFalse).offset <=
      other.offset := by

  exact
    positiveAdditiveParetoRankProfileFirstGapCertificate_le
      minimumCardinalityResult
      minimumAdditiveResult
      ((result.decision_eq_false_iff_not_gapFree).mp
        hDecisionFalse)
      other

/-- The affine profile at the returned missing offset is absent from the finite
rank-minimizing profile set. -/
theorem negativeCertificate_profile_not_mem
    (hDecisionFalse : result.decision = false) :
    correctedConcreteObservationPositiveAdditiveParetoProfileOfOffset
          minimumCardinalityResult
          (result.negativeCertificate hDecisionFalse).offset ∉
      correctedConcreteObservationPositiveAdditiveRankMinimizingParetoProfiles
        (z := z)
        obsFamily
        f
        coordinateWeight
        U
        language
        hTarget := by

  exact
    (result.negativeCertificate hDecisionFalse).profile_not_mem

/-- Every smaller offset is realized. -/
theorem offset_mem_of_lt_negativeCertificate
    (hDecisionFalse : result.decision = false)
    {offset : Nat}
    (hOffsetLt :
      offset <
        (result.negativeCertificate hDecisionFalse).offset) :
    offset ∈
      correctedConcreteObservationPositiveAdditiveParetoRankProfileOffsets
        minimumCardinalityResult := by

  exact
    positiveAdditiveParetoRankProfileOffset_mem_of_lt_firstGap
      minimumCardinalityResult
      minimumAdditiveResult
      ((result.decision_eq_false_iff_not_gapFree).mp
        hDecisionFalse)
      hOffsetLt

/-- The negative branch forces width at least two. -/
theorem two_le_width_of_decision_false
    (hDecisionFalse : result.decision = false) :
    2 <=
      correctedConcreteObservationPositiveAdditiveParetoProfileTradeoffWidth
        minimumCardinalityResult
        minimumAdditiveResult := by

  exact
    two_le_positiveAdditiveParetoProfileTradeoffWidth
      minimumCardinalityResult
      minimumAdditiveResult
      ((result.decision_eq_false_iff_not_gapFree).mp
        hDecisionFalse)

/-- The negative branch forces positive additive rank at least two. -/
theorem two_le_rank_of_decision_false
    (hDecisionFalse : result.decision = false) :
    2 <=
      ambientTargetObservationSelectionPositiveAdditiveMinimumCost
        (z := z)
        obsFamily
        f
        coordinateWeight
        U
        hTarget := by

  exact
    two_le_ambientTargetPositiveAdditiveRank_of_not_gapFree
      minimumCardinalityResult
      minimumAdditiveResult
      ((result.decision_eq_false_iff_not_gapFree).mp
        hDecisionFalse)

end NegativeBranchCertificate


section PositiveBranchCertifiedSelectors

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
  (result :
    CorrectedConcreteObservationPositiveAdditiveParetoRankProfileGapAlternativeResult
      (z := z)
      obsFamily
      f
      coordinateWeight
      U
      language
      hTarget
      minimumCardinalityResult
      minimumAdditiveResult)

/-- In the positive branch, every offset through the width has an actual
Pareto-optimal, exact-rank, irredundant selected interface with a certified
learner. -/
theorem positiveBranch_offset_exists_certifiedSelection
    (hDecisionTrue : result.decision = true)
    {offset : Nat}
    (hOffsetLe :
      offset <=
        correctedConcreteObservationPositiveAdditiveParetoProfileTradeoffWidth
          minimumCardinalityResult
          minimumAdditiveResult) :
    ∃
      (hOffset :
        offset ∈
          correctedConcreteObservationPositiveAdditiveParetoRankProfileOffsets
            minimumCardinalityResult)
      (selection :
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
      selection.selected.card =
          minimumCardinalityResult.profile.1 + offset ∧
        correctedConcreteObservationSelectionAdditiveCost
            coordinateWeight selection.selected =
          minimumCardinalityResult.profile.2 - offset ∧
        correctedConcreteObservationSelectionPositiveAdditiveCost
            coordinateWeight selection.selected =
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
          selection.selected ∧
        CorrectedConcreteObservationSelectionIrredundant
          (z := z)
          α
          ι
          M
          obsFamily
          f
          language
          selection.selected ∧
        IdentifiesLanguageFromPositiveData
          (correctedConcreteCertifiedWorkingGrammarHypLanguage
            (selectedObservationProduct obsFamily selection.selected)
            f)
          (correctedConcreteCertifiedWorkingGrammarLearner
            hα
            (selectedObservationProduct obsFamily selection.selected)
            f)
          language := by

  have hGapFree :=
    (result.decision_eq_true_iff_gapFree).mp
      hDecisionTrue

  let hOffset :=
    hGapFree
      offset
      hOffsetLe

  let selection :=
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
      selection

  exact
    ⟨hOffset,
      selection,
      selection.selected_card_eq,
      selection.selected_additiveCost_eq,
      selection.selected_cost_eq_rank,
      selection.selected_pareto,
      selection.selected_irredundant,
      hCertified.1⟩

end PositiveBranchCertifiedSelectors


section NegativeBranchCertifiedPrefix

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
  (result :
    CorrectedConcreteObservationPositiveAdditiveParetoRankProfileGapAlternativeResult
      (z := z)
      obsFamily
      f
      coordinateWeight
      U
      language
      hTarget
      minimumCardinalityResult
      minimumAdditiveResult)

/-- In the negative branch, every offset below the returned least certificate
has an actual Pareto-optimal, exact-rank, irredundant selected interface with a
certified learner. -/
theorem negativeBranch_prefix_exists_certifiedSelection
    (hDecisionFalse : result.decision = false)
    {offset : Nat}
    (hOffsetLt :
      offset <
        (result.negativeCertificate hDecisionFalse).offset) :
    ∃
      (hOffset :
        offset ∈
          correctedConcreteObservationPositiveAdditiveParetoRankProfileOffsets
            minimumCardinalityResult)
      (selection :
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
      selection.selected.card =
          minimumCardinalityResult.profile.1 + offset ∧
        correctedConcreteObservationSelectionAdditiveCost
            coordinateWeight selection.selected =
          minimumCardinalityResult.profile.2 - offset ∧
        correctedConcreteObservationSelectionPositiveAdditiveCost
            coordinateWeight selection.selected =
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
          selection.selected ∧
        CorrectedConcreteObservationSelectionIrredundant
          (z := z)
          α
          ι
          M
          obsFamily
          f
          language
          selection.selected ∧
        IdentifiesLanguageFromPositiveData
          (correctedConcreteCertifiedWorkingGrammarHypLanguage
            (selectedObservationProduct obsFamily selection.selected)
            f)
          (correctedConcreteCertifiedWorkingGrammarLearner
            hα
            (selectedObservationProduct obsFamily selection.selected)
            f)
          language := by

  have hOffset :=
    result.offset_mem_of_lt_negativeCertificate
      hDecisionFalse
      hOffsetLt

  let selection :=
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
      selection

  exact
    ⟨hOffset,
      selection,
      selection.selected_card_eq,
      selection.selected_additiveCost_eq,
      selection.selected_cost_eq_rank,
      selection.selected_pareto,
      selection.selected_irredundant,
      hCertified.1⟩

end NegativeBranchCertifiedPrefix


section AlternativeFinalPackage

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

/-- Final proof-carrying gap-free/least-gap alternative package. -/
theorem
    correctedConcreteCertifiedWorkingGrammar_observationSelectionParetoRankProfileOffsetGapAlternative_package :
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
      let result :=
        correctedConcreteObservationPositiveAdditiveParetoRankProfileGapAlternativeResult
          (z := z)
          obsFamily
          f
          coordinateWeight
          U
          language
          hTarget
          minimumCardinalityResult
          minimumAdditiveResult
      (result.decision = true ↔
        CorrectedConcreteObservationPositiveAdditiveParetoRankProfileOffsetsGapFree
          minimumCardinalityResult
          minimumAdditiveResult) ∧
        (result.decision = false ↔
          ¬
            CorrectedConcreteObservationPositiveAdditiveParetoRankProfileOffsetsGapFree
              minimumCardinalityResult
              minimumAdditiveResult) ∧
        ((result.decision = true ∧
            CorrectedConcreteObservationPositiveAdditiveParetoRankProfileOffsetsGapFree
              minimumCardinalityResult
              minimumAdditiveResult) ∨
          (result.decision = false ∧
            ¬
              CorrectedConcreteObservationPositiveAdditiveParetoRankProfileOffsetsGapFree
                minimumCardinalityResult
                minimumAdditiveResult)) ∧
        (∀ hDecisionFalse : result.decision = false,
          let certificate :=
            result.negativeCertificate hDecisionFalse
          certificate.offset_mem ∧
            0 < certificate.offset ∧
            certificate.offset <
              correctedConcreteObservationPositiveAdditiveParetoProfileTradeoffWidth
                minimumCardinalityResult
                minimumAdditiveResult ∧
            2 <=
              ambientTargetObservationSelectionPositiveAdditiveMinimumCost
                (z := z)
                obsFamily
                f
                coordinateWeight
                U
                hTarget ∧
            ∀ other :
              CorrectedConcreteObservationPositiveAdditiveParetoRankProfileOffsetGapCertificate
                minimumCardinalityResult
                minimumAdditiveResult,
              certificate.offset <= other.offset) := by

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

  let result :=
    correctedConcreteObservationPositiveAdditiveParetoRankProfileGapAlternativeResult
      (z := z)
      obsFamily
      f
      coordinateWeight
      U
      language
      hTarget
      minimumCardinalityResult
      minimumAdditiveResult

  exact
    ⟨result.decision_eq_true_iff_gapFree,
      result.decision_eq_false_iff_not_gapFree,
      result.decision_dichotomy,
      fun hDecisionFalse =>
        ⟨(result.negativeCertificate hDecisionFalse).offset_mem,
          result.negativeCertificate_pos hDecisionFalse,
          result.negativeCertificate_lt_width hDecisionFalse,
          result.two_le_rank_of_decision_false hDecisionFalse,
          fun other =>
            result.negativeCertificate_le
              hDecisionFalse
              other⟩⟩

end AlternativeFinalPackage

end CorrectedConcreteObservationPositiveAdditiveParetoRankProfileGapAlternativeResult

end MCFG
