/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG.ConcreteCanonicalLearnerWorkingGrammarObservationSelectionParetoRankProfileOffsetFirstGapBounds

/-!
# ConcreteCanonicalLearnerWorkingGrammarObservationSelectionParetoRankProfileOffsetGapDecision.lean

This file adds a finite Boolean decision and certificate layer to the
previously constructed normalized Pareto-profile offset spectrum.

The semantic offset table itself is still noncomputable.  The results below
therefore establish correctness of finite checking relative to that table; no
polynomial-time external presentation result is claimed.

The main objects are:

* a Boolean gap-free decision;
* a Boolean verifier for proposed missing offsets;
* the finite set of verifier-accepted offsets;
* a checked gap certificate; and
* the canonical least certificate given by the first gap.

No target grammar is supplied to any learner.
No `sorry`, `admit`, or `axiom` is used.
-/

namespace MCFG

universe u v w z


section Definitions

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

/-- Boolean decision for gap-freeness of the finite realized offset table. -/
noncomputable def
    correctedConcreteObservationPositiveAdditiveParetoRankProfileGapFreeDecision
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
    Bool :=
  decide
    (correctedConcreteObservationPositiveAdditiveParetoRankProfileOffsetGaps
        minimumCardinalityResult
        minimumAdditiveResult =
      ∅)

/-- Boolean verifier for a proposed missing normalized offset. -/
noncomputable def
    correctedConcreteObservationPositiveAdditiveParetoRankProfileOffsetGapVerifier
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
    (offset : Nat) :
    Bool :=
  decide
    (offset ∈
      correctedConcreteObservationPositiveAdditiveParetoRankProfileOffsetGaps
        minimumCardinalityResult
        minimumAdditiveResult)

/-- Candidate offsets accepted by the Boolean verifier. -/
noncomputable def
    correctedConcreteObservationPositiveAdditiveParetoRankProfileVerifiedGapOffsets
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
  (Finset.range
      (correctedConcreteObservationPositiveAdditiveParetoProfileTradeoffWidth
          minimumCardinalityResult
          minimumAdditiveResult +
        1)).filter
    (fun offset =>
      correctedConcreteObservationPositiveAdditiveParetoRankProfileOffsetGapVerifier
          minimumCardinalityResult
          minimumAdditiveResult
          offset =
        true)

/-- Checked certificate that one normalized offset is missing. -/
structure
    CorrectedConcreteObservationPositiveAdditiveParetoRankProfileOffsetGapCertificate
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
        hTarget) where

  offset :
    Nat

  offset_mem :
    offset ∈
      correctedConcreteObservationPositiveAdditiveParetoRankProfileOffsetGaps
        minimumCardinalityResult
        minimumAdditiveResult

end Definitions


section DecisionCorrectness

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

/-- Correctness of the positive Boolean decision. -/
theorem positiveAdditiveParetoRankProfileGapFreeDecision_eq_true_iff :
    correctedConcreteObservationPositiveAdditiveParetoRankProfileGapFreeDecision
          minimumCardinalityResult
          minimumAdditiveResult =
        true ↔
      CorrectedConcreteObservationPositiveAdditiveParetoRankProfileOffsetsGapFree
        minimumCardinalityResult
        minimumAdditiveResult := by

  unfold
    correctedConcreteObservationPositiveAdditiveParetoRankProfileGapFreeDecision

  rw [decide_eq_true_eq]

  exact
    (positiveAdditiveParetoRankProfileOffsetsGapFree_iff_gaps_eq_empty
      minimumCardinalityResult
      minimumAdditiveResult).symm

/-- Correctness of the negative Boolean decision. -/
theorem positiveAdditiveParetoRankProfileGapFreeDecision_eq_false_iff :
    correctedConcreteObservationPositiveAdditiveParetoRankProfileGapFreeDecision
          minimumCardinalityResult
          minimumAdditiveResult =
        false ↔
      ¬
        CorrectedConcreteObservationPositiveAdditiveParetoRankProfileOffsetsGapFree
          minimumCardinalityResult
          minimumAdditiveResult := by

  constructor

  · intro hFalse hGapFree

    have hTrue :=
      (positiveAdditiveParetoRankProfileGapFreeDecision_eq_true_iff
        minimumCardinalityResult
        minimumAdditiveResult).mpr
        hGapFree

    rw [hFalse] at hTrue

    simp at hTrue

  · intro hNotGapFree

    cases hDecision :
      correctedConcreteObservationPositiveAdditiveParetoRankProfileGapFreeDecision
        minimumCardinalityResult
        minimumAdditiveResult

    · exact hDecision

    · exfalso

      exact
        hNotGapFree
          ((positiveAdditiveParetoRankProfileGapFreeDecision_eq_true_iff
            minimumCardinalityResult
            minimumAdditiveResult).mp
            hDecision)

/-- Correctness of the Boolean gap verifier. -/
theorem positiveAdditiveParetoRankProfileOffsetGapVerifier_eq_true_iff
    {offset : Nat} :
    correctedConcreteObservationPositiveAdditiveParetoRankProfileOffsetGapVerifier
          minimumCardinalityResult
          minimumAdditiveResult
          offset =
        true ↔
      offset ∈
        correctedConcreteObservationPositiveAdditiveParetoRankProfileOffsetGaps
          minimumCardinalityResult
          minimumAdditiveResult := by

  unfold
    correctedConcreteObservationPositiveAdditiveParetoRankProfileOffsetGapVerifier

  exact
    decide_eq_true_eq

/-- Expanded correctness theorem for a proposed missing offset. -/
theorem positiveAdditiveParetoRankProfileOffsetGapVerifier_eq_true_iff_le_and_missing
    {offset : Nat} :
    correctedConcreteObservationPositiveAdditiveParetoRankProfileOffsetGapVerifier
          minimumCardinalityResult
          minimumAdditiveResult
          offset =
        true ↔
      offset <=
          correctedConcreteObservationPositiveAdditiveParetoProfileTradeoffWidth
            minimumCardinalityResult
            minimumAdditiveResult ∧
        offset ∉
          correctedConcreteObservationPositiveAdditiveParetoRankProfileOffsets
            minimumCardinalityResult := by

  rw [
    positiveAdditiveParetoRankProfileOffsetGapVerifier_eq_true_iff
      minimumCardinalityResult
      minimumAdditiveResult,
    mem_correctedConcreteObservationPositiveAdditiveParetoRankProfileOffsetGaps_iff
      minimumCardinalityResult
      minimumAdditiveResult
  ]

/-- Verifier rejection is exactly failure of gap membership. -/
theorem positiveAdditiveParetoRankProfileOffsetGapVerifier_eq_false_iff
    {offset : Nat} :
    correctedConcreteObservationPositiveAdditiveParetoRankProfileOffsetGapVerifier
          minimumCardinalityResult
          minimumAdditiveResult
          offset =
        false ↔
      offset ∉
        correctedConcreteObservationPositiveAdditiveParetoRankProfileOffsetGaps
          minimumCardinalityResult
          minimumAdditiveResult := by

  constructor

  · intro hFalse hGap

    have hTrue :=
      (positiveAdditiveParetoRankProfileOffsetGapVerifier_eq_true_iff
        minimumCardinalityResult
        minimumAdditiveResult).mpr
        hGap

    rw [hFalse] at hTrue

    simp at hTrue

  · intro hNotGap

    cases hVerifier :
      correctedConcreteObservationPositiveAdditiveParetoRankProfileOffsetGapVerifier
        minimumCardinalityResult
        minimumAdditiveResult
        offset

    · exact hVerifier

    · exfalso

      exact
        hNotGap
          ((positiveAdditiveParetoRankProfileOffsetGapVerifier_eq_true_iff
            minimumCardinalityResult
            minimumAdditiveResult).mp
            hVerifier)

end DecisionCorrectness


section VerifiedCandidates

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

/-- The verifier-accepted candidate set is exactly the finite gap set. -/
theorem
    correctedConcreteObservationPositiveAdditiveParetoRankProfileVerifiedGapOffsets_eq_gaps :
    correctedConcreteObservationPositiveAdditiveParetoRankProfileVerifiedGapOffsets
        minimumCardinalityResult
        minimumAdditiveResult =
      correctedConcreteObservationPositiveAdditiveParetoRankProfileOffsetGaps
        minimumCardinalityResult
        minimumAdditiveResult := by

  ext offset

  constructor

  · intro hVerified

    have hFilter :=
      Finset.mem_filter.mp
        hVerified

    exact
      (positiveAdditiveParetoRankProfileOffsetGapVerifier_eq_true_iff
        minimumCardinalityResult
        minimumAdditiveResult).mp
        hFilter.2

  · intro hGap

    exact
      Finset.mem_filter.mpr
        ⟨correctedConcreteObservationPositiveAdditiveParetoRankProfileOffsetGaps_subset_range
            minimumCardinalityResult
            minimumAdditiveResult
            hGap,
          (positiveAdditiveParetoRankProfileOffsetGapVerifier_eq_true_iff
            minimumCardinalityResult
            minimumAdditiveResult).mpr
            hGap⟩

/-- The number of accepted candidates is exactly the gap count. -/
theorem
    correctedConcreteObservationPositiveAdditiveParetoRankProfileVerifiedGapOffsets_card_eq_gapCount :
    (correctedConcreteObservationPositiveAdditiveParetoRankProfileVerifiedGapOffsets
        minimumCardinalityResult
        minimumAdditiveResult).card =
      correctedConcreteObservationPositiveAdditiveParetoRankProfileOffsetGapCount
        minimumCardinalityResult
        minimumAdditiveResult := by

  rw [
    correctedConcreteObservationPositiveAdditiveParetoRankProfileVerifiedGapOffsets_eq_gaps
      minimumCardinalityResult
      minimumAdditiveResult
  ]

  rfl

/-- Exact finite accepted-candidate defect formula. -/
theorem
    positiveAdditiveParetoRankProfiles_card_add_verifiedGapOffsets_card_eq_width_add_one :
    (correctedConcreteObservationPositiveAdditiveRankMinimizingParetoProfiles
          (z := z)
          obsFamily
          f
          coordinateWeight
          U
          language
          hTarget).card +
        (correctedConcreteObservationPositiveAdditiveParetoRankProfileVerifiedGapOffsets
          minimumCardinalityResult
          minimumAdditiveResult).card =
      correctedConcreteObservationPositiveAdditiveParetoProfileTradeoffWidth
          minimumCardinalityResult
          minimumAdditiveResult +
        1 := by

  rw [
    correctedConcreteObservationPositiveAdditiveParetoRankProfileVerifiedGapOffsets_card_eq_gapCount
      minimumCardinalityResult
      minimumAdditiveResult
  ]

  exact
    positiveAdditiveParetoRankProfiles_card_add_gapCount_eq_width_add_one
      minimumCardinalityResult
      minimumAdditiveResult

end VerifiedCandidates


section CertificateCorrectness

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

/-- Gap certificates exist exactly when the spectrum is not gap-free. -/
theorem
    positiveAdditiveParetoRankProfileOffsetGapCertificate_nonempty_iff_not_gapFree :
    Nonempty
        (CorrectedConcreteObservationPositiveAdditiveParetoRankProfileOffsetGapCertificate
          minimumCardinalityResult
          minimumAdditiveResult) ↔
      ¬
        CorrectedConcreteObservationPositiveAdditiveParetoRankProfileOffsetsGapFree
          minimumCardinalityResult
          minimumAdditiveResult := by

  constructor

  · intro hCertificate

    rcases hCertificate with
      ⟨certificate⟩

    exact
      (not_positiveAdditiveParetoRankProfileOffsetsGapFree_iff_gaps_nonempty
        minimumCardinalityResult
        minimumAdditiveResult).mpr
        ⟨certificate.offset,
          certificate.offset_mem⟩

  · intro hNotGapFree

    rcases
        (not_positiveAdditiveParetoRankProfileOffsetsGapFree_iff_gaps_nonempty
          minimumCardinalityResult
          minimumAdditiveResult).mp
          hNotGapFree with
      ⟨offset, hGap⟩

    exact
      ⟨⟨offset,
          hGap⟩⟩

/-- Every certificate is accepted by the Boolean verifier. -/
theorem
    CorrectedConcreteObservationPositiveAdditiveParetoRankProfileOffsetGapCertificate.verifier_eq_true
    (certificate :
      CorrectedConcreteObservationPositiveAdditiveParetoRankProfileOffsetGapCertificate
        minimumCardinalityResult
        minimumAdditiveResult) :
    correctedConcreteObservationPositiveAdditiveParetoRankProfileOffsetGapVerifier
          minimumCardinalityResult
          minimumAdditiveResult
          certificate.offset =
        true := by

  exact
    (positiveAdditiveParetoRankProfileOffsetGapVerifier_eq_true_iff
      minimumCardinalityResult
      minimumAdditiveResult).mpr
      certificate.offset_mem

/-- A certified gap offset has no rank-minimizing Pareto profile. -/
theorem
    CorrectedConcreteObservationPositiveAdditiveParetoRankProfileOffsetGapCertificate.profile_not_mem
    (certificate :
      CorrectedConcreteObservationPositiveAdditiveParetoRankProfileOffsetGapCertificate
        minimumCardinalityResult
        minimumAdditiveResult) :
    correctedConcreteObservationPositiveAdditiveParetoProfileOfOffset
          minimumCardinalityResult
          certificate.offset ∉
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
      certificate.offset ∈
        correctedConcreteObservationPositiveAdditiveParetoRankProfileOffsets
          minimumCardinalityResult := by

    apply
      (mem_correctedConcreteObservationPositiveAdditiveParetoRankProfileOffsets_iff
        minimumCardinalityResult).mpr

    exact
      ⟨correctedConcreteObservationPositiveAdditiveParetoProfileOfOffset
          minimumCardinalityResult
          certificate.offset,
        hProfile,
        positiveAdditiveParetoProfileOfOffset_offset_eq
          minimumCardinalityResult
          certificate.offset⟩

  exact
    ((mem_correctedConcreteObservationPositiveAdditiveParetoRankProfileOffsetGaps_iff
      minimumCardinalityResult
      minimumAdditiveResult).mp
      certificate.offset_mem).2
      hOffsetMem

end CertificateCorrectness


section CanonicalCertificate

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

/-- Canonical certificate given by the least missing offset. -/
noncomputable def
    correctedConcreteObservationPositiveAdditiveParetoRankProfileFirstGapCertificate :
    CorrectedConcreteObservationPositiveAdditiveParetoRankProfileOffsetGapCertificate
      minimumCardinalityResult
      minimumAdditiveResult :=
  ⟨correctedConcreteObservationPositiveAdditiveParetoRankProfileFirstGap
      minimumCardinalityResult
      minimumAdditiveResult
      hNotGapFree,
    positiveAdditiveParetoRankProfileFirstGap_mem
      minimumCardinalityResult
      minimumAdditiveResult
      hNotGapFree⟩

/-- The canonical certificate is strictly positive. -/
theorem positiveAdditiveParetoRankProfileFirstGapCertificate_pos :
    0 <
      (correctedConcreteObservationPositiveAdditiveParetoRankProfileFirstGapCertificate
        minimumCardinalityResult
        minimumAdditiveResult
        hNotGapFree).offset := by

  exact
    positiveAdditiveParetoRankProfileFirstGap_pos
      minimumCardinalityResult
      minimumAdditiveResult
      hNotGapFree

/-- The canonical certificate is strictly below width. -/
theorem positiveAdditiveParetoRankProfileFirstGapCertificate_lt_width :
    (correctedConcreteObservationPositiveAdditiveParetoRankProfileFirstGapCertificate
          minimumCardinalityResult
          minimumAdditiveResult
          hNotGapFree).offset <
      correctedConcreteObservationPositiveAdditiveParetoProfileTradeoffWidth
        minimumCardinalityResult
        minimumAdditiveResult := by

  exact
    positiveAdditiveParetoRankProfileFirstGap_lt_width
      minimumCardinalityResult
      minimumAdditiveResult
      hNotGapFree

/-- The canonical certificate is no larger than any other certificate. -/
theorem positiveAdditiveParetoRankProfileFirstGapCertificate_le
    (certificate :
      CorrectedConcreteObservationPositiveAdditiveParetoRankProfileOffsetGapCertificate
        minimumCardinalityResult
        minimumAdditiveResult) :
    (correctedConcreteObservationPositiveAdditiveParetoRankProfileFirstGapCertificate
          minimumCardinalityResult
          minimumAdditiveResult
          hNotGapFree).offset <=
      certificate.offset := by

  exact
    positiveAdditiveParetoRankProfileFirstGap_le
      minimumCardinalityResult
      minimumAdditiveResult
      hNotGapFree
      certificate.offset_mem

/-- Every smaller offset is rejected by the gap verifier. -/
theorem positiveAdditiveParetoRankProfileOffsetGapVerifier_eq_false_of_lt_firstCertificate
    {offset : Nat}
    (hOffsetLt :
      offset <
        (correctedConcreteObservationPositiveAdditiveParetoRankProfileFirstGapCertificate
          minimumCardinalityResult
          minimumAdditiveResult
          hNotGapFree).offset) :
    correctedConcreteObservationPositiveAdditiveParetoRankProfileOffsetGapVerifier
          minimumCardinalityResult
          minimumAdditiveResult
          offset =
        false := by

  apply
    (positiveAdditiveParetoRankProfileOffsetGapVerifier_eq_false_iff
      minimumCardinalityResult
      minimumAdditiveResult).mpr

  intro hGap

  have hFirstLe :=
    positiveAdditiveParetoRankProfileFirstGapCertificate_le
      minimumCardinalityResult
      minimumAdditiveResult
      hNotGapFree
      ⟨offset,
        hGap⟩

  omega

end CanonicalCertificate


section CertifiedPrefix

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

/-- Every offset below the canonical certificate has a certified selected
interface. -/
theorem
    positiveAdditiveParetoRankProfileOffset_beforeFirstGapCertificate_exists_certifiedSelection
    {offset : Nat}
    (hOffsetLt :
      offset <
        (correctedConcreteObservationPositiveAdditiveParetoRankProfileFirstGapCertificate
          minimumCardinalityResult
          minimumAdditiveResult
          hNotGapFree).offset) :
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
        IdentifiesLanguageFromPositiveData
          (correctedConcreteCertifiedWorkingGrammarHypLanguage
            (selectedObservationProduct obsFamily result.selected)
            f)
          (correctedConcreteCertifiedWorkingGrammarLearner
            hα
            (selectedObservationProduct obsFamily result.selected)
            f)
          language := by

  have hOffsetMem :=
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
      hOffsetMem

  have hCertified :=
    CorrectedConcreteObservationPositiveAdditiveParetoRankProfileOffsetSelectionResult.certified_package
      (z := z)
      hα
      result

  exact
    ⟨hOffsetMem,
      result,
      result.selected_card_eq,
      result.selected_additiveCost_eq,
      result.selected_cost_eq_rank,
      hCertified.1⟩

end CertifiedPrefix


section FinalPackage

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

/-- Final Boolean decision, verifier, exact accepted-candidate count, and
canonical minimal certificate package. -/
theorem
    correctedConcreteCertifiedWorkingGrammar_observationSelectionParetoRankProfileOffsetGapDecision_package :
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
      let decision :=
        correctedConcreteObservationPositiveAdditiveParetoRankProfileGapFreeDecision
          minimumCardinalityResult
          minimumAdditiveResult
      let verified :=
        correctedConcreteObservationPositiveAdditiveParetoRankProfileVerifiedGapOffsets
          minimumCardinalityResult
          minimumAdditiveResult
      (decision = true ↔
        CorrectedConcreteObservationPositiveAdditiveParetoRankProfileOffsetsGapFree
          minimumCardinalityResult
          minimumAdditiveResult) ∧
        (decision = false ↔
          ¬
            CorrectedConcreteObservationPositiveAdditiveParetoRankProfileOffsetsGapFree
              minimumCardinalityResult
              minimumAdditiveResult) ∧
        verified =
          correctedConcreteObservationPositiveAdditiveParetoRankProfileOffsetGaps
            minimumCardinalityResult
            minimumAdditiveResult ∧
        (correctedConcreteObservationPositiveAdditiveRankMinimizingParetoProfiles
              (z := z)
              obsFamily
              f
              coordinateWeight
              U
              language
              hTarget).card +
            verified.card =
          correctedConcreteObservationPositiveAdditiveParetoProfileTradeoffWidth
              minimumCardinalityResult
              minimumAdditiveResult +
            1 ∧
        (Nonempty
            (CorrectedConcreteObservationPositiveAdditiveParetoRankProfileOffsetGapCertificate
              minimumCardinalityResult
              minimumAdditiveResult) ↔
          decision = false) := by

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

  let decision :=
    correctedConcreteObservationPositiveAdditiveParetoRankProfileGapFreeDecision
      minimumCardinalityResult
      minimumAdditiveResult

  let verified :=
    correctedConcreteObservationPositiveAdditiveParetoRankProfileVerifiedGapOffsets
      minimumCardinalityResult
      minimumAdditiveResult

  refine
    ⟨positiveAdditiveParetoRankProfileGapFreeDecision_eq_true_iff
        minimumCardinalityResult
        minimumAdditiveResult,
      positiveAdditiveParetoRankProfileGapFreeDecision_eq_false_iff
        minimumCardinalityResult
        minimumAdditiveResult,
      correctedConcreteObservationPositiveAdditiveParetoRankProfileVerifiedGapOffsets_eq_gaps
        minimumCardinalityResult
        minimumAdditiveResult,
      positiveAdditiveParetoRankProfiles_card_add_verifiedGapOffsets_card_eq_width_add_one
        minimumCardinalityResult
        minimumAdditiveResult,
      ?_⟩

  rw [
    positiveAdditiveParetoRankProfileGapFreeDecision_eq_false_iff
      minimumCardinalityResult
      minimumAdditiveResult
  ]

  exact
    positiveAdditiveParetoRankProfileOffsetGapCertificate_nonempty_iff_not_gapFree
      minimumCardinalityResult
      minimumAdditiveResult

end FinalPackage

end MCFG
