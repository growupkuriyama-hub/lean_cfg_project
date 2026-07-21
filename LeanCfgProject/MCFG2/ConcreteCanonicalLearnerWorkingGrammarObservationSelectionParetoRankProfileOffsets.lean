/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG.ConcreteCanonicalLearnerWorkingGrammarObservationSelectionParetoRankProfileWidth

/-!
# ConcreteCanonicalLearnerWorkingGrammarObservationSelectionParetoRankProfileOffsets.lean

The preceding file defines the exact tradeoff width of the finite
positive-additive-rank-minimizing Pareto profile set.

This file normalizes that profile set to finite natural-number offsets.

## Normalized offsets

Fix the minimum-cardinality endpoint

```text
(c_min, a_max).
```

For every rank-minimizing profile `(c,a)`, define its cardinality offset by

```text
d = c - c_min.
```

The preceding interval theorem implies

```text
0 ≤ d ≤ width.
```

The finite set of all realized offsets is

```lean
correctedConcreteObservationPositiveAdditiveParetoRankProfileOffsets.
```

## Exact profile reconstruction

Every rank-minimizing profile is reconstructed from its offset by

```text
(c,a) = (c_min + d, a_max - d).
```

Consequently, two rank-minimizing profiles having the same offset are equal.

Thus the two-dimensional Pareto profile set is faithfully normalized to a
finite subset of

```text
{0,1,...,width}.
```

No claim is made that every intermediate offset is realized.

## Endpoint offsets

The minimum-cardinality endpoint has offset zero.
The minimum-additive endpoint has offset `width`.

Therefore both `0` and `width` belong to the realized offset set.

The offset set is `{0}` exactly when `width = 0`, equivalently exactly when the
rank-minimizing profile is rigid.

## Certified offset witnesses

Every realized offset has an actual selected-product witness whose profile is

```text
(c_min + d, a_max - d).
```

The selected product is Pareto optimal, attains the exact positive additive
rank, and has its own certified learner identifying the target.

The actual Pareto-rank selector from the preceding files chooses one realized
offset.

No target grammar is supplied to any learner.
No `sorry`, `admit`, or `axiom` is used.
-/

namespace MCFG

universe u v w z


section ParetoRankProfileOffsetDefinitions

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

/-- Reconstruct a rank-line profile from its normalized offset relative to the
minimum-cardinality endpoint. -/
def correctedConcreteObservationPositiveAdditiveParetoProfileOfOffset
    (minimumCardinalityResult :
      CorrectedConcreteObservationPositiveAdditiveParetoMinimumCardinalityProfileResult
        (z := z)
        obsFamily
        f
        coordinateWeight
        U
        language
        hTarget)
    (offset : Nat) :
    Nat × Nat :=
  (minimumCardinalityResult.profile.1 + offset,
    minimumCardinalityResult.profile.2 - offset)

/-- Finite set of normalized cardinality offsets realized by
rank-minimizing Pareto profiles. -/
noncomputable def
    correctedConcreteObservationPositiveAdditiveParetoRankProfileOffsets
    (minimumCardinalityResult :
      CorrectedConcreteObservationPositiveAdditiveParetoMinimumCardinalityProfileResult
        (z := z)
        obsFamily
        f
        coordinateWeight
        U
        language
        hTarget) :
    Finset Nat := by

  classical

  exact
    (correctedConcreteObservationPositiveAdditiveRankMinimizingParetoProfiles
      (z := z)
      obsFamily
      f
      coordinateWeight
      U
      language
      hTarget).image
      (correctedConcreteObservationPositiveAdditiveParetoProfileCardinalityOffset
        minimumCardinalityResult)

end ParetoRankProfileOffsetDefinitions


section ParetoRankProfileOffsetMembership

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

/-- Exact membership theorem for realized normalized offsets. -/
theorem
    mem_correctedConcreteObservationPositiveAdditiveParetoRankProfileOffsets_iff
    {offset : Nat} :
    offset ∈
        correctedConcreteObservationPositiveAdditiveParetoRankProfileOffsets
          minimumCardinalityResult ↔
      ∃ profile : Nat × Nat,
        profile ∈
            correctedConcreteObservationPositiveAdditiveRankMinimizingParetoProfiles
              (z := z)
              obsFamily
              f
              coordinateWeight
              U
              language
              hTarget ∧
          correctedConcreteObservationPositiveAdditiveParetoProfileCardinalityOffset
              minimumCardinalityResult
              profile =
            offset := by

  classical

  constructor

  · intro hOffset

    rcases Finset.mem_image.mp hOffset with
      ⟨profile, hProfile, hEq⟩

    exact
      ⟨profile,
        hProfile,
        hEq⟩

  · intro hOffset

    rcases hOffset with
      ⟨profile, hProfile, hEq⟩

    exact
      Finset.mem_image.mpr
        ⟨profile,
          hProfile,
          hEq⟩

/-- The realized normalized offset set is nonempty. -/
theorem
    correctedConcreteObservationPositiveAdditiveParetoRankProfileOffsets_nonempty :
    (correctedConcreteObservationPositiveAdditiveParetoRankProfileOffsets
      minimumCardinalityResult).Nonempty := by

  exact
    ⟨correctedConcreteObservationPositiveAdditiveParetoProfileCardinalityOffset
        minimumCardinalityResult
        minimumCardinalityResult.profile,
      (mem_correctedConcreteObservationPositiveAdditiveParetoRankProfileOffsets_iff
        minimumCardinalityResult).mpr
        ⟨minimumCardinalityResult.profile,
          minimumCardinalityResult.profile_mem,
          rfl⟩⟩

/-- The minimum-cardinality endpoint has normalized offset zero. -/
theorem
    positiveAdditiveParetoMinimumCardinalityProfile_offset_eq_zero :
    correctedConcreteObservationPositiveAdditiveParetoProfileCardinalityOffset
        minimumCardinalityResult
        minimumCardinalityResult.profile =
      0 := by

  unfold
    correctedConcreteObservationPositiveAdditiveParetoProfileCardinalityOffset

  simp

/-- Offset zero belongs to the realized offset set. -/
theorem
    zero_mem_correctedConcreteObservationPositiveAdditiveParetoRankProfileOffsets :
    0 ∈
      correctedConcreteObservationPositiveAdditiveParetoRankProfileOffsets
        minimumCardinalityResult := by

  apply
    (mem_correctedConcreteObservationPositiveAdditiveParetoRankProfileOffsets_iff
      minimumCardinalityResult).mpr

  exact
    ⟨minimumCardinalityResult.profile,
      minimumCardinalityResult.profile_mem,
      positiveAdditiveParetoMinimumCardinalityProfile_offset_eq_zero
        minimumCardinalityResult⟩

end ParetoRankProfileOffsetMembership


section ParetoRankProfileReconstruction

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

/-- Every rank-minimizing Pareto profile is reconstructed exactly from its
normalized offset. -/
theorem positiveAdditiveParetoProfile_eq_profileOfOffset
    {profile : Nat × Nat}
    (hProfile :
      profile ∈
        correctedConcreteObservationPositiveAdditiveRankMinimizingParetoProfiles
          (z := z)
          obsFamily
          f
          coordinateWeight
          U
          language
          hTarget) :
    profile =
      correctedConcreteObservationPositiveAdditiveParetoProfileOfOffset
        minimumCardinalityResult
        (correctedConcreteObservationPositiveAdditiveParetoProfileCardinalityOffset
          minimumCardinalityResult
          profile) := by

  have hInterval :
      profile ∈
        correctedConcreteObservationPositiveAdditiveParetoProfileTradeoffInterval
          minimumCardinalityResult
          minimumAdditiveResult :=
    correctedConcreteObservationPositiveAdditiveRankMinimizingParetoProfiles_subset_tradeoffInterval
      minimumCardinalityResult
      minimumAdditiveResult
      hProfile

  unfold
    correctedConcreteObservationPositiveAdditiveParetoProfileTradeoffInterval
    at hInterval

  rcases Finset.mem_image.mp hInterval with
    ⟨offset, hOffsetRange, hGenerated⟩

  have hMinimumLe :
      minimumCardinalityResult.profile.1 <=
        profile.1 :=
    minimumCardinalityResult.profile_card_le
      hProfile

  have hFirstCoordinate :
      minimumCardinalityResult.profile.1 + offset =
        profile.1 :=
    congrArg Prod.fst
      hGenerated

  have hOffsetEq :
      correctedConcreteObservationPositiveAdditiveParetoProfileCardinalityOffset
          minimumCardinalityResult
          profile =
        offset := by

    unfold
      correctedConcreteObservationPositiveAdditiveParetoProfileCardinalityOffset

    omega

  rw [hOffsetEq]

  unfold
    correctedConcreteObservationPositiveAdditiveParetoProfileOfOffset

  exact
    hGenerated.symm

/-- A realized offset reconstructs an actual rank-minimizing Pareto profile. -/
theorem positiveAdditiveParetoProfileOfOffset_mem
    {offset : Nat}
    (hOffset :
      offset ∈
        correctedConcreteObservationPositiveAdditiveParetoRankProfileOffsets
          minimumCardinalityResult) :
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
        hTarget := by

  rcases
      (mem_correctedConcreteObservationPositiveAdditiveParetoRankProfileOffsets_iff
        minimumCardinalityResult).mp
        hOffset with
    ⟨profile, hProfile, hOffsetEq⟩

  have hReconstruction :=
    positiveAdditiveParetoProfile_eq_profileOfOffset
      minimumCardinalityResult
      minimumAdditiveResult
      hProfile

  rw [hOffsetEq] at hReconstruction

  simpa [hReconstruction] using
    hProfile

/-- Equal normalized offsets imply equality of rank-minimizing profiles. -/
theorem positiveAdditiveParetoProfiles_eq_of_offset_eq
    {profile₀ profile₁ : Nat × Nat}
    (hProfile₀ :
      profile₀ ∈
        correctedConcreteObservationPositiveAdditiveRankMinimizingParetoProfiles
          (z := z)
          obsFamily
          f
          coordinateWeight
          U
          language
          hTarget)
    (hProfile₁ :
      profile₁ ∈
        correctedConcreteObservationPositiveAdditiveRankMinimizingParetoProfiles
          (z := z)
          obsFamily
          f
          coordinateWeight
          U
          language
          hTarget)
    (hOffsetEq :
      correctedConcreteObservationPositiveAdditiveParetoProfileCardinalityOffset
          minimumCardinalityResult
          profile₀ =
        correctedConcreteObservationPositiveAdditiveParetoProfileCardinalityOffset
          minimumCardinalityResult
          profile₁) :
    profile₀ = profile₁ := by

  rw [
    positiveAdditiveParetoProfile_eq_profileOfOffset
      minimumCardinalityResult
      minimumAdditiveResult
      hProfile₀,
    positiveAdditiveParetoProfile_eq_profileOfOffset
      minimumCardinalityResult
      minimumAdditiveResult
      hProfile₁,
    hOffsetEq
  ]

/-- The normalized offset map is injective on the finite rank-minimizing
profile set. -/
theorem
    positiveAdditiveParetoProfileCardinalityOffset_injective_on_profiles :
    Set.InjOn
      (correctedConcreteObservationPositiveAdditiveParetoProfileCardinalityOffset
        minimumCardinalityResult)
      {profile : Nat × Nat |
        profile ∈
          correctedConcreteObservationPositiveAdditiveRankMinimizingParetoProfiles
            (z := z)
            obsFamily
            f
            coordinateWeight
            U
            language
            hTarget} := by

  intro profile₀ hProfile₀ profile₁ hProfile₁ hOffsetEq

  exact
    positiveAdditiveParetoProfiles_eq_of_offset_eq
      minimumCardinalityResult
      minimumAdditiveResult
      hProfile₀
      hProfile₁
      hOffsetEq

end ParetoRankProfileReconstruction


section ParetoRankProfileOffsetBounds

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

/-- Every realized normalized offset is at most the Pareto-profile tradeoff
width. -/
theorem positiveAdditiveParetoRankProfileOffset_le_width
    {offset : Nat}
    (hOffset :
      offset ∈
        correctedConcreteObservationPositiveAdditiveParetoRankProfileOffsets
          minimumCardinalityResult) :
    offset <=
      correctedConcreteObservationPositiveAdditiveParetoProfileTradeoffWidth
        minimumCardinalityResult
        minimumAdditiveResult := by

  rcases
      (mem_correctedConcreteObservationPositiveAdditiveParetoRankProfileOffsets_iff
        minimumCardinalityResult).mp
        hOffset with
    ⟨profile, hProfile, hOffsetEq⟩

  rw [← hOffsetEq]

  exact
    positiveAdditiveParetoProfile_cardinalityOffset_le_width
      minimumCardinalityResult
      minimumAdditiveResult
      hProfile

/-- The realized offset set is a subset of `range (width + 1)`. -/
theorem
    correctedConcreteObservationPositiveAdditiveParetoRankProfileOffsets_subset_range :
    correctedConcreteObservationPositiveAdditiveParetoRankProfileOffsets
        minimumCardinalityResult ⊆
      Finset.range
        (correctedConcreteObservationPositiveAdditiveParetoProfileTradeoffWidth
            minimumCardinalityResult
            minimumAdditiveResult +
          1) := by

  intro offset hOffset

  exact
    Finset.mem_range.mpr
      (by
        have hLe :=
          positiveAdditiveParetoRankProfileOffset_le_width
            minimumCardinalityResult
            minimumAdditiveResult
            hOffset

        omega)

/-- The number of realized offsets is at most `width + 1`. -/
theorem
    correctedConcreteObservationPositiveAdditiveParetoRankProfileOffsets_card_le_width_add_one :
    (correctedConcreteObservationPositiveAdditiveParetoRankProfileOffsets
        minimumCardinalityResult).card <=
      correctedConcreteObservationPositiveAdditiveParetoProfileTradeoffWidth
          minimumCardinalityResult
          minimumAdditiveResult +
        1 := by

  calc
    (correctedConcreteObservationPositiveAdditiveParetoRankProfileOffsets
        minimumCardinalityResult).card <=
      (Finset.range
        (correctedConcreteObservationPositiveAdditiveParetoProfileTradeoffWidth
            minimumCardinalityResult
            minimumAdditiveResult +
          1)).card :=
            Finset.card_le_card
              (correctedConcreteObservationPositiveAdditiveParetoRankProfileOffsets_subset_range
                minimumCardinalityResult
                minimumAdditiveResult)

    _ =
      correctedConcreteObservationPositiveAdditiveParetoProfileTradeoffWidth
          minimumCardinalityResult
          minimumAdditiveResult +
        1 := by
          simp

/-- The maximum endpoint has normalized offset exactly `width`. -/
theorem
    positiveAdditiveParetoMinimumAdditiveProfile_offset_eq_width :
    correctedConcreteObservationPositiveAdditiveParetoProfileCardinalityOffset
          minimumCardinalityResult
          minimumAdditiveResult.profile =
      correctedConcreteObservationPositiveAdditiveParetoProfileTradeoffWidth
        minimumCardinalityResult
        minimumAdditiveResult := by

  rfl

/-- The tradeoff width belongs to the realized normalized offset set. -/
theorem
    width_mem_correctedConcreteObservationPositiveAdditiveParetoRankProfileOffsets :
    correctedConcreteObservationPositiveAdditiveParetoProfileTradeoffWidth
          minimumCardinalityResult
          minimumAdditiveResult ∈
      correctedConcreteObservationPositiveAdditiveParetoRankProfileOffsets
        minimumCardinalityResult := by

  apply
    (mem_correctedConcreteObservationPositiveAdditiveParetoRankProfileOffsets_iff
      minimumCardinalityResult).mpr

  exact
    ⟨minimumAdditiveResult.profile,
      minimumAdditiveResult.profile_mem,
      positiveAdditiveParetoMinimumAdditiveProfile_offset_eq_width
        minimumCardinalityResult
        minimumAdditiveResult⟩

end ParetoRankProfileOffsetBounds


section ParetoRankProfileOffsetRigidity

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

/-- Width zero is equivalent to the realized normalized offset set being
exactly `{0}`. -/
theorem
    positiveAdditiveParetoProfile_tradeoffWidth_eq_zero_iff_offsets_singleton :
    correctedConcreteObservationPositiveAdditiveParetoProfileTradeoffWidth
          minimumCardinalityResult
          minimumAdditiveResult =
        0 ↔
      correctedConcreteObservationPositiveAdditiveParetoRankProfileOffsets
          minimumCardinalityResult =
        {0} := by

  constructor

  · intro hWidthZero

    ext offset

    constructor

    · intro hOffset

      have hLe :=
        positiveAdditiveParetoRankProfileOffset_le_width
          minimumCardinalityResult
          minimumAdditiveResult
          hOffset

      rw [hWidthZero] at hLe

      have hOffsetZero :
          offset = 0 := by
        omega

      simp [hOffsetZero]

    · intro hOffset

      have hOffsetZero :
          offset = 0 := by
        simpa using hOffset

      subst offset

      exact
        zero_mem_correctedConcreteObservationPositiveAdditiveParetoRankProfileOffsets
          minimumCardinalityResult

  · intro hSingleton

    have hWidthMem :
        correctedConcreteObservationPositiveAdditiveParetoProfileTradeoffWidth
              minimumCardinalityResult
              minimumAdditiveResult ∈
          ({0} : Finset Nat) := by

      rw [← hSingleton]

      exact
        width_mem_correctedConcreteObservationPositiveAdditiveParetoRankProfileOffsets
          minimumCardinalityResult
          minimumAdditiveResult

    simpa using
      hWidthMem

/-- Positive width is equivalent to the realized offset set containing a
nonzero offset. -/
theorem
    positiveAdditiveParetoProfile_tradeoffWidth_pos_iff_exists_nonzero_offset :
    0 <
        correctedConcreteObservationPositiveAdditiveParetoProfileTradeoffWidth
          minimumCardinalityResult
          minimumAdditiveResult ↔
      ∃ offset : Nat,
        offset ∈
            correctedConcreteObservationPositiveAdditiveParetoRankProfileOffsets
              minimumCardinalityResult ∧
          offset ≠ 0 := by

  constructor

  · intro hPositive

    exact
      ⟨correctedConcreteObservationPositiveAdditiveParetoProfileTradeoffWidth
          minimumCardinalityResult
          minimumAdditiveResult,
        width_mem_correctedConcreteObservationPositiveAdditiveParetoRankProfileOffsets
          minimumCardinalityResult
          minimumAdditiveResult,
        by omega⟩

  · intro hOffset

    rcases hOffset with
      ⟨offset, hOffsetMem, hOffsetNe⟩

    have hLe :=
      positiveAdditiveParetoRankProfileOffset_le_width
        minimumCardinalityResult
        minimumAdditiveResult
        hOffsetMem

    omega

end ParetoRankProfileOffsetRigidity


section CertifiedParetoRankProfileOffsetWitness

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

/-- Every realized normalized offset has an actual certified selected-product
witness with the exactly reconstructed profile. -/
theorem positiveAdditiveParetoRankProfileOffset_exists_certifiedWitness
    {offset : Nat}
    (hOffset :
      offset ∈
        correctedConcreteObservationPositiveAdditiveParetoRankProfileOffsets
          minimumCardinalityResult) :
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
      (S.card,
          correctedConcreteObservationSelectionAdditiveCost
            coordinateWeight S) =
        correctedConcreteObservationPositiveAdditiveParetoProfileOfOffset
          minimumCardinalityResult
          offset ∧
        CorrectedConcreteObservationSelectionParetoOptimal
          (z := z)
          obsFamily
          f
          (correctedConcreteObservationSelectionAdditiveCost
            coordinateWeight)
          U
          language
          S ∧
        correctedConcreteObservationSelectionPositiveAdditiveCost
            coordinateWeight S =
          ambientTargetObservationSelectionPositiveAdditiveMinimumCost
            (z := z)
            obsFamily
            f
            coordinateWeight
            U
            hTarget ∧
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

  exact
    positiveAdditiveRankMinimizingParetoProfile_exists_certifiedWitness
      (z := z)
      hα
      hProfileMem

end CertifiedParetoRankProfileOffsetWitness


section ActualSelectorParetoRankProfileOffset

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
  (result :
    CorrectedConcreteObservationPositiveAdditiveParetoRankSelectionResult
      (z := z)
      obsFamily
      f
      coordinateWeight
      U
      language
      hTarget)

/-- Normalized offset chosen by the actual Pareto-rank selector. -/
def correctedConcreteObservationPositiveAdditiveSelectedParetoRankProfileOffset :
    Nat :=
  correctedConcreteObservationPositiveAdditiveParetoProfileCardinalityOffset
    minimumCardinalityResult
    (correctedConcreteObservationPositiveAdditiveSelectedParetoRankProfile
      result)

/-- The actual selector chooses a realized normalized offset. -/
theorem
    correctedConcreteObservationPositiveAdditiveSelectedParetoRankProfileOffset_mem :
    correctedConcreteObservationPositiveAdditiveSelectedParetoRankProfileOffset
          minimumCardinalityResult
          result ∈
      correctedConcreteObservationPositiveAdditiveParetoRankProfileOffsets
        minimumCardinalityResult := by

  apply
    (mem_correctedConcreteObservationPositiveAdditiveParetoRankProfileOffsets_iff
      minimumCardinalityResult).mpr

  exact
    ⟨correctedConcreteObservationPositiveAdditiveSelectedParetoRankProfile
        result,
      correctedConcreteObservationPositiveAdditiveSelectedParetoRankProfile_mem
        (z := z)
        result,
      rfl⟩

end ActualSelectorParetoRankProfileOffset


section ParetoRankProfileOffsetsFinalPackage

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

/-- Final normalized-offset reconstruction, endpoint realization, rigidity,
actual-selector offset, and certified-offset-witness package. -/
theorem
    correctedConcreteCertifiedWorkingGrammar_observationSelectionParetoRankProfileOffsets_package :
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
        correctedConcreteObservationPositiveAdditiveParetoRankSelectionResult
          (z := z)
          obsFamily
          f
          coordinateWeight
          U
          language
          hTarget
      let offsets :=
        correctedConcreteObservationPositiveAdditiveParetoRankProfileOffsets
          minimumCardinalityResult
      offsets.Nonempty ∧
        offsets ⊆
          Finset.range
            (correctedConcreteObservationPositiveAdditiveParetoProfileTradeoffWidth
                minimumCardinalityResult
                minimumAdditiveResult +
              1) ∧
        0 ∈ offsets ∧
        correctedConcreteObservationPositiveAdditiveParetoProfileTradeoffWidth
              minimumCardinalityResult
              minimumAdditiveResult ∈
          offsets ∧
        (correctedConcreteObservationPositiveAdditiveParetoProfileTradeoffWidth
              minimumCardinalityResult
              minimumAdditiveResult =
            0 ↔
          offsets = {0}) ∧
        correctedConcreteObservationPositiveAdditiveSelectedParetoRankProfileOffset
              minimumCardinalityResult
              result ∈
          offsets ∧
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

  let result :=
    correctedConcreteObservationPositiveAdditiveParetoRankSelectionResult
      (z := z)
      obsFamily
      f
      coordinateWeight
      U
      language
      hTarget

  let offsets :=
    correctedConcreteObservationPositiveAdditiveParetoRankProfileOffsets
      minimumCardinalityResult

  have hCertified :=
    CorrectedConcreteObservationPositiveAdditiveParetoRankSelectionResult.certified_package
      (z := z)
      hα
      result

  exact
    ⟨correctedConcreteObservationPositiveAdditiveParetoRankProfileOffsets_nonempty
        minimumCardinalityResult,
      correctedConcreteObservationPositiveAdditiveParetoRankProfileOffsets_subset_range
        minimumCardinalityResult
        minimumAdditiveResult,
      zero_mem_correctedConcreteObservationPositiveAdditiveParetoRankProfileOffsets
        minimumCardinalityResult,
      width_mem_correctedConcreteObservationPositiveAdditiveParetoRankProfileOffsets
        minimumCardinalityResult
        minimumAdditiveResult,
      positiveAdditiveParetoProfile_tradeoffWidth_eq_zero_iff_offsets_singleton
        minimumCardinalityResult
        minimumAdditiveResult,
      correctedConcreteObservationPositiveAdditiveSelectedParetoRankProfileOffset_mem
        minimumCardinalityResult
        result,
      hCertified.1⟩

end ParetoRankProfileOffsetsFinalPackage

end MCFG
