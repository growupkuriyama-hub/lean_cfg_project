/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG.ConcreteCanonicalLearnerWorkingGrammarObservationSelectionParetoRankProfileOffsetOrder

/-!
# ConcreteCanonicalLearnerWorkingGrammarObservationSelectionParetoRankProfileOffsetBijection.lean

The preceding file proves that realized normalized offsets and
rank-minimizing Pareto profiles carry exactly the same tradeoff order.

This file upgrades the correspondence to an explicit finite bijection.

## Offset/profile round trips

Fix the minimum-cardinality endpoint

```text
(c_min, a_max).
```

The maps are

```text
offsetToProfile(d) = (c_min + d, a_max - d)
```

and

```text
profileToOffset(c,a) = c - c_min.
```

On the realized finite sets, both composites are identities.

Therefore:

* every rank-minimizing Pareto profile has a unique realized offset;
* every realized offset has a unique rank-minimizing Pareto profile;
* the finite offset set and finite profile set have equal cardinality.

## Explicit finite equivalence

The round trips are packaged as an actual equivalence

```lean
correctedConcreteObservationPositiveAdditiveParetoRankProfileOffsetEquiv.
```

Its forward direction reconstructs a profile from a realized offset.
Its inverse direction extracts the normalized offset from a realized profile.

The equivalence preserves and reflects the linear order:

```text
d₀ ≤ d₁
  ↔ profile(d₀).cardinality ≤ profile(d₁).cardinality
  ↔ profile(d₁).additiveCost ≤ profile(d₀).additiveCost.
```

## Actual selected interfaces

Every profile in the finite profile set can be passed through its unique offset
to the offset-indexed selector.

This yields an actual selected subset having exactly that profile.  The subset
is Pareto optimal, attains the exact positive additive rank, is
inclusion-irredundant, and has its own certified learner identifying the target.

No uniqueness of the selected subset itself is asserted.

No target grammar is supplied to any learner.
No `sorry`, `admit`, or `axiom` is used.
-/

namespace MCFG

universe u v w z


section OffsetProfileRoundTrips

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

/-- Extracting the normalized offset from a reconstructed profile returns the
original offset. -/
theorem positiveAdditiveParetoProfileOfOffset_offset_eq
    (offset : Nat) :
    correctedConcreteObservationPositiveAdditiveParetoProfileCardinalityOffset
        minimumCardinalityResult
        (correctedConcreteObservationPositiveAdditiveParetoProfileOfOffset
          minimumCardinalityResult
          offset) =
      offset := by

  unfold
    correctedConcreteObservationPositiveAdditiveParetoProfileCardinalityOffset
    correctedConcreteObservationPositiveAdditiveParetoProfileOfOffset

  simp

/-- Reconstructing a realized profile from its extracted offset returns the
original profile. -/
theorem positiveAdditiveParetoProfile_offset_roundTrip
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
    correctedConcreteObservationPositiveAdditiveParetoProfileOfOffset
        minimumCardinalityResult
        (correctedConcreteObservationPositiveAdditiveParetoProfileCardinalityOffset
          minimumCardinalityResult
          profile) =
      profile := by

  exact
    (positiveAdditiveParetoProfile_eq_profileOfOffset
      minimumCardinalityResult
      minimumAdditiveResult
      hProfile).symm

/-- Every rank-minimizing Pareto profile has a unique realized normalized
offset. -/
theorem positiveAdditiveParetoProfile_existsUnique_realizedOffset
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
    ∃! offset : Nat,
      offset ∈
          correctedConcreteObservationPositiveAdditiveParetoRankProfileOffsets
            minimumCardinalityResult ∧
        correctedConcreteObservationPositiveAdditiveParetoProfileOfOffset
            minimumCardinalityResult
            offset =
          profile := by

  let offset :=
    correctedConcreteObservationPositiveAdditiveParetoProfileCardinalityOffset
      minimumCardinalityResult
      profile

  have hOffsetMem :
      offset ∈
        correctedConcreteObservationPositiveAdditiveParetoRankProfileOffsets
          minimumCardinalityResult := by

    apply
      (mem_correctedConcreteObservationPositiveAdditiveParetoRankProfileOffsets_iff
        minimumCardinalityResult).mpr

    exact
      ⟨profile,
        hProfile,
        rfl⟩

  have hRoundTrip :
      correctedConcreteObservationPositiveAdditiveParetoProfileOfOffset
          minimumCardinalityResult
          offset =
        profile :=
    positiveAdditiveParetoProfile_offset_roundTrip
      minimumCardinalityResult
      minimumAdditiveResult
      hProfile

  refine
    ⟨offset,
      ⟨hOffsetMem,
        hRoundTrip⟩,
      ?_⟩

  intro candidate hCandidate

  apply
    positiveAdditiveParetoProfileOfOffset_injective
      minimumCardinalityResult

  calc
    correctedConcreteObservationPositiveAdditiveParetoProfileOfOffset
        minimumCardinalityResult
        candidate =
      profile :=
        hCandidate.2

    _ =
      correctedConcreteObservationPositiveAdditiveParetoProfileOfOffset
        minimumCardinalityResult
        offset :=
          hRoundTrip.symm

/-- Every realized normalized offset has a unique rank-minimizing Pareto
profile. -/
theorem positiveAdditiveParetoRankProfileOffset_existsUnique_profile
    {offset : Nat}
    (hOffset :
      offset ∈
        correctedConcreteObservationPositiveAdditiveParetoRankProfileOffsets
          minimumCardinalityResult) :
    ∃! profile : Nat × Nat,
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

  let profile :=
    correctedConcreteObservationPositiveAdditiveParetoProfileOfOffset
      minimumCardinalityResult
      offset

  have hProfileMem :
      profile ∈
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

  have hOffsetRoundTrip :
      correctedConcreteObservationPositiveAdditiveParetoProfileCardinalityOffset
          minimumCardinalityResult
          profile =
        offset :=
    positiveAdditiveParetoProfileOfOffset_offset_eq
      minimumCardinalityResult
      offset

  refine
    ⟨profile,
      ⟨hProfileMem,
        hOffsetRoundTrip⟩,
      ?_⟩

  intro candidate hCandidate

  exact
    positiveAdditiveParetoProfiles_eq_of_offset_eq
      minimumCardinalityResult
      minimumAdditiveResult
      hCandidate.1
      hProfileMem
      (by
        rw [
          hCandidate.2,
          hOffsetRoundTrip
        ])

end OffsetProfileRoundTrips


section OffsetProfileImageEqualities

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

/-- Reconstructing every realized offset gives exactly the finite
rank-minimizing Pareto profile set. -/
theorem
    correctedConcreteObservationPositiveAdditiveParetoRankProfileOffsets_image_profileOfOffset_eq_profiles :
    (correctedConcreteObservationPositiveAdditiveParetoRankProfileOffsets
        minimumCardinalityResult).image
      (correctedConcreteObservationPositiveAdditiveParetoProfileOfOffset
        minimumCardinalityResult) =
      correctedConcreteObservationPositiveAdditiveRankMinimizingParetoProfiles
        (z := z)
        obsFamily
        f
        coordinateWeight
        U
        language
        hTarget := by

  ext profile

  constructor

  · intro hProfile

    rcases Finset.mem_image.mp hProfile with
      ⟨offset, hOffset, hEq⟩

    have hGenerated :
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

    simpa [hEq] using
      hGenerated

  · intro hProfile

    let offset :=
      correctedConcreteObservationPositiveAdditiveParetoProfileCardinalityOffset
        minimumCardinalityResult
        profile

    have hOffset :
        offset ∈
          correctedConcreteObservationPositiveAdditiveParetoRankProfileOffsets
            minimumCardinalityResult := by

      apply
        (mem_correctedConcreteObservationPositiveAdditiveParetoRankProfileOffsets_iff
          minimumCardinalityResult).mpr

      exact
        ⟨profile,
          hProfile,
          rfl⟩

    apply Finset.mem_image.mpr

    exact
      ⟨offset,
        hOffset,
        positiveAdditiveParetoProfile_offset_roundTrip
          minimumCardinalityResult
          minimumAdditiveResult
          hProfile⟩

/-- Extracting the normalized offset from every finite profile gives exactly
the realized offset set. -/
theorem
    correctedConcreteObservationPositiveAdditiveRankMinimizingParetoProfiles_image_offset_eq_offsets :
    (correctedConcreteObservationPositiveAdditiveRankMinimizingParetoProfiles
        (z := z)
        obsFamily
        f
        coordinateWeight
        U
        language
        hTarget).image
      (correctedConcreteObservationPositiveAdditiveParetoProfileCardinalityOffset
        minimumCardinalityResult) =
      correctedConcreteObservationPositiveAdditiveParetoRankProfileOffsets
        minimumCardinalityResult := by

  rfl

end OffsetProfileImageEqualities


section OffsetProfileFiniteEquivalence

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

/-- Explicit equivalence between realized normalized offsets and
rank-minimizing Pareto profiles. -/
noncomputable def
    correctedConcreteObservationPositiveAdditiveParetoRankProfileOffsetEquiv :
    {offset : Nat //
      offset ∈
        correctedConcreteObservationPositiveAdditiveParetoRankProfileOffsets
          minimumCardinalityResult} ≃
      {profile : Nat × Nat //
        profile ∈
          correctedConcreteObservationPositiveAdditiveRankMinimizingParetoProfiles
            (z := z)
            obsFamily
            f
            coordinateWeight
            U
            language
            hTarget} where

  toFun offset :=
    ⟨correctedConcreteObservationPositiveAdditiveParetoProfileOfOffset
        minimumCardinalityResult
        offset.1,
      positiveAdditiveParetoProfileOfOffset_mem
        minimumCardinalityResult
        minimumAdditiveResult
        offset.2⟩

  invFun profile :=
    ⟨correctedConcreteObservationPositiveAdditiveParetoProfileCardinalityOffset
        minimumCardinalityResult
        profile.1,
      (mem_correctedConcreteObservationPositiveAdditiveParetoRankProfileOffsets_iff
        minimumCardinalityResult).mpr
        ⟨profile.1,
          profile.2,
          rfl⟩⟩

  left_inv offset := by
    apply Subtype.ext
    exact
      positiveAdditiveParetoProfileOfOffset_offset_eq
        minimumCardinalityResult
        offset.1

  right_inv profile := by
    apply Subtype.ext
    exact
      positiveAdditiveParetoProfile_offset_roundTrip
        minimumCardinalityResult
        minimumAdditiveResult
        profile.2

/-- The forward direction of the finite equivalence is profile reconstruction
from offset. -/
theorem positiveAdditiveParetoRankProfileOffsetEquiv_apply
    (offset :
      {offset : Nat //
        offset ∈
          correctedConcreteObservationPositiveAdditiveParetoRankProfileOffsets
            minimumCardinalityResult}) :
    (correctedConcreteObservationPositiveAdditiveParetoRankProfileOffsetEquiv
        minimumCardinalityResult
        minimumAdditiveResult
        offset).1 =
      correctedConcreteObservationPositiveAdditiveParetoProfileOfOffset
        minimumCardinalityResult
        offset.1 := by

  rfl

/-- The inverse direction of the finite equivalence extracts the normalized
cardinality offset. -/
theorem positiveAdditiveParetoRankProfileOffsetEquiv_symm_apply
    (profile :
      {profile : Nat × Nat //
        profile ∈
          correctedConcreteObservationPositiveAdditiveRankMinimizingParetoProfiles
            (z := z)
            obsFamily
            f
            coordinateWeight
            U
            language
            hTarget}) :
    ((correctedConcreteObservationPositiveAdditiveParetoRankProfileOffsetEquiv
        minimumCardinalityResult
        minimumAdditiveResult).symm
        profile).1 =
      correctedConcreteObservationPositiveAdditiveParetoProfileCardinalityOffset
        minimumCardinalityResult
        profile.1 := by

  rfl

/-- The finite realized-offset set and finite profile set have exactly the same
cardinality. -/
theorem
    correctedConcreteObservationPositiveAdditiveParetoRankProfileOffsets_card_eq_profiles_card :
    (correctedConcreteObservationPositiveAdditiveParetoRankProfileOffsets
        minimumCardinalityResult).card =
      (correctedConcreteObservationPositiveAdditiveRankMinimizingParetoProfiles
        (z := z)
        obsFamily
        f
        coordinateWeight
        U
        language
        hTarget).card := by

  classical

  simpa using
    Fintype.card_congr
      (correctedConcreteObservationPositiveAdditiveParetoRankProfileOffsetEquiv
        minimumCardinalityResult
        minimumAdditiveResult)

/-- The finite equivalence preserves cardinality order exactly. -/
theorem positiveAdditiveParetoRankProfileOffsetEquiv_fst_le_iff
    (offset₀ offset₁ :
      {offset : Nat //
        offset ∈
          correctedConcreteObservationPositiveAdditiveParetoRankProfileOffsets
            minimumCardinalityResult}) :
    ((correctedConcreteObservationPositiveAdditiveParetoRankProfileOffsetEquiv
          minimumCardinalityResult
          minimumAdditiveResult
          offset₀).1).1 <=
        ((correctedConcreteObservationPositiveAdditiveParetoRankProfileOffsetEquiv
          minimumCardinalityResult
          minimumAdditiveResult
          offset₁).1).1 ↔
      offset₀.1 <= offset₁.1 := by

  exact
    positiveAdditiveParetoProfileOfOffset_fst_le_iff
      minimumCardinalityResult
      offset₀.1
      offset₁.1

/-- The finite equivalence reverses additive-coordinate order exactly. -/
theorem positiveAdditiveParetoRankProfileOffsetEquiv_snd_reverse_le_iff
    (offset₀ offset₁ :
      {offset : Nat //
        offset ∈
          correctedConcreteObservationPositiveAdditiveParetoRankProfileOffsets
            minimumCardinalityResult}) :
    ((correctedConcreteObservationPositiveAdditiveParetoRankProfileOffsetEquiv
          minimumCardinalityResult
          minimumAdditiveResult
          offset₁).1).2 <=
        ((correctedConcreteObservationPositiveAdditiveParetoRankProfileOffsetEquiv
          minimumCardinalityResult
          minimumAdditiveResult
          offset₀).1).2 ↔
      offset₀.1 <= offset₁.1 := by

  exact
    positiveAdditiveParetoProfileOfOffset_snd_reverse_le_iff
      minimumCardinalityResult
      minimumAdditiveResult
      offset₀.2
      offset₁.2

end OffsetProfileFiniteEquivalence


section ProfileBijectionCertifiedSelection

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

/-- Every finite Pareto profile has an actual offset-indexed selected interface
with exactly that profile and its own certified learner. -/
theorem positiveAdditiveParetoProfile_exists_offsetSelectedCertifiedWitness
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
    ∃
      (offset : Nat)
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
      (result.selected.card,
          correctedConcreteObservationSelectionAdditiveCost
            coordinateWeight result.selected) =
        profile ∧
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

  let offset :=
    correctedConcreteObservationPositiveAdditiveParetoProfileCardinalityOffset
      minimumCardinalityResult
      profile

  have hOffset :
      offset ∈
        correctedConcreteObservationPositiveAdditiveParetoRankProfileOffsets
          minimumCardinalityResult := by

    apply
      (mem_correctedConcreteObservationPositiveAdditiveParetoRankProfileOffsets_iff
        minimumCardinalityResult).mpr

    exact
      ⟨profile,
        hProfile,
        rfl⟩

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

  have hRoundTrip :
      correctedConcreteObservationPositiveAdditiveParetoProfileOfOffset
          minimumCardinalityResult
          offset =
        profile :=
    positiveAdditiveParetoProfile_offset_roundTrip
      minimumCardinalityResult
      minimumAdditiveResult
      hProfile

  have hSelectedProfile :
      (result.selected.card,
          correctedConcreteObservationSelectionAdditiveCost
            coordinateWeight result.selected) =
        profile := by

    calc
      (result.selected.card,
          correctedConcreteObservationSelectionAdditiveCost
            coordinateWeight result.selected) =
        correctedConcreteObservationPositiveAdditiveParetoProfileOfOffset
          minimumCardinalityResult
          offset :=
            result.selected_profile_eq

      _ =
        profile :=
          hRoundTrip

  have hCertified :=
    CorrectedConcreteObservationPositiveAdditiveParetoRankProfileOffsetSelectionResult.certified_package
      (z := z)
      hα
      result

  exact
    ⟨offset,
      hOffset,
      result,
      hSelectedProfile,
      result.selected_pareto,
      result.selected_cost_eq_rank,
      result.selected_irredundant,
      hCertified.1⟩

end ProfileBijectionCertifiedSelection


section ParetoRankProfileOffsetBijectionFinalPackage

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

/-- Final finite offset/profile equivalence, cardinality equality, unique
correspondence, order compatibility, and certified-profile-selection package. -/
theorem
    correctedConcreteCertifiedWorkingGrammar_observationSelectionParetoRankProfileOffsetBijection_package :
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
      (correctedConcreteObservationPositiveAdditiveParetoRankProfileOffsets
          minimumCardinalityResult).card =
        (correctedConcreteObservationPositiveAdditiveRankMinimizingParetoProfiles
          (z := z)
          obsFamily
          f
          coordinateWeight
          U
          language
          hTarget).card ∧
      (∀ profile : Nat × Nat,
        profile ∈
            correctedConcreteObservationPositiveAdditiveRankMinimizingParetoProfiles
              (z := z)
              obsFamily
              f
              coordinateWeight
              U
              language
              hTarget →
          ∃! offset : Nat,
            offset ∈
                correctedConcreteObservationPositiveAdditiveParetoRankProfileOffsets
                  minimumCardinalityResult ∧
              correctedConcreteObservationPositiveAdditiveParetoProfileOfOffset
                  minimumCardinalityResult
                  offset =
                profile) ∧
      (∀ offset : Nat,
        offset ∈
            correctedConcreteObservationPositiveAdditiveParetoRankProfileOffsets
              minimumCardinalityResult →
          ∃! profile : Nat × Nat,
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
                offset) ∧
      (∀
        offset₀ offset₁ :
          {offset : Nat //
            offset ∈
              correctedConcreteObservationPositiveAdditiveParetoRankProfileOffsets
                minimumCardinalityResult},
          ((correctedConcreteObservationPositiveAdditiveParetoRankProfileOffsetEquiv
                minimumCardinalityResult
                minimumAdditiveResult
                offset₀).1).1 <=
              ((correctedConcreteObservationPositiveAdditiveParetoRankProfileOffsetEquiv
                minimumCardinalityResult
                minimumAdditiveResult
                offset₁).1).1 ↔
            offset₀.1 <= offset₁.1) ∧
      (∀ profile : Nat × Nat,
        ∀ hProfile :
          profile ∈
            correctedConcreteObservationPositiveAdditiveRankMinimizingParetoProfiles
              (z := z)
              obsFamily
              f
              coordinateWeight
              U
              language
              hTarget,
          ∃
            (offset : Nat)
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
            (result.selected.card,
                correctedConcreteObservationSelectionAdditiveCost
                  coordinateWeight result.selected) =
              profile ∧
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

  refine
    ⟨correctedConcreteObservationPositiveAdditiveParetoRankProfileOffsets_card_eq_profiles_card
        minimumCardinalityResult
        minimumAdditiveResult,
      ?_,
      ?_,
      ?_,
      ?_⟩

  · intro profile hProfile

    exact
      positiveAdditiveParetoProfile_existsUnique_realizedOffset
        minimumCardinalityResult
        minimumAdditiveResult
        hProfile

  · intro offset hOffset

    exact
      positiveAdditiveParetoRankProfileOffset_existsUnique_profile
        minimumCardinalityResult
        minimumAdditiveResult
        hOffset

  · intro offset₀ offset₁

    exact
      positiveAdditiveParetoRankProfileOffsetEquiv_fst_le_iff
        minimumCardinalityResult
        minimumAdditiveResult
        offset₀
        offset₁

  · intro profile hProfile

    rcases
        positiveAdditiveParetoProfile_exists_offsetSelectedCertifiedWitness
          (z := z)
          hα
          minimumCardinalityResult
          minimumAdditiveResult
          hProfile with
      ⟨offset,
        hOffset,
        result,
        hSelectedProfile,
        hPareto,
        hCost,
        hIrredundant,
        hIdentifies⟩

    exact
      ⟨offset,
        hOffset,
        result,
        hSelectedProfile,
        hIdentifies⟩

end ParetoRankProfileOffsetBijectionFinalPackage

end MCFG
