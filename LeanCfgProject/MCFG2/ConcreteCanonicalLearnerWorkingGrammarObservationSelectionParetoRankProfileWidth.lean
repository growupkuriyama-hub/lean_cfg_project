/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG.ConcreteCanonicalLearnerWorkingGrammarObservationSelectionParetoRankProfileExtremes

/-!
# ConcreteCanonicalLearnerWorkingGrammarObservationSelectionParetoRankProfileWidth.lean

The preceding file constructs the two endpoint profiles of the finite
positive-additive-rank-minimizing Pareto profile set.

This file measures the exact distance between those endpoints.

## Tradeoff width

Let

```text
(c_min, a_max)
```

be the minimum-cardinality endpoint and

```text
(c_max, a_min)
```

the minimum-additive-cost endpoint.

Define the Pareto-profile tradeoff width by

```text
width = c_max - c_min.
```

The endpoint rank equations imply the equivalent formula

```text
width = a_max - a_min.
```

Thus width is exactly the amount of cardinality/additive-weight exchange
available while preserving the same positive additive rank.

## Finite tradeoff interval

Normalize every profile by its cardinality offset from the minimum-cardinality
endpoint.

Every rank-minimizing profile belongs to the finite interval

```text
{(c_min + d, a_max - d) | d < width + 1}.
```

Consequently,

```text
number of rank-minimizing Pareto profiles ≤ width + 1.
```

This sharpens the preceding bound `rank + 1`, since

```text
width ≤ rank.
```

## Rigidity

The following are equivalent:

```text
width = 0,
the two endpoint profiles are equal,
the rank-minimizing Pareto profile set is a singleton.
```

Hence width zero is the exact rigidity condition for the two-objective
observation-selection optimum.

At ranks zero and one the width is necessarily zero.

## Actual selected profile

The profile chosen by the actual Pareto-rank selector belongs to the finite
tradeoff interval and therefore has a normalized offset at most `width`.

Its selected-product certified learner continues to identify the target.

## Boundary

Width concerns only the observation-interface profile.  It is not a bound on
the certified grammar-description rank or on construction time.

No target grammar is supplied to any learner.
No `sorry`, `admit`, or `axiom` is used.
-/

namespace MCFG

universe u v w z


section ParetoProfileTradeoffWidthDefinitions

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

/-- Cardinality distance between the two endpoint profiles. -/
def correctedConcreteObservationPositiveAdditiveParetoProfileTradeoffWidth
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
  minimumAdditiveResult.profile.1 -
    minimumCardinalityResult.profile.1

/-- Additive-coordinate distance between the two endpoint profiles. -/
def correctedConcreteObservationPositiveAdditiveParetoProfileAdditiveTradeoffWidth
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
  minimumCardinalityResult.profile.2 -
    minimumAdditiveResult.profile.2

/-- Canonical finite rank-line interval between the two endpoint profiles. -/
def correctedConcreteObservationPositiveAdditiveParetoProfileTradeoffInterval
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
    Finset (Nat × Nat) :=
  (Finset.range
      (correctedConcreteObservationPositiveAdditiveParetoProfileTradeoffWidth
        minimumCardinalityResult
        minimumAdditiveResult +
        1)).image
    (fun offset =>
      (minimumCardinalityResult.profile.1 + offset,
        minimumCardinalityResult.profile.2 - offset))

/-- Cardinality offset of a profile from the minimum-cardinality endpoint. -/
def correctedConcreteObservationPositiveAdditiveParetoProfileCardinalityOffset
    (minimumCardinalityResult :
      CorrectedConcreteObservationPositiveAdditiveParetoMinimumCardinalityProfileResult
        (z := z)
        obsFamily
        f
        coordinateWeight
        U
        language
        hTarget)
    (profile : Nat × Nat) :
    Nat :=
  profile.1 - minimumCardinalityResult.profile.1

end ParetoProfileTradeoffWidthDefinitions


section ParetoProfileTradeoffWidthEquality

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

/-- Cardinality width and additive-coordinate width are exactly equal. -/
theorem positiveAdditiveParetoProfile_tradeoffWidth_eq_additiveTradeoffWidth :
    correctedConcreteObservationPositiveAdditiveParetoProfileTradeoffWidth
        minimumCardinalityResult
        minimumAdditiveResult =
      correctedConcreteObservationPositiveAdditiveParetoProfileAdditiveTradeoffWidth
        minimumCardinalityResult
        minimumAdditiveResult := by

  exact
    positiveAdditiveParetoProfile_endpoint_width_eq
      minimumCardinalityResult
      minimumAdditiveResult

/-- Tradeoff width is bounded by the target's positive additive rank. -/
theorem positiveAdditiveParetoProfile_tradeoffWidth_le_rank :
    correctedConcreteObservationPositiveAdditiveParetoProfileTradeoffWidth
          minimumCardinalityResult
          minimumAdditiveResult <=
      ambientTargetObservationSelectionPositiveAdditiveMinimumCost
        (z := z)
        obsFamily
        f
        coordinateWeight
        U
        hTarget := by

  have hMaximumCardinalityLe :=
    (correctedConcreteObservationPositiveAdditiveRankMinimizingParetoProfile_coordinates_le_rank
      (z := z)
      minimumAdditiveResult.profile_mem).1

  unfold
    correctedConcreteObservationPositiveAdditiveParetoProfileTradeoffWidth

  omega

/-- The additive-coordinate form of the width is also bounded by rank. -/
theorem positiveAdditiveParetoProfile_additiveTradeoffWidth_le_rank :
    correctedConcreteObservationPositiveAdditiveParetoProfileAdditiveTradeoffWidth
          minimumCardinalityResult
          minimumAdditiveResult <=
      ambientTargetObservationSelectionPositiveAdditiveMinimumCost
        (z := z)
        obsFamily
        f
        coordinateWeight
        U
        hTarget := by

  rw [
    ← positiveAdditiveParetoProfile_tradeoffWidth_eq_additiveTradeoffWidth
        minimumCardinalityResult
        minimumAdditiveResult
  ]

  exact
    positiveAdditiveParetoProfile_tradeoffWidth_le_rank
      minimumCardinalityResult
      minimumAdditiveResult

/-- The two endpoint profiles are exactly `width` apart in cardinality. -/
theorem positiveAdditiveParetoProfile_maxCardinality_eq_minCardinality_add_width :
    minimumAdditiveResult.profile.1 =
      minimumCardinalityResult.profile.1 +
        correctedConcreteObservationPositiveAdditiveParetoProfileTradeoffWidth
          minimumCardinalityResult
          minimumAdditiveResult := by

  have hOrder :
      minimumCardinalityResult.profile.1 <=
        minimumAdditiveResult.profile.1 :=
    minimumCardinalityResult.profile_card_le
      minimumAdditiveResult.profile_mem

  unfold
    correctedConcreteObservationPositiveAdditiveParetoProfileTradeoffWidth

  omega

/-- The maximum additive coordinate is minimum additive cost plus `width`. -/
theorem positiveAdditiveParetoProfile_maxAdditive_eq_minAdditive_add_width :
    minimumCardinalityResult.profile.2 =
      minimumAdditiveResult.profile.2 +
        correctedConcreteObservationPositiveAdditiveParetoProfileTradeoffWidth
          minimumCardinalityResult
          minimumAdditiveResult := by

  have hOrder :
      minimumAdditiveResult.profile.2 <=
        minimumCardinalityResult.profile.2 :=
    minimumAdditiveResult.profile_additive_le
      minimumCardinalityResult.profile_mem

  have hWidthEq :=
    positiveAdditiveParetoProfile_tradeoffWidth_eq_additiveTradeoffWidth
      minimumCardinalityResult
      minimumAdditiveResult

  unfold
    correctedConcreteObservationPositiveAdditiveParetoProfileAdditiveTradeoffWidth
    at hWidthEq

  omega

end ParetoProfileTradeoffWidthEquality


section ParetoProfileTradeoffInterval

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

/-- The canonical endpoint interval has at most `width + 1` profiles. -/
theorem positiveAdditiveParetoProfile_tradeoffInterval_card_le :
    (correctedConcreteObservationPositiveAdditiveParetoProfileTradeoffInterval
        minimumCardinalityResult
        minimumAdditiveResult).card <=
      correctedConcreteObservationPositiveAdditiveParetoProfileTradeoffWidth
          minimumCardinalityResult
          minimumAdditiveResult +
        1 := by

  unfold
    correctedConcreteObservationPositiveAdditiveParetoProfileTradeoffInterval

  calc
    ((Finset.range
        (correctedConcreteObservationPositiveAdditiveParetoProfileTradeoffWidth
            minimumCardinalityResult
            minimumAdditiveResult +
          1)).image
        (fun offset =>
          (minimumCardinalityResult.profile.1 + offset,
            minimumCardinalityResult.profile.2 - offset))).card <=
      (Finset.range
        (correctedConcreteObservationPositiveAdditiveParetoProfileTradeoffWidth
            minimumCardinalityResult
            minimumAdditiveResult +
          1)).card :=
            Finset.card_image_le

    _ =
      correctedConcreteObservationPositiveAdditiveParetoProfileTradeoffWidth
          minimumCardinalityResult
          minimumAdditiveResult +
        1 := by
          simp

/-- Every rank-minimizing Pareto profile belongs to the finite endpoint
interval. -/
theorem
    correctedConcreteObservationPositiveAdditiveRankMinimizingParetoProfiles_subset_tradeoffInterval :
    correctedConcreteObservationPositiveAdditiveRankMinimizingParetoProfiles
        (z := z)
        obsFamily
        f
        coordinateWeight
        U
        language
        hTarget ⊆
      correctedConcreteObservationPositiveAdditiveParetoProfileTradeoffInterval
        minimumCardinalityResult
        minimumAdditiveResult := by

  intro profile hProfile

  have hBounds :=
    positiveAdditiveParetoProfile_between_endpoints
      minimumCardinalityResult
      minimumAdditiveResult
      hProfile

  have hMinimumSum :=
    minimumCardinalityResult.profile_sum_eq_rank

  have hProfileSum :=
    correctedConcreteObservationPositiveAdditiveRankMinimizingParetoProfile_sum_eq_rank
      (z := z)
      hProfile

  let offset :=
    correctedConcreteObservationPositiveAdditiveParetoProfileCardinalityOffset
      minimumCardinalityResult
      profile

  unfold
    correctedConcreteObservationPositiveAdditiveParetoProfileTradeoffInterval

  apply Finset.mem_image.mpr

  refine
    ⟨offset,
      Finset.mem_range.mpr
        ?_,
      ?_⟩

  · unfold offset
    unfold
      correctedConcreteObservationPositiveAdditiveParetoProfileCardinalityOffset
      correctedConcreteObservationPositiveAdditiveParetoProfileTradeoffWidth

    omega

  · apply Prod.ext

    · unfold offset
      unfold
        correctedConcreteObservationPositiveAdditiveParetoProfileCardinalityOffset

      omega

    · unfold offset
      unfold
        correctedConcreteObservationPositiveAdditiveParetoProfileCardinalityOffset

      omega

/-- Every profile's normalized cardinality offset is at most the tradeoff
width. -/
theorem positiveAdditiveParetoProfile_cardinalityOffset_le_width
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
    correctedConcreteObservationPositiveAdditiveParetoProfileCardinalityOffset
          minimumCardinalityResult
          profile <=
      correctedConcreteObservationPositiveAdditiveParetoProfileTradeoffWidth
        minimumCardinalityResult
        minimumAdditiveResult := by

  have hBounds :=
    positiveAdditiveParetoProfile_between_endpoints
      minimumCardinalityResult
      minimumAdditiveResult
      hProfile

  unfold
    correctedConcreteObservationPositiveAdditiveParetoProfileCardinalityOffset
    correctedConcreteObservationPositiveAdditiveParetoProfileTradeoffWidth

  omega

/-- The number of rank-minimizing Pareto profiles is at most `width + 1`. -/
theorem
    correctedConcreteObservationPositiveAdditiveRankMinimizingParetoProfiles_card_le_width_add_one :
    (correctedConcreteObservationPositiveAdditiveRankMinimizingParetoProfiles
        (z := z)
        obsFamily
        f
        coordinateWeight
        U
        language
        hTarget).card <=
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
        hTarget).card <=
      (correctedConcreteObservationPositiveAdditiveParetoProfileTradeoffInterval
        minimumCardinalityResult
        minimumAdditiveResult).card :=
          Finset.card_le_card
            (correctedConcreteObservationPositiveAdditiveRankMinimizingParetoProfiles_subset_tradeoffInterval
              minimumCardinalityResult
              minimumAdditiveResult)

    _ <=
      correctedConcreteObservationPositiveAdditiveParetoProfileTradeoffWidth
          minimumCardinalityResult
          minimumAdditiveResult +
        1 :=
          positiveAdditiveParetoProfile_tradeoffInterval_card_le
            minimumCardinalityResult
            minimumAdditiveResult

/-- The width bound refines the preceding rank-plus-one bound. -/
theorem
    positiveAdditiveParetoProfile_width_add_one_le_rank_add_one :
    correctedConcreteObservationPositiveAdditiveParetoProfileTradeoffWidth
          minimumCardinalityResult
          minimumAdditiveResult +
        1 <=
      ambientTargetObservationSelectionPositiveAdditiveMinimumCost
          (z := z)
          obsFamily
          f
          coordinateWeight
          U
          hTarget +
        1 := by

  exact
    Nat.add_le_add_right
      (positiveAdditiveParetoProfile_tradeoffWidth_le_rank
        minimumCardinalityResult
        minimumAdditiveResult)
      1

end ParetoProfileTradeoffInterval


section ParetoProfileTradeoffRigidity

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

/-- Width zero is equivalent to equality of the two endpoint profiles. -/
theorem positiveAdditiveParetoProfile_tradeoffWidth_eq_zero_iff_endpoints_eq :
    correctedConcreteObservationPositiveAdditiveParetoProfileTradeoffWidth
          minimumCardinalityResult
          minimumAdditiveResult =
        0 ↔
      minimumCardinalityResult.profile =
        minimumAdditiveResult.profile := by

  constructor

  · intro hWidthZero

    have hCardOrder :
        minimumCardinalityResult.profile.1 <=
          minimumAdditiveResult.profile.1 :=
      minimumCardinalityResult.profile_card_le
        minimumAdditiveResult.profile_mem

    have hCardEq :
        minimumCardinalityResult.profile.1 =
          minimumAdditiveResult.profile.1 := by

      unfold
        correctedConcreteObservationPositiveAdditiveParetoProfileTradeoffWidth
        at hWidthZero

      omega

    have hMinimumSum :=
      minimumCardinalityResult.profile_sum_eq_rank

    have hMaximumSum :=
      minimumAdditiveResult.profile_sum_eq_rank

    apply Prod.ext

    · exact hCardEq

    · omega

  · intro hEndpoints

    unfold
      correctedConcreteObservationPositiveAdditiveParetoProfileTradeoffWidth

    rw [hEndpoints]

    simp

/-- Width zero is equivalent to the profile set being a singleton. -/
theorem positiveAdditiveParetoProfile_tradeoffWidth_eq_zero_iff_profiles_singleton :
    correctedConcreteObservationPositiveAdditiveParetoProfileTradeoffWidth
          minimumCardinalityResult
          minimumAdditiveResult =
        0 ↔
      correctedConcreteObservationPositiveAdditiveRankMinimizingParetoProfiles
          (z := z)
          obsFamily
          f
          coordinateWeight
          U
          language
          hTarget =
        {minimumCardinalityResult.profile} := by

  rw [
    positiveAdditiveParetoProfile_tradeoffWidth_eq_zero_iff_endpoints_eq
      minimumCardinalityResult
      minimumAdditiveResult,
    positiveAdditiveParetoProfile_endpoints_eq_iff_profiles_singleton
      minimumCardinalityResult
      minimumAdditiveResult
  ]

/-- Positive width is equivalent to the endpoint profiles being distinct. -/
theorem positiveAdditiveParetoProfile_tradeoffWidth_pos_iff_endpoints_ne :
    0 <
        correctedConcreteObservationPositiveAdditiveParetoProfileTradeoffWidth
          minimumCardinalityResult
          minimumAdditiveResult ↔
      minimumCardinalityResult.profile ≠
        minimumAdditiveResult.profile := by

  constructor

  · intro hPositive hEndpoints

    have hZero :
        correctedConcreteObservationPositiveAdditiveParetoProfileTradeoffWidth
            minimumCardinalityResult
            minimumAdditiveResult =
          0 :=
      (positiveAdditiveParetoProfile_tradeoffWidth_eq_zero_iff_endpoints_eq
        minimumCardinalityResult
        minimumAdditiveResult).mpr
        hEndpoints

    omega

  · intro hEndpointsNe

    by_contra hNotPositive

    have hZero :
        correctedConcreteObservationPositiveAdditiveParetoProfileTradeoffWidth
            minimumCardinalityResult
            minimumAdditiveResult =
          0 := by
      omega

    exact
      hEndpointsNe
        ((positiveAdditiveParetoProfile_tradeoffWidth_eq_zero_iff_endpoints_eq
          minimumCardinalityResult
          minimumAdditiveResult).mp
          hZero)

end ParetoProfileTradeoffRigidity


section ParetoProfileTradeoffBottomRanks

variable {α : Type u}
variable {ι : Type v}
variable {M : Type w}
variable [DecidableEq ι]
variable [Monoid M]
variable (obsFamily : ι → α → M)
variable (f : Nat)
variable (coordinateWeight : ι → Nat)
variable (U : Finset ι)

/-- Positive-additive rank zero forces zero Pareto-profile width. -/
theorem positiveAdditiveParetoProfile_tradeoffWidth_eq_zero_of_rank_zero
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
    correctedConcreteObservationPositiveAdditiveParetoProfileTradeoffWidth
        minimumCardinalityResult
        minimumAdditiveResult =
      0 := by

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

  have hEndpoints :=
    positiveAdditiveParetoProfile_endpoints_eq_zero
      (z := z)
      obsFamily
      f
      coordinateWeight
      U
      hTarget
      hRankZero

  unfold
    correctedConcreteObservationPositiveAdditiveParetoProfileTradeoffWidth

  rw [hEndpoints.1, hEndpoints.2]

  simp

/-- Positive-additive rank one forces zero Pareto-profile width. -/
theorem positiveAdditiveParetoProfile_tradeoffWidth_eq_zero_of_rank_one
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
    correctedConcreteObservationPositiveAdditiveParetoProfileTradeoffWidth
        minimumCardinalityResult
        minimumAdditiveResult =
      0 := by

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

  have hEndpoints :=
    positiveAdditiveParetoProfile_endpoints_eq_one
      (z := z)
      obsFamily
      f
      coordinateWeight
      U
      hTarget
      hRankOne

  unfold
    correctedConcreteObservationPositiveAdditiveParetoProfileTradeoffWidth

  rw [hEndpoints.1, hEndpoints.2]

  simp

end ParetoProfileTradeoffBottomRanks


section ActualSelectorTradeoffInterval

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
  (result :
    CorrectedConcreteObservationPositiveAdditiveParetoRankSelectionResult
      (z := z)
      obsFamily
      f
      coordinateWeight
      U
      language
      hTarget)

/-- The actual selector's profile belongs to the endpoint tradeoff interval. -/
theorem
    correctedConcreteObservationPositiveAdditiveSelectedParetoRankProfile_mem_tradeoffInterval :
    correctedConcreteObservationPositiveAdditiveSelectedParetoRankProfile
        result ∈
      correctedConcreteObservationPositiveAdditiveParetoProfileTradeoffInterval
        minimumCardinalityResult
        minimumAdditiveResult := by

  apply
    correctedConcreteObservationPositiveAdditiveRankMinimizingParetoProfiles_subset_tradeoffInterval
      minimumCardinalityResult
      minimumAdditiveResult

  exact
    correctedConcreteObservationPositiveAdditiveSelectedParetoRankProfile_mem
      (z := z)
      result

/-- The actual selector's normalized cardinality offset is bounded by width. -/
theorem
    correctedConcreteObservationPositiveAdditiveSelectedParetoRankProfile_offset_le_width :
    correctedConcreteObservationPositiveAdditiveParetoProfileCardinalityOffset
          minimumCardinalityResult
          (correctedConcreteObservationPositiveAdditiveSelectedParetoRankProfile
            result) <=
      correctedConcreteObservationPositiveAdditiveParetoProfileTradeoffWidth
        minimumCardinalityResult
        minimumAdditiveResult := by

  exact
    positiveAdditiveParetoProfile_cardinalityOffset_le_width
      minimumCardinalityResult
      minimumAdditiveResult
      (correctedConcreteObservationPositiveAdditiveSelectedParetoRankProfile_mem
        (z := z)
        result)

end ActualSelectorTradeoffInterval


section ParetoProfileWidthFinalPackage

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

/-- Final width equality, sharp profile-count bound, rigidity, actual-selector
interval, and certified-learning package. -/
theorem
    correctedConcreteCertifiedWorkingGrammar_observationSelectionParetoRankProfileWidth_package :
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
      let width :=
        correctedConcreteObservationPositiveAdditiveParetoProfileTradeoffWidth
          minimumCardinalityResult
          minimumAdditiveResult
      width =
          correctedConcreteObservationPositiveAdditiveParetoProfileAdditiveTradeoffWidth
            minimumCardinalityResult
            minimumAdditiveResult ∧
        width <=
          ambientTargetObservationSelectionPositiveAdditiveMinimumCost
            (z := z)
            obsFamily
            f
            coordinateWeight
            U
            hTarget ∧
        (correctedConcreteObservationPositiveAdditiveRankMinimizingParetoProfiles
            (z := z)
            obsFamily
            f
            coordinateWeight
            U
            language
            hTarget).card <=
          width + 1 ∧
        (width = 0 ↔
          correctedConcreteObservationPositiveAdditiveRankMinimizingParetoProfiles
              (z := z)
              obsFamily
              f
              coordinateWeight
              U
              language
              hTarget =
            {minimumCardinalityResult.profile}) ∧
        correctedConcreteObservationPositiveAdditiveSelectedParetoRankProfile
            result ∈
          correctedConcreteObservationPositiveAdditiveParetoProfileTradeoffInterval
            minimumCardinalityResult
            minimumAdditiveResult ∧
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

  let width :=
    correctedConcreteObservationPositiveAdditiveParetoProfileTradeoffWidth
      minimumCardinalityResult
      minimumAdditiveResult

  have hCertified :=
    CorrectedConcreteObservationPositiveAdditiveParetoRankSelectionResult.certified_package
      (z := z)
      hα
      result

  exact
    ⟨positiveAdditiveParetoProfile_tradeoffWidth_eq_additiveTradeoffWidth
        minimumCardinalityResult
        minimumAdditiveResult,
      positiveAdditiveParetoProfile_tradeoffWidth_le_rank
        minimumCardinalityResult
        minimumAdditiveResult,
      correctedConcreteObservationPositiveAdditiveRankMinimizingParetoProfiles_card_le_width_add_one
        minimumCardinalityResult
        minimumAdditiveResult,
      positiveAdditiveParetoProfile_tradeoffWidth_eq_zero_iff_profiles_singleton
        minimumCardinalityResult
        minimumAdditiveResult,
      correctedConcreteObservationPositiveAdditiveSelectedParetoRankProfile_mem_tradeoffInterval
        minimumCardinalityResult
        minimumAdditiveResult
        result,
      hCertified.1⟩

end ParetoProfileWidthFinalPackage

end MCFG
