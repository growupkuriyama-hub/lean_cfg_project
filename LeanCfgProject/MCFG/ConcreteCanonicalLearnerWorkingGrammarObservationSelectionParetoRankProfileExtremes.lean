/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG.ConcreteCanonicalLearnerWorkingGrammarObservationSelectionParetoRankProfiles

/-!
# ConcreteCanonicalLearnerWorkingGrammarObservationSelectionParetoRankProfileExtremes.lean

The preceding file compresses all positive-additive-rank-minimizing Pareto
selections to a finite set of two-dimensional profiles

```text
(cardinality, additive coordinate weight).
```

Every such profile lies on the exact rank line.

This file selects the two endpoint profiles of that finite tradeoff set.

## Minimum-cardinality endpoint

Among all rank-minimizing Pareto profiles, define the least cardinality by
`Nat.find`.  Select an actual profile attaining it.

Because all profiles have the same coordinate sum, this endpoint simultaneously
has the greatest additive coordinate weight.

## Minimum-additive endpoint

Dually, define the least additive coordinate weight and select an actual
profile attaining it.

This endpoint simultaneously has the greatest selected-set cardinality.

Thus every rank-minimizing profile `(c,a)` lies in the interval

```text
minimumCardinality ≤ c ≤ maximumCardinality,
minimumAdditiveCost ≤ a ≤ maximumAdditiveCost.
```

The two endpoint equations are exact:

```text
minimumCardinality + maximumAdditiveCost = rank,
maximumCardinality + minimumAdditiveCost = rank.
```

## Tradeoff width

The cardinality width and additive-weight width agree:

```text
maximumCardinality - minimumCardinality
  =
maximumAdditiveCost - minimumAdditiveCost.
```

This is the exact amount of tradeoff available while preserving the same
positive additive observation-selection rank.

The endpoint profiles coincide exactly when the finite rank-minimizing profile
set is a singleton.

## Bottom ranks

At rank zero both endpoints are `(0,0)`.
At rank one both endpoints are `(1,0)`.

## Certified endpoint witnesses

Each endpoint profile is realized by an actual Pareto-optimal selected product.
The corresponding selected-product certified learner identifies the target and
has an exact checked grammar output at its minimum certified-description rank.

No relation between observation-profile endpoints and grammar-description rank
is asserted.

No target grammar is supplied to any learner.
No `sorry`, `admit`, or `axiom` is used.
-/

namespace MCFG

universe u v w z


section ParetoProfileEndpointBudgetDefinitions

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

/-- Some rank-minimizing Pareto profile has cardinality at most `budget`. -/
def
    CorrectedConcreteObservationPositiveAdditiveParetoProfileAtCardinalityBudget
    (budget : Nat) :
    Prop :=
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
      profile.1 <= budget

/-- Existence of a finite cardinality budget for the rank-minimizing Pareto
profile set. -/
def
    HasCorrectedConcreteObservationPositiveAdditiveParetoProfileCardinalityBudget :
    Prop :=
  ∃ budget : Nat,
    CorrectedConcreteObservationPositiveAdditiveParetoProfileAtCardinalityBudget
      (z := z)
      obsFamily
      f
      coordinateWeight
      U
      language
      hTarget
      budget

/-- Some rank-minimizing Pareto profile has additive coordinate cost at most
`budget`. -/
def
    CorrectedConcreteObservationPositiveAdditiveParetoProfileAtAdditiveBudget
    (budget : Nat) :
    Prop :=
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
      profile.2 <= budget

/-- Existence of a finite additive-coordinate budget for the rank-minimizing
Pareto profile set. -/
def
    HasCorrectedConcreteObservationPositiveAdditiveParetoProfileAdditiveBudget :
    Prop :=
  ∃ budget : Nat,
    CorrectedConcreteObservationPositiveAdditiveParetoProfileAtAdditiveBudget
      (z := z)
      obsFamily
      f
      coordinateWeight
      U
      language
      hTarget
      budget

/-- A cardinality budget exists because the finite profile set is nonempty. -/
theorem
    hasPositiveAdditiveParetoProfileCardinalityBudget :
    HasCorrectedConcreteObservationPositiveAdditiveParetoProfileCardinalityBudget
      (z := z)
      obsFamily
      f
      coordinateWeight
      U
      language
      hTarget := by

  rcases
      correctedConcreteObservationPositiveAdditiveRankMinimizingParetoProfiles_nonempty
        (z := z)
        (obsFamily := obsFamily)
        (f := f)
        (coordinateWeight := coordinateWeight)
        (U := U)
        (language := language)
        (hTarget := hTarget) with
    ⟨profile, hProfile⟩

  exact
    ⟨profile.1,
      profile,
      hProfile,
      Nat.le_refl _⟩

/-- An additive-coordinate budget exists because the finite profile set is
nonempty. -/
theorem
    hasPositiveAdditiveParetoProfileAdditiveBudget :
    HasCorrectedConcreteObservationPositiveAdditiveParetoProfileAdditiveBudget
      (z := z)
      obsFamily
      f
      coordinateWeight
      U
      language
      hTarget := by

  rcases
      correctedConcreteObservationPositiveAdditiveRankMinimizingParetoProfiles_nonempty
        (z := z)
        (obsFamily := obsFamily)
        (f := f)
        (coordinateWeight := coordinateWeight)
        (U := U)
        (language := language)
        (hTarget := hTarget) with
    ⟨profile, hProfile⟩

  exact
    ⟨profile.2,
      profile,
      hProfile,
      Nat.le_refl _⟩

end ParetoProfileEndpointBudgetDefinitions


section ParetoProfileEndpointValues

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

/-- Least cardinality coordinate among all rank-minimizing Pareto profiles. -/
noncomputable def
    correctedConcreteObservationPositiveAdditiveParetoProfileMinimumCardinality :
    Nat :=
  Nat.find
    (hasPositiveAdditiveParetoProfileCardinalityBudget
      (z := z)
      obsFamily
      f
      coordinateWeight
      U
      language
      hTarget)

/-- Least additive coordinate among all rank-minimizing Pareto profiles. -/
noncomputable def
    correctedConcreteObservationPositiveAdditiveParetoProfileMinimumAdditiveCost :
    Nat :=
  Nat.find
    (hasPositiveAdditiveParetoProfileAdditiveBudget
      (z := z)
      obsFamily
      f
      coordinateWeight
      U
      language
      hTarget)

/-- The minimum profile cardinality budget is attained. -/
theorem
    positiveAdditiveParetoProfileMinimumCardinality_spec :
    CorrectedConcreteObservationPositiveAdditiveParetoProfileAtCardinalityBudget
      (z := z)
      obsFamily
      f
      coordinateWeight
      U
      language
      hTarget
      (correctedConcreteObservationPositiveAdditiveParetoProfileMinimumCardinality
        (z := z)
        obsFamily
        f
        coordinateWeight
        U
        language
        hTarget) := by

  exact
    Nat.find_spec
      (hasPositiveAdditiveParetoProfileCardinalityBudget
        (z := z)
        obsFamily
        f
        coordinateWeight
        U
        language
        hTarget)

/-- The minimum additive profile budget is attained. -/
theorem
    positiveAdditiveParetoProfileMinimumAdditiveCost_spec :
    CorrectedConcreteObservationPositiveAdditiveParetoProfileAtAdditiveBudget
      (z := z)
      obsFamily
      f
      coordinateWeight
      U
      language
      hTarget
      (correctedConcreteObservationPositiveAdditiveParetoProfileMinimumAdditiveCost
        (z := z)
        obsFamily
        f
        coordinateWeight
        U
        language
        hTarget) := by

  exact
    Nat.find_spec
      (hasPositiveAdditiveParetoProfileAdditiveBudget
        (z := z)
        obsFamily
        f
        coordinateWeight
        U
        language
        hTarget)

/-- Minimum profile cardinality is no greater than the cardinality coordinate
of every rank-minimizing Pareto profile. -/
theorem
    positiveAdditiveParetoProfileMinimumCardinality_le
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
    correctedConcreteObservationPositiveAdditiveParetoProfileMinimumCardinality
        (z := z)
        obsFamily
        f
        coordinateWeight
        U
        language
        hTarget <=
      profile.1 := by

  apply
    Nat.find_min'
      (hasPositiveAdditiveParetoProfileCardinalityBudget
        (z := z)
        obsFamily
        f
        coordinateWeight
        U
        language
        hTarget)

  exact
    ⟨profile,
      hProfile,
      Nat.le_refl _⟩

/-- Minimum additive profile cost is no greater than the additive coordinate of
every rank-minimizing Pareto profile. -/
theorem
    positiveAdditiveParetoProfileMinimumAdditiveCost_le
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
    correctedConcreteObservationPositiveAdditiveParetoProfileMinimumAdditiveCost
        (z := z)
        obsFamily
        f
        coordinateWeight
        U
        language
        hTarget <=
      profile.2 := by

  apply
    Nat.find_min'
      (hasPositiveAdditiveParetoProfileAdditiveBudget
        (z := z)
        obsFamily
        f
        coordinateWeight
        U
        language
        hTarget)

  exact
    ⟨profile,
      hProfile,
      Nat.le_refl _⟩

end ParetoProfileEndpointValues


section ParetoProfileEndpointResultDefinitions

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

/-- An actual rank-minimizing Pareto profile attaining minimum cardinality. -/
structure
    CorrectedConcreteObservationPositiveAdditiveParetoMinimumCardinalityProfileResult where

  profile :
    Nat × Nat

  profile_mem :
    profile ∈
      correctedConcreteObservationPositiveAdditiveRankMinimizingParetoProfiles
        (z := z)
        obsFamily
        f
        coordinateWeight
        U
        language
        hTarget

  profile_card_eq :
    profile.1 =
      correctedConcreteObservationPositiveAdditiveParetoProfileMinimumCardinality
        (z := z)
        obsFamily
        f
        coordinateWeight
        U
        language
        hTarget

/-- An actual rank-minimizing Pareto profile attaining minimum additive
coordinate cost. -/
structure
    CorrectedConcreteObservationPositiveAdditiveParetoMinimumAdditiveProfileResult where

  profile :
    Nat × Nat

  profile_mem :
    profile ∈
      correctedConcreteObservationPositiveAdditiveRankMinimizingParetoProfiles
        (z := z)
        obsFamily
        f
        coordinateWeight
        U
        language
        hTarget

  profile_additive_eq :
    profile.2 =
      correctedConcreteObservationPositiveAdditiveParetoProfileMinimumAdditiveCost
        (z := z)
        obsFamily
        f
        coordinateWeight
        U
        language
        hTarget

/-- Choose one minimum-cardinality endpoint profile. -/
noncomputable def
    correctedConcreteObservationPositiveAdditiveParetoMinimumCardinalityProfileResult :
    CorrectedConcreteObservationPositiveAdditiveParetoMinimumCardinalityProfileResult
      (z := z)
      obsFamily
      f
      coordinateWeight
      U
      language
      hTarget := by

  rcases
      positiveAdditiveParetoProfileMinimumCardinality_spec
        (z := z)
        obsFamily
        f
        coordinateWeight
        U
        language
        hTarget with
    ⟨profile, hProfile, hCardLe⟩

  have hMinimumLe :
      correctedConcreteObservationPositiveAdditiveParetoProfileMinimumCardinality
          (z := z)
          obsFamily
          f
          coordinateWeight
          U
          language
          hTarget <=
        profile.1 :=
    positiveAdditiveParetoProfileMinimumCardinality_le
      (z := z)
      obsFamily
      f
      coordinateWeight
      U
      language
      hTarget
      hProfile

  exact
    ⟨profile,
      hProfile,
      Nat.le_antisymm
        hCardLe
        hMinimumLe⟩

/-- Choose one minimum-additive-cost endpoint profile. -/
noncomputable def
    correctedConcreteObservationPositiveAdditiveParetoMinimumAdditiveProfileResult :
    CorrectedConcreteObservationPositiveAdditiveParetoMinimumAdditiveProfileResult
      (z := z)
      obsFamily
      f
      coordinateWeight
      U
      language
      hTarget := by

  rcases
      positiveAdditiveParetoProfileMinimumAdditiveCost_spec
        (z := z)
        obsFamily
        f
        coordinateWeight
        U
        language
        hTarget with
    ⟨profile, hProfile, hAdditiveLe⟩

  have hMinimumLe :
      correctedConcreteObservationPositiveAdditiveParetoProfileMinimumAdditiveCost
          (z := z)
          obsFamily
          f
          coordinateWeight
          U
          language
          hTarget <=
        profile.2 :=
    positiveAdditiveParetoProfileMinimumAdditiveCost_le
      (z := z)
      obsFamily
      f
      coordinateWeight
      U
      language
      hTarget
      hProfile

  exact
    ⟨profile,
      hProfile,
      Nat.le_antisymm
        hAdditiveLe
        hMinimumLe⟩

end ParetoProfileEndpointResultDefinitions


namespace CorrectedConcreteObservationPositiveAdditiveParetoMinimumCardinalityProfileResult

section MinimumCardinalityEndpointProperties

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
  (result :
    CorrectedConcreteObservationPositiveAdditiveParetoMinimumCardinalityProfileResult
      (z := z)
      obsFamily
      f
      coordinateWeight
      U
      language
      hTarget)

/-- The minimum-cardinality endpoint lies on the exact target-rank line. -/
theorem profile_sum_eq_rank :
    result.profile.1 + result.profile.2 =
      ambientTargetObservationSelectionPositiveAdditiveMinimumCost
        (z := z)
        obsFamily
        f
        coordinateWeight
        U
        hTarget := by

  exact
    correctedConcreteObservationPositiveAdditiveRankMinimizingParetoProfile_sum_eq_rank
      (z := z)
      result.profile_mem

/-- The endpoint's cardinality is no greater than that of every rank-minimizing
profile. -/
theorem profile_card_le
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
    result.profile.1 <= profile.1 := by

  rw [result.profile_card_eq]

  exact
    positiveAdditiveParetoProfileMinimumCardinality_le
      (z := z)
      obsFamily
      f
      coordinateWeight
      U
      language
      hTarget
      hProfile

/-- The minimum-cardinality endpoint has greatest additive coordinate cost. -/
theorem profile_additive_ge
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
    profile.2 <= result.profile.2 := by

  have hResultSum :=
    result.profile_sum_eq_rank

  have hProfileSum :=
    correctedConcreteObservationPositiveAdditiveRankMinimizingParetoProfile_sum_eq_rank
      (z := z)
      hProfile

  have hCardLe :=
    result.profile_card_le
      hProfile

  omega

end MinimumCardinalityEndpointProperties

end CorrectedConcreteObservationPositiveAdditiveParetoMinimumCardinalityProfileResult


namespace CorrectedConcreteObservationPositiveAdditiveParetoMinimumAdditiveProfileResult

section MinimumAdditiveEndpointProperties

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
  (result :
    CorrectedConcreteObservationPositiveAdditiveParetoMinimumAdditiveProfileResult
      (z := z)
      obsFamily
      f
      coordinateWeight
      U
      language
      hTarget)

/-- The minimum-additive endpoint lies on the exact target-rank line. -/
theorem profile_sum_eq_rank :
    result.profile.1 + result.profile.2 =
      ambientTargetObservationSelectionPositiveAdditiveMinimumCost
        (z := z)
        obsFamily
        f
        coordinateWeight
        U
        hTarget := by

  exact
    correctedConcreteObservationPositiveAdditiveRankMinimizingParetoProfile_sum_eq_rank
      (z := z)
      result.profile_mem

/-- The endpoint's additive coordinate is no greater than that of every
rank-minimizing profile. -/
theorem profile_additive_le
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
    result.profile.2 <= profile.2 := by

  rw [result.profile_additive_eq]

  exact
    positiveAdditiveParetoProfileMinimumAdditiveCost_le
      (z := z)
      obsFamily
      f
      coordinateWeight
      U
      language
      hTarget
      hProfile

/-- The minimum-additive endpoint has greatest selected-set cardinality. -/
theorem profile_card_ge
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
    profile.1 <= result.profile.1 := by

  have hResultSum :=
    result.profile_sum_eq_rank

  have hProfileSum :=
    correctedConcreteObservationPositiveAdditiveRankMinimizingParetoProfile_sum_eq_rank
      (z := z)
      hProfile

  have hAdditiveLe :=
    result.profile_additive_le
      hProfile

  omega

end MinimumAdditiveEndpointProperties

end CorrectedConcreteObservationPositiveAdditiveParetoMinimumAdditiveProfileResult


section ParetoProfileEndpointEnvelope

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

/-- Every rank-minimizing Pareto profile lies between the two endpoint
profiles in both coordinates. -/
theorem positiveAdditiveParetoProfile_between_endpoints
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
    minimumCardinalityResult.profile.1 <= profile.1 ∧
      profile.1 <= minimumAdditiveResult.profile.1 ∧
      minimumAdditiveResult.profile.2 <= profile.2 ∧
      profile.2 <= minimumCardinalityResult.profile.2 := by

  exact
    ⟨minimumCardinalityResult.profile_card_le
        hProfile,
      minimumAdditiveResult.profile_card_ge
        hProfile,
      minimumAdditiveResult.profile_additive_le
        hProfile,
      minimumCardinalityResult.profile_additive_ge
        hProfile⟩

/-- The two endpoint profiles satisfy the exact target-rank equations. -/
theorem positiveAdditiveParetoProfile_endpoint_rank_equations
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
    minimumCardinalityResult.profile.1 +
          minimumCardinalityResult.profile.2 =
        ambientTargetObservationSelectionPositiveAdditiveMinimumCost
          (z := z)
          obsFamily
          f
          coordinateWeight
          U
          hTarget ∧
      minimumAdditiveResult.profile.1 +
          minimumAdditiveResult.profile.2 =
        ambientTargetObservationSelectionPositiveAdditiveMinimumCost
          (z := z)
          obsFamily
          f
          coordinateWeight
          U
          hTarget := by

  exact
    ⟨minimumCardinalityResult.profile_sum_eq_rank,
      minimumAdditiveResult.profile_sum_eq_rank⟩

/-- The cardinality and additive-coordinate tradeoff widths are equal. -/
theorem positiveAdditiveParetoProfile_endpoint_width_eq
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
    minimumAdditiveResult.profile.1 -
          minimumCardinalityResult.profile.1 =
      minimumCardinalityResult.profile.2 -
        minimumAdditiveResult.profile.2 := by

  have hCardOrder :
      minimumCardinalityResult.profile.1 <=
        minimumAdditiveResult.profile.1 :=
    minimumCardinalityResult.profile_card_le
      minimumAdditiveResult.profile_mem

  have hAdditiveOrder :
      minimumAdditiveResult.profile.2 <=
        minimumCardinalityResult.profile.2 :=
    minimumAdditiveResult.profile_additive_le
      minimumCardinalityResult.profile_mem

  have hSum₀ :=
    minimumCardinalityResult.profile_sum_eq_rank

  have hSum₁ :=
    minimumAdditiveResult.profile_sum_eq_rank

  omega

/-- The two endpoint profiles coincide exactly when the rank-minimizing profile
set is a singleton. -/
theorem positiveAdditiveParetoProfile_endpoints_eq_iff_profiles_singleton
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
    minimumCardinalityResult.profile =
        minimumAdditiveResult.profile ↔
      correctedConcreteObservationPositiveAdditiveRankMinimizingParetoProfiles
          (z := z)
          obsFamily
          f
          coordinateWeight
          U
          language
          hTarget =
        {minimumCardinalityResult.profile} := by

  constructor

  · intro hEndpoints

    ext profile

    constructor

    · intro hProfile

      have hBounds :=
        positiveAdditiveParetoProfile_between_endpoints
          minimumCardinalityResult
          minimumAdditiveResult
          hProfile

      have hProfileEq :
          profile = minimumCardinalityResult.profile := by

        apply Prod.ext

        · rw [← hEndpoints] at hBounds

          omega

        · have hSumProfile :=
            correctedConcreteObservationPositiveAdditiveRankMinimizingParetoProfile_sum_eq_rank
              (z := z)
              hProfile

          have hSumMinimum :=
            minimumCardinalityResult.profile_sum_eq_rank

          have hCardEq :
              profile.1 =
                minimumCardinalityResult.profile.1 := by

            rw [← hEndpoints] at hBounds

            omega

          omega

      simp [hProfileEq]

    · intro hProfile

      have hProfileEq :
          profile = minimumCardinalityResult.profile := by
        simpa using hProfile

      subst profile

      exact
        minimumCardinalityResult.profile_mem

  · intro hSingleton

    have hMinimumAdditiveMem :
        minimumAdditiveResult.profile ∈
          ({minimumCardinalityResult.profile} :
            Finset (Nat × Nat)) := by

      rw [← hSingleton]

      exact
        minimumAdditiveResult.profile_mem

    simpa using
      hMinimumAdditiveMem

end ParetoProfileEndpointEnvelope


section ParetoProfileEndpointBottomRanks

variable {α : Type u}
variable {ι : Type v}
variable {M : Type w}
variable [DecidableEq ι]
variable [Monoid M]
variable (obsFamily : ι → α → M)
variable (f : Nat)
variable (coordinateWeight : ι → Nat)
variable (U : Finset ι)

/-- At rank zero, both endpoint profiles are `(0,0)`. -/
theorem positiveAdditiveParetoProfile_endpoints_eq_zero
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
    minimumCardinalityResult.profile = (0, 0) ∧
      minimumAdditiveResult.profile = (0, 0) := by

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

  have hProfiles :=
    positiveAdditiveRankMinimizingParetoProfiles_eq_singleton_zero
      (z := z)
      obsFamily
      f
      coordinateWeight
      U
      hTarget
      hRankZero

  have hMinCardMem :
      minimumCardinalityResult.profile ∈
        ({(0, 0)} : Finset (Nat × Nat)) := by

    rw [← hProfiles]

    exact
      minimumCardinalityResult.profile_mem

  have hMinAddMem :
      minimumAdditiveResult.profile ∈
        ({(0, 0)} : Finset (Nat × Nat)) := by

    rw [← hProfiles]

    exact
      minimumAdditiveResult.profile_mem

  exact
    ⟨by simpa using hMinCardMem,
      by simpa using hMinAddMem⟩

/-- At rank one, both endpoint profiles are `(1,0)`. -/
theorem positiveAdditiveParetoProfile_endpoints_eq_one
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
    minimumCardinalityResult.profile = (1, 0) ∧
      minimumAdditiveResult.profile = (1, 0) := by

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

  have hProfiles :=
    positiveAdditiveRankMinimizingParetoProfiles_eq_singleton_one
      (z := z)
      obsFamily
      f
      coordinateWeight
      U
      hTarget
      hRankOne

  have hMinCardMem :
      minimumCardinalityResult.profile ∈
        ({(1, 0)} : Finset (Nat × Nat)) := by

    rw [← hProfiles]

    exact
      minimumCardinalityResult.profile_mem

  have hMinAddMem :
      minimumAdditiveResult.profile ∈
        ({(1, 0)} : Finset (Nat × Nat)) := by

    rw [← hProfiles]

    exact
      minimumAdditiveResult.profile_mem

  exact
    ⟨by simpa using hMinCardMem,
      by simpa using hMinAddMem⟩

end ParetoProfileEndpointBottomRanks


section ParetoProfileEndpointCertifiedWitnesses

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

/-- The minimum-cardinality endpoint profile has an actual certified selected
product witness. -/
theorem
    positiveAdditiveParetoMinimumCardinalityProfile_exists_certifiedWitness
    (result :
      CorrectedConcreteObservationPositiveAdditiveParetoMinimumCardinalityProfileResult
        (z := z)
        obsFamily
        f
        coordinateWeight
        U
        language
        hTarget) :
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
        result.profile ∧
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

  rcases
      positiveAdditiveRankMinimizingParetoProfile_exists_certifiedWitness
        (z := z)
        hα
        result.profile_mem with
    ⟨S,
      hSelected,
      hProfile,
      hPareto,
      hCost,
      hIdentifies,
      C,
      hLanguage,
      hBits,
      hSearch⟩

  exact
    ⟨S,
      hSelected,
      hProfile,
      hIdentifies,
      C,
      hLanguage,
      hBits,
      hSearch⟩

/-- The minimum-additive endpoint profile has an actual certified selected
product witness. -/
theorem
    positiveAdditiveParetoMinimumAdditiveProfile_exists_certifiedWitness
    (result :
      CorrectedConcreteObservationPositiveAdditiveParetoMinimumAdditiveProfileResult
        (z := z)
        obsFamily
        f
        coordinateWeight
        U
        language
        hTarget) :
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
        result.profile ∧
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

  rcases
      positiveAdditiveRankMinimizingParetoProfile_exists_certifiedWitness
        (z := z)
        hα
        result.profile_mem with
    ⟨S,
      hSelected,
      hProfile,
      hPareto,
      hCost,
      hIdentifies,
      C,
      hLanguage,
      hBits,
      hSearch⟩

  exact
    ⟨S,
      hSelected,
      hProfile,
      hIdentifies,
      C,
      hLanguage,
      hBits,
      hSearch⟩

end ParetoProfileEndpointCertifiedWitnesses


section ParetoProfileExtremesFinalPackage

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

/-- Final endpoint existence, envelope, equal-width tradeoff, and certified
endpoint-witness package. -/
theorem
    correctedConcreteCertifiedWorkingGrammar_observationSelectionParetoRankProfileExtremes_package :
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
      minimumCardinalityResult.profile ∈
          correctedConcreteObservationPositiveAdditiveRankMinimizingParetoProfiles
            (z := z)
            obsFamily
            f
            coordinateWeight
            U
            language
            hTarget ∧
        minimumAdditiveResult.profile ∈
          correctedConcreteObservationPositiveAdditiveRankMinimizingParetoProfiles
            (z := z)
            obsFamily
            f
            coordinateWeight
            U
            language
            hTarget ∧
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
            minimumCardinalityResult.profile.1 <= profile.1 ∧
              profile.1 <= minimumAdditiveResult.profile.1 ∧
              minimumAdditiveResult.profile.2 <= profile.2 ∧
              profile.2 <= minimumCardinalityResult.profile.2) ∧
        minimumAdditiveResult.profile.1 -
              minimumCardinalityResult.profile.1 =
          minimumCardinalityResult.profile.2 -
            minimumAdditiveResult.profile.2 ∧
        (∃
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
            minimumCardinalityResult.profile ∧
            IdentifiesLanguageFromPositiveData
              (correctedConcreteCertifiedWorkingGrammarHypLanguage
                (selectedObservationProduct obsFamily S)
                f)
              (correctedConcreteCertifiedWorkingGrammarLearner
                hα
                (selectedObservationProduct obsFamily S)
                f)
              language) ∧
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
            minimumAdditiveResult.profile ∧
            IdentifiesLanguageFromPositiveData
              (correctedConcreteCertifiedWorkingGrammarHypLanguage
                (selectedObservationProduct obsFamily S)
                f)
              (correctedConcreteCertifiedWorkingGrammarLearner
                hα
                (selectedObservationProduct obsFamily S)
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

  rcases
      positiveAdditiveParetoMinimumCardinalityProfile_exists_certifiedWitness
        (z := z)
        hα
        minimumCardinalityResult with
    ⟨S₀,
      hSelected₀,
      hProfile₀,
      hIdentifies₀,
      C₀,
      hLanguage₀,
      hBits₀,
      hSearch₀⟩

  rcases
      positiveAdditiveParetoMinimumAdditiveProfile_exists_certifiedWitness
        (z := z)
        hα
        minimumAdditiveResult with
    ⟨S₁,
      hSelected₁,
      hProfile₁,
      hIdentifies₁,
      C₁,
      hLanguage₁,
      hBits₁,
      hSearch₁⟩

  exact
    ⟨minimumCardinalityResult.profile_mem,
      minimumAdditiveResult.profile_mem,
      fun profile hProfile =>
        positiveAdditiveParetoProfile_between_endpoints
          minimumCardinalityResult
          minimumAdditiveResult
          hProfile,
      positiveAdditiveParetoProfile_endpoint_width_eq
        minimumCardinalityResult
        minimumAdditiveResult,
      ⟨S₀,
        hSelected₀,
        hProfile₀,
        hIdentifies₀⟩,
      ⟨S₁,
        hSelected₁,
        hProfile₁,
        hIdentifies₁⟩⟩

end ParetoProfileExtremesFinalPackage

end MCFG
