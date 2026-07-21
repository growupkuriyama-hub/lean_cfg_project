/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG2.ConcreteCanonicalLearnerWorkingGrammarObservationSelectionParetoRankSelector

/-!
# ConcreteCanonicalLearnerWorkingGrammarObservationSelectionParetoRankProfiles.lean

The preceding file constructs an actual selector from the finite set of
positive-additive-rank-minimizing Pareto selections.

This file passes from selected subsets to their two-dimensional profiles.

## Rank-minimizing Pareto profiles

For every rank-minimizing Pareto selection `S`, record

```text
(S.card, AdditiveCost(weight,S)).
```

The resulting explicit finite profile set is

```lean
correctedConcreteObservationPositiveAdditiveRankMinimizingParetoProfiles.
```

Every profile `(c,a)` satisfies the exact affine equation

```text
c + a = PositiveAdditiveRank(language).
```

Thus all profiles lie on one finite rank line.

## Sharper profile-count bound

The selected-subset search has at most `2^|U|` candidates.  Profiles are much
more compressed.

Because every profile lies on

```text
c + a = rank
```

and `c` ranges from `0` through `rank`, there are at most

```text
rank + 1
```

distinct rank-minimizing Pareto profiles.

This bound is independent of the ambient interface cardinality once the target
rank is fixed.

## Tradeoff law

For two rank-minimizing profiles `(c₀,a₀)` and `(c₁,a₁)`:

```text
c₀ < c₁  ↔  a₁ < a₀.
```

More coordinates mean strictly less additional weight, and conversely.

If both coordinates of one profile are weakly no larger than those of another,
the profiles are equal.  Hence the finite profile set is an antichain under
coordinatewise order.

## Bottom profiles

If the target rank is zero, the profile set is exactly

```text
{(0,0)}.
```

If the target rank is one, the profile set is exactly

```text
{(1,0)}.
```

The second statement uses the positive-additive rank-one characterization:
the empty selection has cost zero, so an exact rank-one witness must select
one coordinate with zero extra weight.

## Certified profile witnesses

Every profile in the finite set is realized by an actual Pareto-optimal
selected product.  Its certified learner identifies the target and returns an
exact checked grammar output at the selected product's minimum certified-
description rank.

The selector from the preceding file chooses one such certified profile
witness.

No target grammar is supplied to any learner.
No `sorry`, `admit`, or `axiom` is used.
-/

namespace MCFG

universe u v w z


section PositiveAdditiveRankLineDefinition

/-- The finite affine rank line

```text
{(c, rank - c) | c < rank + 1}.
```

Every natural pair whose coordinates sum to `rank` belongs to this set. -/
def correctedConcreteObservationPositiveAdditiveRankLine
    (rank : Nat) :
    Finset (Nat × Nat) :=
  (Finset.range (rank + 1)).image
    (fun cardinality =>
      (cardinality, rank - cardinality))

/-- The finite affine rank line has at most `rank + 1` points. -/
theorem correctedConcreteObservationPositiveAdditiveRankLine_card_le
    (rank : Nat) :
    (correctedConcreteObservationPositiveAdditiveRankLine rank).card <=
      rank + 1 := by

  unfold
    correctedConcreteObservationPositiveAdditiveRankLine

  calc
    ((Finset.range (rank + 1)).image
        (fun cardinality =>
          (cardinality, rank - cardinality))).card <=
      (Finset.range (rank + 1)).card :=
        Finset.card_image_le

    _ = rank + 1 := by
      simp

end PositiveAdditiveRankLineDefinition


section RankMinimizingParetoProfilesDefinition

variable {α : Type u}
variable {ι : Type v}
variable {M : Type w}
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

/-- Explicit finite set of cardinality/additive-weight profiles realized by
positive-additive-rank-minimizing Pareto selections. -/
noncomputable def
    correctedConcreteObservationPositiveAdditiveRankMinimizingParetoProfiles :
    Finset (Nat × Nat) := by

  classical

  exact
    (correctedConcreteObservationPositiveAdditiveRankMinimizingParetoSelections
      (z := z)
      obsFamily
      f
      coordinateWeight
      U
      language
      hTarget).image
      (fun S =>
        (S.card,
          correctedConcreteObservationSelectionAdditiveCost
            coordinateWeight S))

end RankMinimizingParetoProfilesDefinition


section RankMinimizingParetoProfilesMembership

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

/-- Exact membership theorem for finite rank-minimizing Pareto profiles. -/
theorem
    mem_correctedConcreteObservationPositiveAdditiveRankMinimizingParetoProfiles_iff
    {profile : Nat × Nat} :
    profile ∈
        correctedConcreteObservationPositiveAdditiveRankMinimizingParetoProfiles
          (z := z)
          obsFamily
          f
          coordinateWeight
          U
          language
          hTarget ↔
      ∃ S : Finset ι,
        S ∈
            correctedConcreteObservationPositiveAdditiveRankMinimizingParetoSelections
              (z := z)
              obsFamily
              f
              coordinateWeight
              U
              language
              hTarget ∧
          (S.card,
            correctedConcreteObservationSelectionAdditiveCost
              coordinateWeight S) =
            profile := by

  classical

  constructor

  · intro hProfile

    rcases Finset.mem_image.mp hProfile with
      ⟨S, hS, hEq⟩

    exact
      ⟨S,
        hS,
        hEq⟩

  · intro hProfile

    rcases hProfile with
      ⟨S, hS, hEq⟩

    exact
      Finset.mem_image.mpr
        ⟨S,
          hS,
          hEq⟩

/-- The finite rank-minimizing Pareto profile set is nonempty. -/
theorem
    correctedConcreteObservationPositiveAdditiveRankMinimizingParetoProfiles_nonempty :
    (correctedConcreteObservationPositiveAdditiveRankMinimizingParetoProfiles
      (z := z)
      obsFamily
      f
      coordinateWeight
      U
      language
      hTarget).Nonempty := by

  rcases
      correctedConcreteObservationPositiveAdditiveRankMinimizingParetoSelections_nonempty
        (z := z)
        (obsFamily := obsFamily)
        (f := f)
        (coordinateWeight := coordinateWeight)
        (U := U)
        (language := language)
        (hTarget := hTarget) with
    ⟨S, hS⟩

  exact
    ⟨(S.card,
        correctedConcreteObservationSelectionAdditiveCost
          coordinateWeight S),
      (mem_correctedConcreteObservationPositiveAdditiveRankMinimizingParetoProfiles_iff
        (z := z)).mpr
        ⟨S,
          hS,
          rfl⟩⟩

/-- Every rank-minimizing Pareto profile lies on the exact affine rank line. -/
theorem
    correctedConcreteObservationPositiveAdditiveRankMinimizingParetoProfile_sum_eq_rank
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
    profile.1 + profile.2 =
      ambientTargetObservationSelectionPositiveAdditiveMinimumCost
        (z := z)
        obsFamily
        f
        coordinateWeight
        U
        hTarget := by

  rcases
      (mem_correctedConcreteObservationPositiveAdditiveRankMinimizingParetoProfiles_iff
        (z := z)).mp
        hProfile with
    ⟨S, hS, hProfileEq⟩

  have hCost :=
    ((mem_correctedConcreteObservationPositiveAdditiveRankMinimizingParetoSelections_iff
      (z := z)).mp
      hS).2

  unfold
    correctedConcreteObservationSelectionPositiveAdditiveCost
    at hCost

  rw [← hProfileEq]

  exact hCost

/-- Every rank-minimizing Pareto profile belongs to the canonical finite rank
line. -/
theorem
    correctedConcreteObservationPositiveAdditiveRankMinimizingParetoProfiles_subset_rankLine :
    correctedConcreteObservationPositiveAdditiveRankMinimizingParetoProfiles
        (z := z)
        obsFamily
        f
        coordinateWeight
        U
        language
        hTarget ⊆
      correctedConcreteObservationPositiveAdditiveRankLine
        (ambientTargetObservationSelectionPositiveAdditiveMinimumCost
          (z := z)
          obsFamily
          f
          coordinateWeight
          U
          hTarget) := by

  intro profile hProfile

  let rank :=
    ambientTargetObservationSelectionPositiveAdditiveMinimumCost
      (z := z)
      obsFamily
      f
      coordinateWeight
      U
      hTarget

  have hSum :
      profile.1 + profile.2 = rank := by

    simpa [rank] using
      correctedConcreteObservationPositiveAdditiveRankMinimizingParetoProfile_sum_eq_rank
        (z := z)
        hProfile

  unfold
    correctedConcreteObservationPositiveAdditiveRankLine

  apply Finset.mem_image.mpr

  refine
    ⟨profile.1,
      Finset.mem_range.mpr
        (by omega),
      ?_⟩

  apply Prod.ext

  · rfl

  · dsimp

    omega

/-- The number of distinct rank-minimizing Pareto profiles is at most
`rank + 1`. -/
theorem
    correctedConcreteObservationPositiveAdditiveRankMinimizingParetoProfiles_card_le_rank_add_one :
    (correctedConcreteObservationPositiveAdditiveRankMinimizingParetoProfiles
        (z := z)
        obsFamily
        f
        coordinateWeight
        U
        language
        hTarget).card <=
      ambientTargetObservationSelectionPositiveAdditiveMinimumCost
          (z := z)
          obsFamily
          f
          coordinateWeight
          U
          hTarget +
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
      (correctedConcreteObservationPositiveAdditiveRankLine
        (ambientTargetObservationSelectionPositiveAdditiveMinimumCost
          (z := z)
          obsFamily
          f
          coordinateWeight
          U
          hTarget)).card :=
            Finset.card_le_card
              correctedConcreteObservationPositiveAdditiveRankMinimizingParetoProfiles_subset_rankLine

    _ <=
      ambientTargetObservationSelectionPositiveAdditiveMinimumCost
          (z := z)
          obsFamily
          f
          coordinateWeight
          U
          hTarget +
        1 :=
          correctedConcreteObservationPositiveAdditiveRankLine_card_le
            _

/-- Every coordinate of a rank-minimizing Pareto profile is bounded by the
target rank. -/
theorem
    correctedConcreteObservationPositiveAdditiveRankMinimizingParetoProfile_coordinates_le_rank
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
    profile.1 <=
        ambientTargetObservationSelectionPositiveAdditiveMinimumCost
          (z := z)
          obsFamily
          f
          coordinateWeight
          U
          hTarget ∧
      profile.2 <=
        ambientTargetObservationSelectionPositiveAdditiveMinimumCost
          (z := z)
          obsFamily
          f
          coordinateWeight
          U
          hTarget := by

  have hSum :=
    correctedConcreteObservationPositiveAdditiveRankMinimizingParetoProfile_sum_eq_rank
      (z := z)
      hProfile

  omega

end RankMinimizingParetoProfilesMembership


section RankMinimizingParetoProfileTradeoff

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

/-- Strictly more selected coordinates means strictly less additive weight
among rank-minimizing Pareto profiles. -/
theorem
    positiveAdditiveRankMinimizingParetoProfiles_card_lt_iff_additive_gt
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
          hTarget) :
    profile₀.1 < profile₁.1 ↔
      profile₁.2 < profile₀.2 := by

  have hSum₀ :=
    correctedConcreteObservationPositiveAdditiveRankMinimizingParetoProfile_sum_eq_rank
      (z := z)
      hProfile₀

  have hSum₁ :=
    correctedConcreteObservationPositiveAdditiveRankMinimizingParetoProfile_sum_eq_rank
      (z := z)
      hProfile₁

  omega

/-- Equality of cardinality coordinates is equivalent to equality of additive
coordinates on one fixed rank line. -/
theorem
    positiveAdditiveRankMinimizingParetoProfiles_card_eq_iff_additive_eq
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
          hTarget) :
    profile₀.1 = profile₁.1 ↔
      profile₀.2 = profile₁.2 := by

  have hSum₀ :=
    correctedConcreteObservationPositiveAdditiveRankMinimizingParetoProfile_sum_eq_rank
      (z := z)
      hProfile₀

  have hSum₁ :=
    correctedConcreteObservationPositiveAdditiveRankMinimizingParetoProfile_sum_eq_rank
      (z := z)
      hProfile₁

  constructor <;> intro hEq <;> omega

/-- A rank-minimizing Pareto profile is uniquely determined by either
coordinate. -/
theorem
    positiveAdditiveRankMinimizingParetoProfiles_eq_of_card_eq
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
    (hCardEq :
      profile₀.1 = profile₁.1) :
    profile₀ = profile₁ := by

  apply Prod.ext

  · exact hCardEq

  · exact
      (positiveAdditiveRankMinimizingParetoProfiles_card_eq_iff_additive_eq
        (z := z)
        hProfile₀
        hProfile₁).mp
        hCardEq

/-- Rank-minimizing Pareto profiles form an antichain under coordinatewise
order. -/
theorem
    positiveAdditiveRankMinimizingParetoProfiles_antichain
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
    (hCardLe :
      profile₀.1 <= profile₁.1)
    (hAdditiveLe :
      profile₀.2 <= profile₁.2) :
    profile₀ = profile₁ := by

  have hSum₀ :=
    correctedConcreteObservationPositiveAdditiveRankMinimizingParetoProfile_sum_eq_rank
      (z := z)
      hProfile₀

  have hSum₁ :=
    correctedConcreteObservationPositiveAdditiveRankMinimizingParetoProfile_sum_eq_rank
      (z := z)
      hProfile₁

  apply Prod.ext <;> omega

end RankMinimizingParetoProfileTradeoff


section RankMinimizingParetoBottomProfiles

variable {α : Type u}
variable {ι : Type v}
variable {M : Type w}
variable [DecidableEq ι]
variable [Monoid M]
variable (obsFamily : ι → α → M)
variable (f : Nat)
variable (coordinateWeight : ι → Nat)
variable (U : Finset ι)

/-- At positive-additive rank zero, the finite rank-minimizing Pareto profile
set is exactly `{(0,0)}`. -/
theorem
    positiveAdditiveRankMinimizingParetoProfiles_eq_singleton_zero
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
    correctedConcreteObservationPositiveAdditiveRankMinimizingParetoProfiles
        (z := z)
        obsFamily
        f
        coordinateWeight
        U
        language
        hTarget =
      {(0, 0)} := by

  ext profile

  constructor

  · intro hProfile

    have hSum :=
      correctedConcreteObservationPositiveAdditiveRankMinimizingParetoProfile_sum_eq_rank
        (z := z)
        hProfile

    rw [hRankZero] at hSum

    have hProfileEq :
        profile = (0, 0) := by

      apply Prod.ext <;> omega

    simp [hProfileEq]

  · intro hProfile

    have hProfileEq :
        profile = (0, 0) := by
      simpa using hProfile

    subst profile

    rcases
        correctedConcreteObservationPositiveAdditiveRankMinimizingParetoProfiles_nonempty
          (z := z)
          (obsFamily := obsFamily)
          (f := f)
          (coordinateWeight := coordinateWeight)
          (U := U)
          (language := language)
          (hTarget := hTarget) with
      ⟨profile, hProfileMem⟩

    have hSum :=
      correctedConcreteObservationPositiveAdditiveRankMinimizingParetoProfile_sum_eq_rank
        (z := z)
        hProfileMem

    rw [hRankZero] at hSum

    have hProfileZero :
        profile = (0, 0) := by

      apply Prod.ext <;> omega

    simpa [hProfileZero] using
      hProfileMem

/-- At positive-additive rank one, the finite rank-minimizing Pareto profile
set is exactly `{(1,0)}`. -/
theorem
    positiveAdditiveRankMinimizingParetoProfiles_eq_singleton_one
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
    correctedConcreteObservationPositiveAdditiveRankMinimizingParetoProfiles
        (z := z)
        obsFamily
        f
        coordinateWeight
        U
        language
        hTarget =
      {(1, 0)} := by

  have hEveryProfile :
      ∀ profile : Nat × Nat,
        profile ∈
            correctedConcreteObservationPositiveAdditiveRankMinimizingParetoProfiles
              (z := z)
              obsFamily
              f
              coordinateWeight
              U
              language
              hTarget →
          profile = (1, 0) := by

    intro profile hProfile

    rcases
        (mem_correctedConcreteObservationPositiveAdditiveRankMinimizingParetoProfiles_iff
          (z := z)).mp
          hProfile with
      ⟨S, hS, hProfileEq⟩

    have hCost :=
      ((mem_correctedConcreteObservationPositiveAdditiveRankMinimizingParetoSelections_iff
        (z := z)).mp
        hS).2

    have hCostOne :
        correctedConcreteObservationSelectionPositiveAdditiveCost
            coordinateWeight S =
          1 := by

      rw [hCost, hRankOne]

    rcases
        (observationSelectionPositiveAdditiveCost_eq_one_iff
          coordinateWeight
          S).mp
          hCostOne with
      ⟨hCardOne, hAdditiveZero⟩

    rw [← hProfileEq]

    simp [hCardOne, hAdditiveZero]

  ext profile

  constructor

  · intro hProfile

    have hProfileEq :=
      hEveryProfile
        profile
        hProfile

    simp [hProfileEq]

  · intro hProfile

    have hProfileEq :
        profile = (1, 0) := by
      simpa using hProfile

    subst profile

    rcases
        correctedConcreteObservationPositiveAdditiveRankMinimizingParetoProfiles_nonempty
          (z := z)
          (obsFamily := obsFamily)
          (f := f)
          (coordinateWeight := coordinateWeight)
          (U := U)
          (language := language)
          (hTarget := hTarget) with
      ⟨profile, hProfileMem⟩

    have hProfileOne :=
      hEveryProfile
        profile
        hProfileMem

    simpa [hProfileOne] using
      hProfileMem

end RankMinimizingParetoBottomProfiles


section CertifiedParetoProfileWitness

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

/-- Every finite rank-minimizing Pareto profile has an actual
Pareto-optimal selected-product certified witness. -/
theorem
    positiveAdditiveRankMinimizingParetoProfile_exists_certifiedWitness
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
        profile ∧
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

  rcases
      (mem_correctedConcreteObservationPositiveAdditiveRankMinimizingParetoProfiles_iff
        (z := z)).mp
        hProfile with
    ⟨S, hS, hProfileEq⟩

  rcases
      (mem_correctedConcreteObservationPositiveAdditiveRankMinimizingParetoSelections_iff
        (z := z)).mp
        hS with
    ⟨hPareto, hCost⟩

  let hSelected :=
    hPareto.2.1

  exact
    ⟨S,
      hSelected,
      hProfileEq,
      hPareto,
      hCost,
      selectedProductCertifiedLearner_identifies_targetClass
        (z := z)
        hα
        obsFamily
        f
        S
        language
        hSelected,
      startRootedTarget_exists_output_at_minimumCertifiedDescriptionRank
        (v := z)
        hα
        (selectedObservationProduct obsFamily S)
        f
        hSelected⟩

end CertifiedParetoProfileWitness


section SelectedParetoRankProfile

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

/-- The two-dimensional profile selected by the actual Pareto-rank selector. -/
def correctedConcreteObservationPositiveAdditiveSelectedParetoRankProfile
    (result :
      CorrectedConcreteObservationPositiveAdditiveParetoRankSelectionResult
        (z := z)
        obsFamily
        f
        coordinateWeight
        U
        language
        hTarget) :
    Nat × Nat :=
  (result.selected.card,
    correctedConcreteObservationSelectionAdditiveCost
      coordinateWeight result.selected)

/-- The actual selector's profile belongs to the finite rank-minimizing Pareto
profile set. -/
theorem
    correctedConcreteObservationPositiveAdditiveSelectedParetoRankProfile_mem
    (result :
      CorrectedConcreteObservationPositiveAdditiveParetoRankSelectionResult
        (z := z)
        obsFamily
        f
        coordinateWeight
        U
        language
        hTarget) :
    correctedConcreteObservationPositiveAdditiveSelectedParetoRankProfile
        result ∈
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

/-- The actual selector's profile coordinates sum to the target rank. -/
theorem
    correctedConcreteObservationPositiveAdditiveSelectedParetoRankProfile_sum_eq_rank
    (result :
      CorrectedConcreteObservationPositiveAdditiveParetoRankSelectionResult
        (z := z)
        obsFamily
        f
        coordinateWeight
        U
        language
        hTarget) :
    (correctedConcreteObservationPositiveAdditiveSelectedParetoRankProfile
        result).1 +
        (correctedConcreteObservationPositiveAdditiveSelectedParetoRankProfile
          result).2 =
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
      (correctedConcreteObservationPositiveAdditiveSelectedParetoRankProfile_mem
        (z := z)
        result)

end SelectedParetoRankProfile


section ParetoRankProfilesFinalPackage

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

/-- Final finite-profile, sharp profile-count, tradeoff-antichain, actual
selector-profile, and certified-profile-witness package. -/
theorem
    correctedConcreteCertifiedWorkingGrammar_observationSelectionParetoRankProfiles_package :
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
      let profiles :=
        correctedConcreteObservationPositiveAdditiveRankMinimizingParetoProfiles
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
      profiles.Nonempty ∧
        profiles.card <=
          ambientTargetObservationSelectionPositiveAdditiveMinimumCost
              (z := z)
              obsFamily
              f
              coordinateWeight
              U
              hTarget +
            1 ∧
        (∀ profile : Nat × Nat,
          profile ∈ profiles →
            profile.1 + profile.2 =
              ambientTargetObservationSelectionPositiveAdditiveMinimumCost
                (z := z)
                obsFamily
                f
                coordinateWeight
                U
                hTarget) ∧
        (∀ profile₀ profile₁ : Nat × Nat,
          profile₀ ∈ profiles →
          profile₁ ∈ profiles →
          profile₀.1 <= profile₁.1 →
          profile₀.2 <= profile₁.2 →
          profile₀ = profile₁) ∧
        correctedConcreteObservationPositiveAdditiveSelectedParetoRankProfile
            result ∈
          profiles ∧
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

  let profiles :=
    correctedConcreteObservationPositiveAdditiveRankMinimizingParetoProfiles
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

  have hCertified :=
    CorrectedConcreteObservationPositiveAdditiveParetoRankSelectionResult.certified_package
      (z := z)
      hα
      result

  exact
    ⟨correctedConcreteObservationPositiveAdditiveRankMinimizingParetoProfiles_nonempty
        (z := z)
        (obsFamily := obsFamily)
        (f := f)
        (coordinateWeight := coordinateWeight)
        (U := U)
        (language := language)
        (hTarget := hTarget),
      correctedConcreteObservationPositiveAdditiveRankMinimizingParetoProfiles_card_le_rank_add_one
        (z := z)
        (obsFamily := obsFamily)
        (f := f)
        (coordinateWeight := coordinateWeight)
        (U := U)
        (language := language)
        (hTarget := hTarget),
      fun profile hProfile =>
        correctedConcreteObservationPositiveAdditiveRankMinimizingParetoProfile_sum_eq_rank
          (z := z)
          hProfile,
      fun profile₀ profile₁ hProfile₀ hProfile₁ hCardLe hAdditiveLe =>
        positiveAdditiveRankMinimizingParetoProfiles_antichain
          (z := z)
          hProfile₀
          hProfile₁
          hCardLe
          hAdditiveLe,
      correctedConcreteObservationPositiveAdditiveSelectedParetoRankProfile_mem
        (z := z)
        result,
      hCertified.1⟩

end ParetoRankProfilesFinalPackage

end MCFG
