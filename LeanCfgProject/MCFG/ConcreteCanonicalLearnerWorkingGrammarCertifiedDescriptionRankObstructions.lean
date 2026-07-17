/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG.ConcreteCanonicalLearnerWorkingGrammarCertifiedDescriptionRank

/-!
# ConcreteCanonicalLearnerWorkingGrammarCertifiedDescriptionRankObstructions.lean

The preceding file defines the least simultaneous certified-description rank

```lean
startRootedTargetCertifiedDescriptionRank hα obs f hL
```

at which a semantic target enters the increasing profile hierarchy

```lean
CorrectedConcreteCertifiedRankProfileClass obs f rank.
```

It also proves

```text
certified description rank
  ≤
characteristic rank.
```

This file turns that comparison into lower-bound and obstruction principles.

## Exact profile obstruction

For every semantic target `L` and every rank `r`,

```text
L ∉ CertifiedRankProfileClass r
  ↔
r < certifiedDescriptionRank(L).
```

Hence failure to possess one simultaneous certified bit/search description at
rank `r` forces

```text
r < characteristicRank(L).
```

This is the direct profile-obstruction route to characteristic-rank lower
bounds.

## Complexity obstructions

The separately minimized certified bit and search complexities satisfy

```text
minimum bit complexity
  ≤
rankBitBudget(certifiedDescriptionRank),

minimum search complexity
  ≤
rankSearchBudget(certifiedDescriptionRank).
```

Therefore either strict budget violation

```text
rankBitBudget r
  < minimum bit complexity
```

or

```text
rankSearchBudget r
  < minimum search complexity
```

forces

```text
r < certifiedDescriptionRank(L)
  ≤
characteristicRank(L).
```

Thus certified description lower bounds imply characteristic-sample-rank lower
bounds.

## Exactness criterion

The general comparison

```text
certifiedDescriptionRank(L)
  ≤
characteristicRank(L)
```

is an equality exactly when no certified profile level strictly below the
characteristic rank contains `L`.

This isolates the missing lower-bound obligation required to prove exact
characteristic complexity.

## Exact-rank shells

We define the semantic target class of exact certified-description rank `r`:

```lean
StartRootedCorrectedConcreteTargetCertifiedDescriptionRankExactClass.
```

A target lies in this shell exactly when

* it belongs to profile level `r`; and
* it belongs to no lower profile level.

Different exact-rank shells are disjoint, every target belongs to exactly one
shell, and their union is the whole semantic target class.

The final package combines positive-data identification, profile obstructions,
bit/search-complexity obstructions, the exactness criterion, and the exact-rank
partition.

These are semantic lower-bound principles.  They do not by themselves provide
a method for proving that a concrete target fails a profile level; such a
failure theorem is the substantive obstruction input to be supplied in future
applications.

No target grammar is supplied to the learner.
No `sorry`, `admit`, or `axiom` is used.
-/

namespace MCFG

universe u v w


section TargetProfileObstructions

variable {α : Type u}
variable {M : Type v}
variable [Fintype M]
variable [DecidableEq α]
variable [DecidableEq M]
variable [Monoid M]
variable (hα : Nonempty α)
variable (obs : α → M)
variable (f : Nat)

/-- Exact obstruction form of the certified-description-rank threshold. -/
theorem startRootedTarget_not_mem_rankProfile_iff_lt_descriptionRank
    {L : Set (Word α)}
    (hL :
      L ∈
        StartRootedCorrectedConcreteTargetClass
          (v := w) α M obs f)
    (rank : Nat) :
    L ∉
        CorrectedConcreteCertifiedRankProfileClass
          (α := α)
          (M := M)
          obs f rank ↔
      rank <
        startRootedTargetCertifiedDescriptionRank
          (v := w) hα obs f hL := by

  constructor

  · intro hnot

    by_contra hnotlt

    have hle :
        startRootedTargetCertifiedDescriptionRank
            (v := w) hα obs f hL <=
          rank := by
      omega

    exact
      hnot
        ((startRootedTarget_mem_rankProfile_iff_descriptionRank_le
          (v := w) hα obs f hL rank).mpr
          hle)

  · intro hrank hmem

    have hle :
        startRootedTargetCertifiedDescriptionRank
            (v := w) hα obs f hL <=
          rank :=
      (startRootedTarget_mem_rankProfile_iff_descriptionRank_le
        (v := w) hα obs f hL rank).mp
        hmem

    omega

/-- Failure of a certified profile level forces a strict characteristic-rank
lower bound. -/
theorem
    startRootedTarget_characteristicRank_gt_of_not_mem_certifiedRankProfile
    {L : Set (Word α)}
    (hL :
      L ∈
        StartRootedCorrectedConcreteTargetClass
          (v := w) α M obs f)
    {rank : Nat}
    (hnot :
      L ∉
        CorrectedConcreteCertifiedRankProfileClass
          (α := α)
          (M := M)
          obs f rank) :
    rank <
      startRootedTargetCharacteristicRank
        (v := w) hα obs f hL := by

  have hdescription :
      rank <
        startRootedTargetCertifiedDescriptionRank
          (v := w) hα obs f hL :=
    (startRootedTarget_not_mem_rankProfile_iff_lt_descriptionRank
      (v := w) hα obs f hL rank).mp
      hnot

  exact
    lt_of_lt_of_le
      hdescription
      (startRootedTargetCertifiedDescriptionRank_le_characteristicRank
        (v := w) hα obs f hL)

/-- If the target characteristic rank is at most `rank`, profile membership at
`rank` is mandatory. -/
theorem
    startRootedTarget_mem_certifiedRankProfile_of_characteristicRank_le
    {L : Set (Word α)}
    (hL :
      L ∈
        StartRootedCorrectedConcreteTargetClass
          (v := w) α M obs f)
    {rank : Nat}
    (hrank :
      startRootedTargetCharacteristicRank
          (v := w) hα obs f hL <=
        rank) :
    L ∈
      CorrectedConcreteCertifiedRankProfileClass
        (α := α)
        (M := M)
        obs f rank := by

  exact
    startRootedTarget_mem_certifiedRankProfileClass_of_characteristicRank_le
      (v := w) hα obs f hL hrank

/-- Profile non-membership is incompatible with a characteristic-rank upper
bound at the same level. -/
theorem
    startRootedTarget_not_characteristicRank_le_of_not_mem_certifiedRankProfile
    {L : Set (Word α)}
    (hL :
      L ∈
        StartRootedCorrectedConcreteTargetClass
          (v := w) α M obs f)
    {rank : Nat}
    (hnot :
      L ∉
        CorrectedConcreteCertifiedRankProfileClass
          (α := α)
          (M := M)
          obs f rank) :
    ¬
      startRootedTargetCharacteristicRank
          (v := w) hα obs f hL <=
        rank := by

  intro hrank

  exact
    hnot
      (startRootedTarget_mem_certifiedRankProfile_of_characteristicRank_le
        (v := w) hα obs f hL hrank)

end TargetProfileObstructions


section TargetComplexityObstructions

variable {α : Type u}
variable {M : Type v}
variable [Fintype M]
variable [DecidableEq α]
variable [DecidableEq M]
variable [Monoid M]
variable (hα : Nonempty α)
variable (obs : α → M)
variable (f : Nat)

/-- Exceeding the rank-`r` bit budget forces the minimum simultaneous certified
description rank to exceed `r`. -/
theorem
    startRootedTarget_descriptionRank_gt_of_bitComplexity_gt_rankBudget
    {L : Set (Word α)}
    (hL :
      L ∈
        StartRootedCorrectedConcreteTargetClass
          (v := w) α M obs f)
    {rank : Nat}
    (hcomplexity :
      correctedConcreteCertifiedRankBitBudget
          rank f <
        startRootedTargetCertifiedBitDescriptionComplexity
          (v := w) hα obs f hL) :
    rank <
      startRootedTargetCertifiedDescriptionRank
        (v := w) hα obs f hL := by

  by_contra hnot

  have hrank :
      startRootedTargetCertifiedDescriptionRank
          (v := w) hα obs f hL <=
        rank := by
    omega

  have hminimum :
      startRootedTargetCertifiedBitDescriptionComplexity
          (v := w) hα obs f hL <=
        correctedConcreteCertifiedRankBitBudget
          (startRootedTargetCertifiedDescriptionRank
            (v := w) hα obs f hL)
          f :=
    startRootedTargetCertifiedBitDescriptionComplexity_le_descriptionRankBudget
      (v := w) hα obs f hL

  have hbudget :
      correctedConcreteCertifiedRankBitBudget
          (startRootedTargetCertifiedDescriptionRank
            (v := w) hα obs f hL)
          f <=
        correctedConcreteCertifiedRankBitBudget
          rank f :=
    correctedConcreteCertifiedRankBitBudget_mono
      hrank

  have hupper :
      startRootedTargetCertifiedBitDescriptionComplexity
          (v := w) hα obs f hL <=
        correctedConcreteCertifiedRankBitBudget
          rank f :=
    hminimum.trans hbudget

  omega

/-- Exceeding the rank-`r` finite-search budget forces the minimum simultaneous
certified description rank to exceed `r`. -/
theorem
    startRootedTarget_descriptionRank_gt_of_searchComplexity_gt_rankBudget
    {L : Set (Word α)}
    (hL :
      L ∈
        StartRootedCorrectedConcreteTargetClass
          (v := w) α M obs f)
    {rank : Nat}
    (hcomplexity :
      correctedConcreteCertifiedRankSearchBudget
          rank f <
        startRootedTargetCertifiedCanonicalSearchComplexity
          (v := w) hα obs f hL) :
    rank <
      startRootedTargetCertifiedDescriptionRank
        (v := w) hα obs f hL := by

  by_contra hnot

  have hrank :
      startRootedTargetCertifiedDescriptionRank
          (v := w) hα obs f hL <=
        rank := by
    omega

  have hminimum :
      startRootedTargetCertifiedCanonicalSearchComplexity
          (v := w) hα obs f hL <=
        correctedConcreteCertifiedRankSearchBudget
          (startRootedTargetCertifiedDescriptionRank
            (v := w) hα obs f hL)
          f :=
    startRootedTargetCertifiedCanonicalSearchComplexity_le_descriptionRankBudget
      (v := w) hα obs f hL

  have hbudget :
      correctedConcreteCertifiedRankSearchBudget
          (startRootedTargetCertifiedDescriptionRank
            (v := w) hα obs f hL)
          f <=
        correctedConcreteCertifiedRankSearchBudget
          rank f :=
    correctedConcreteCertifiedRankSearchBudget_mono
      hrank

  have hupper :
      startRootedTargetCertifiedCanonicalSearchComplexity
          (v := w) hα obs f hL <=
        correctedConcreteCertifiedRankSearchBudget
          rank f :=
    hminimum.trans hbudget

  omega

/-- A certified bit-complexity lower bound implies the corresponding strict
characteristic-rank lower bound. -/
theorem
    startRootedTarget_characteristicRank_gt_of_bitComplexity_gt_rankBudget
    {L : Set (Word α)}
    (hL :
      L ∈
        StartRootedCorrectedConcreteTargetClass
          (v := w) α M obs f)
    {rank : Nat}
    (hcomplexity :
      correctedConcreteCertifiedRankBitBudget
          rank f <
        startRootedTargetCertifiedBitDescriptionComplexity
          (v := w) hα obs f hL) :
    rank <
      startRootedTargetCharacteristicRank
        (v := w) hα obs f hL := by

  exact
    lt_of_lt_of_le
      (startRootedTarget_descriptionRank_gt_of_bitComplexity_gt_rankBudget
        (v := w) hα obs f hL hcomplexity)
      (startRootedTargetCertifiedDescriptionRank_le_characteristicRank
        (v := w) hα obs f hL)

/-- A certified finite-search-complexity lower bound implies the corresponding
strict characteristic-rank lower bound. -/
theorem
    startRootedTarget_characteristicRank_gt_of_searchComplexity_gt_rankBudget
    {L : Set (Word α)}
    (hL :
      L ∈
        StartRootedCorrectedConcreteTargetClass
          (v := w) α M obs f)
    {rank : Nat}
    (hcomplexity :
      correctedConcreteCertifiedRankSearchBudget
          rank f <
        startRootedTargetCertifiedCanonicalSearchComplexity
          (v := w) hα obs f hL) :
    rank <
      startRootedTargetCharacteristicRank
        (v := w) hα obs f hL := by

  exact
    lt_of_lt_of_le
      (startRootedTarget_descriptionRank_gt_of_searchComplexity_gt_rankBudget
        (v := w) hα obs f hL hcomplexity)
      (startRootedTargetCertifiedDescriptionRank_le_characteristicRank
        (v := w) hα obs f hL)

/-- Bit-budget obstruction directly implies profile non-membership. -/
theorem
    startRootedTarget_not_mem_rankProfile_of_bitComplexity_gt_rankBudget
    {L : Set (Word α)}
    (hL :
      L ∈
        StartRootedCorrectedConcreteTargetClass
          (v := w) α M obs f)
    {rank : Nat}
    (hcomplexity :
      correctedConcreteCertifiedRankBitBudget
          rank f <
        startRootedTargetCertifiedBitDescriptionComplexity
          (v := w) hα obs f hL) :
    L ∉
      CorrectedConcreteCertifiedRankProfileClass
        (α := α)
        (M := M)
        obs f rank := by

  exact
    (startRootedTarget_not_mem_rankProfile_iff_lt_descriptionRank
      (v := w) hα obs f hL rank).mpr
      (startRootedTarget_descriptionRank_gt_of_bitComplexity_gt_rankBudget
        (v := w) hα obs f hL hcomplexity)

/-- Search-budget obstruction directly implies profile non-membership. -/
theorem
    startRootedTarget_not_mem_rankProfile_of_searchComplexity_gt_rankBudget
    {L : Set (Word α)}
    (hL :
      L ∈
        StartRootedCorrectedConcreteTargetClass
          (v := w) α M obs f)
    {rank : Nat}
    (hcomplexity :
      correctedConcreteCertifiedRankSearchBudget
          rank f <
        startRootedTargetCertifiedCanonicalSearchComplexity
          (v := w) hα obs f hL) :
    L ∉
      CorrectedConcreteCertifiedRankProfileClass
        (α := α)
        (M := M)
        obs f rank := by

  exact
    (startRootedTarget_not_mem_rankProfile_iff_lt_descriptionRank
      (v := w) hα obs f hL rank).mpr
      (startRootedTarget_descriptionRank_gt_of_searchComplexity_gt_rankBudget
        (v := w) hα obs f hL hcomplexity)

end TargetComplexityObstructions


section CharacteristicRankExactnessCriterion

variable {α : Type u}
variable {M : Type v}
variable [Fintype M]
variable [DecidableEq α]
variable [DecidableEq M]
variable [Monoid M]
variable (hα : Nonempty α)
variable (obs : α → M)
variable (f : Nat)

/-- The certified description rank equals the characteristic rank exactly when
the target occurs in no profile level strictly below its characteristic rank. -/
theorem
    startRootedTarget_descriptionRank_eq_characteristicRank_iff_no_lower_profile
    {L : Set (Word α)}
    (hL :
      L ∈
        StartRootedCorrectedConcreteTargetClass
          (v := w) α M obs f) :
    startRootedTargetCertifiedDescriptionRank
        (v := w) hα obs f hL =
      startRootedTargetCharacteristicRank
        (v := w) hα obs f hL ↔
    ∀ rank : Nat,
      rank <
          startRootedTargetCharacteristicRank
            (v := w) hα obs f hL →
        L ∉
          CorrectedConcreteCertifiedRankProfileClass
            (α := α)
            (M := M)
            obs f rank := by

  constructor

  · intro heq rank hrank

    apply
      startRootedTarget_not_mem_rankProfile_of_lt_descriptionRank
        (v := w) hα obs f hL rank
        |>.mpr

    simpa [heq] using hrank

  · intro hlower

    have hle :
        startRootedTargetCertifiedDescriptionRank
            (v := w) hα obs f hL <=
          startRootedTargetCharacteristicRank
            (v := w) hα obs f hL :=
      startRootedTargetCertifiedDescriptionRank_le_characteristicRank
        (v := w) hα obs f hL

    apply Nat.le_antisymm hle

    by_contra hnot

    have hlt :
        startRootedTargetCertifiedDescriptionRank
            (v := w) hα obs f hL <
          startRootedTargetCharacteristicRank
            (v := w) hα obs f hL := by
      omega

    exact
      hlower
        (startRootedTargetCertifiedDescriptionRank
          (v := w) hα obs f hL)
        hlt
        (startRootedTarget_mem_minimumCertifiedDescriptionRankProfile
          (v := w) hα obs f hL)

/-- A lower-profile obstruction at every rank below the characteristic rank
proves exact equality of the two ranks. -/
theorem
    startRootedTarget_descriptionRank_eq_characteristicRank_of_no_lower_profile
    {L : Set (Word α)}
    (hL :
      L ∈
        StartRootedCorrectedConcreteTargetClass
          (v := w) α M obs f)
    (hlower :
      ∀ rank : Nat,
        rank <
            startRootedTargetCharacteristicRank
              (v := w) hα obs f hL →
          L ∉
            CorrectedConcreteCertifiedRankProfileClass
              (α := α)
              (M := M)
              obs f rank) :
    startRootedTargetCertifiedDescriptionRank
        (v := w) hα obs f hL =
      startRootedTargetCharacteristicRank
        (v := w) hα obs f hL := by

  exact
    (startRootedTarget_descriptionRank_eq_characteristicRank_iff_no_lower_profile
      (v := w) hα obs f hL).mpr
      hlower

/-- If the target already lies below its characteristic-rank level, then the
certified description rank is strictly smaller than the characteristic rank. -/
theorem
    startRootedTarget_descriptionRank_lt_characteristicRank_of_mem_lower_profile
    {L : Set (Word α)}
    (hL :
      L ∈
        StartRootedCorrectedConcreteTargetClass
          (v := w) α M obs f)
    {rank : Nat}
    (hrank :
      rank <
        startRootedTargetCharacteristicRank
          (v := w) hα obs f hL)
    (hmem :
      L ∈
        CorrectedConcreteCertifiedRankProfileClass
          (α := α)
          (M := M)
          obs f rank) :
    startRootedTargetCertifiedDescriptionRank
        (v := w) hα obs f hL <
      startRootedTargetCharacteristicRank
        (v := w) hα obs f hL := by

  have hdescription :
      startRootedTargetCertifiedDescriptionRank
          (v := w) hα obs f hL <=
        rank :=
    (startRootedTarget_mem_rankProfile_iff_descriptionRank_le
      (v := w) hα obs f hL rank).mp
      hmem

  exact
    lt_of_le_of_lt
      hdescription
      hrank

end CharacteristicRankExactnessCriterion


section ExactCertifiedDescriptionRankShells

variable {α : Type u}
variable {M : Type v}
variable [Fintype M]
variable [DecidableEq α]
variable [DecidableEq M]
variable [Monoid M]
variable (hα : Nonempty α)
variable (obs : α → M)
variable (f : Nat)

/-- Semantic targets of one exact minimum simultaneous certified-description
rank. -/
def StartRootedCorrectedConcreteTargetCertifiedDescriptionRankExactClass
    (rank : Nat) :
    Set (Set (Word α)) :=
  {L |
    ∃
      hL :
        L ∈
          StartRootedCorrectedConcreteTargetClass
            (v := w) α M obs f,
      startRootedTargetCertifiedDescriptionRank
          (v := w) hα obs f hL =
        rank}

/-- Exact-shell membership is equivalent to membership at `rank` together with
failure of every lower profile level. -/
theorem
    startRootedTarget_mem_certifiedDescriptionRankExactClass_iff
    (rank : Nat)
    (L : Set (Word α)) :
    L ∈
        StartRootedCorrectedConcreteTargetCertifiedDescriptionRankExactClass
          (v := w) hα obs f rank ↔
      ∃
        hL :
          L ∈
            StartRootedCorrectedConcreteTargetClass
              (v := w) α M obs f,
        L ∈
            CorrectedConcreteCertifiedRankProfileClass
              (α := α)
              (M := M)
              obs f rank ∧
          ∀ lower : Nat,
            lower < rank →
              L ∉
                CorrectedConcreteCertifiedRankProfileClass
                  (α := α)
                  (M := M)
                  obs f lower := by

  constructor

  · intro hExact

    rcases hExact with
      ⟨hL, hRank⟩

    refine
      ⟨hL,
        ?_,
        ?_⟩

    · rw [← hRank]

      exact
        startRootedTarget_mem_minimumCertifiedDescriptionRankProfile
          (v := w) hα obs f hL

    · intro lower hlower

      apply
        startRootedTarget_not_mem_rankProfile_of_lt_descriptionRank
          (v := w) hα obs f hL lower
          |>.mpr

      simpa [hRank] using hlower

  · intro hCriterion

    rcases hCriterion with
      ⟨hL, hmem, hlower⟩

    have hle :
        startRootedTargetCertifiedDescriptionRank
            (v := w) hα obs f hL <=
          rank :=
      (startRootedTarget_mem_rankProfile_iff_descriptionRank_le
        (v := w) hα obs f hL rank).mp
        hmem

    have hge :
        rank <=
          startRootedTargetCertifiedDescriptionRank
            (v := w) hα obs f hL := by

      by_contra hnot

      have hlt :
          startRootedTargetCertifiedDescriptionRank
              (v := w) hα obs f hL <
            rank := by
        omega

      exact
        hlower
          (startRootedTargetCertifiedDescriptionRank
            (v := w) hα obs f hL)
          hlt
          (startRootedTarget_mem_minimumCertifiedDescriptionRankProfile
            (v := w) hα obs f hL)

    exact
      ⟨hL,
        Nat.le_antisymm hle hge⟩

/-- Every exact-rank shell is contained in the corresponding at-most-rank
stratum. -/
theorem
    startRootedTargetCertifiedDescriptionRankExactClass_subset_atMostClass
    (rank : Nat) :
    StartRootedCorrectedConcreteTargetCertifiedDescriptionRankExactClass
        (v := w) hα obs f rank ⊆
      StartRootedCorrectedConcreteTargetCertifiedDescriptionRankAtMostClass
        (v := w) hα obs f rank := by

  intro L hL

  rcases hL with
    ⟨hTarget, hRank⟩

  exact
    ⟨hTarget,
      by
        rw [hRank]⟩

/-- Every exact-rank shell is contained in the corresponding certified profile
class. -/
theorem
    startRootedTargetCertifiedDescriptionRankExactClass_subset_rankProfileClass
    (rank : Nat) :
    StartRootedCorrectedConcreteTargetCertifiedDescriptionRankExactClass
        (v := w) hα obs f rank ⊆
      CorrectedConcreteCertifiedRankProfileClass
        (α := α)
        (M := M)
        obs f rank := by

  intro L hL

  rcases hL with
    ⟨hTarget, hRank⟩

  rw [← hRank]

  exact
    startRootedTarget_mem_minimumCertifiedDescriptionRankProfile
      (v := w) hα obs f hTarget

/-- Exact certified-description rank is unique. -/
theorem startRootedTargetCertifiedDescriptionRankExactClass_rank_unique
    {rank rank' : Nat}
    {L : Set (Word α)}
    (hRank :
      L ∈
        StartRootedCorrectedConcreteTargetCertifiedDescriptionRankExactClass
          (v := w) hα obs f rank)
    (hRank' :
      L ∈
        StartRootedCorrectedConcreteTargetCertifiedDescriptionRankExactClass
          (v := w) hα obs f rank') :
    rank = rank' := by

  rcases hRank with
    ⟨hL, hrank⟩

  rcases hRank' with
    ⟨hL', hrank'⟩

  cases Subsingleton.elim hL hL'

  exact
    hrank.symm.trans
      hrank'

/-- Distinct exact-rank shells are disjoint. -/
theorem
    startRootedTargetCertifiedDescriptionRankExactClasses_disjoint
    {rank rank' : Nat}
    (hne :
      rank ≠ rank') :
    Set.Disjoint
      (StartRootedCorrectedConcreteTargetCertifiedDescriptionRankExactClass
        (v := w) hα obs f rank)
      (StartRootedCorrectedConcreteTargetCertifiedDescriptionRankExactClass
        (v := w) hα obs f rank') := by

  rw [Set.disjoint_left]

  intro L hRank hRank'

  exact
    hne
      (startRootedTargetCertifiedDescriptionRankExactClass_rank_unique
        (v := w) hα obs f hRank hRank')

/-- Every semantic target belongs to the exact shell indexed by its own minimum
certified-description rank. -/
theorem
    startRootedTarget_mem_ownCertifiedDescriptionRankExactClass
    {L : Set (Word α)}
    (hL :
      L ∈
        StartRootedCorrectedConcreteTargetClass
          (v := w) α M obs f) :
    L ∈
      StartRootedCorrectedConcreteTargetCertifiedDescriptionRankExactClass
        (v := w) hα obs f
        (startRootedTargetCertifiedDescriptionRank
          (v := w) hα obs f hL) := by

  exact
    ⟨hL,
      rfl⟩

/-- The union of all exact certified-description-rank shells is the full
semantic target class. -/
theorem
    startRootedTargetClass_eq_exists_certifiedDescriptionRankExactClass :
    StartRootedCorrectedConcreteTargetClass
        (v := w) α M obs f =
      {L : Set (Word α) |
        ∃ rank : Nat,
          L ∈
            StartRootedCorrectedConcreteTargetCertifiedDescriptionRankExactClass
              (v := w) hα obs f rank} := by

  ext L

  constructor

  · intro hL

    exact
      ⟨startRootedTargetCertifiedDescriptionRank
          (v := w) hα obs f hL,
        startRootedTarget_mem_ownCertifiedDescriptionRankExactClass
          (v := w) hα obs f hL⟩

  · intro hL

    rcases hL with
      ⟨rank, hRank⟩

    rcases hRank with
      ⟨hTarget, hdescription⟩

    exact hTarget

end ExactCertifiedDescriptionRankShells


section CertifiedDescriptionRankObstructionPackages

variable {α : Type u}
variable {M : Type v}
variable [Fintype M]
variable [DecidableEq α]
variable [DecidableEq M]
variable [Monoid M]
variable (hα : Nonempty α)
variable (obs : α → M)
variable (f : Nat)

/-- Target-level obstruction, exactness, and exact-shell package. -/
theorem startRootedTargetCertifiedDescriptionRankObstruction_package
    {L : Set (Word α)}
    (hL :
      L ∈
        StartRootedCorrectedConcreteTargetClass
          (v := w) α M obs f) :
    (∀ rank : Nat,
      L ∉
          CorrectedConcreteCertifiedRankProfileClass
            (α := α)
            (M := M)
            obs f rank ↔
        rank <
          startRootedTargetCertifiedDescriptionRank
            (v := w) hα obs f hL) ∧
      (∀ rank : Nat,
        L ∉
            CorrectedConcreteCertifiedRankProfileClass
              (α := α)
              (M := M)
              obs f rank →
          rank <
            startRootedTargetCharacteristicRank
              (v := w) hα obs f hL) ∧
      (∀ rank : Nat,
        correctedConcreteCertifiedRankBitBudget
              rank f <
            startRootedTargetCertifiedBitDescriptionComplexity
              (v := w) hα obs f hL →
          rank <
            startRootedTargetCharacteristicRank
              (v := w) hα obs f hL) ∧
      (∀ rank : Nat,
        correctedConcreteCertifiedRankSearchBudget
              rank f <
            startRootedTargetCertifiedCanonicalSearchComplexity
              (v := w) hα obs f hL →
          rank <
            startRootedTargetCharacteristicRank
              (v := w) hα obs f hL) ∧
      (startRootedTargetCertifiedDescriptionRank
          (v := w) hα obs f hL =
        startRootedTargetCharacteristicRank
          (v := w) hα obs f hL ↔
        ∀ rank : Nat,
          rank <
              startRootedTargetCharacteristicRank
                (v := w) hα obs f hL →
            L ∉
              CorrectedConcreteCertifiedRankProfileClass
                (α := α)
                (M := M)
                obs f rank) ∧
      (L ∈
        StartRootedCorrectedConcreteTargetCertifiedDescriptionRankExactClass
          (v := w) hα obs f
          (startRootedTargetCertifiedDescriptionRank
            (v := w) hα obs f hL)) := by

  exact
    ⟨fun rank =>
        startRootedTarget_not_mem_rankProfile_iff_lt_descriptionRank
          (v := w) hα obs f hL rank,
      fun rank hnot =>
        startRootedTarget_characteristicRank_gt_of_not_mem_certifiedRankProfile
          (v := w) hα obs f hL hnot,
      fun rank hcomplexity =>
        startRootedTarget_characteristicRank_gt_of_bitComplexity_gt_rankBudget
          (v := w) hα obs f hL hcomplexity,
      fun rank hcomplexity =>
        startRootedTarget_characteristicRank_gt_of_searchComplexity_gt_rankBudget
          (v := w) hα obs f hL hcomplexity,
      startRootedTarget_descriptionRank_eq_characteristicRank_iff_no_lower_profile
        (v := w) hα obs f hL,
      startRootedTarget_mem_ownCertifiedDescriptionRankExactClass
        (v := w) hα obs f hL⟩

/-- Final class-level identification and certified-description obstruction
package. -/
theorem
    correctedConcreteCertifiedWorkingGrammarLearner_identification_descriptionRankObstruction_package :
    IdentifiesClassFromPositiveData
        (correctedConcreteCertifiedWorkingGrammarHypLanguage
          obs f)
        (correctedConcreteCertifiedWorkingGrammarLearner
          hα obs f)
        (StartRootedCorrectedConcreteTargetClass
          (v := w) α M obs f) ∧
      (∀
        L : Set (Word α),
        ∀ hL :
          L ∈
            StartRootedCorrectedConcreteTargetClass
              (v := w) α M obs f,
        ∀ rank : Nat,
          L ∉
              CorrectedConcreteCertifiedRankProfileClass
                (α := α)
                (M := M)
                obs f rank ↔
            rank <
              startRootedTargetCertifiedDescriptionRank
                (v := w) hα obs f hL) ∧
      (∀
        L : Set (Word α),
        ∀ hL :
          L ∈
            StartRootedCorrectedConcreteTargetClass
              (v := w) α M obs f,
        ∀ rank : Nat,
          L ∉
              CorrectedConcreteCertifiedRankProfileClass
                (α := α)
                (M := M)
                obs f rank →
            rank <
              startRootedTargetCharacteristicRank
                (v := w) hα obs f hL) ∧
      (∀
        L : Set (Word α),
        ∀ hL :
          L ∈
            StartRootedCorrectedConcreteTargetClass
              (v := w) α M obs f,
        ∀ rank : Nat,
          correctedConcreteCertifiedRankBitBudget
                rank f <
              startRootedTargetCertifiedBitDescriptionComplexity
                (v := w) hα obs f hL →
            rank <
              startRootedTargetCharacteristicRank
                (v := w) hα obs f hL) ∧
      (∀
        L : Set (Word α),
        ∀ hL :
          L ∈
            StartRootedCorrectedConcreteTargetClass
              (v := w) α M obs f,
        ∀ rank : Nat,
          correctedConcreteCertifiedRankSearchBudget
                rank f <
              startRootedTargetCertifiedCanonicalSearchComplexity
                (v := w) hα obs f hL →
            rank <
              startRootedTargetCharacteristicRank
                (v := w) hα obs f hL) ∧
      (∀
        L : Set (Word α),
        ∀ hL :
          L ∈
            StartRootedCorrectedConcreteTargetClass
              (v := w) α M obs f,
        startRootedTargetCertifiedDescriptionRank
            (v := w) hα obs f hL =
          startRootedTargetCharacteristicRank
            (v := w) hα obs f hL ↔
          ∀ rank : Nat,
            rank <
                startRootedTargetCharacteristicRank
                  (v := w) hα obs f hL →
              L ∉
                CorrectedConcreteCertifiedRankProfileClass
                  (α := α)
                  (M := M)
                  obs f rank) ∧
      (∀ rank rank' : Nat,
        rank ≠ rank' →
        Set.Disjoint
          (StartRootedCorrectedConcreteTargetCertifiedDescriptionRankExactClass
            (v := w) hα obs f rank)
          (StartRootedCorrectedConcreteTargetCertifiedDescriptionRankExactClass
            (v := w) hα obs f rank')) ∧
      (StartRootedCorrectedConcreteTargetClass
          (v := w) α M obs f =
        {L : Set (Word α) |
          ∃ rank : Nat,
            L ∈
              StartRootedCorrectedConcreteTargetCertifiedDescriptionRankExactClass
                (v := w) hα obs f rank}) := by

  exact
    ⟨correctedConcreteCertifiedWorkingGrammarLearner_identifies_startRootedTargetClass
        (v := w) hα obs f,
      fun L hL rank =>
        startRootedTarget_not_mem_rankProfile_iff_lt_descriptionRank
          (v := w) hα obs f hL rank,
      fun L hL rank hnot =>
        startRootedTarget_characteristicRank_gt_of_not_mem_certifiedRankProfile
          (v := w) hα obs f hL hnot,
      fun L hL rank hcomplexity =>
        startRootedTarget_characteristicRank_gt_of_bitComplexity_gt_rankBudget
          (v := w) hα obs f hL hcomplexity,
      fun L hL rank hcomplexity =>
        startRootedTarget_characteristicRank_gt_of_searchComplexity_gt_rankBudget
          (v := w) hα obs f hL hcomplexity,
      fun L hL =>
        startRootedTarget_descriptionRank_eq_characteristicRank_iff_no_lower_profile
          (v := w) hα obs f hL,
      fun rank rank' hne =>
        startRootedTargetCertifiedDescriptionRankExactClasses_disjoint
          (v := w) hα obs f hne,
      startRootedTargetClass_eq_exists_certifiedDescriptionRankExactClass
        (v := w) hα obs f⟩

end CertifiedDescriptionRankObstructionPackages

end MCFG
