/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG2.ConcreteCanonicalLearnerWorkingGrammarCertifiedDescriptionProfile

/-!
# ConcreteCanonicalLearnerWorkingGrammarCertifiedDescriptionRank.lean

The preceding file constructs an increasing hierarchy

```lean
CorrectedConcreteCertifiedRankProfileClass obs f rank
```

whose level `rank` consists of languages represented by one and the same
certified output satisfying both

```text
checked bit length
  ≤ correctedConcreteCertifiedRankBitBudget rank f
```

and

```text
finite canonical-search length
  ≤ correctedConcreteCertifiedRankSearchBudget rank f.
```

This file defines the first level at which a language enters that hierarchy.

## Minimum simultaneous certified-description rank

A language has a certified rank profile when it belongs to some finite level:

```lean
HasCorrectedConcreteCertifiedRankProfile obs f L.
```

Its minimum rank is

```lean
correctedConcreteCertifiedDescriptionRank.
```

Because the profile hierarchy is indexed by natural numbers, `Nat.find`
provides an attained minimum.  We prove the exact threshold theorem

```text
L ∈ CertifiedRankProfileClass rank
  ↔
certifiedDescriptionRank(L) ≤ rank.
```

Consequently the language belongs at the minimum rank and belongs at no
strictly smaller rank.

The minimum rank is witnessed by one exact certified output simultaneously
satisfying the rank-induced bit and search budgets.  Hence it upper-bounds the
two separately defined minimum complexities through the rank budget functions.

## Semantic start-rooted targets

Every semantic target has a certified rank profile because it belongs at its
characteristic rank.  Define

```lean
startRootedTargetCertifiedDescriptionRank.
```

We prove

```text
certifiedDescriptionRank(L)
  ≤
characteristicRank(L).
```

The minimum profile-rank witness therefore supplies one exact target grammar
whose checked code and finite canonical search simultaneously satisfy the
budgets at the minimum certified-description rank, not merely at the possibly
larger characteristic rank.

The exact threshold theorem specializes to

```text
L ∈ CertifiedRankProfileClass rank
  ↔
startRootedTargetCertifiedDescriptionRank(L) ≤ rank.
```

The separately minimized bit and search complexities satisfy

```text
minimum bit complexity
  ≤ rankBitBudget(minimum description rank),

minimum search complexity
  ≤ rankSearchBudget(minimum description rank).
```

These bounds are then chained to the characteristic-rank budgets by monotonicity.

## Rank strata

The class of semantic targets whose minimum certified-description rank is at
most `rank` is exactly

```text
semantic target class
∩
certified rank profile class at `rank`.
```

Thus the minimum-description-rank strata form an increasing hierarchy, and
their union is the whole semantic target class.

This rank is a semantic minimum over certified outputs.  No algorithm for
computing it from an unknown target language is asserted.

No target grammar is supplied to the learner.
No `sorry`, `admit`, or `axiom` is used.
-/

namespace MCFG

universe u v w


section GenericCertifiedDescriptionRank

variable {α : Type u}
variable {M : Type v}
variable [Monoid M]
variable {obs : α → M}
variable {f : Nat}

/-- Existence of membership in some finite simultaneous certified-description
rank profile. -/
def HasCorrectedConcreteCertifiedRankProfile
    (L : Set (Word α)) :
    Prop :=
  ∃ rank : Nat,
    L ∈
      CorrectedConcreteCertifiedRankProfileClass
        (α := α)
        (M := M)
        obs f rank

/-- Every explicit rank-profile membership proves existence of some finite
certified-description rank. -/
theorem hasCorrectedConcreteCertifiedRankProfile_of_mem
    {L : Set (Word α)}
    {rank : Nat}
    (hmem :
      L ∈
        CorrectedConcreteCertifiedRankProfileClass
          (α := α)
          (M := M)
          obs f rank) :
    HasCorrectedConcreteCertifiedRankProfile
      (obs := obs)
      (f := f)
      L := by

  exact
    ⟨rank, hmem⟩

/-- Least rank at which a language has one simultaneous certified bit/search
profile. -/
noncomputable def correctedConcreteCertifiedDescriptionRank
    {L : Set (Word α)}
    (hL :
      HasCorrectedConcreteCertifiedRankProfile
        (obs := obs)
        (f := f)
        L) :
    Nat :=
  Nat.find hL

namespace HasCorrectedConcreteCertifiedRankProfile

variable {L : Set (Word α)}

/-- The language belongs to the certified profile hierarchy at its minimum
description rank. -/
theorem descriptionRank_spec
    (hL :
      HasCorrectedConcreteCertifiedRankProfile
        (obs := obs)
        (f := f)
        L) :
    L ∈
      CorrectedConcreteCertifiedRankProfileClass
        (α := α)
        (M := M)
        obs f
        (correctedConcreteCertifiedDescriptionRank
          hL) := by

  exact
    Nat.find_spec hL

/-- Minimality of the certified-description rank. -/
theorem descriptionRank_le_of_mem
    (hL :
      HasCorrectedConcreteCertifiedRankProfile
        (obs := obs)
        (f := f)
        L)
    {rank : Nat}
    (hmem :
      L ∈
        CorrectedConcreteCertifiedRankProfileClass
          (α := α)
          (M := M)
          obs f rank) :
    correctedConcreteCertifiedDescriptionRank
        hL <=
      rank := by

  exact
    Nat.find_min' hL hmem

/-- Exact threshold characterization of the increasing certified profile
hierarchy. -/
theorem mem_rankProfile_iff_descriptionRank_le
    (hL :
      HasCorrectedConcreteCertifiedRankProfile
        (obs := obs)
        (f := f)
        L)
    (rank : Nat) :
    L ∈
        CorrectedConcreteCertifiedRankProfileClass
          (α := α)
          (M := M)
          obs f rank ↔
      correctedConcreteCertifiedDescriptionRank
          hL <=
        rank := by

  constructor

  · exact
      hL.descriptionRank_le_of_mem

  · intro hrank

    exact
      correctedConcreteCertifiedRankProfileClass_mono
        (obs := obs)
        (f := f)
        hrank
        hL.descriptionRank_spec

/-- No strictly smaller rank contains the language. -/
theorem not_mem_rankProfile_of_lt_descriptionRank
    (hL :
      HasCorrectedConcreteCertifiedRankProfile
        (obs := obs)
        (f := f)
        L)
    {rank : Nat}
    (hrank :
      rank <
        correctedConcreteCertifiedDescriptionRank
          hL) :
    L ∉
      CorrectedConcreteCertifiedRankProfileClass
        (α := α)
        (M := M)
        obs f rank := by

  intro hmem

  have hminimum :
      correctedConcreteCertifiedDescriptionRank
          hL <=
        rank :=
    hL.descriptionRank_le_of_mem hmem

  omega

/-- The minimum certified description rank is exactly the first occupied
profile level. -/
theorem first_rankProfile_level
    (hL :
      HasCorrectedConcreteCertifiedRankProfile
        (obs := obs)
        (f := f)
        L) :
    L ∈
        CorrectedConcreteCertifiedRankProfileClass
          (α := α)
          (M := M)
          obs f
          (correctedConcreteCertifiedDescriptionRank hL) ∧
      ∀ rank : Nat,
        rank <
            correctedConcreteCertifiedDescriptionRank hL →
          L ∉
            CorrectedConcreteCertifiedRankProfileClass
              (α := α)
              (M := M)
              obs f rank := by

  exact
    ⟨hL.descriptionRank_spec,
      fun rank hrank =>
        hL.not_mem_rankProfile_of_lt_descriptionRank
          hrank⟩

/-- The minimum rank is witnessed by one exact certified output satisfying both
rank-induced budgets simultaneously. -/
theorem exists_output_at_exact_descriptionRank
    (hL :
      HasCorrectedConcreteCertifiedRankProfile
        (obs := obs)
        (f := f)
        L) :
    ∃
      C :
        CorrectedConcreteCertifiedWorkingGrammarHypothesis
          α M obs f,
      C.output.grammar.StringLanguage = L ∧
        C.bits.length <=
          correctedConcreteCertifiedRankBitBudget
            (correctedConcreteCertifiedDescriptionRank hL)
            f ∧
        C.canonicalSearch.length <=
          correctedConcreteCertifiedRankSearchBudget
            (correctedConcreteCertifiedDescriptionRank hL)
            f := by

  exact
    hL.descriptionRank_spec

/-- Minimum-rank profile membership supplies existence of a certified bit
description. -/
theorem hasBitDescription
    (hL :
      HasCorrectedConcreteCertifiedRankProfile
        (obs := obs)
        (f := f)
        L) :
    HasCorrectedConcreteCertifiedBitDescription
      (obs := obs)
      (f := f)
      L := by

  exact
    CorrectedConcreteCertifiedDescriptionProfileAtBudgets.hasBitDescription
      hL.descriptionRank_spec

/-- Minimum-rank profile membership supplies existence of a certified finite
canonical search. -/
theorem hasCanonicalSearch
    (hL :
      HasCorrectedConcreteCertifiedRankProfile
        (obs := obs)
        (f := f)
        L) :
    HasCorrectedConcreteCertifiedCanonicalSearch
      (obs := obs)
      (f := f)
      L := by

  exact
    CorrectedConcreteCertifiedDescriptionProfileAtBudgets.hasCanonicalSearch
      hL.descriptionRank_spec

/-- The separately minimized certified bit complexity is bounded by the bit
budget at the minimum simultaneous certified-description rank. -/
theorem bitComplexity_le_rankBudget
    (hL :
      HasCorrectedConcreteCertifiedRankProfile
        (obs := obs)
        (f := f)
        L) :
    correctedConcreteCertifiedBitDescriptionComplexity
        hL.hasBitDescription <=
      correctedConcreteCertifiedRankBitBudget
        (correctedConcreteCertifiedDescriptionRank hL)
        f := by

  exact
    hL.hasBitDescription.complexity_le_of_atBudget
      (CorrectedConcreteCertifiedDescriptionProfileAtBudgets.bitDescription
        hL.descriptionRank_spec)

/-- The separately minimized certified search complexity is bounded by the
search budget at the minimum simultaneous certified-description rank. -/
theorem searchComplexity_le_rankBudget
    (hL :
      HasCorrectedConcreteCertifiedRankProfile
        (obs := obs)
        (f := f)
        L) :
    correctedConcreteCertifiedCanonicalSearchComplexity
        hL.hasCanonicalSearch <=
      correctedConcreteCertifiedRankSearchBudget
        (correctedConcreteCertifiedDescriptionRank hL)
        f := by

  exact
    hL.hasCanonicalSearch.complexity_le_of_atBudget
      (CorrectedConcreteCertifiedDescriptionProfileAtBudgets.canonicalSearch
        hL.descriptionRank_spec)

/-- Compact generic minimum simultaneous-description-rank package. -/
theorem descriptionRank_package
    (hL :
      HasCorrectedConcreteCertifiedRankProfile
        (obs := obs)
        (f := f)
        L) :
    (L ∈
      CorrectedConcreteCertifiedRankProfileClass
        (α := α)
        (M := M)
        obs f
        (correctedConcreteCertifiedDescriptionRank hL)) ∧
      (∀ rank : Nat,
        rank <
            correctedConcreteCertifiedDescriptionRank hL →
          L ∉
            CorrectedConcreteCertifiedRankProfileClass
              (α := α)
              (M := M)
              obs f rank) ∧
      (∃
        C :
          CorrectedConcreteCertifiedWorkingGrammarHypothesis
            α M obs f,
        C.output.grammar.StringLanguage = L ∧
          C.bits.length <=
            correctedConcreteCertifiedRankBitBudget
              (correctedConcreteCertifiedDescriptionRank hL)
              f ∧
          C.canonicalSearch.length <=
            correctedConcreteCertifiedRankSearchBudget
              (correctedConcreteCertifiedDescriptionRank hL)
              f) := by

  exact
    ⟨hL.descriptionRank_spec,
      fun rank hrank =>
        hL.not_mem_rankProfile_of_lt_descriptionRank
          hrank,
      hL.exists_output_at_exact_descriptionRank⟩

end HasCorrectedConcreteCertifiedRankProfile

end GenericCertifiedDescriptionRank


section StartRootedTargetCertifiedDescriptionRank

variable {α : Type u}
variable {M : Type v}
variable [Fintype M]
variable [DecidableEq α]
variable [DecidableEq M]
variable [Monoid M]
variable (hα : Nonempty α)
variable (obs : α → M)
variable (f : Nat)

/-- Every semantic start-rooted target belongs to some finite simultaneous
certified-description rank profile. -/
theorem startRootedTarget_hasCertifiedRankProfile
    {L : Set (Word α)}
    (hL :
      L ∈
        StartRootedCorrectedConcreteTargetClass
          (v := w) α M obs f) :
    HasCorrectedConcreteCertifiedRankProfile
      (obs := obs)
      (f := f)
      L := by

  exact
    ⟨startRootedTargetCharacteristicRank
        (v := w) hα obs f hL,
      startRootedTarget_mem_certifiedCharacteristicRankProfileClass
        (v := w) hα obs f hL⟩

/-- Minimum simultaneous certified-description rank of one semantic target. -/
noncomputable def startRootedTargetCertifiedDescriptionRank
    {L : Set (Word α)}
    (hL :
      L ∈
        StartRootedCorrectedConcreteTargetClass
          (v := w) α M obs f) :
    Nat :=
  correctedConcreteCertifiedDescriptionRank
    (startRootedTarget_hasCertifiedRankProfile
      (v := w) hα obs f hL)

/-- The target belongs to the profile hierarchy at its minimum certified
description rank. -/
theorem startRootedTarget_mem_minimumCertifiedDescriptionRankProfile
    {L : Set (Word α)}
    (hL :
      L ∈
        StartRootedCorrectedConcreteTargetClass
          (v := w) α M obs f) :
    L ∈
      CorrectedConcreteCertifiedRankProfileClass
        (α := α)
        (M := M)
        obs f
        (startRootedTargetCertifiedDescriptionRank
          (v := w) hα obs f hL) := by

  exact
    (startRootedTarget_hasCertifiedRankProfile
      (v := w) hα obs f hL).descriptionRank_spec

/-- The target's minimum simultaneous certified-description rank is no larger
than its characteristic rank. -/
theorem
    startRootedTargetCertifiedDescriptionRank_le_characteristicRank
    {L : Set (Word α)}
    (hL :
      L ∈
        StartRootedCorrectedConcreteTargetClass
          (v := w) α M obs f) :
    startRootedTargetCertifiedDescriptionRank
        (v := w) hα obs f hL <=
      startRootedTargetCharacteristicRank
        (v := w) hα obs f hL := by

  unfold
    startRootedTargetCertifiedDescriptionRank

  exact
    (startRootedTarget_hasCertifiedRankProfile
      (v := w) hα obs f hL).descriptionRank_le_of_mem
      (startRootedTarget_mem_certifiedCharacteristicRankProfileClass
        (v := w) hα obs f hL)

/-- Exact threshold theorem for one semantic target. -/
theorem startRootedTarget_mem_rankProfile_iff_descriptionRank_le
    {L : Set (Word α)}
    (hL :
      L ∈
        StartRootedCorrectedConcreteTargetClass
          (v := w) α M obs f)
    (rank : Nat) :
    L ∈
        CorrectedConcreteCertifiedRankProfileClass
          (α := α)
          (M := M)
          obs f rank ↔
      startRootedTargetCertifiedDescriptionRank
          (v := w) hα obs f hL <=
        rank := by

  exact
    (startRootedTarget_hasCertifiedRankProfile
      (v := w) hα obs f hL).mem_rankProfile_iff_descriptionRank_le
      rank

/-- No rank below the target's minimum certified-description rank contains the
target. -/
theorem startRootedTarget_not_mem_rankProfile_of_lt_descriptionRank
    {L : Set (Word α)}
    (hL :
      L ∈
        StartRootedCorrectedConcreteTargetClass
          (v := w) α M obs f)
    {rank : Nat}
    (hrank :
      rank <
        startRootedTargetCertifiedDescriptionRank
          (v := w) hα obs f hL) :
    L ∉
      CorrectedConcreteCertifiedRankProfileClass
        (α := α)
        (M := M)
        obs f rank := by

  exact
    (startRootedTarget_hasCertifiedRankProfile
      (v := w) hα obs f hL).not_mem_rankProfile_of_lt_descriptionRank
      hrank

/-- The minimum target description rank is witnessed by one exact certified
output simultaneously satisfying its induced bit and search budgets. -/
theorem startRootedTarget_exists_output_at_minimumCertifiedDescriptionRank
    {L : Set (Word α)}
    (hL :
      L ∈
        StartRootedCorrectedConcreteTargetClass
          (v := w) α M obs f) :
    ∃
      C :
        CorrectedConcreteCertifiedWorkingGrammarHypothesis
          α M obs f,
      C.output.grammar.StringLanguage = L ∧
        C.bits.length <=
          correctedConcreteCertifiedRankBitBudget
            (startRootedTargetCertifiedDescriptionRank
              (v := w) hα obs f hL)
            f ∧
        C.canonicalSearch.length <=
          correctedConcreteCertifiedRankSearchBudget
            (startRootedTargetCertifiedDescriptionRank
              (v := w) hα obs f hL)
            f := by

  exact
    (startRootedTarget_hasCertifiedRankProfile
      (v := w) hα obs f hL).exists_output_at_exact_descriptionRank

/-- The separately minimized target bit complexity is bounded already at the
minimum simultaneous certified-description rank. -/
theorem
    startRootedTargetCertifiedBitDescriptionComplexity_le_descriptionRankBudget
    {L : Set (Word α)}
    (hL :
      L ∈
        StartRootedCorrectedConcreteTargetClass
          (v := w) α M obs f) :
    startRootedTargetCertifiedBitDescriptionComplexity
        (v := w) hα obs f hL <=
      correctedConcreteCertifiedRankBitBudget
        (startRootedTargetCertifiedDescriptionRank
          (v := w) hα obs f hL)
        f := by

  let hprofile :=
    startRootedTarget_mem_minimumCertifiedDescriptionRankProfile
      (v := w) hα obs f hL

  exact
    startRootedTargetCertifiedBitDescriptionComplexity_le_of_profile
      (v := w) hα obs f hL hprofile

/-- The separately minimized target search complexity is bounded already at the
minimum simultaneous certified-description rank. -/
theorem
    startRootedTargetCertifiedCanonicalSearchComplexity_le_descriptionRankBudget
    {L : Set (Word α)}
    (hL :
      L ∈
        StartRootedCorrectedConcreteTargetClass
          (v := w) α M obs f) :
    startRootedTargetCertifiedCanonicalSearchComplexity
        (v := w) hα obs f hL <=
      correctedConcreteCertifiedRankSearchBudget
        (startRootedTargetCertifiedDescriptionRank
          (v := w) hα obs f hL)
        f := by

  let hprofile :=
    startRootedTarget_mem_minimumCertifiedDescriptionRankProfile
      (v := w) hα obs f hL

  exact
    startRootedTargetCertifiedCanonicalSearchComplexity_le_of_profile
      (v := w) hα obs f hL hprofile

/-- The minimum-description-rank bit budget is no larger than the
characteristic-rank bit budget. -/
theorem
    startRootedTarget_descriptionRankBitBudget_le_characteristicRankBitBudget
    {L : Set (Word α)}
    (hL :
      L ∈
        StartRootedCorrectedConcreteTargetClass
          (v := w) α M obs f) :
    correctedConcreteCertifiedRankBitBudget
        (startRootedTargetCertifiedDescriptionRank
          (v := w) hα obs f hL)
        f <=
      correctedConcreteCertifiedRankBitBudget
        (startRootedTargetCharacteristicRank
          (v := w) hα obs f hL)
        f := by

  exact
    correctedConcreteCertifiedRankBitBudget_mono
      (startRootedTargetCertifiedDescriptionRank_le_characteristicRank
        (v := w) hα obs f hL)

/-- The minimum-description-rank search budget is no larger than the
characteristic-rank search budget. -/
theorem
    startRootedTarget_descriptionRankSearchBudget_le_characteristicRankSearchBudget
    {L : Set (Word α)}
    (hL :
      L ∈
        StartRootedCorrectedConcreteTargetClass
          (v := w) α M obs f) :
    correctedConcreteCertifiedRankSearchBudget
        (startRootedTargetCertifiedDescriptionRank
          (v := w) hα obs f hL)
        f <=
      correctedConcreteCertifiedRankSearchBudget
        (startRootedTargetCharacteristicRank
          (v := w) hα obs f hL)
        f := by

  exact
    correctedConcreteCertifiedRankSearchBudget_mono
      (startRootedTargetCertifiedDescriptionRank_le_characteristicRank
        (v := w) hα obs f hL)

/-- Compact target minimum simultaneous-description-rank package. -/
theorem startRootedTargetCertifiedDescriptionRank_package
    {L : Set (Word α)}
    (hL :
      L ∈
        StartRootedCorrectedConcreteTargetClass
          (v := w) α M obs f) :
    (startRootedTargetCertifiedDescriptionRank
        (v := w) hα obs f hL <=
      startRootedTargetCharacteristicRank
        (v := w) hα obs f hL) ∧
      (L ∈
        CorrectedConcreteCertifiedRankProfileClass
          (α := α)
          (M := M)
          obs f
          (startRootedTargetCertifiedDescriptionRank
            (v := w) hα obs f hL)) ∧
      (∀ rank : Nat,
        rank <
            startRootedTargetCertifiedDescriptionRank
              (v := w) hα obs f hL →
          L ∉
            CorrectedConcreteCertifiedRankProfileClass
              (α := α)
              (M := M)
              obs f rank) ∧
      (∃
        C :
          CorrectedConcreteCertifiedWorkingGrammarHypothesis
            α M obs f,
        C.output.grammar.StringLanguage = L ∧
          C.bits.length <=
            correctedConcreteCertifiedRankBitBudget
              (startRootedTargetCertifiedDescriptionRank
                (v := w) hα obs f hL)
              f ∧
          C.canonicalSearch.length <=
            correctedConcreteCertifiedRankSearchBudget
              (startRootedTargetCertifiedDescriptionRank
                (v := w) hα obs f hL)
              f) := by

  exact
    ⟨startRootedTargetCertifiedDescriptionRank_le_characteristicRank
        (v := w) hα obs f hL,
      startRootedTarget_mem_minimumCertifiedDescriptionRankProfile
        (v := w) hα obs f hL,
      fun rank hrank =>
        startRootedTarget_not_mem_rankProfile_of_lt_descriptionRank
          (v := w) hα obs f hL hrank,
      startRootedTarget_exists_output_at_minimumCertifiedDescriptionRank
        (v := w) hα obs f hL⟩

end StartRootedTargetCertifiedDescriptionRank


section CertifiedDescriptionRankStrata

variable {α : Type u}
variable {M : Type v}
variable [Fintype M]
variable [DecidableEq α]
variable [DecidableEq M]
variable [Monoid M]
variable (hα : Nonempty α)
variable (obs : α → M)
variable (f : Nat)

/-- Semantic targets whose minimum simultaneous certified-description rank is
at most `rank`. -/
def StartRootedCorrectedConcreteTargetCertifiedDescriptionRankAtMostClass
    (rank : Nat) :
    Set (Set (Word α)) :=
  {L |
    ∃
      hL :
        L ∈
          StartRootedCorrectedConcreteTargetClass
            (v := w) α M obs f,
      startRootedTargetCertifiedDescriptionRank
          (v := w) hα obs f hL <=
        rank}

/-- The minimum certified-description-rank strata are increasing. -/
theorem
    startRootedCorrectedConcreteTargetCertifiedDescriptionRankAtMostClass_mono
    {rank rank' : Nat}
    (hrank :
      rank <= rank') :
    StartRootedCorrectedConcreteTargetCertifiedDescriptionRankAtMostClass
        (v := w) hα obs f rank ⊆
      StartRootedCorrectedConcreteTargetCertifiedDescriptionRankAtMostClass
        (v := w) hα obs f rank' := by

  intro L hL

  rcases hL with
    ⟨hTarget, hbound⟩

  exact
    ⟨hTarget,
      hbound.trans hrank⟩

/-- Exact class characterization: the targets of minimum description rank at
most `rank` are precisely the semantic targets lying in the certified profile
class at level `rank`. -/
theorem
    startRootedTargetCertifiedDescriptionRankAtMostClass_eq_target_inter_rankProfile
    (rank : Nat) :
    StartRootedCorrectedConcreteTargetCertifiedDescriptionRankAtMostClass
        (v := w) hα obs f rank =
      {L : Set (Word α) |
        L ∈
            StartRootedCorrectedConcreteTargetClass
              (v := w) α M obs f ∧
          L ∈
            CorrectedConcreteCertifiedRankProfileClass
              (α := α)
              (M := M)
              obs f rank} := by

  ext L

  constructor

  · intro hL

    rcases hL with
      ⟨hTarget, hbound⟩

    exact
      ⟨hTarget,
        (startRootedTarget_mem_rankProfile_iff_descriptionRank_le
          (v := w) hα obs f hTarget rank).mpr
          hbound⟩

  · intro hL

    rcases hL with
      ⟨hTarget, hprofile⟩

    exact
      ⟨hTarget,
        (startRootedTarget_mem_rankProfile_iff_descriptionRank_le
          (v := w) hα obs f hTarget rank).mp
          hprofile⟩

/-- Every minimum-description-rank stratum is contained in the semantic target
class. -/
theorem
    startRootedTargetCertifiedDescriptionRankAtMostClass_subset_targetClass
    (rank : Nat) :
    StartRootedCorrectedConcreteTargetCertifiedDescriptionRankAtMostClass
        (v := w) hα obs f rank ⊆
      StartRootedCorrectedConcreteTargetClass
        (v := w) α M obs f := by

  intro L hL

  rcases hL with
    ⟨hTarget, hbound⟩

  exact hTarget

/-- Every minimum-description-rank stratum is contained in the corresponding
certified profile class. -/
theorem
    startRootedTargetCertifiedDescriptionRankAtMostClass_subset_rankProfileClass
    (rank : Nat) :
    StartRootedCorrectedConcreteTargetCertifiedDescriptionRankAtMostClass
        (v := w) hα obs f rank ⊆
      CorrectedConcreteCertifiedRankProfileClass
        (α := α)
        (M := M)
        obs f rank := by

  intro L hL

  rcases hL with
    ⟨hTarget, hbound⟩

  exact
    (startRootedTarget_mem_rankProfile_iff_descriptionRank_le
      (v := w) hα obs f hTarget rank).mpr
      hbound

/-- Every semantic target lies in the stratum indexed by its own minimum
certified-description rank. -/
theorem
    startRootedTarget_mem_ownCertifiedDescriptionRankAtMostClass
    {L : Set (Word α)}
    (hL :
      L ∈
        StartRootedCorrectedConcreteTargetClass
          (v := w) α M obs f) :
    L ∈
      StartRootedCorrectedConcreteTargetCertifiedDescriptionRankAtMostClass
        (v := w) hα obs f
        (startRootedTargetCertifiedDescriptionRank
          (v := w) hα obs f hL) := by

  exact
    ⟨hL,
      Nat.le_refl _⟩

/-- The union of all finite minimum-description-rank strata is the whole
semantic target class, stated as mutual inclusion. -/
theorem
    startRootedTargetClass_eq_exists_certifiedDescriptionRankAtMostClass :
    StartRootedCorrectedConcreteTargetClass
        (v := w) α M obs f =
      {L : Set (Word α) |
        ∃ rank : Nat,
          L ∈
            StartRootedCorrectedConcreteTargetCertifiedDescriptionRankAtMostClass
              (v := w) hα obs f rank} := by

  ext L

  constructor

  · intro hL

    exact
      ⟨startRootedTargetCertifiedDescriptionRank
          (v := w) hα obs f hL,
        startRootedTarget_mem_ownCertifiedDescriptionRankAtMostClass
          (v := w) hα obs f hL⟩

  · intro hL

    rcases hL with
      ⟨rank, hRank⟩

    exact
      startRootedTargetCertifiedDescriptionRankAtMostClass_subset_targetClass
        (v := w) hα obs f rank hRank

end CertifiedDescriptionRankStrata


section CertifiedDescriptionRankPackages

variable {α : Type u}
variable {M : Type v}
variable [Fintype M]
variable [DecidableEq α]
variable [DecidableEq M]
variable [Monoid M]
variable (hα : Nonempty α)
variable (obs : α → M)
variable (f : Nat)

/-- Final class-level identification and minimum simultaneous certified
description-rank package. -/
theorem
    correctedConcreteCertifiedWorkingGrammarLearner_identification_descriptionRank_package :
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
        startRootedTargetCertifiedDescriptionRank
            (v := w) hα obs f hL <=
          startRootedTargetCharacteristicRank
            (v := w) hα obs f hL) ∧
      (∀
        L : Set (Word α),
        ∀ hL :
          L ∈
            StartRootedCorrectedConcreteTargetClass
              (v := w) α M obs f,
        ∀ rank : Nat,
          L ∈
              CorrectedConcreteCertifiedRankProfileClass
                (α := α)
                (M := M)
                obs f rank ↔
            startRootedTargetCertifiedDescriptionRank
                (v := w) hα obs f hL <=
              rank) ∧
      (∀
        L : Set (Word α),
        ∀ hL :
          L ∈
            StartRootedCorrectedConcreteTargetClass
              (v := w) α M obs f,
        ∃
          C :
            CorrectedConcreteCertifiedWorkingGrammarHypothesis
              α M obs f,
          C.output.grammar.StringLanguage = L ∧
            C.bits.length <=
              correctedConcreteCertifiedRankBitBudget
                (startRootedTargetCertifiedDescriptionRank
                  (v := w) hα obs f hL)
                f ∧
            C.canonicalSearch.length <=
              correctedConcreteCertifiedRankSearchBudget
                (startRootedTargetCertifiedDescriptionRank
                  (v := w) hα obs f hL)
                f) ∧
      (∀
        L : Set (Word α),
        ∀ hL :
          L ∈
            StartRootedCorrectedConcreteTargetClass
              (v := w) α M obs f,
        startRootedTargetCertifiedBitDescriptionComplexity
            (v := w) hα obs f hL <=
          correctedConcreteCertifiedRankBitBudget
            (startRootedTargetCertifiedDescriptionRank
              (v := w) hα obs f hL)
            f ∧
        startRootedTargetCertifiedCanonicalSearchComplexity
            (v := w) hα obs f hL <=
          correctedConcreteCertifiedRankSearchBudget
            (startRootedTargetCertifiedDescriptionRank
              (v := w) hα obs f hL)
            f) ∧
      (∀ rank : Nat,
        StartRootedCorrectedConcreteTargetCertifiedDescriptionRankAtMostClass
            (v := w) hα obs f rank =
          {L : Set (Word α) |
            L ∈
                StartRootedCorrectedConcreteTargetClass
                  (v := w) α M obs f ∧
              L ∈
                CorrectedConcreteCertifiedRankProfileClass
                  (α := α)
                  (M := M)
                  obs f rank}) := by

  exact
    ⟨correctedConcreteCertifiedWorkingGrammarLearner_identifies_startRootedTargetClass
        (v := w) hα obs f,
      fun L hL =>
        startRootedTargetCertifiedDescriptionRank_le_characteristicRank
          (v := w) hα obs f hL,
      fun L hL rank =>
        startRootedTarget_mem_rankProfile_iff_descriptionRank_le
          (v := w) hα obs f hL rank,
      fun L hL =>
        startRootedTarget_exists_output_at_minimumCertifiedDescriptionRank
          (v := w) hα obs f hL,
      fun L hL =>
        ⟨startRootedTargetCertifiedBitDescriptionComplexity_le_descriptionRankBudget
            (v := w) hα obs f hL,
          startRootedTargetCertifiedCanonicalSearchComplexity_le_descriptionRankBudget
            (v := w) hα obs f hL⟩,
      startRootedTargetCertifiedDescriptionRankAtMostClass_eq_target_inter_rankProfile
        (v := w) hα obs f⟩

end CertifiedDescriptionRankPackages

end MCFG
