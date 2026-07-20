/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG.ConcreteCanonicalLearnerWorkingGrammarCertifiedDescriptionComplexity

/-!
# ConcreteCanonicalLearnerWorkingGrammarCertifiedDescriptionProfile.lean

The preceding file defines two target-specific minimum complexity measures:

* minimum checked Boolean-code length; and
* minimum finite canonical-search-list length.

Those two minima are taken separately.  In general, separate minima need not
be realized by the same certified output.

This file therefore introduces a simultaneous two-dimensional description
profile.

## Joint certified profile

A language has a certified profile at budgets `(b,q)` when one and the same

```lean
CorrectedConcreteCertifiedWorkingGrammarHypothesis α M obs f
```

has

```text
exact language L,
checked code length ≤ b,
canonical search length ≤ q.
```

This is written

```lean
CorrectedConcreteCertifiedDescriptionProfileAtBudgets L b q.
```

The profile is upward closed in both coordinates.  It projects to each of the
one-dimensional budget notions from the preceding file, so any joint profile
simultaneously upper-bounds both separately defined minimum complexities.

## Rank-indexed paper profile

For characteristic/sample rank `r`, define

```lean
correctedConcreteCertifiedRankBitBudget r f
  =
correctedConcreteCompiledGrammarPaperPowerBitBound r f
```

and

```lean
correctedConcreteCertifiedRankSearchBudget r f
  =
2 ^ (correctedConcreteCertifiedRankBitBudget r f + 1).
```

Both budgets are monotone in `r`.

The rank profile class consists of all languages having one exact certified
output within these two simultaneous budgets.

## Learner outputs and semantic targets

For every finite sample `K`, the certified learner output belongs to the rank
profile class at level

```lean
sampleLengthBudget K.
```

For every semantic start-rooted target `L`, the selected
minimum-characteristic certified output belongs to the rank profile class at
level

```lean
startRootedTargetCharacteristicRank hα obs f hL.
```

Thus characteristic rank bounds the complete simultaneous description profile,
not merely the two separate minima.

We also define the semantic target stratum of targets whose characteristic rank
is at most `r`.  That stratum is contained in the certified rank profile class
at level `r`.  Hence the rank profile classes form an increasing hierarchy
containing the corresponding increasing target-rank strata.

The final package combines

* positive-data identification by the certified learner;
* every learner output's own-level profile membership;
* every target's characteristic-rank profile membership;
* monotonicity of the profile hierarchy; and
* inclusion of every bounded characteristic-rank target stratum.

No claim is made that the two separate minima are attained by the same output.
The joint profile records exactly the simultaneous statement that is verified.

No target grammar is supplied to the learner.
No `sorry`, `admit`, or `axiom` is used.
-/

namespace MCFG

universe u v w


section GenericCertifiedDescriptionProfile

variable {α : Type u}
variable {M : Type v}
variable [Monoid M]
variable {obs : α → M}
variable {f : Nat}

/-- One exact certified output simultaneously satisfying checked bit-length and
finite canonical-search-length budgets. -/
def CorrectedConcreteCertifiedDescriptionProfileAtBudgets
    (L : Set (Word α))
    (bitBudget searchBudget : Nat) :
    Prop :=
  ∃
    C :
      CorrectedConcreteCertifiedWorkingGrammarHypothesis
        α M obs f,
    C.output.grammar.StringLanguage = L ∧
      C.bits.length <= bitBudget ∧
      C.canonicalSearch.length <= searchBudget

/-- The simultaneous certified profile is upward closed in both coordinates. -/
theorem correctedConcreteCertifiedDescriptionProfileAtBudgets_mono
    {L : Set (Word α)}
    {bitBudget bitBudget' searchBudget searchBudget' : Nat}
    (hbit :
      bitBudget <= bitBudget')
    (hsearch :
      searchBudget <= searchBudget')
    (hprofile :
      CorrectedConcreteCertifiedDescriptionProfileAtBudgets
        (obs := obs)
        (f := f)
        L bitBudget searchBudget) :
    CorrectedConcreteCertifiedDescriptionProfileAtBudgets
      (obs := obs)
      (f := f)
      L bitBudget' searchBudget' := by

  rcases hprofile with
    ⟨C, hlanguage, hbits, hsearchLength⟩

  exact
    ⟨C,
      hlanguage,
      hbits.trans hbit,
      hsearchLength.trans hsearch⟩

/-- Every exact certified output realizes its own simultaneous profile. -/
theorem correctedConcreteCertifiedDescriptionProfileAtBudgets_of_output
    {L : Set (Word α)}
    (C :
      CorrectedConcreteCertifiedWorkingGrammarHypothesis
        α M obs f)
    (hlanguage :
      C.output.grammar.StringLanguage = L) :
    CorrectedConcreteCertifiedDescriptionProfileAtBudgets
      (obs := obs)
      (f := f)
      L
      C.bits.length
      C.canonicalSearch.length := by

  exact
    ⟨C,
      hlanguage,
      Nat.le_refl _,
      Nat.le_refl _⟩

/-- A simultaneous profile projects to a certified bit-description budget. -/
theorem
    CorrectedConcreteCertifiedDescriptionProfileAtBudgets.bitDescription
    {L : Set (Word α)}
    {bitBudget searchBudget : Nat}
    (hprofile :
      CorrectedConcreteCertifiedDescriptionProfileAtBudgets
        (obs := obs)
        (f := f)
        L bitBudget searchBudget) :
    CorrectedConcreteCertifiedBitDescriptionAtBudget
      (obs := obs)
      (f := f)
      L bitBudget := by

  rcases hprofile with
    ⟨C, hlanguage, hbits, hsearch⟩

  exact
    ⟨C,
      hlanguage,
      hbits⟩

/-- A simultaneous profile projects to a certified canonical-search budget. -/
theorem
    CorrectedConcreteCertifiedDescriptionProfileAtBudgets.canonicalSearch
    {L : Set (Word α)}
    {bitBudget searchBudget : Nat}
    (hprofile :
      CorrectedConcreteCertifiedDescriptionProfileAtBudgets
        (obs := obs)
        (f := f)
        L bitBudget searchBudget) :
    CorrectedConcreteCertifiedCanonicalSearchAtBudget
      (obs := obs)
      (f := f)
      L searchBudget := by

  rcases hprofile with
    ⟨C, hlanguage, hbits, hsearch⟩

  exact
    ⟨C,
      hlanguage,
      hsearch⟩

/-- A simultaneous profile proves existence of some finite certified bit
description. -/
theorem
    CorrectedConcreteCertifiedDescriptionProfileAtBudgets.hasBitDescription
    {L : Set (Word α)}
    {bitBudget searchBudget : Nat}
    (hprofile :
      CorrectedConcreteCertifiedDescriptionProfileAtBudgets
        (obs := obs)
        (f := f)
        L bitBudget searchBudget) :
    HasCorrectedConcreteCertifiedBitDescription
      (obs := obs)
      (f := f)
      L := by

  exact
    ⟨bitBudget,
      hprofile.bitDescription⟩

/-- A simultaneous profile proves existence of some finite certified canonical
search. -/
theorem
    CorrectedConcreteCertifiedDescriptionProfileAtBudgets.hasCanonicalSearch
    {L : Set (Word α)}
    {bitBudget searchBudget : Nat}
    (hprofile :
      CorrectedConcreteCertifiedDescriptionProfileAtBudgets
        (obs := obs)
        (f := f)
        L bitBudget searchBudget) :
    HasCorrectedConcreteCertifiedCanonicalSearch
      (obs := obs)
      (f := f)
      L := by

  exact
    ⟨searchBudget,
      hprofile.canonicalSearch⟩

/-- Languages admitting a simultaneous certified profile at fixed budgets. -/
def CorrectedConcreteCertifiedDescriptionProfileClass
    (α : Type u)
    (M : Type v)
    [Monoid M]
    (obs : α → M)
    (f bitBudget searchBudget : Nat) :
    Set (Set (Word α)) :=
  {L |
    CorrectedConcreteCertifiedDescriptionProfileAtBudgets
      (obs := obs)
      (f := f)
      L bitBudget searchBudget}

/-- Fixed-budget profile classes are monotone in both coordinates. -/
theorem correctedConcreteCertifiedDescriptionProfileClass_mono
    {bitBudget bitBudget' searchBudget searchBudget' : Nat}
    (hbit :
      bitBudget <= bitBudget')
    (hsearch :
      searchBudget <= searchBudget') :
    CorrectedConcreteCertifiedDescriptionProfileClass
        α M obs f bitBudget searchBudget ⊆
      CorrectedConcreteCertifiedDescriptionProfileClass
        α M obs f bitBudget' searchBudget' := by

  intro L hL

  exact
    correctedConcreteCertifiedDescriptionProfileAtBudgets_mono
      hbit hsearch hL

end GenericCertifiedDescriptionProfile


section RankProfileBudgets

/-- Checked bit budget associated with one sample/characteristic rank. -/
def correctedConcreteCertifiedRankBitBudget
    (rank f : Nat) :
    Nat :=
  correctedConcreteCompiledGrammarPaperPowerBitBound
    rank f

/-- Finite canonical-search budget associated with one
sample/characteristic rank. -/
def correctedConcreteCertifiedRankSearchBudget
    (rank f : Nat) :
    Nat :=
  2 ^
    (correctedConcreteCertifiedRankBitBudget
        rank f +
      1)

/-- The rank-indexed checked bit budget is monotone in the rank. -/
theorem correctedConcreteCertifiedRankBitBudget_mono
    {rank rank' f : Nat}
    (hrank :
      rank <= rank') :
    correctedConcreteCertifiedRankBitBudget
        rank f <=
      correctedConcreteCertifiedRankBitBudget
        rank' f := by

  exact
    correctedConcreteCompiledGrammarPaperPowerBitBound_mono_sampleLength
      hrank

/-- The rank-indexed finite canonical-search budget is monotone in the rank. -/
theorem correctedConcreteCertifiedRankSearchBudget_mono
    {rank rank' f : Nat}
    (hrank :
      rank <= rank') :
    correctedConcreteCertifiedRankSearchBudget
        rank f <=
      correctedConcreteCertifiedRankSearchBudget
        rank' f := by

  unfold
    correctedConcreteCertifiedRankSearchBudget

  have hbit :
      correctedConcreteCertifiedRankBitBudget
            rank f +
          1 <=
        correctedConcreteCertifiedRankBitBudget
            rank' f +
          1 :=
    Nat.add_le_add_right
      (correctedConcreteCertifiedRankBitBudget_mono
        hrank)
      1

  exact
    Nat.pow_le_pow_of_le
      (by omega)
      hbit

end RankProfileBudgets


section RankProfileClasses

variable {α : Type u}
variable {M : Type v}
variable [Monoid M]
variable (obs : α → M)
variable (f : Nat)

/-- Languages possessing one simultaneous certified description within the
paper budgets induced by rank `rank`. -/
def CorrectedConcreteCertifiedRankProfileClass
    (rank : Nat) :
    Set (Set (Word α)) :=
  CorrectedConcreteCertifiedDescriptionProfileClass
    α M obs f
    (correctedConcreteCertifiedRankBitBudget
      rank f)
    (correctedConcreteCertifiedRankSearchBudget
      rank f)

/-- The certified rank profile classes form an increasing hierarchy. -/
theorem correctedConcreteCertifiedRankProfileClass_mono
    {rank rank' : Nat}
    (hrank :
      rank <= rank') :
    CorrectedConcreteCertifiedRankProfileClass
        (α := α) (M := M) obs f rank ⊆
      CorrectedConcreteCertifiedRankProfileClass
        (α := α) (M := M) obs f rank' := by

  exact
    correctedConcreteCertifiedDescriptionProfileClass_mono
      (correctedConcreteCertifiedRankBitBudget_mono
        hrank)
      (correctedConcreteCertifiedRankSearchBudget_mono
        hrank)

end RankProfileClasses


section CertifiedLearnerOwnRankProfile

variable {α : Type u}
variable {M : Type v}
variable [Fintype M]
variable [DecidableEq α]
variable [DecidableEq M]
variable [Monoid M]

/-- Every certified learner output realizes the simultaneous profile induced by
the total length of its own finite input sample. -/
theorem
    correctedConcreteCertifiedWorkingGrammarLearner_profileAtOwnSampleLength
    (hα : Nonempty α)
    (obs : α → M)
    (f : Nat)
    (K : Finset (Word α)) :
    CorrectedConcreteCertifiedDescriptionProfileAtBudgets
      (obs := obs)
      (f := f)
      ((correctedConcreteCertifiedWorkingGrammarLearner
          hα obs f K).output.grammar.StringLanguage)
      (correctedConcreteCertifiedRankBitBudget
        (sampleLengthBudget K)
        f)
      (correctedConcreteCertifiedRankSearchBudget
        (sampleLengthBudget K)
        f) := by

  let C :=
    correctedConcreteCertifiedWorkingGrammarLearner
      hα obs f K

  exact
    ⟨C,
      rfl,
      by
        simpa [
          C,
          correctedConcreteCertifiedRankBitBudget
        ] using
          correctedConcreteCertifiedWorkingGrammarLearner_bitLength_le
            hα obs f K,
      by
        simpa [
          C,
          correctedConcreteCertifiedRankSearchBudget,
          correctedConcreteCertifiedRankBitBudget
        ] using
          correctedConcreteCertifiedWorkingGrammarLearner_searchLength_le
            hα obs f K⟩

/-- Every certified learner output language belongs to its own rank profile
class. -/
theorem
    correctedConcreteCertifiedWorkingGrammarLearner_language_mem_ownRankProfileClass
    (hα : Nonempty α)
    (obs : α → M)
    (f : Nat)
    (K : Finset (Word α)) :
    (correctedConcreteCertifiedWorkingGrammarLearner
        hα obs f K).output.grammar.StringLanguage ∈
      CorrectedConcreteCertifiedRankProfileClass
        (α := α)
        (M := M)
        obs f
        (sampleLengthBudget K) := by

  exact
    correctedConcreteCertifiedWorkingGrammarLearner_profileAtOwnSampleLength
      hα obs f K

/-- The original corrected concrete learner language belongs to the same
own-sample rank profile class. -/
theorem
    correctedConcreteCanonicalLearnerLanguage_mem_certifiedOwnRankProfileClass
    (hα : Nonempty α)
    (obs : α → M)
    (f : Nat)
    (K : Finset (Word α)) :
    CorrectedConcreteCanonicalLearnerLanguage
        K obs f ∈
      CorrectedConcreteCertifiedRankProfileClass
        (α := α)
        (M := M)
        obs f
        (sampleLengthBudget K) := by

  rw [
    ← correctedConcreteCertifiedWorkingGrammarLearner_language_eq_corrected
      hα obs f K
  ]

  exact
    correctedConcreteCertifiedWorkingGrammarLearner_language_mem_ownRankProfileClass
      hα obs f K

/-- Raising the rank preserves membership of a certified learner output
language. -/
theorem
    correctedConcreteCertifiedWorkingGrammarLearner_language_mem_rankProfileClass_of_sampleLength_le
    (hα : Nonempty α)
    (obs : α → M)
    (f : Nat)
    (K : Finset (Word α))
    {rank : Nat}
    (hK :
      sampleLengthBudget K <= rank) :
    (correctedConcreteCertifiedWorkingGrammarLearner
        hα obs f K).output.grammar.StringLanguage ∈
      CorrectedConcreteCertifiedRankProfileClass
        (α := α)
        (M := M)
        obs f rank := by

  exact
    correctedConcreteCertifiedRankProfileClass_mono
      (obs := obs)
      (f := f)
      hK
      (correctedConcreteCertifiedWorkingGrammarLearner_language_mem_ownRankProfileClass
        hα obs f K)

end CertifiedLearnerOwnRankProfile


section TargetCharacteristicRankProfile

variable {α : Type u}
variable {M : Type v}
variable [Fintype M]
variable [DecidableEq α]
variable [DecidableEq M]
variable [Monoid M]
variable (hα : Nonempty α)
variable (obs : α → M)
variable (f : Nat)

/-- The selected minimum-characteristic certified output simultaneously
satisfies the bit and search budgets induced by the target characteristic
rank. -/
theorem
    startRootedTarget_certifiedProfileAtCharacteristicRank
    {L : Set (Word α)}
    (hL :
      L ∈
        StartRootedCorrectedConcreteTargetClass
          (v := w) α M obs f) :
    CorrectedConcreteCertifiedDescriptionProfileAtBudgets
      (obs := obs)
      (f := f)
      L
      (correctedConcreteCertifiedRankBitBudget
        (startRootedTargetCharacteristicRank
          (v := w) hα obs f hL)
        f)
      (correctedConcreteCertifiedRankSearchBudget
        (startRootedTargetCharacteristicRank
          (v := w) hα obs f hL)
        f) := by

  let C :=
    startRootedTargetMinimalCharacteristicCertifiedOutput
      (v := w) hα obs f hL

  exact
    ⟨C,
      by
        simpa [C] using
          startRootedTargetMinimalCharacteristicCertifiedOutput_language_eq
            (v := w) hα obs f hL,
      by
        simpa [
          C,
          correctedConcreteCertifiedRankBitBudget
        ] using
          startRootedTargetMinimalCharacteristicCertifiedOutput_bitLength_le_rank
            (v := w) hα obs f hL,
      by
        simpa [
          C,
          correctedConcreteCertifiedRankSearchBudget,
          correctedConcreteCertifiedRankBitBudget
        ] using
          startRootedTargetMinimalCharacteristicCertifiedOutput_searchLength_le_rank
            (v := w) hα obs f hL⟩

/-- Every semantic target belongs to the simultaneous certified rank profile
class at its own characteristic rank. -/
theorem startRootedTarget_mem_certifiedCharacteristicRankProfileClass
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
        (startRootedTargetCharacteristicRank
          (v := w) hα obs f hL) := by

  exact
    startRootedTarget_certifiedProfileAtCharacteristicRank
      (v := w) hα obs f hL

/-- If a target's characteristic rank is at most `rank`, then the target belongs
to the simultaneous certified profile class at level `rank`. -/
theorem
    startRootedTarget_mem_certifiedRankProfileClass_of_characteristicRank_le
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
    correctedConcreteCertifiedRankProfileClass_mono
      (obs := obs)
      (f := f)
      hrank
      (startRootedTarget_mem_certifiedCharacteristicRankProfileClass
        (v := w) hα obs f hL)

/-- Any simultaneous profile for a semantic target upper-bounds its separately
defined minimum certified bit complexity. -/
theorem
    startRootedTargetCertifiedBitDescriptionComplexity_le_of_profile
    {L : Set (Word α)}
    (hL :
      L ∈
        StartRootedCorrectedConcreteTargetClass
          (v := w) α M obs f)
    {bitBudget searchBudget : Nat}
    (hprofile :
      CorrectedConcreteCertifiedDescriptionProfileAtBudgets
        (obs := obs)
        (f := f)
        L bitBudget searchBudget) :
    startRootedTargetCertifiedBitDescriptionComplexity
        (v := w) hα obs f hL <=
      bitBudget := by

  unfold
    startRootedTargetCertifiedBitDescriptionComplexity

  exact
    (startRootedTarget_hasCertifiedBitDescription
      (v := w) hα obs f hL).complexity_le_of_atBudget
      hprofile.bitDescription

/-- Any simultaneous profile for a semantic target upper-bounds its separately
defined minimum certified canonical-search complexity. -/
theorem
    startRootedTargetCertifiedCanonicalSearchComplexity_le_of_profile
    {L : Set (Word α)}
    (hL :
      L ∈
        StartRootedCorrectedConcreteTargetClass
          (v := w) α M obs f)
    {bitBudget searchBudget : Nat}
    (hprofile :
      CorrectedConcreteCertifiedDescriptionProfileAtBudgets
        (obs := obs)
        (f := f)
        L bitBudget searchBudget) :
    startRootedTargetCertifiedCanonicalSearchComplexity
        (v := w) hα obs f hL <=
      searchBudget := by

  unfold
    startRootedTargetCertifiedCanonicalSearchComplexity

  exact
    (startRootedTarget_hasCertifiedCanonicalSearch
      (v := w) hα obs f hL).complexity_le_of_atBudget
      hprofile.canonicalSearch

end TargetCharacteristicRankProfile


section CharacteristicRankTargetStrata

variable {α : Type u}
variable {M : Type v}
variable [Fintype M]
variable [DecidableEq α]
variable [DecidableEq M]
variable [Monoid M]
variable (hα : Nonempty α)
variable (obs : α → M)
variable (f : Nat)

/-- Semantic start-rooted targets whose selected characteristic rank is at most
`rank`. -/
def StartRootedCorrectedConcreteTargetCharacteristicRankAtMostClass
    (rank : Nat) :
    Set (Set (Word α)) :=
  {L |
    ∃
      hL :
        L ∈
          StartRootedCorrectedConcreteTargetClass
            (v := w) α M obs f,
      startRootedTargetCharacteristicRank
          (v := w) hα obs f hL <=
        rank}

/-- The bounded characteristic-rank target strata are increasing. -/
theorem
    startRootedCorrectedConcreteTargetCharacteristicRankAtMostClass_mono
    {rank rank' : Nat}
    (hrank :
      rank <= rank') :
    StartRootedCorrectedConcreteTargetCharacteristicRankAtMostClass
        (v := w) hα obs f rank ⊆
      StartRootedCorrectedConcreteTargetCharacteristicRankAtMostClass
        (v := w) hα obs f rank' := by

  intro L hL

  rcases hL with
    ⟨hTarget, hbound⟩

  exact
    ⟨hTarget,
      hbound.trans hrank⟩

/-- Every target of characteristic rank at most `rank` lies in the certified
simultaneous description profile class at level `rank`. -/
theorem
    startRootedCharacteristicRankAtMostClass_subset_certifiedRankProfileClass
    (rank : Nat) :
    StartRootedCorrectedConcreteTargetCharacteristicRankAtMostClass
        (v := w) hα obs f rank ⊆
      CorrectedConcreteCertifiedRankProfileClass
        (α := α)
        (M := M)
        obs f rank := by

  intro L hL

  rcases hL with
    ⟨hTarget, hbound⟩

  exact
    startRootedTarget_mem_certifiedRankProfileClass_of_characteristicRank_le
      (v := w) hα obs f hTarget hbound

/-- Every semantic start-rooted target lies in some bounded
characteristic-rank stratum. -/
theorem
    startRootedTargetClass_subset_exists_characteristicRankAtMostClass :
    StartRootedCorrectedConcreteTargetClass
        (v := w) α M obs f ⊆
      {L : Set (Word α) |
        ∃ rank : Nat,
          L ∈
            StartRootedCorrectedConcreteTargetCharacteristicRankAtMostClass
              (v := w) hα obs f rank} := by

  intro L hL

  exact
    ⟨startRootedTargetCharacteristicRank
        (v := w) hα obs f hL,
      hL,
      Nat.le_refl _⟩

/-- Every semantic start-rooted target lies in some simultaneous certified rank
profile class. -/
theorem
    startRootedTargetClass_subset_exists_certifiedRankProfileClass :
    StartRootedCorrectedConcreteTargetClass
        (v := w) α M obs f ⊆
      {L : Set (Word α) |
        ∃ rank : Nat,
          L ∈
            CorrectedConcreteCertifiedRankProfileClass
              (α := α)
              (M := M)
              obs f rank} := by

  intro L hL

  exact
    ⟨startRootedTargetCharacteristicRank
        (v := w) hα obs f hL,
      startRootedTarget_mem_certifiedCharacteristicRankProfileClass
        (v := w) hα obs f hL⟩

end CharacteristicRankTargetStrata


section CertifiedDescriptionProfilePackages

variable {α : Type u}
variable {M : Type v}
variable [Fintype M]
variable [DecidableEq α]
variable [DecidableEq M]
variable [Monoid M]
variable (hα : Nonempty α)
variable (obs : α → M)
variable (f : Nat)

/-- Target-level simultaneous profile and separate-minimum upper-bound package. -/
theorem startRootedTargetCertifiedDescriptionProfile_package
    {L : Set (Word α)}
    (hL :
      L ∈
        StartRootedCorrectedConcreteTargetClass
          (v := w) α M obs f) :
    CorrectedConcreteCertifiedDescriptionProfileAtBudgets
        (obs := obs)
        (f := f)
        L
        (correctedConcreteCertifiedRankBitBudget
          (startRootedTargetCharacteristicRank
            (v := w) hα obs f hL)
          f)
        (correctedConcreteCertifiedRankSearchBudget
          (startRootedTargetCharacteristicRank
            (v := w) hα obs f hL)
          f) ∧
      (startRootedTargetCertifiedBitDescriptionComplexity
          (v := w) hα obs f hL <=
        correctedConcreteCertifiedRankBitBudget
          (startRootedTargetCharacteristicRank
            (v := w) hα obs f hL)
          f) ∧
      (startRootedTargetCertifiedCanonicalSearchComplexity
          (v := w) hα obs f hL <=
        correctedConcreteCertifiedRankSearchBudget
          (startRootedTargetCharacteristicRank
            (v := w) hα obs f hL)
          f) := by

  let hprofile :=
    startRootedTarget_certifiedProfileAtCharacteristicRank
      (v := w) hα obs f hL

  exact
    ⟨hprofile,
      startRootedTargetCertifiedBitDescriptionComplexity_le_of_profile
        (v := w) hα obs f hL hprofile,
      startRootedTargetCertifiedCanonicalSearchComplexity_le_of_profile
        (v := w) hα obs f hL hprofile⟩

/-- Final class-level identification and simultaneous certified-description
profile hierarchy package. -/
theorem
    correctedConcreteCertifiedWorkingGrammarLearner_identification_descriptionProfile_package :
    IdentifiesClassFromPositiveData
        (correctedConcreteCertifiedWorkingGrammarHypLanguage
          obs f)
        (correctedConcreteCertifiedWorkingGrammarLearner
          hα obs f)
        (StartRootedCorrectedConcreteTargetClass
          (v := w) α M obs f) ∧
      (∀ rank rank' : Nat,
        rank <= rank' →
        CorrectedConcreteCertifiedRankProfileClass
            (α := α)
            (M := M)
            obs f rank ⊆
          CorrectedConcreteCertifiedRankProfileClass
            (α := α)
            (M := M)
            obs f rank') ∧
      (∀ K : Finset (Word α),
        (correctedConcreteCertifiedWorkingGrammarLearner
            hα obs f K).output.grammar.StringLanguage ∈
          CorrectedConcreteCertifiedRankProfileClass
            (α := α)
            (M := M)
            obs f
            (sampleLengthBudget K)) ∧
      (∀
        L : Set (Word α),
        ∀ hL :
          L ∈
            StartRootedCorrectedConcreteTargetClass
              (v := w) α M obs f,
        L ∈
          CorrectedConcreteCertifiedRankProfileClass
            (α := α)
            (M := M)
            obs f
            (startRootedTargetCharacteristicRank
              (v := w) hα obs f hL)) ∧
      (∀ rank : Nat,
        StartRootedCorrectedConcreteTargetCharacteristicRankAtMostClass
            (v := w) hα obs f rank ⊆
          CorrectedConcreteCertifiedRankProfileClass
            (α := α)
            (M := M)
            obs f rank) ∧
      (StartRootedCorrectedConcreteTargetClass
          (v := w) α M obs f ⊆
        {L : Set (Word α) |
          ∃ rank : Nat,
            L ∈
              CorrectedConcreteCertifiedRankProfileClass
                (α := α)
                (M := M)
                obs f rank}) := by

  exact
    ⟨correctedConcreteCertifiedWorkingGrammarLearner_identifies_startRootedTargetClass
        (v := w) hα obs f,
      fun rank rank' hrank =>
        correctedConcreteCertifiedRankProfileClass_mono
          (obs := obs)
          (f := f)
          hrank,
      correctedConcreteCertifiedWorkingGrammarLearner_language_mem_ownRankProfileClass
        hα obs f,
      fun L hL =>
        startRootedTarget_mem_certifiedCharacteristicRankProfileClass
          (v := w) hα obs f hL,
      startRootedCharacteristicRankAtMostClass_subset_certifiedRankProfileClass
        (v := w) hα obs f,
      startRootedTargetClass_subset_exists_certifiedRankProfileClass
        (v := w) hα obs f⟩

end CertifiedDescriptionProfilePackages

end MCFG
