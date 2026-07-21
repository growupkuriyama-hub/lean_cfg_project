/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG2.ConcreteCanonicalLearnerWorkingGrammarCertifiedOutputLearner

/-!
# ConcreteCanonicalLearnerWorkingGrammarCertifiedOutputMindChanges.lean

The preceding file lifts the actual `WorkingMCFG` learner to a certified learner
whose output itself stores

* the actual compiled grammar;
* the complete tagged presentation;
* the checked logarithmic code;
* the decoder and re-encoder;
* the finite canonical search;
* the exact selector result; and
* all code-length and search-size proofs.

The semantic language of a certified output is definitionally the language of
the original actual grammar output.  This file transfers the complete
mind-change and minimum-characteristic-sample theory to the certified learner.

## Certified semantic hypotheses

For a positive text `T`, define

```lean
correctedConcreteCertifiedWorkingGrammarTextLanguage hα obs f T n
```

to be the semantic language stored in the certified output at prefix stage
`n`.

A certified semantic mind change occurs when two consecutive certified output
languages differ:

```lean
CorrectedConcreteCertifiedWorkingGrammarLanguageChangesAt.
```

We prove exact equality with the original grammar-valued semantic hypothesis
and exact equivalence of the two mind-change predicates.

## Certified mind-change count

The recursive certified count

```lean
correctedConcreteCertifiedWorkingGrammarMindChangeCount
```

is defined directly from the certified mind-change predicate.  It is not merely
an abbreviation.  We prove

```lean
correctedConcreteCertifiedWorkingGrammarMindChangeCount_eq_original.
```

Consequently

```text
certified mind-change count before N
  ≤
number of distinct observed words in T.prefixSample N.
```

Repeated text entries still cannot cause semantic mind changes.

## Characteristic samples

Because the original and certified learners have the same semantic language at
every finite sample, one finite set is characteristic for the original learner
if and only if it is characteristic for the certified learner.

Therefore the previously selected minimum-budget characteristic sample is also
characteristic for the certified learner.  Its original coverage stage is a
stabilization stage for certified output languages and certified mind-change
counts.

## Minimum-rank certified descriptions

Let `Smin` be the selected minimum-budget characteristic sample.  Its total word
length is at most

```lean
startRootedTargetCharacteristicRank hα obs f hL.
```

The certified output on `Smin` therefore has

```text
checked code length
  ≤ paperPowerBitBound(characteristicRank, f),
```

and its finite canonical search has size at most

```text
2 ^ (paperPowerBitBound(characteristicRank, f) + 1).
```

This gives one target-dependent finite exact certified grammar description at
the minimum characteristic-sample rank, independently of the order and
repetitions of any text.

The final packages combine

* positive-data identification;
* the finite mind-change bound;
* stabilization after minimum characteristic coverage;
* the minimum-rank checked code bound; and
* the minimum-rank finite canonical-search bound.

The certificate payload itself may change as the positive sample grows.
Only semantic language mind changes are counted here.

No target grammar is supplied to the learner.
No `sorry`, `admit`, or `axiom` is used.
-/

namespace MCFG

universe u v w


section CertifiedTextHypothesisLanguage

variable {α : Type u}
variable {M : Type v}
variable [Fintype M]
variable [DecidableEq α]
variable [DecidableEq M]
variable [Monoid M]

/-- Semantic language hypothesized by the certified learner at one text-prefix
stage. -/
def correctedConcreteCertifiedWorkingGrammarTextLanguage
    {L : Set (Word α)}
    (hα : Nonempty α)
    (obs : α → M)
    (f : Nat)
    (T : TextFor L)
    (n : Nat) :
    Set (Word α) :=
  correctedConcreteCertifiedWorkingGrammarHypLanguage
    obs f
    (correctedConcreteCertifiedWorkingGrammarLearner
      hα obs f
      (T.prefixSample n))

/-- Certified and original actual grammar-valued text hypotheses agree at every
stage. -/
@[simp] theorem
    correctedConcreteCertifiedWorkingGrammarTextLanguage_eq_original
    {L : Set (Word α)}
    (hα : Nonempty α)
    (obs : α → M)
    (f : Nat)
    (T : TextFor L)
    (n : Nat) :
    correctedConcreteCertifiedWorkingGrammarTextLanguage
        hα obs f T n =
      correctedConcreteWorkingGrammarTextLanguage
        hα obs f T n := by

  unfold
    correctedConcreteCertifiedWorkingGrammarTextLanguage
    correctedConcreteWorkingGrammarTextLanguage

  exact
    correctedConcreteCertifiedWorkingGrammarHypLanguage_eq_original
      hα obs f
      (T.prefixSample n)

/-- The certified text hypothesis is the language of the actual grammar stored
inside the certified output. -/
@[simp] theorem
    correctedConcreteCertifiedWorkingGrammarTextLanguage_eq_outputGrammar
    {L : Set (Word α)}
    (hα : Nonempty α)
    (obs : α → M)
    (f : Nat)
    (T : TextFor L)
    (n : Nat) :
    correctedConcreteCertifiedWorkingGrammarTextLanguage
        hα obs f T n =
      (correctedConcreteCertifiedWorkingGrammarLearner
        hα obs f
        (T.prefixSample n)).output.grammar.StringLanguage := by

  rfl

/-- A semantic language mind change between two consecutive certified learner
outputs. -/
def CorrectedConcreteCertifiedWorkingGrammarLanguageChangesAt
    {L : Set (Word α)}
    (hα : Nonempty α)
    (obs : α → M)
    (f : Nat)
    (T : TextFor L)
    (n : Nat) :
    Prop :=
  correctedConcreteCertifiedWorkingGrammarTextLanguage
      hα obs f T n ≠
    correctedConcreteCertifiedWorkingGrammarTextLanguage
      hα obs f T (n + 1)

/-- Certified and original semantic mind-change predicates are exactly
equivalent. -/
theorem
    correctedConcreteCertifiedWorkingGrammarLanguageChangesAt_iff_original
    {L : Set (Word α)}
    (hα : Nonempty α)
    (obs : α → M)
    (f : Nat)
    (T : TextFor L)
    (n : Nat) :
    CorrectedConcreteCertifiedWorkingGrammarLanguageChangesAt
        hα obs f T n ↔
      CorrectedConcreteWorkingGrammarLanguageChangesAt
        hα obs f T n := by

  unfold
    CorrectedConcreteCertifiedWorkingGrammarLanguageChangesAt
    CorrectedConcreteWorkingGrammarLanguageChangesAt

  rw [
    correctedConcreteCertifiedWorkingGrammarTextLanguage_eq_original,
    correctedConcreteCertifiedWorkingGrammarTextLanguage_eq_original
  ]

/-- Certified output languages form a monotone chain along every positive
text. -/
theorem correctedConcreteCertifiedWorkingGrammarTextLanguage_mono
    {L : Set (Word α)}
    (hα : Nonempty α)
    (obs : α → M)
    (f : Nat)
    (T : TextFor L)
    {m n : Nat}
    (hmn : m <= n) :
    correctedConcreteCertifiedWorkingGrammarTextLanguage
        hα obs f T m ⊆
      correctedConcreteCertifiedWorkingGrammarTextLanguage
        hα obs f T n := by

  rw [
    correctedConcreteCertifiedWorkingGrammarTextLanguage_eq_original,
    correctedConcreteCertifiedWorkingGrammarTextLanguage_eq_original
  ]

  exact
    correctedConcreteWorkingGrammarTextLanguage_mono
      hα obs f T hmn

/-- Equal prefix samples force equal certified semantic hypotheses. -/
theorem
    correctedConcreteCertifiedWorkingGrammarTextLanguage_eq_of_prefixSample_eq
    {L : Set (Word α)}
    (hα : Nonempty α)
    (obs : α → M)
    (f : Nat)
    (T : TextFor L)
    {m n : Nat}
    (hmn :
      T.prefixSample m =
        T.prefixSample n) :
    correctedConcreteCertifiedWorkingGrammarTextLanguage
        hα obs f T m =
      correctedConcreteCertifiedWorkingGrammarTextLanguage
        hα obs f T n := by

  unfold
    correctedConcreteCertifiedWorkingGrammarTextLanguage

  rw [hmn]

/-- A certified semantic mind change requires a finite prefix-sample change. -/
theorem
    correctedConcreteCertifiedWorkingGrammarLanguageChangesAt_implies_prefixSampleChangesAt
    {L : Set (Word α)}
    (hα : Nonempty α)
    (obs : α → M)
    (f : Nat)
    (T : TextFor L)
    {n : Nat}
    (hchange :
      CorrectedConcreteCertifiedWorkingGrammarLanguageChangesAt
        hα obs f T n) :
    TextPrefixSampleChangesAt T n := by

  exact
    correctedConcreteWorkingGrammarLanguageChangesAt_implies_prefixSampleChangesAt
      hα obs f T
      ((correctedConcreteCertifiedWorkingGrammarLanguageChangesAt_iff_original
        hα obs f T n).mp
        hchange)

/-- Every certified semantic mind change strictly increases the observed
finite-sample cardinality. -/
theorem
    correctedConcreteCertifiedWorkingGrammarLanguageChangesAt_implies_prefixSample_card_lt
    {L : Set (Word α)}
    (hα : Nonempty α)
    (obs : α → M)
    (f : Nat)
    (T : TextFor L)
    {n : Nat}
    (hchange :
      CorrectedConcreteCertifiedWorkingGrammarLanguageChangesAt
        hα obs f T n) :
    (T.prefixSample n).card <
      (T.prefixSample (n + 1)).card := by

  exact
    correctedConcreteWorkingGrammarLanguageChangesAt_implies_prefixSample_card_lt
      hα obs f T
      ((correctedConcreteCertifiedWorkingGrammarLanguageChangesAt_iff_original
        hα obs f T n).mp
        hchange)

end CertifiedTextHypothesisLanguage


section CertifiedRecursiveMindChangeCount

variable {α : Type u}
variable {M : Type v}
variable [Fintype M]
variable [DecidableEq α]
variable [DecidableEq M]
variable [Monoid M]

/-- Number of certified semantic output-language changes before stage `N`. -/
noncomputable def correctedConcreteCertifiedWorkingGrammarMindChangeCount
    {L : Set (Word α)}
    (hα : Nonempty α)
    (obs : α → M)
    (f : Nat)
    (T : TextFor L) :
    Nat → Nat

  | 0 =>
      0

  | n + 1 =>
      correctedConcreteCertifiedWorkingGrammarMindChangeCount
          hα obs f T n +
        if
          CorrectedConcreteCertifiedWorkingGrammarLanguageChangesAt
            hα obs f T n
        then 1
        else 0

@[simp] theorem
    correctedConcreteCertifiedWorkingGrammarMindChangeCount_zero
    {L : Set (Word α)}
    (hα : Nonempty α)
    (obs : α → M)
    (f : Nat)
    (T : TextFor L) :
    correctedConcreteCertifiedWorkingGrammarMindChangeCount
        hα obs f T 0 =
      0 :=
  rfl

@[simp] theorem
    correctedConcreteCertifiedWorkingGrammarMindChangeCount_succ
    {L : Set (Word α)}
    (hα : Nonempty α)
    (obs : α → M)
    (f : Nat)
    (T : TextFor L)
    (n : Nat) :
    correctedConcreteCertifiedWorkingGrammarMindChangeCount
        hα obs f T (n + 1) =
      correctedConcreteCertifiedWorkingGrammarMindChangeCount
          hα obs f T n +
        if
          CorrectedConcreteCertifiedWorkingGrammarLanguageChangesAt
            hα obs f T n
        then 1
        else 0 :=
  rfl

/-- The independently defined certified mind-change count is exactly the
original grammar-valued semantic mind-change count. -/
theorem
    correctedConcreteCertifiedWorkingGrammarMindChangeCount_eq_original
    {L : Set (Word α)}
    (hα : Nonempty α)
    (obs : α → M)
    (f : Nat)
    (T : TextFor L) :
    ∀ N : Nat,
      correctedConcreteCertifiedWorkingGrammarMindChangeCount
          hα obs f T N =
        correctedConcreteWorkingGrammarMindChangeCount
          hα obs f T N

  | 0 => by
      rfl

  | N + 1 => by
      rw [
        correctedConcreteCertifiedWorkingGrammarMindChangeCount_succ,
        correctedConcreteWorkingGrammarMindChangeCount_succ,
        correctedConcreteCertifiedWorkingGrammarMindChangeCount_eq_original
          hα obs f T N
      ]

      by_cases hcertified :
          CorrectedConcreteCertifiedWorkingGrammarLanguageChangesAt
            hα obs f T N

      · have horiginal :
            CorrectedConcreteWorkingGrammarLanguageChangesAt
              hα obs f T N :=
          (correctedConcreteCertifiedWorkingGrammarLanguageChangesAt_iff_original
            hα obs f T N).mp
            hcertified

        simp [
          hcertified,
          horiginal
        ]

      · have horiginal :
            ¬
              CorrectedConcreteWorkingGrammarLanguageChangesAt
                hα obs f T N := by

          intro horiginal

          exact
            hcertified
              ((correctedConcreteCertifiedWorkingGrammarLanguageChangesAt_iff_original
                hα obs f T N).mpr
                horiginal)

        simp [
          hcertified,
          horiginal
        ]

/-- Certified semantic mind-change counts are monotone in the stage. -/
theorem
    correctedConcreteCertifiedWorkingGrammarMindChangeCount_mono
    {L : Set (Word α)}
    (hα : Nonempty α)
    (obs : α → M)
    (f : Nat)
    (T : TextFor L)
    {m n : Nat}
    (hmn : m <= n) :
    correctedConcreteCertifiedWorkingGrammarMindChangeCount
        hα obs f T m <=
      correctedConcreteCertifiedWorkingGrammarMindChangeCount
        hα obs f T n := by

  rw [
    correctedConcreteCertifiedWorkingGrammarMindChangeCount_eq_original,
    correctedConcreteCertifiedWorkingGrammarMindChangeCount_eq_original
  ]

  exact
    correctedConcreteWorkingGrammarMindChangeCount_mono
      hα obs f T hmn

/-- The certified semantic mind-change count before `N` is bounded by the
number of distinct observed words in the prefix sample at `N`. -/
theorem
    correctedConcreteCertifiedWorkingGrammarMindChangeCount_le_prefixSample_card
    {L : Set (Word α)}
    (hα : Nonempty α)
    (obs : α → M)
    (f : Nat)
    (T : TextFor L)
    (N : Nat) :
    correctedConcreteCertifiedWorkingGrammarMindChangeCount
        hα obs f T N <=
      (T.prefixSample N).card := by

  rw [
    correctedConcreteCertifiedWorkingGrammarMindChangeCount_eq_original
  ]

  exact
    correctedConcreteWorkingGrammarMindChangeCount_le_prefixSample_card
      hα obs f T N

end CertifiedRecursiveMindChangeCount


section CertifiedCharacteristicSampleTransfer

variable {α : Type u}
variable {M : Type v}
variable [Fintype M]
variable [DecidableEq α]
variable [DecidableEq M]
variable [Monoid M]

/-- A finite set is characteristic for the certified learner exactly when it is
characteristic for the original actual grammar-valued learner. -/
theorem
    characteristicSample_certifiedWorkingGrammar_iff_original
    (hα : Nonempty α)
    (obs : α → M)
    (f : Nat)
    (S : Finset (Word α))
    (L : Set (Word α)) :
    CharacteristicSample
        (correctedConcreteCertifiedWorkingGrammarHypLanguage
          obs f)
        (correctedConcreteCertifiedWorkingGrammarLearner
          hα obs f)
        S L ↔
      CharacteristicSample
        (correctedConcreteWorkingGrammarHypLanguage
          obs f)
        (correctedConcreteWorkingGrammarLearner
          hα obs f)
        S L := by

  constructor

  · intro hcertified

    refine
      ⟨hcertified.1,
        ?_⟩

    intro K hSK hKL

    have hcorrect :=
      hcertified.2 K hSK hKL

    rw [
      correctedConcreteCertifiedWorkingGrammarHypLanguage_eq_original
        hα obs f K
    ] at hcorrect

    exact hcorrect

  · intro horiginal

    refine
      ⟨horiginal.1,
        ?_⟩

    intro K hSK hKL

    have hcorrect :=
      horiginal.2 K hSK hKL

    rw [
      correctedConcreteCertifiedWorkingGrammarHypLanguage_eq_original
        hα obs f K
    ]

    exact hcorrect

/-- Original characteristic samples are characteristic for the certified
learner. -/
theorem
    characteristicSample_certifiedWorkingGrammar_of_original
    (hα : Nonempty α)
    (obs : α → M)
    (f : Nat)
    (S : Finset (Word α))
    (L : Set (Word α))
    (hS :
      CharacteristicSample
        (correctedConcreteWorkingGrammarHypLanguage
          obs f)
        (correctedConcreteWorkingGrammarLearner
          hα obs f)
        S L) :
    CharacteristicSample
      (correctedConcreteCertifiedWorkingGrammarHypLanguage
        obs f)
      (correctedConcreteCertifiedWorkingGrammarLearner
        hα obs f)
      S L := by

  exact
    (characteristicSample_certifiedWorkingGrammar_iff_original
      hα obs f S L).mpr
      hS

/-- Certified characteristic samples are characteristic for the original
learner. -/
theorem
    characteristicSample_original_of_certifiedWorkingGrammar
    (hα : Nonempty α)
    (obs : α → M)
    (f : Nat)
    (S : Finset (Word α))
    (L : Set (Word α))
    (hS :
      CharacteristicSample
        (correctedConcreteCertifiedWorkingGrammarHypLanguage
          obs f)
        (correctedConcreteCertifiedWorkingGrammarLearner
          hα obs f)
        S L) :
    CharacteristicSample
      (correctedConcreteWorkingGrammarHypLanguage
        obs f)
      (correctedConcreteWorkingGrammarLearner
        hα obs f)
      S L := by

  exact
    (characteristicSample_certifiedWorkingGrammar_iff_original
      hα obs f S L).mp
      hS

end CertifiedCharacteristicSampleTransfer


section MinimumCharacteristicCertifiedStabilization

variable {α : Type u}
variable {M : Type v}
variable [Fintype M]
variable [DecidableEq α]
variable [DecidableEq M]
variable [Monoid M]
variable (hα : Nonempty α)
variable (obs : α → M)
variable (f : Nat)

/-- The selected minimum-budget original characteristic sample is also
characteristic for the certified learner. -/
theorem
    startRootedTargetMinimalCharacteristicSample_certified_characteristic
    {L : Set (Word α)}
    (hL :
      L ∈
        StartRootedCorrectedConcreteTargetClass
          (v := w) α M obs f) :
    CharacteristicSample
      (correctedConcreteCertifiedWorkingGrammarHypLanguage
        obs f)
      (correctedConcreteCertifiedWorkingGrammarLearner
        hα obs f)
      (startRootedTargetMinimalCharacteristicSample
        (v := w) hα obs f hL)
      L := by

  exact
    characteristicSample_certifiedWorkingGrammar_of_original
      hα obs f
      (startRootedTargetMinimalCharacteristicSample
        (v := w) hα obs f hL)
      L
      (startRootedTargetMinimalCharacteristicSample_characteristic
        (v := w) hα obs f hL)

/-- Every certified output after minimum-characteristic-sample coverage has
exactly the target language. -/
theorem
    correctedConcreteCertifiedWorkingGrammar_correct_after_minimalCharacteristicCoverage
    {L : Set (Word α)}
    (hL :
      L ∈
        StartRootedCorrectedConcreteTargetClass
          (v := w) α M obs f)
    (T : TextFor L)
    {n : Nat}
    (hn :
      startRootedTargetMinimalCharacteristicCoverageStage
          (v := w) hα obs f hL T <=
        n) :
    correctedConcreteCertifiedWorkingGrammarTextLanguage
        hα obs f T n =
      L := by

  rw [
    correctedConcreteCertifiedWorkingGrammarTextLanguage_eq_original
  ]

  exact
    correctedConcreteWorkingGrammar_correct_after_minimalCharacteristicCoverage
      (v := w) hα obs f hL T hn

/-- No certified semantic language mind change occurs after
minimum-characteristic-sample coverage. -/
theorem
    correctedConcreteCertifiedWorkingGrammar_no_mindChanges_after_minimalCharacteristicCoverage
    {L : Set (Word α)}
    (hL :
      L ∈
        StartRootedCorrectedConcreteTargetClass
          (v := w) α M obs f)
    (T : TextFor L)
    {n : Nat}
    (hn :
      startRootedTargetMinimalCharacteristicCoverageStage
          (v := w) hα obs f hL T <=
        n) :
    ¬
      CorrectedConcreteCertifiedWorkingGrammarLanguageChangesAt
        hα obs f T n := by

  intro hchange

  have horiginal :
      CorrectedConcreteWorkingGrammarLanguageChangesAt
        hα obs f T n :=
    (correctedConcreteCertifiedWorkingGrammarLanguageChangesAt_iff_original
      hα obs f T n).mp
      hchange

  exact
    correctedConcreteWorkingGrammar_no_mindChanges_after_minimalCharacteristicCoverage
      (v := w) hα obs f hL T hn
      horiginal

/-- The certified cumulative semantic mind-change count is constant after
minimum-characteristic-sample coverage. -/
theorem
    correctedConcreteCertifiedWorkingGrammarMindChangeCount_constant_after_minimalCharacteristicCoverage
    {L : Set (Word α)}
    (hL :
      L ∈
        StartRootedCorrectedConcreteTargetClass
          (v := w) α M obs f)
    (T : TextFor L)
    {N : Nat}
    (hN :
      startRootedTargetMinimalCharacteristicCoverageStage
          (v := w) hα obs f hL T <=
        N) :
    correctedConcreteCertifiedWorkingGrammarMindChangeCount
        hα obs f T N =
      correctedConcreteCertifiedWorkingGrammarMindChangeCount
        hα obs f T
        (startRootedTargetMinimalCharacteristicCoverageStage
          (v := w) hα obs f hL T) := by

  rw [
    correctedConcreteCertifiedWorkingGrammarMindChangeCount_eq_original,
    correctedConcreteCertifiedWorkingGrammarMindChangeCount_eq_original
  ]

  exact
    correctedConcreteWorkingGrammarMindChangeCount_constant_after_minimalCharacteristicCoverage
      (v := w) hα obs f hL T hN

end MinimumCharacteristicCertifiedStabilization


section MinimumCharacteristicCertifiedDescriptionBounds

variable {α : Type u}
variable {M : Type v}
variable [Fintype M]
variable [DecidableEq α]
variable [DecidableEq M]
variable [Monoid M]
variable (hα : Nonempty α)
variable (obs : α → M)
variable (f : Nat)

/-- Certified output on the selected minimum-budget characteristic sample. -/
noncomputable def
    startRootedTargetMinimalCharacteristicCertifiedOutput
    {L : Set (Word α)}
    (hL :
      L ∈
        StartRootedCorrectedConcreteTargetClass
          (v := w) α M obs f) :
    CorrectedConcreteCertifiedWorkingGrammarHypothesis
      α M obs f :=
  correctedConcreteCertifiedWorkingGrammarLearner
    hα obs f
    (startRootedTargetMinimalCharacteristicSample
      (v := w) hα obs f hL)

/-- The minimum-characteristic certified output has exactly the target
language. -/
theorem
    startRootedTargetMinimalCharacteristicCertifiedOutput_language_eq
    {L : Set (Word α)}
    (hL :
      L ∈
        StartRootedCorrectedConcreteTargetClass
          (v := w) α M obs f) :
    (startRootedTargetMinimalCharacteristicCertifiedOutput
        (v := w) hα obs f hL).output.grammar.StringLanguage =
      L := by

  let S :=
    startRootedTargetMinimalCharacteristicSample
      (v := w) hα obs f hL

  have hcharacteristic :
      CharacteristicSample
        (correctedConcreteWorkingGrammarHypLanguage
          obs f)
        (correctedConcreteWorkingGrammarLearner
          hα obs f)
        S L :=
    startRootedTargetMinimalCharacteristicSample_characteristic
      (v := w) hα obs f hL

  have hpositive :
      (S : Set (Word α)) ⊆ L :=
    hcharacteristic.1

  have hcorrect :
      correctedConcreteWorkingGrammarHypLanguage
          obs f
          (correctedConcreteWorkingGrammarLearner
            hα obs f S) =
        L :=
    hcharacteristic.2
      S
      (by
        intro word hword
        exact hword)
      hpositive

  simpa [
    startRootedTargetMinimalCharacteristicCertifiedOutput,
    S
  ] using hcorrect

/-- The selected minimum-characteristic certified code length is bounded at the
numerical characteristic rank itself. -/
theorem
    startRootedTargetMinimalCharacteristicCertifiedOutput_bitLength_le_rank
    {L : Set (Word α)}
    (hL :
      L ∈
        StartRootedCorrectedConcreteTargetClass
          (v := w) α M obs f) :
    (startRootedTargetMinimalCharacteristicCertifiedOutput
        (v := w) hα obs f hL).bits.length <=
      correctedConcreteCompiledGrammarPaperPowerBitBound
        (startRootedTargetCharacteristicRank
          (v := w) hα obs f hL)
        f := by

  let S :=
    startRootedTargetMinimalCharacteristicSample
      (v := w) hα obs f hL

  have hlength :
      (correctedConcreteCertifiedWorkingGrammarLearner
          hα obs f S).bits.length <=
        correctedConcreteCompiledGrammarPaperPowerBitBound
          (sampleLengthBudget S)
          f :=
    correctedConcreteCertifiedWorkingGrammarLearner_bitLength_le
      hα obs f S

  have hrank :
      sampleLengthBudget S <=
        startRootedTargetCharacteristicRank
          (v := w) hα obs f hL := by

    simpa [S] using
      startRootedTargetMinimalCharacteristicSample_length_le_rank
        (v := w) hα obs f hL

  exact
    hlength.trans
      (correctedConcreteCompiledGrammarPaperPowerBitBound_mono_sampleLength
        hrank)

/-- The selected minimum-characteristic finite canonical search is bounded at
the numerical characteristic rank itself. -/
theorem
    startRootedTargetMinimalCharacteristicCertifiedOutput_searchLength_le_rank
    {L : Set (Word α)}
    (hL :
      L ∈
        StartRootedCorrectedConcreteTargetClass
          (v := w) α M obs f) :
    (startRootedTargetMinimalCharacteristicCertifiedOutput
        (v := w) hα obs f hL).canonicalSearch.length <=
      2 ^
        (correctedConcreteCompiledGrammarPaperPowerBitBound
            (startRootedTargetCharacteristicRank
              (v := w) hα obs f hL)
            f +
          1) := by

  let S :=
    startRootedTargetMinimalCharacteristicSample
      (v := w) hα obs f hL

  have hsearch :
      (correctedConcreteCertifiedWorkingGrammarLearner
          hα obs f S).canonicalSearch.length <=
        2 ^
          (correctedConcreteCompiledGrammarPaperPowerBitBound
              (sampleLengthBudget S)
              f +
            1) :=
    correctedConcreteCertifiedWorkingGrammarLearner_searchLength_le
      hα obs f S

  have hrank :
      sampleLengthBudget S <=
        startRootedTargetCharacteristicRank
          (v := w) hα obs f hL := by

    simpa [S] using
      startRootedTargetMinimalCharacteristicSample_length_le_rank
        (v := w) hα obs f hL

  have hbudget :
      correctedConcreteCompiledGrammarPaperPowerBitBound
            (sampleLengthBudget S)
            f +
          1 <=
        correctedConcreteCompiledGrammarPaperPowerBitBound
            (startRootedTargetCharacteristicRank
              (v := w) hα obs f hL)
            f +
          1 :=
    Nat.add_le_add_right
      (correctedConcreteCompiledGrammarPaperPowerBitBound_mono_sampleLength
        hrank)
      1

  have hpow :
      2 ^
          (correctedConcreteCompiledGrammarPaperPowerBitBound
              (sampleLengthBudget S)
              f +
            1) <=
        2 ^
          (correctedConcreteCompiledGrammarPaperPowerBitBound
              (startRootedTargetCharacteristicRank
                (v := w) hα obs f hL)
              f +
            1) :=
    Nat.pow_le_pow_of_le
      (by omega)
      hbudget

  exact
    hsearch.trans
      hpow

/-- The selected minimum-characteristic output remains a complete checked
decoder/re-encoder fixed point. -/
theorem
    startRootedTargetMinimalCharacteristicCertifiedOutput_checked
    {L : Set (Word α)}
    (hL :
      L ∈
        StartRootedCorrectedConcreteTargetClass
          (v := w) α M obs f) :
    (startRootedTargetMinimalCharacteristicCertifiedOutput
        (v := w) hα obs f hL).decode
        (startRootedTargetMinimalCharacteristicCertifiedOutput
          (v := w) hα obs f hL).bits =
      some
        (startRootedTargetMinimalCharacteristicCertifiedOutput
          (v := w) hα obs f hL).presentation ∧
      (startRootedTargetMinimalCharacteristicCertifiedOutput
          (v := w) hα obs f hL).reencode
          (startRootedTargetMinimalCharacteristicCertifiedOutput
            (v := w) hα obs f hL).presentation =
        (startRootedTargetMinimalCharacteristicCertifiedOutput
          (v := w) hα obs f hL).bits ∧
      ((startRootedTargetMinimalCharacteristicCertifiedOutput
            (v := w) hα obs f hL).bits,
        (startRootedTargetMinimalCharacteristicCertifiedOutput
            (v := w) hα obs f hL).presentation) ∈
          (startRootedTargetMinimalCharacteristicCertifiedOutput
            (v := w) hα obs f hL).canonicalSearch := by

  let C :=
    startRootedTargetMinimalCharacteristicCertifiedOutput
      (v := w) hα obs f hL

  exact
    ⟨C.decode_bits,
      C.reencode_presentation,
      C.pair_mem_search⟩

/-- Compact minimum-characteristic-rank certified description package. -/
theorem
    startRootedTargetMinimalCharacteristicCertifiedOutput_package
    {L : Set (Word α)}
    (hL :
      L ∈
        StartRootedCorrectedConcreteTargetClass
          (v := w) α M obs f) :
    (startRootedTargetMinimalCharacteristicCertifiedOutput
        (v := w) hα obs f hL).output.grammar.StringLanguage =
      L ∧
      (startRootedTargetMinimalCharacteristicCertifiedOutput
          (v := w) hα obs f hL).bits.length <=
        correctedConcreteCompiledGrammarPaperPowerBitBound
          (startRootedTargetCharacteristicRank
            (v := w) hα obs f hL)
          f ∧
      (startRootedTargetMinimalCharacteristicCertifiedOutput
          (v := w) hα obs f hL).canonicalSearch.length <=
        2 ^
          (correctedConcreteCompiledGrammarPaperPowerBitBound
              (startRootedTargetCharacteristicRank
                (v := w) hα obs f hL)
              f +
            1) ∧
      (startRootedTargetMinimalCharacteristicCertifiedOutput
          (v := w) hα obs f hL).decode
          (startRootedTargetMinimalCharacteristicCertifiedOutput
            (v := w) hα obs f hL).bits =
        some
          (startRootedTargetMinimalCharacteristicCertifiedOutput
            (v := w) hα obs f hL).presentation ∧
      (startRootedTargetMinimalCharacteristicCertifiedOutput
          (v := w) hα obs f hL).reencode
          (startRootedTargetMinimalCharacteristicCertifiedOutput
            (v := w) hα obs f hL).presentation =
        (startRootedTargetMinimalCharacteristicCertifiedOutput
          (v := w) hα obs f hL).bits := by

  rcases
      startRootedTargetMinimalCharacteristicCertifiedOutput_checked
        (v := w) hα obs f hL with
    ⟨hdecode, hreencode, hpair⟩

  exact
    ⟨startRootedTargetMinimalCharacteristicCertifiedOutput_language_eq
        (v := w) hα obs f hL,
      startRootedTargetMinimalCharacteristicCertifiedOutput_bitLength_le_rank
        (v := w) hα obs f hL,
      startRootedTargetMinimalCharacteristicCertifiedOutput_searchLength_le_rank
        (v := w) hα obs f hL,
      hdecode,
      hreencode⟩

end MinimumCharacteristicCertifiedDescriptionBounds


section CertifiedMindChangePackages

variable {α : Type u}
variable {M : Type v}
variable [Fintype M]
variable [DecidableEq α]
variable [DecidableEq M]
variable [Monoid M]
variable (hα : Nonempty α)
variable (obs : α → M)
variable (f : Nat)

/-- Finite semantic mind-change, stabilization, and minimum-rank certified
description package for one target text. -/
theorem
    correctedConcreteCertifiedWorkingGrammarLearner_mindChange_stabilization_package
    {L : Set (Word α)}
    (hL :
      L ∈
        StartRootedCorrectedConcreteTargetClass
          (v := w) α M obs f)
    (T : TextFor L) :
    (∀ N : Nat,
      correctedConcreteCertifiedWorkingGrammarMindChangeCount
          hα obs f T N <=
        (T.prefixSample N).card) ∧
      (∀ n : Nat,
        startRootedTargetMinimalCharacteristicCoverageStage
            (v := w) hα obs f hL T <=
          n →
        correctedConcreteCertifiedWorkingGrammarTextLanguage
            hα obs f T n =
          L) ∧
      (∀ n : Nat,
        startRootedTargetMinimalCharacteristicCoverageStage
            (v := w) hα obs f hL T <=
          n →
        ¬
          CorrectedConcreteCertifiedWorkingGrammarLanguageChangesAt
            hα obs f T n) ∧
      (∀ N : Nat,
        startRootedTargetMinimalCharacteristicCoverageStage
            (v := w) hα obs f hL T <=
          N →
        correctedConcreteCertifiedWorkingGrammarMindChangeCount
            hα obs f T N =
          correctedConcreteCertifiedWorkingGrammarMindChangeCount
            hα obs f T
            (startRootedTargetMinimalCharacteristicCoverageStage
              (v := w) hα obs f hL T)) ∧
      ((startRootedTargetMinimalCharacteristicCertifiedOutput
          (v := w) hα obs f hL).bits.length <=
        correctedConcreteCompiledGrammarPaperPowerBitBound
          (startRootedTargetCharacteristicRank
            (v := w) hα obs f hL)
          f) ∧
      ((startRootedTargetMinimalCharacteristicCertifiedOutput
          (v := w) hα obs f hL).canonicalSearch.length <=
        2 ^
          (correctedConcreteCompiledGrammarPaperPowerBitBound
              (startRootedTargetCharacteristicRank
                (v := w) hα obs f hL)
              f +
            1)) := by

  exact
    ⟨correctedConcreteCertifiedWorkingGrammarMindChangeCount_le_prefixSample_card
        hα obs f T,
      fun n hn =>
        correctedConcreteCertifiedWorkingGrammar_correct_after_minimalCharacteristicCoverage
          (v := w) hα obs f hL T hn,
      fun n hn =>
        correctedConcreteCertifiedWorkingGrammar_no_mindChanges_after_minimalCharacteristicCoverage
          (v := w) hα obs f hL T hn,
      fun N hN =>
        correctedConcreteCertifiedWorkingGrammarMindChangeCount_constant_after_minimalCharacteristicCoverage
          (v := w) hα obs f hL T hN,
      startRootedTargetMinimalCharacteristicCertifiedOutput_bitLength_le_rank
        (v := w) hα obs f hL,
      startRootedTargetMinimalCharacteristicCertifiedOutput_searchLength_le_rank
        (v := w) hα obs f hL⟩

/-- Final class-level certified-output theorem combining identification,
semantic mind-change control, minimum-characteristic stabilization, and one
minimum-rank checked finite grammar description for every target. -/
theorem
    correctedConcreteCertifiedWorkingGrammarLearner_identification_mindChange_package :
    IdentifiesClassFromPositiveData
        (correctedConcreteCertifiedWorkingGrammarHypLanguage
          obs f)
        (correctedConcreteCertifiedWorkingGrammarLearner
          hα obs f)
        (StartRootedCorrectedConcreteTargetClass
          (v := w) α M obs f) ∧
      (∀
        L : Set (Word α),
        L ∈
            StartRootedCorrectedConcreteTargetClass
              (v := w) α M obs f →
        ∀ T : TextFor L,
          ∀ N : Nat,
            correctedConcreteCertifiedWorkingGrammarMindChangeCount
                hα obs f T N <=
              (T.prefixSample N).card) ∧
      (∀
        L : Set (Word α),
        ∀ hL :
          L ∈
            StartRootedCorrectedConcreteTargetClass
              (v := w) α M obs f,
        ∀ T : TextFor L,
          ∃ n0 : Nat,
            (∀ n : Nat, n0 <= n →
              correctedConcreteCertifiedWorkingGrammarTextLanguage
                  hα obs f T n =
                L) ∧
            (∀ n : Nat, n0 <= n →
              ¬
                CorrectedConcreteCertifiedWorkingGrammarLanguageChangesAt
                  hα obs f T n) ∧
            (∀ N : Nat, n0 <= N →
              correctedConcreteCertifiedWorkingGrammarMindChangeCount
                  hα obs f T N =
                correctedConcreteCertifiedWorkingGrammarMindChangeCount
                  hα obs f T n0)) ∧
      (∀
        L : Set (Word α),
        ∀ hL :
          L ∈
            StartRootedCorrectedConcreteTargetClass
              (v := w) α M obs f,
        (startRootedTargetMinimalCharacteristicCertifiedOutput
            (v := w) hα obs f hL).output.grammar.StringLanguage =
          L ∧
        (startRootedTargetMinimalCharacteristicCertifiedOutput
            (v := w) hα obs f hL).bits.length <=
          correctedConcreteCompiledGrammarPaperPowerBitBound
            (startRootedTargetCharacteristicRank
              (v := w) hα obs f hL)
            f ∧
        (startRootedTargetMinimalCharacteristicCertifiedOutput
            (v := w) hα obs f hL).canonicalSearch.length <=
          2 ^
            (correctedConcreteCompiledGrammarPaperPowerBitBound
                (startRootedTargetCharacteristicRank
                  (v := w) hα obs f hL)
                f +
              1)) := by

  refine
    ⟨correctedConcreteCertifiedWorkingGrammarLearner_identifies_startRootedTargetClass
        (v := w) hα obs f,
      ?_,
      ?_,
      ?_⟩

  · intro L hL T N

    exact
      correctedConcreteCertifiedWorkingGrammarMindChangeCount_le_prefixSample_card
        hα obs f T N

  · intro L hL T

    refine
      ⟨startRootedTargetMinimalCharacteristicCoverageStage
          (v := w) hα obs f hL T,
        ?_,
        ?_,
        ?_⟩

    · intro n hn

      exact
        correctedConcreteCertifiedWorkingGrammar_correct_after_minimalCharacteristicCoverage
          (v := w) hα obs f hL T hn

    · intro n hn

      exact
        correctedConcreteCertifiedWorkingGrammar_no_mindChanges_after_minimalCharacteristicCoverage
          (v := w) hα obs f hL T hn

    · intro N hN

      exact
        correctedConcreteCertifiedWorkingGrammarMindChangeCount_constant_after_minimalCharacteristicCoverage
          (v := w) hα obs f hL T hN

  · intro L hL

    exact
      ⟨startRootedTargetMinimalCharacteristicCertifiedOutput_language_eq
          (v := w) hα obs f hL,
        startRootedTargetMinimalCharacteristicCertifiedOutput_bitLength_le_rank
          (v := w) hα obs f hL,
        startRootedTargetMinimalCharacteristicCertifiedOutput_searchLength_le_rank
          (v := w) hα obs f hL⟩

end CertifiedMindChangePackages

end MCFG
