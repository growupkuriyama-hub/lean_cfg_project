/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG.ConcreteCanonicalLearnerWorkingGrammarCharacteristicRank

/-!
# ConcreteCanonicalLearnerWorkingGrammarMindChanges.lean

This file connects the actual grammar-valued learner to stabilization and
mind-change complexity along positive texts.

For a text `T`, define the semantic hypothesis at stage `n` by

```lean
correctedConcreteWorkingGrammarTextLanguage hα obs f T n.
```

A language mind change occurs at stage `n` when the languages at stages `n`
and `n + 1` differ.

The learner is set-driven and language-monotone.  Therefore:

* a language change requires the finite prefix sample to change;
* since prefix samples are nested, every language change strictly increases
  the prefix-sample cardinality.

The recursive count

```lean
correctedConcreteWorkingGrammarMindChangeCount hα obs f T N
```

counts semantic language changes before stage `N`.  It satisfies

```lean
mindChangeCount N ≤ (T.prefixSample N).card.
```

Thus repeated text entries cannot cause semantic mind changes.

For every finite characteristic sample, a finite coverage stage can be
selected.  After that stage every output language equals the target, so no
further language mind changes occur.

Finally, for each semantic start-rooted target, this file selects a
characteristic sample attaining the minimum characteristic-sample budget from
the preceding rank file.  The selected minimum sample has total word length at
most the characteristic rank, and its coverage stage is a semantic
stabilization stage for the actual `WorkingMCFG` outputs.

Main results:

```lean
correctedConcreteWorkingGrammarLanguageChangesAt_implies_prefixSample_card_lt
correctedConcreteWorkingGrammarMindChangeCount_le_prefixSample_card
correctedConcreteWorkingGrammar_not_languageChangesAt_after_characteristicCoverage
startRootedTargetMinimalCharacteristicSample_characteristic
correctedConcreteWorkingGrammar_correct_after_minimalCharacteristicCoverage
correctedConcreteWorkingGrammar_no_mindChanges_after_minimalCharacteristicCoverage
correctedConcreteWorkingGrammarLearner_mindChange_stabilization_package.
```

The coverage stage depends on the order and repetitions of the text.  This
file does not claim that the numerical stage is bounded by the total length of
the characteristic sample.

No target grammar is supplied to the learner.
No `sorry`, `admit`, or `axiom` is used.
-/

namespace MCFG

universe u v w

section TextHypothesisLanguage

variable {α : Type u}
variable {M : Type v}
variable [Monoid M]
variable [DecidableEq α]

/-- Semantic language hypothesized by the actual grammar-valued learner at one
text-prefix stage. -/
def correctedConcreteWorkingGrammarTextLanguage
    {L : Set (Word α)}
    (hα : Nonempty α)
    (obs : α → M)
    (f : Nat)
    (T : TextFor L)
    (n : Nat) :
    Set (Word α) :=
  (correctedConcreteWorkingGrammarLearner
    hα obs f
    (T.prefixSample n)).grammar.StringLanguage

/-- A semantic language mind change between two consecutive text prefixes. -/
def CorrectedConcreteWorkingGrammarLanguageChangesAt
    {L : Set (Word α)}
    (hα : Nonempty α)
    (obs : α → M)
    (f : Nat)
    (T : TextFor L)
    (n : Nat) :
    Prop :=
  correctedConcreteWorkingGrammarTextLanguage
      hα obs f T n ≠
    correctedConcreteWorkingGrammarTextLanguage
      hα obs f T (n + 1)

/-- A finite prefix sample changes between two consecutive stages. -/
def TextPrefixSampleChangesAt
    {L : Set (Word α)}
    (T : TextFor L)
    (n : Nat) :
    Prop :=
  T.prefixSample n ≠
    T.prefixSample (n + 1)

/-- The actual grammar-output languages form a monotone chain along a text. -/
theorem correctedConcreteWorkingGrammarTextLanguage_mono
    {L : Set (Word α)}
    (hα : Nonempty α)
    (obs : α → M)
    (f : Nat)
    (T : TextFor L)
    {m n : Nat}
    (hmn : m ≤ n) :
    correctedConcreteWorkingGrammarTextLanguage
        hα obs f T m ⊆
      correctedConcreteWorkingGrammarTextLanguage
        hα obs f T n := by

  exact
    correctedConcreteWorkingGrammarLearner_language_mono
      hα obs f
      (T.prefixSample_mono hmn)

/-- Equal prefix samples force equal actual output languages. -/
theorem correctedConcreteWorkingGrammarTextLanguage_eq_of_prefixSample_eq
    {L : Set (Word α)}
    (hα : Nonempty α)
    (obs : α → M)
    (f : Nat)
    (T : TextFor L)
    {m n : Nat}
    (hmn :
      T.prefixSample m =
        T.prefixSample n) :
    correctedConcreteWorkingGrammarTextLanguage
        hα obs f T m =
      correctedConcreteWorkingGrammarTextLanguage
        hα obs f T n := by

  unfold
    correctedConcreteWorkingGrammarTextLanguage

  rw [hmn]

/-- A semantic language mind change requires a prefix-sample change. -/
theorem correctedConcreteWorkingGrammarLanguageChangesAt_implies_prefixSampleChangesAt
    {L : Set (Word α)}
    (hα : Nonempty α)
    (obs : α → M)
    (f : Nat)
    (T : TextFor L)
    {n : Nat}
    (hchange :
      CorrectedConcreteWorkingGrammarLanguageChangesAt
        hα obs f T n) :
    TextPrefixSampleChangesAt T n := by

  intro hsample

  apply hchange

  exact
    correctedConcreteWorkingGrammarTextLanguage_eq_of_prefixSample_eq
      hα obs f T hsample

/-- Consecutive prefix samples are nested. -/
theorem textPrefixSample_subset_succ
    {L : Set (Word α)}
    (T : TextFor L)
    (n : Nat) :
    T.prefixSample n ⊆
      T.prefixSample (n + 1) := by

  intro word hword

  exact
    T.prefixSample_mono
      (Nat.le_succ n)
      hword

/-- A changed prefix sample has strictly larger cardinality at the next stage. -/
theorem textPrefixSample_card_lt_of_changesAt
    {L : Set (Word α)}
    (T : TextFor L)
    {n : Nat}
    (hchange :
      TextPrefixSampleChangesAt T n) :
    (T.prefixSample n).card <
      (T.prefixSample (n + 1)).card := by

  apply Finset.card_lt_card

  exact
    Finset.ssubset_iff_subset_ne.mpr
      ⟨textPrefixSample_subset_succ
          T n,
        hchange⟩

/-- Every semantic mind change strictly increases the observed finite-sample
cardinality. -/
theorem correctedConcreteWorkingGrammarLanguageChangesAt_implies_prefixSample_card_lt
    {L : Set (Word α)}
    (hα : Nonempty α)
    (obs : α → M)
    (f : Nat)
    (T : TextFor L)
    {n : Nat}
    (hchange :
      CorrectedConcreteWorkingGrammarLanguageChangesAt
        hα obs f T n) :
    (T.prefixSample n).card <
      (T.prefixSample (n + 1)).card := by

  exact
    textPrefixSample_card_lt_of_changesAt
      T
      (correctedConcreteWorkingGrammarLanguageChangesAt_implies_prefixSampleChangesAt
        hα obs f T hchange)

end TextHypothesisLanguage


section RecursiveMindChangeCount

variable {α : Type u}
variable {M : Type v}
variable [Monoid M]
variable [DecidableEq α]

/-- Number of semantic output-language changes before stage `N`. -/
noncomputable def correctedConcreteWorkingGrammarMindChangeCount
    {L : Set (Word α)}
    (hα : Nonempty α)
    (obs : α → M)
    (f : Nat)
    (T : TextFor L) :
    Nat → Nat

  | 0 =>
      0

  | n + 1 =>
      correctedConcreteWorkingGrammarMindChangeCount
          hα obs f T n +
        if
          CorrectedConcreteWorkingGrammarLanguageChangesAt
            hα obs f T n
        then 1
        else 0

@[simp] theorem correctedConcreteWorkingGrammarMindChangeCount_zero
    {L : Set (Word α)}
    (hα : Nonempty α)
    (obs : α → M)
    (f : Nat)
    (T : TextFor L) :
    correctedConcreteWorkingGrammarMindChangeCount
        hα obs f T 0 =
      0 :=
  rfl

@[simp] theorem correctedConcreteWorkingGrammarMindChangeCount_succ
    {L : Set (Word α)}
    (hα : Nonempty α)
    (obs : α → M)
    (f : Nat)
    (T : TextFor L)
    (n : Nat) :
    correctedConcreteWorkingGrammarMindChangeCount
        hα obs f T (n + 1) =
      correctedConcreteWorkingGrammarMindChangeCount
          hα obs f T n +
        if
          CorrectedConcreteWorkingGrammarLanguageChangesAt
            hα obs f T n
        then 1
        else 0 :=
  rfl

/-- The mind-change count is monotone in the stage. -/
theorem correctedConcreteWorkingGrammarMindChangeCount_mono
    {L : Set (Word α)}
    (hα : Nonempty α)
    (obs : α → M)
    (f : Nat)
    (T : TextFor L)
    {m n : Nat}
    (hmn : m ≤ n) :
    correctedConcreteWorkingGrammarMindChangeCount
        hα obs f T m ≤
      correctedConcreteWorkingGrammarMindChangeCount
        hα obs f T n := by

  induction n with

  | zero =>
      have hm :
          m = 0 := by
        omega

      subst m

      exact Nat.le_refl _

  | succ n ih =>
      by_cases hmn' : m ≤ n

      · have hstep :
            correctedConcreteWorkingGrammarMindChangeCount
                hα obs f T n ≤
              correctedConcreteWorkingGrammarMindChangeCount
                hα obs f T (n + 1) := by

          rw [
            correctedConcreteWorkingGrammarMindChangeCount_succ
          ]

          by_cases hchange :
            CorrectedConcreteWorkingGrammarLanguageChangesAt
              hα obs f T n

          · simp [hchange]

          · simp [hchange]

        exact
          (ih hmn').trans hstep

      · have hm :
            m = n + 1 := by
          omega

        subst m

        exact Nat.le_refl _

/-- The number of semantic language changes before `N` is bounded by the
number of distinct observed words in the prefix sample at `N`. -/
theorem correctedConcreteWorkingGrammarMindChangeCount_le_prefixSample_card
    {L : Set (Word α)}
    (hα : Nonempty α)
    (obs : α → M)
    (f : Nat)
    (T : TextFor L)
    (N : Nat) :
    correctedConcreteWorkingGrammarMindChangeCount
        hα obs f T N ≤
      (T.prefixSample N).card := by

  classical

  induction N with

  | zero =>
      simp

  | succ N ih =>
      rw [
        correctedConcreteWorkingGrammarMindChangeCount_succ
      ]

      by_cases hchange :
        CorrectedConcreteWorkingGrammarLanguageChangesAt
          hα obs f T N

      · simp [hchange]

        have hcard :
            (T.prefixSample N).card <
              (T.prefixSample (N + 1)).card :=
          correctedConcreteWorkingGrammarLanguageChangesAt_implies_prefixSample_card_lt
            hα obs f T hchange

        omega

      · simp [hchange]

        have hsubset :
            T.prefixSample N ⊆
              T.prefixSample (N + 1) :=
          textPrefixSample_subset_succ
            T N

        have hcard :
            (T.prefixSample N).card ≤
              (T.prefixSample (N + 1)).card :=
          Finset.card_le_card hsubset

        omega

/-- If no language change occurs at stage `n`, the cumulative count is
unchanged at the next stage. -/
theorem correctedConcreteWorkingGrammarMindChangeCount_succ_eq_of_not_changesAt
    {L : Set (Word α)}
    (hα : Nonempty α)
    (obs : α → M)
    (f : Nat)
    (T : TextFor L)
    {n : Nat}
    (hchange :
      ¬
        CorrectedConcreteWorkingGrammarLanguageChangesAt
          hα obs f T n) :
    correctedConcreteWorkingGrammarMindChangeCount
        hα obs f T (n + 1) =
      correctedConcreteWorkingGrammarMindChangeCount
        hα obs f T n := by

  rw [
    correctedConcreteWorkingGrammarMindChangeCount_succ
  ]

  simp [hchange]

/-- Once all later stages have no language changes, the cumulative mind-change
count is constant. -/
theorem correctedConcreteWorkingGrammarMindChangeCount_eq_of_no_changes_from
    {L : Set (Word α)}
    (hα : Nonempty α)
    (obs : α → M)
    (f : Nat)
    (T : TextFor L)
    (n0 : Nat)
    (hstable :
      ∀ n : Nat, n0 ≤ n →
        ¬
          CorrectedConcreteWorkingGrammarLanguageChangesAt
            hα obs f T n)
    {N : Nat}
    (hN : n0 ≤ N) :
    correctedConcreteWorkingGrammarMindChangeCount
        hα obs f T N =
      correctedConcreteWorkingGrammarMindChangeCount
        hα obs f T n0 := by

  induction N generalizing n0 with

  | zero =>
      have hn0 :
          n0 = 0 := by
        omega

      subst n0

      rfl

  | succ N ih =>
      by_cases hprev :
        n0 ≤ N

      · rw [
          correctedConcreteWorkingGrammarMindChangeCount_succ_eq_of_not_changesAt
            hα obs f T
            (hstable N hprev)
        ]

        exact
          ih (n0 := n0) hstable hprev

      · have hn0 :
            n0 = N + 1 := by
          omega

        subst n0

        rfl

end RecursiveMindChangeCount


section GenericCharacteristicCoverage

variable {α : Type u}
variable {M : Type v}
variable [Monoid M]
variable [DecidableEq α]

/-- Select a text stage after which a fixed finite characteristic sample is
contained in every prefix sample. -/
noncomputable def correctedConcreteWorkingGrammarCharacteristicCoverageStage
    {L : Set (Word α)}
    (hα : Nonempty α)
    (obs : α → M)
    (f : Nat)
    (S : Finset (Word α))
    (hS :
      CharacteristicSample
        (correctedConcreteWorkingGrammarHypLanguage
          obs f)
        (correctedConcreteWorkingGrammarLearner
          hα obs f)
        S L)
    (T : TextFor L) :
    Nat :=
  Classical.choose
    (TextFor.eventuallyContains_finite_subset
      S hS.1 T)

/-- Every prefix after the selected characteristic coverage stage contains
the characteristic sample. -/
theorem correctedConcreteWorkingGrammarCharacteristicSample_subset_prefix_after
    {L : Set (Word α)}
    (hα : Nonempty α)
    (obs : α → M)
    (f : Nat)
    (S : Finset (Word α))
    (hS :
      CharacteristicSample
        (correctedConcreteWorkingGrammarHypLanguage
          obs f)
        (correctedConcreteWorkingGrammarLearner
          hα obs f)
        S L)
    (T : TextFor L)
    {n : Nat}
    (hn :
      correctedConcreteWorkingGrammarCharacteristicCoverageStage
          hα obs f S hS T ≤ n) :
    (S : Set (Word α)) ⊆
      (T.prefixSample n : Set (Word α)) := by

  exact
    (Classical.choose_spec
      (TextFor.eventuallyContains_finite_subset
        S hS.1 T))
      n hn

/-- Every actual grammar output after characteristic-sample coverage has
exactly the target language. -/
theorem correctedConcreteWorkingGrammar_correct_after_characteristicCoverage
    {L : Set (Word α)}
    (hα : Nonempty α)
    (obs : α → M)
    (f : Nat)
    (S : Finset (Word α))
    (hS :
      CharacteristicSample
        (correctedConcreteWorkingGrammarHypLanguage
          obs f)
        (correctedConcreteWorkingGrammarLearner
          hα obs f)
        S L)
    (T : TextFor L)
    {n : Nat}
    (hn :
      correctedConcreteWorkingGrammarCharacteristicCoverageStage
          hα obs f S hS T ≤ n) :
    correctedConcreteWorkingGrammarTextLanguage
        hα obs f T n =
      L := by

  exact
    hS.2
      (T.prefixSample n)
      (correctedConcreteWorkingGrammarCharacteristicSample_subset_prefix_after
        hα obs f S hS T hn)
      (T.prefixSample_subset n)

/-- No semantic language mind change occurs after characteristic-sample
coverage. -/
theorem correctedConcreteWorkingGrammar_not_languageChangesAt_after_characteristicCoverage
    {L : Set (Word α)}
    (hα : Nonempty α)
    (obs : α → M)
    (f : Nat)
    (S : Finset (Word α))
    (hS :
      CharacteristicSample
        (correctedConcreteWorkingGrammarHypLanguage
          obs f)
        (correctedConcreteWorkingGrammarLearner
          hα obs f)
        S L)
    (T : TextFor L)
    {n : Nat}
    (hn :
      correctedConcreteWorkingGrammarCharacteristicCoverageStage
          hα obs f S hS T ≤ n) :
    ¬
      CorrectedConcreteWorkingGrammarLanguageChangesAt
        hα obs f T n := by

  intro hchange

  apply hchange

  calc
    correctedConcreteWorkingGrammarTextLanguage
          hα obs f T n =
        L :=
      correctedConcreteWorkingGrammar_correct_after_characteristicCoverage
        hα obs f S hS T hn
    _ =
        correctedConcreteWorkingGrammarTextLanguage
          hα obs f T (n + 1) := by
      symm

      exact
        correctedConcreteWorkingGrammar_correct_after_characteristicCoverage
          hα obs f S hS T
          (hn.trans
            (Nat.le_succ n))

/-- The cumulative mind-change count is constant after a characteristic sample
has been covered. -/
theorem correctedConcreteWorkingGrammarMindChangeCount_constant_after_characteristicCoverage
    {L : Set (Word α)}
    (hα : Nonempty α)
    (obs : α → M)
    (f : Nat)
    (S : Finset (Word α))
    (hS :
      CharacteristicSample
        (correctedConcreteWorkingGrammarHypLanguage
          obs f)
        (correctedConcreteWorkingGrammarLearner
          hα obs f)
        S L)
    (T : TextFor L)
    {N : Nat}
    (hN :
      correctedConcreteWorkingGrammarCharacteristicCoverageStage
          hα obs f S hS T ≤ N) :
    correctedConcreteWorkingGrammarMindChangeCount
        hα obs f T N =
      correctedConcreteWorkingGrammarMindChangeCount
        hα obs f T
        (correctedConcreteWorkingGrammarCharacteristicCoverageStage
          hα obs f S hS T) := by

  apply
    correctedConcreteWorkingGrammarMindChangeCount_eq_of_no_changes_from
      hα obs f T
      (correctedConcreteWorkingGrammarCharacteristicCoverageStage
        hα obs f S hS T)

  · intro n hn

    exact
      correctedConcreteWorkingGrammar_not_languageChangesAt_after_characteristicCoverage
        hα obs f S hS T hn

  · exact hN

end GenericCharacteristicCoverage


section MinimumCharacteristicSample

variable {α : Type u}
variable {M : Type v}
variable [Fintype M]
variable [DecidableEq α]
variable [DecidableEq M]
variable [Monoid M]
variable (hα : Nonempty α)
variable (obs : α → M)
variable (f : Nat)

/-- Select one characteristic sample attaining the minimum characteristic
budget of a semantic start-rooted target. -/
noncomputable def startRootedTargetMinimalCharacteristicSample
    {L : Set (Word α)}
    (hL :
      L ∈ StartRootedCorrectedConcreteTargetClass
        (v := w) α M obs f) :
    Finset (Word α) :=
  Classical.choose
    (startRootedTarget_exists_characteristicSample_at_rank
      (v := w) hα obs f hL)

/-- The selected minimum-budget sample is characteristic. -/
theorem startRootedTargetMinimalCharacteristicSample_characteristic
    {L : Set (Word α)}
    (hL :
      L ∈ StartRootedCorrectedConcreteTargetClass
        (v := w) α M obs f) :
    CharacteristicSample
      (correctedConcreteWorkingGrammarHypLanguage
        obs f)
      (correctedConcreteWorkingGrammarLearner
        hα obs f)
      (startRootedTargetMinimalCharacteristicSample
        (v := w) hα obs f hL)
      L := by

  exact
    (Classical.choose_spec
      (startRootedTarget_exists_characteristicSample_at_rank
        (v := w) hα obs f hL)).1

/-- The selected minimum-budget sample has total length at most the
characteristic rank. -/
theorem startRootedTargetMinimalCharacteristicSample_length_le_rank
    {L : Set (Word α)}
    (hL :
      L ∈ StartRootedCorrectedConcreteTargetClass
        (v := w) α M obs f) :
    sampleLengthBudget
        (startRootedTargetMinimalCharacteristicSample
          (v := w) hα obs f hL) ≤
      startRootedTargetCharacteristicRank
        (v := w) hα obs f hL := by

  exact
    (Classical.choose_spec
      (startRootedTarget_exists_characteristicSample_at_rank
        (v := w) hα obs f hL)).2

/-- The selected minimum sample is positive. -/
theorem startRootedTargetMinimalCharacteristicSample_positive
    {L : Set (Word α)}
    (hL :
      L ∈ StartRootedCorrectedConcreteTargetClass
        (v := w) α M obs f) :
    (startRootedTargetMinimalCharacteristicSample
        (v := w) hα obs f hL :
      Set (Word α)) ⊆
        L := by

  exact
    (startRootedTargetMinimalCharacteristicSample_characteristic
      (v := w) hα obs f hL).1

/-- Coverage stage of a minimum-budget characteristic sample along one text. -/
noncomputable def startRootedTargetMinimalCharacteristicCoverageStage
    {L : Set (Word α)}
    (hL :
      L ∈ StartRootedCorrectedConcreteTargetClass
        (v := w) α M obs f)
    (T : TextFor L) :
    Nat :=
  correctedConcreteWorkingGrammarCharacteristicCoverageStage
    hα obs f
    (startRootedTargetMinimalCharacteristicSample
      (v := w) hα obs f hL)
    (startRootedTargetMinimalCharacteristicSample_characteristic
      (v := w) hα obs f hL)
    T

/-- Every output after minimum-characteristic-sample coverage has exactly the
target language. -/
theorem correctedConcreteWorkingGrammar_correct_after_minimalCharacteristicCoverage
    {L : Set (Word α)}
    (hL :
      L ∈ StartRootedCorrectedConcreteTargetClass
        (v := w) α M obs f)
    (T : TextFor L)
    {n : Nat}
    (hn :
      startRootedTargetMinimalCharacteristicCoverageStage
          (v := w) hα obs f hL T ≤ n) :
    correctedConcreteWorkingGrammarTextLanguage
        hα obs f T n =
      L := by

  exact
    correctedConcreteWorkingGrammar_correct_after_characteristicCoverage
      hα obs f
      (startRootedTargetMinimalCharacteristicSample
        (v := w) hα obs f hL)
      (startRootedTargetMinimalCharacteristicSample_characteristic
        (v := w) hα obs f hL)
      T hn

/-- No language mind changes occur after minimum-characteristic-sample
coverage. -/
theorem correctedConcreteWorkingGrammar_no_mindChanges_after_minimalCharacteristicCoverage
    {L : Set (Word α)}
    (hL :
      L ∈ StartRootedCorrectedConcreteTargetClass
        (v := w) α M obs f)
    (T : TextFor L)
    {n : Nat}
    (hn :
      startRootedTargetMinimalCharacteristicCoverageStage
          (v := w) hα obs f hL T ≤ n) :
    ¬
      CorrectedConcreteWorkingGrammarLanguageChangesAt
        hα obs f T n := by

  exact
    correctedConcreteWorkingGrammar_not_languageChangesAt_after_characteristicCoverage
      hα obs f
      (startRootedTargetMinimalCharacteristicSample
        (v := w) hα obs f hL)
      (startRootedTargetMinimalCharacteristicSample_characteristic
        (v := w) hα obs f hL)
      T hn

/-- The cumulative semantic mind-change count stabilizes at the coverage stage
of a minimum-budget characteristic sample. -/
theorem correctedConcreteWorkingGrammarMindChangeCount_constant_after_minimalCharacteristicCoverage
    {L : Set (Word α)}
    (hL :
      L ∈ StartRootedCorrectedConcreteTargetClass
        (v := w) α M obs f)
    (T : TextFor L)
    {N : Nat}
    (hN :
      startRootedTargetMinimalCharacteristicCoverageStage
          (v := w) hα obs f hL T ≤ N) :
    correctedConcreteWorkingGrammarMindChangeCount
        hα obs f T N =
      correctedConcreteWorkingGrammarMindChangeCount
        hα obs f T
        (startRootedTargetMinimalCharacteristicCoverageStage
          (v := w) hα obs f hL T) := by

  exact
    correctedConcreteWorkingGrammarMindChangeCount_constant_after_characteristicCoverage
      hα obs f
      (startRootedTargetMinimalCharacteristicSample
        (v := w) hα obs f hL)
      (startRootedTargetMinimalCharacteristicSample_characteristic
        (v := w) hα obs f hL)
      T hN

end MinimumCharacteristicSample


section StartRootedMindChangePackages

variable {α : Type u}
variable {M : Type v}
variable [Fintype M]
variable [DecidableEq α]
variable [DecidableEq M]
variable [Monoid M]
variable (hα : Nonempty α)
variable (obs : α → M)
variable (f : Nat)

/-- Finite semantic mind-change and stabilization package for one target text. -/
theorem correctedConcreteWorkingGrammarLearner_mindChange_stabilization_package
    {L : Set (Word α)}
    (hL :
      L ∈ StartRootedCorrectedConcreteTargetClass
        (v := w) α M obs f)
    (T : TextFor L) :
    (∀ N : Nat,
      correctedConcreteWorkingGrammarMindChangeCount
          hα obs f T N ≤
        (T.prefixSample N).card) ∧
      (∀ n : Nat,
        startRootedTargetMinimalCharacteristicCoverageStage
            (v := w) hα obs f hL T ≤ n →
          correctedConcreteWorkingGrammarTextLanguage
              hα obs f T n =
            L) ∧
      (∀ n : Nat,
        startRootedTargetMinimalCharacteristicCoverageStage
            (v := w) hα obs f hL T ≤ n →
          ¬
            CorrectedConcreteWorkingGrammarLanguageChangesAt
              hα obs f T n) ∧
      (∀ N : Nat,
        startRootedTargetMinimalCharacteristicCoverageStage
            (v := w) hα obs f hL T ≤ N →
          correctedConcreteWorkingGrammarMindChangeCount
              hα obs f T N =
            correctedConcreteWorkingGrammarMindChangeCount
              hα obs f T
              (startRootedTargetMinimalCharacteristicCoverageStage
                (v := w) hα obs f hL T)) := by

  exact
    ⟨correctedConcreteWorkingGrammarMindChangeCount_le_prefixSample_card
        hα obs f T,
      fun n hn =>
        correctedConcreteWorkingGrammar_correct_after_minimalCharacteristicCoverage
          (v := w) hα obs f hL T hn,
      fun n hn =>
        correctedConcreteWorkingGrammar_no_mindChanges_after_minimalCharacteristicCoverage
          (v := w) hα obs f hL T hn,
      fun N hN =>
        correctedConcreteWorkingGrammarMindChangeCount_constant_after_minimalCharacteristicCoverage
          (v := w) hα obs f hL T hN⟩

/-- Class-level endpoint: every positive text has finitely many semantic
language changes and stabilizes to the target after coverage of a
minimum-budget characteristic sample. -/
theorem correctedConcreteWorkingGrammarLearner_class_mindChange_package :
    ∀ L : Set (Word α),
      ∀ hL :
        L ∈ StartRootedCorrectedConcreteTargetClass
          (v := w) α M obs f,
      ∀ T : TextFor L,
        ∃ n0 : Nat,
          (∀ n : Nat, n0 ≤ n →
            correctedConcreteWorkingGrammarTextLanguage
                hα obs f T n =
              L) ∧
          (∀ n : Nat, n0 ≤ n →
            ¬
              CorrectedConcreteWorkingGrammarLanguageChangesAt
                hα obs f T n) ∧
          (∀ N : Nat, n0 ≤ N →
            correctedConcreteWorkingGrammarMindChangeCount
                hα obs f T N =
              correctedConcreteWorkingGrammarMindChangeCount
                hα obs f T n0) := by

  intro L hL T

  refine
    ⟨startRootedTargetMinimalCharacteristicCoverageStage
        (v := w) hα obs f hL T,
      ?_,
      ?_,
      ?_⟩

  · intro n hn

    exact
      correctedConcreteWorkingGrammar_correct_after_minimalCharacteristicCoverage
        (v := w) hα obs f hL T hn

  · intro n hn

    exact
      correctedConcreteWorkingGrammar_no_mindChanges_after_minimalCharacteristicCoverage
        (v := w) hα obs f hL T hn

  · intro N hN

    exact
      correctedConcreteWorkingGrammarMindChangeCount_constant_after_minimalCharacteristicCoverage
        (v := w) hα obs f hL T hN

end StartRootedMindChangePackages

end MCFG
