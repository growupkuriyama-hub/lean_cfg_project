/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG2.ConcreteCanonicalLearnerWorkingGrammarPaperPowerBitBound

/-!
# ConcreteCanonicalLearnerWorkingGrammarFinalDescriptionPackage.lean

The preceding file proves a single-power upper bound for the complete checked
logarithmic serialization of the canonical finite hypothesis compiled to an
actual `WorkingMCFG`.

This file attaches that serialization directly to the actual
`WorkingMCFG`-valued learner and combines it with the previously verified
semantic learning theorem.

For a nonempty terminal alphabet, the learner output on `K` is definitionally

```lean
(correctedConcreteFiniteHypothesis K obs f).toCutWorkingMCFG
  (Classical.choice hα).
```

We therefore define the learner's checked logarithmic description by using the
same selected dummy terminal:

```lean
correctedConcreteWorkingGrammarLearnerLogarithmicBitList
correctedConcreteWorkingGrammarLearnerLogarithmicBitCount
correctedConcreteWorkingGrammarLearnerLogarithmicBitDecode
```

The decoder returns the complete top-level presentation-entry list of the
actual cut compilation.  We prove

```text
decode(encode(output on K))
  =
some(compiled presentation entries on K),
```

and

```text
encoded bit-list length
  =
exact logarithmic bit count
  ≤
(4 * (sampleLengthBudget K + f + 1)) ^
  ((64 *
      (sampleLengthBudget K + f + 1) *
      (sampleLengthBudget K + f + 1)) * 13).
```

The final class package combines:

* one target-independent actual `WorkingMCFG`-valued learner;
* Gold identification of the semantic start-rooted target class;
* exact agreement with the corrected concrete learner language;
* consistency;
* language monotonicity;
* source-rule, compiled-rule, and presentation-item bounds;
* checked decoder round trip; and
* the final single-power logarithmic description-size bound.

A selected-stage package additionally states that after one finite
characteristic-sample coverage stage, every later actual grammar output has
exactly the target language and retains its checked bounded serialization.

No target grammar is supplied to the learner.
No `sorry`, `admit`, or `axiom` is used.
-/

namespace MCFG

universe u v w

section LearnerCheckedLogarithmicDescription

variable {α : Type u}
variable {M : Type v}
variable [Fintype M]
variable [DecidableEq α]
variable [DecidableEq M]
variable [Monoid M]

/-- The actual learner output grammar is definitionally the cut compilation of
its retained canonical finite hypothesis, using the selected dummy terminal. -/
@[simp] theorem
    correctedConcreteWorkingGrammarLearner_grammar_eq_cutWorkingGrammar
    (hα : Nonempty α)
    (obs : α → M)
    (f : Nat)
    (K : Finset (Word α)) :
    (correctedConcreteWorkingGrammarLearner
        hα obs f K).grammar =
      (correctedConcreteFiniteHypothesis
        K obs f).toCutWorkingMCFG
          (Classical.choice hα) := by

  rfl

/-- Complete checked logarithmic bit list attached directly to the actual
working-grammar learner output. -/
noncomputable def
    correctedConcreteWorkingGrammarLearnerLogarithmicBitList
    (hα : Nonempty α)
    (obs : α → M)
    (f : Nat)
    (K : Finset (Word α)) :
    List Bool :=
  (correctedConcreteFiniteHypothesis K obs f).
    encodeCompiledWorkingGrammarLogarithmicBitList
      (Classical.choice hα)

/-- Exact length of the learner output's checked logarithmic bit list. -/
noncomputable def
    correctedConcreteWorkingGrammarLearnerLogarithmicBitCount
    (hα : Nonempty α)
    (obs : α → M)
    (f : Nat)
    (K : Finset (Word α)) :
    Nat :=
  (correctedConcreteFiniteHypothesis K obs f).
    compiledWorkingGrammarLogarithmicBitCount
      (Classical.choice hα)

/-- Checked decoder for the learner output's logarithmic bit list. -/
noncomputable def
    correctedConcreteWorkingGrammarLearnerLogarithmicBitDecode
    (hα : Nonempty α)
    (obs : α → M)
    (f : Nat)
    (K : Finset (Word α))
    (bits : List Bool) :
    Option
      (List
        (CorrectedConcreteCompiledGrammarPresentationEntry
          (correctedConcreteFiniteHypothesis K obs f))) :=
  (correctedConcreteFiniteHypothesis K obs f).
    decodeCompiledWorkingGrammarLogarithmicBitList
      (Classical.choice hα)
      bits

/-- The learner-attached logarithmic bit list decodes to the complete actual
compiled presentation. -/
@[simp] theorem
    correctedConcreteWorkingGrammarLearnerLogarithmicBitDecode_encode
    (hα : Nonempty α)
    (obs : α → M)
    (f : Nat)
    (K : Finset (Word α)) :
    correctedConcreteWorkingGrammarLearnerLogarithmicBitDecode
        hα obs f K
        (correctedConcreteWorkingGrammarLearnerLogarithmicBitList
          hα obs f K) =
      some
        ((correctedConcreteFiniteHypothesis K obs f).
          compiledGrammarPresentationEntries
            (Classical.choice hα)) := by

  exact
    (correctedConcreteFiniteHypothesis K obs f).
      decodeCompiledWorkingGrammarLogarithmicBitList_encode
        (Classical.choice hα)

/-- The attached bit-list length is the exact learner-output logarithmic bit
count. -/
@[simp] theorem
    correctedConcreteWorkingGrammarLearnerLogarithmicBitList_length
    (hα : Nonempty α)
    (obs : α → M)
    (f : Nat)
    (K : Finset (Word α)) :
    (correctedConcreteWorkingGrammarLearnerLogarithmicBitList
        hα obs f K).length =
      correctedConcreteWorkingGrammarLearnerLogarithmicBitCount
        hα obs f K := by

  exact
    (correctedConcreteFiniteHypothesis K obs f).
      encodeCompiledWorkingGrammarLogarithmicBitList_length
        (Classical.choice hα)

/-- The exact learner-output logarithmic bit count satisfies the final
single-power paper bound. -/
theorem
    correctedConcreteWorkingGrammarLearnerLogarithmicBitCount_le_paperPower
    (hα : Nonempty α)
    (obs : α → M)
    (f : Nat)
    (K : Finset (Word α)) :
    correctedConcreteWorkingGrammarLearnerLogarithmicBitCount
        hα obs f K <=
      correctedConcreteCompiledGrammarPaperPowerBitBound
        (sampleLengthBudget K)
        f := by

  exact
    correctedConcreteFiniteHypothesis_logarithmicBitCount_le_paperPower
      K obs f
      (Classical.choice hα)

/-- Fully expanded single-power bound for the exact learner-output logarithmic
bit count. -/
theorem
    correctedConcreteWorkingGrammarLearnerLogarithmicBitCount_le_explicit_paperPower
    (hα : Nonempty α)
    (obs : α → M)
    (f : Nat)
    (K : Finset (Word α)) :
    correctedConcreteWorkingGrammarLearnerLogarithmicBitCount
        hα obs f K <=
      (4 * (sampleLengthBudget K + f + 1)) ^
        ((64 *
            (sampleLengthBudget K + f + 1) *
            (sampleLengthBudget K + f + 1)) *
          13) := by

  exact
    correctedConcreteWorkingGrammarLearnerLogarithmicBitCount_le_paperPower
      hα obs f K

/-- The attached bit-list itself satisfies the final single-power length
bound. -/
theorem
    correctedConcreteWorkingGrammarLearnerLogarithmicBitList_length_le_paperPower
    (hα : Nonempty α)
    (obs : α → M)
    (f : Nat)
    (K : Finset (Word α)) :
    (correctedConcreteWorkingGrammarLearnerLogarithmicBitList
        hα obs f K).length <=
      correctedConcreteCompiledGrammarPaperPowerBitBound
        (sampleLengthBudget K)
        f := by

  rw [
    correctedConcreteWorkingGrammarLearnerLogarithmicBitList_length
      hα obs f K
  ]

  exact
    correctedConcreteWorkingGrammarLearnerLogarithmicBitCount_le_paperPower
      hα obs f K

/-- Fully expanded attached bit-list length bound. -/
theorem
    correctedConcreteWorkingGrammarLearnerLogarithmicBitList_length_le_explicit_paperPower
    (hα : Nonempty α)
    (obs : α → M)
    (f : Nat)
    (K : Finset (Word α)) :
    (correctedConcreteWorkingGrammarLearnerLogarithmicBitList
        hα obs f K).length <=
      (4 * (sampleLengthBudget K + f + 1)) ^
        ((64 *
            (sampleLengthBudget K + f + 1) *
            (sampleLengthBudget K + f + 1)) *
          13) := by

  exact
    correctedConcreteWorkingGrammarLearnerLogarithmicBitList_length_le_paperPower
      hα obs f K

/-- Prefix form of the learner-output checked logarithmic bit-count theorem. -/
theorem
    correctedConcreteWorkingGrammarLearner_prefix_logarithmicBitCount_le_paperPower
    {L : Set (Word α)}
    (hα : Nonempty α)
    (obs : α → M)
    (f : Nat)
    (T : TextFor L)
    (n : Nat) :
    correctedConcreteWorkingGrammarLearnerLogarithmicBitCount
        hα obs f
        (T.prefixSample n) <=
      correctedConcreteCompiledGrammarPaperPowerBitBound
        (sampleLengthBudget
          (T.prefixSample n))
        f := by

  exact
    correctedConcreteWorkingGrammarLearnerLogarithmicBitCount_le_paperPower
      hα obs f
      (T.prefixSample n)

/-- Prefix form of the checked bit-list length theorem. -/
theorem
    correctedConcreteWorkingGrammarLearner_prefix_logarithmicBitList_length_le_paperPower
    {L : Set (Word α)}
    (hα : Nonempty α)
    (obs : α → M)
    (f : Nat)
    (T : TextFor L)
    (n : Nat) :
    (correctedConcreteWorkingGrammarLearnerLogarithmicBitList
        hα obs f
        (T.prefixSample n)).length <=
      correctedConcreteCompiledGrammarPaperPowerBitBound
        (sampleLengthBudget
          (T.prefixSample n))
        f := by

  exact
    correctedConcreteWorkingGrammarLearnerLogarithmicBitList_length_le_paperPower
      hα obs f
      (T.prefixSample n)

/-- Compact checked-description package for one finite sample. -/
theorem
    correctedConcreteWorkingGrammarLearner_checkedDescription_package
    (hα : Nonempty α)
    (obs : α → M)
    (f : Nat)
    (K : Finset (Word α)) :
    ((correctedConcreteWorkingGrammarLearner
        hα obs f K).grammar =
      (correctedConcreteFiniteHypothesis
        K obs f).toCutWorkingMCFG
          (Classical.choice hα)) ∧
      (correctedConcreteWorkingGrammarLearnerLogarithmicBitDecode
          hα obs f K
          (correctedConcreteWorkingGrammarLearnerLogarithmicBitList
            hα obs f K) =
        some
          ((correctedConcreteFiniteHypothesis K obs f).
            compiledGrammarPresentationEntries
              (Classical.choice hα))) ∧
      ((correctedConcreteWorkingGrammarLearnerLogarithmicBitList
          hα obs f K).length =
        correctedConcreteWorkingGrammarLearnerLogarithmicBitCount
          hα obs f K) ∧
      (correctedConcreteWorkingGrammarLearnerLogarithmicBitCount
          hα obs f K <=
        correctedConcreteCompiledGrammarPaperPowerBitBound
          (sampleLengthBudget K)
          f) := by

  exact
    ⟨correctedConcreteWorkingGrammarLearner_grammar_eq_cutWorkingGrammar
        hα obs f K,
      correctedConcreteWorkingGrammarLearnerLogarithmicBitDecode_encode
        hα obs f K,
      correctedConcreteWorkingGrammarLearnerLogarithmicBitList_length
        hα obs f K,
      correctedConcreteWorkingGrammarLearnerLogarithmicBitCount_le_paperPower
        hα obs f K⟩

end LearnerCheckedLogarithmicDescription


section FinalCheckedDescriptionSemanticPackage

variable {α : Type u}
variable {M : Type v}
variable [Fintype M]
variable [DecidableEq α]
variable [DecidableEq M]
variable [Monoid M]
variable (hα : Nonempty α)
variable (obs : α → M)
variable (f : Nat)

/-- Final paper-facing package combining semantic identification, actual
working-grammar outputs, all previously verified structural counts, checked
decoding, and the single-power logarithmic description-size theorem. -/
theorem
    correctedConcreteWorkingGrammarLearner_checkedDescription_semantic_package :
    IdentifiesClassFromPositiveData
        (correctedConcreteWorkingGrammarHypLanguage
          obs f)
        (correctedConcreteWorkingGrammarLearner
          hα obs f)
        (StartRootedCorrectedConcreteTargetClass
          (v := w) α M obs f) ∧
      (∀ K : Finset (Word α),
        (correctedConcreteWorkingGrammarLearner
            hα obs f K).grammar.StringLanguage =
          CorrectedConcreteCanonicalLearnerLanguage
            K obs f) ∧
      (∀ K : Finset (Word α),
        (K : Set (Word α)) ⊆
          (correctedConcreteWorkingGrammarLearner
            hα obs f K).grammar.StringLanguage) ∧
      (∀ S K : Finset (Word α),
        (S : Set (Word α)) ⊆
            (K : Set (Word α)) →
        (correctedConcreteWorkingGrammarLearner
            hα obs f S).grammar.StringLanguage ⊆
          (correctedConcreteWorkingGrammarLearner
            hα obs f K).grammar.StringLanguage) ∧
      (∀ K : Finset (Word α),
        (correctedConcreteWorkingGrammarLearner
            hα obs f K).sourceRuleCount <=
          correctedLearnerPaperRuleCountBound
            (sampleLengthBudget K)
            f) ∧
      (∀ K : Finset (Word α),
        (correctedConcreteWorkingGrammarLearner
            hα obs f K).grammarRuleCount <=
          correctedConcreteCompiledGrammarRuleCountBound
            (sampleLengthBudget K)
            f) ∧
      (∀ K : Finset (Word α),
        (correctedConcreteWorkingGrammarLearner
            hα obs f K).presentationItemCount <=
          correctedConcreteCompiledGrammarPresentationItemBound
            (sampleLengthBudget K)
            f) ∧
      (∀ K : Finset (Word α),
        correctedConcreteWorkingGrammarLearnerLogarithmicBitDecode
            hα obs f K
            (correctedConcreteWorkingGrammarLearnerLogarithmicBitList
              hα obs f K) =
          some
            ((correctedConcreteFiniteHypothesis K obs f).
              compiledGrammarPresentationEntries
                (Classical.choice hα))) ∧
      (∀ K : Finset (Word α),
        (correctedConcreteWorkingGrammarLearnerLogarithmicBitList
            hα obs f K).length =
          correctedConcreteWorkingGrammarLearnerLogarithmicBitCount
            hα obs f K) ∧
      (∀ K : Finset (Word α),
        correctedConcreteWorkingGrammarLearnerLogarithmicBitCount
            hα obs f K <=
          correctedConcreteCompiledGrammarPaperPowerBitBound
            (sampleLengthBudget K)
            f) := by

  exact
    ⟨correctedConcreteWorkingGrammarLearner_identifies_startRootedTargetClass
        (v := w) hα obs f,
      correctedConcreteWorkingGrammarLearner_stringLanguage_eq_corrected
        hα obs f,
      correctedConcreteWorkingGrammarLearner_consistent
        hα obs f,
      fun S K hSK =>
        correctedConcreteWorkingGrammarLearner_language_mono
          hα obs f hSK,
      fun K =>
        correctedConcreteFiniteHypothesis_ruleCount_le_paperBound
          K obs f,
      correctedConcreteWorkingGrammarLearner_grammarRuleCount_le_paperBound
        hα obs f,
      correctedConcreteWorkingGrammarLearner_presentationItemCount_le_paperBound
        hα obs f,
      correctedConcreteWorkingGrammarLearnerLogarithmicBitDecode_encode
        hα obs f,
      correctedConcreteWorkingGrammarLearnerLogarithmicBitList_length
        hα obs f,
      correctedConcreteWorkingGrammarLearnerLogarithmicBitCount_le_paperPower
        hα obs f⟩

/-- Fully expanded version of the final class-level checked-description size
component. -/
theorem
    correctedConcreteWorkingGrammarLearner_class_logarithmicBitCount_le_explicit_paperPower :
    ∀ K : Finset (Word α),
      correctedConcreteWorkingGrammarLearnerLogarithmicBitCount
          hα obs f K <=
        (4 * (sampleLengthBudget K + f + 1)) ^
          ((64 *
              (sampleLengthBudget K + f + 1) *
              (sampleLengthBudget K + f + 1)) *
            13) := by

  intro K

  exact
    correctedConcreteWorkingGrammarLearnerLogarithmicBitCount_le_explicit_paperPower
      hα obs f K

/-- Selected-stage package: after one finite characteristic-sample coverage
stage, every later output grammar is exact, its checked logarithmic
serialization decodes, and its exact bit length satisfies the final
single-power estimate. -/
theorem
    correctedConcreteWorkingGrammarLearner_selectedStage_checkedDescription_package :
    ∀ L : Set (Word α),
      L ∈ StartRootedCorrectedConcreteTargetClass
          (v := w) α M obs f →
      ∀ T : TextFor L,
        ∃ n0 : Nat,
          ∀ n : Nat, n0 <= n →
            (correctedConcreteWorkingGrammarLearner
                hα obs f
                (T.prefixSample n)).grammar.StringLanguage =
              L ∧
            correctedConcreteWorkingGrammarLearnerLogarithmicBitDecode
                hα obs f
                (T.prefixSample n)
                (correctedConcreteWorkingGrammarLearnerLogarithmicBitList
                  hα obs f
                  (T.prefixSample n)) =
              some
                ((correctedConcreteFiniteHypothesis
                    (T.prefixSample n) obs f).
                  compiledGrammarPresentationEntries
                    (Classical.choice hα)) ∧
            ((correctedConcreteWorkingGrammarLearnerLogarithmicBitList
                hα obs f
                (T.prefixSample n)).length =
              correctedConcreteWorkingGrammarLearnerLogarithmicBitCount
                hα obs f
                (T.prefixSample n)) ∧
            (correctedConcreteWorkingGrammarLearnerLogarithmicBitCount
                hα obs f
                (T.prefixSample n) <=
              correctedConcreteCompiledGrammarPaperPowerBitBound
                (sampleLengthBudget
                  (T.prefixSample n))
                f) := by

  intro L hL T

  refine
    ⟨startRootedCorrectedConcreteTargetCoverageStage
        (v := w) obs f hL T,
      ?_⟩

  intro n hn

  exact
    ⟨correctedConcreteWorkingGrammarLearner_correct_after_startRootedCoverageStage
        (v := w) hα obs f hL T hn,
      correctedConcreteWorkingGrammarLearnerLogarithmicBitDecode_encode
        hα obs f
        (T.prefixSample n),
      correctedConcreteWorkingGrammarLearnerLogarithmicBitList_length
        hα obs f
        (T.prefixSample n),
      correctedConcreteWorkingGrammarLearner_prefix_logarithmicBitCount_le_paperPower
        hα obs f T n⟩

/-- Compact final conclusion package: class identification plus eventual exact
checked bounded grammar descriptions along every positive text. -/
theorem
    correctedConcreteWorkingGrammarLearner_finalDescriptionConclusion_package :
    IdentifiesClassFromPositiveData
        (correctedConcreteWorkingGrammarHypLanguage
          obs f)
        (correctedConcreteWorkingGrammarLearner
          hα obs f)
        (StartRootedCorrectedConcreteTargetClass
          (v := w) α M obs f) ∧
      (∀ K : Finset (Word α),
        correctedConcreteWorkingGrammarLearnerLogarithmicBitDecode
            hα obs f K
            (correctedConcreteWorkingGrammarLearnerLogarithmicBitList
              hα obs f K) =
          some
            ((correctedConcreteFiniteHypothesis K obs f).
              compiledGrammarPresentationEntries
                (Classical.choice hα))) ∧
      (∀ K : Finset (Word α),
        (correctedConcreteWorkingGrammarLearnerLogarithmicBitList
            hα obs f K).length <=
          correctedConcreteCompiledGrammarPaperPowerBitBound
            (sampleLengthBudget K)
            f) ∧
      (∀ L : Set (Word α),
        L ∈ StartRootedCorrectedConcreteTargetClass
            (v := w) α M obs f →
        ∀ T : TextFor L,
          ∃ n0 : Nat,
            ∀ n : Nat, n0 <= n →
              (correctedConcreteWorkingGrammarLearner
                  hα obs f
                  (T.prefixSample n)).grammar.StringLanguage =
                L ∧
              (correctedConcreteWorkingGrammarLearnerLogarithmicBitList
                  hα obs f
                  (T.prefixSample n)).length <=
                correctedConcreteCompiledGrammarPaperPowerBitBound
                  (sampleLengthBudget
                    (T.prefixSample n))
                  f) := by

  refine
    ⟨correctedConcreteWorkingGrammarLearner_identifies_startRootedTargetClass
        (v := w) hα obs f,
      correctedConcreteWorkingGrammarLearnerLogarithmicBitDecode_encode
        hα obs f,
      correctedConcreteWorkingGrammarLearnerLogarithmicBitList_length_le_paperPower
        hα obs f,
      ?_⟩

  intro L hL T

  refine
    ⟨startRootedCorrectedConcreteTargetCoverageStage
        (v := w) obs f hL T,
      ?_⟩

  intro n hn

  exact
    ⟨correctedConcreteWorkingGrammarLearner_correct_after_startRootedCoverageStage
        (v := w) hα obs f hL T hn,
      correctedConcreteWorkingGrammarLearner_prefix_logarithmicBitList_length_le_paperPower
        hα obs f T n⟩

end FinalCheckedDescriptionSemanticPackage

end MCFG
