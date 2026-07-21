/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG2.ConcreteCanonicalLearnerWorkingGrammarEquivalence

/-!
# ConcreteCanonicalLearnerWorkingGrammarIdentification.lean

The preceding construction and equivalence files show that, over a nonempty
terminal alphabet, every actual finite learner object can be compiled into a
finite `WorkingMCFG` with exactly the same string language.

This file makes that compiled grammar the output of the learner itself.

A hypothesis stores:

```lean
sample
rules
Nonterminal
grammar
language_eq
```

where `language_eq` certifies that the stored grammar has exactly the listed
finite-object language.

The learner

```lean
correctedConcreteWorkingGrammarLearner
```

takes only:

* the fixed finite observation map `obs`;
* the fixed fan-out bound `f`;
* one nonemptiness witness for the terminal alphabet;
* the current positive sample.

It does not receive the target grammar or target language.

The main verified properties are:

* every output is an actual `WorkingMCFG`;
* its string language equals the corrected concrete learner language;
* its string language equals the exact-once reachable semantics;
* the learner is consistent;
* its output languages are monotone under sample extension;
* it has finite characteristic samples for every semantic start-rooted target;
* it identifies the entire start-rooted target class from positive data;
* after the selected coverage stage, the actual output grammar has exactly the
  target language;
* the stored finite rule object retains the previously proved explicit size
  bound.

The constructed grammar is a compilation target for the lightweight
`WorkingMCFG` syntax.  It is not claimed to satisfy the paper-side exact-once
or nondeleting working conditions: constant and cut rules intentionally use
dummy seed children.

No target grammar is an input to the learner.
No `sorry`, `admit`, or `axiom` is used.
-/

namespace MCFG

universe u v w

section CompiledWorkingGrammarHypothesis

variable (α : Type u)
variable (M : Type v)
variable [Monoid M]
variable (obs : α → M)
variable (f : Nat)

/-- Fixed output type of the learner whose hypotheses are actual compiled
`WorkingMCFG` objects.

The nonterminal type is existentially stored as a field in one fixed universe.
The finite rule object is retained so that its exact semantics and size bound
remain available. -/
structure CorrectedConcreteWorkingGrammarHypothesis where

  sample :
    Finset (Word α)

  rules :
    CorrectedConcreteFiniteHypothesis
      sample obs f

  Nonterminal :
    Type (max u v)

  grammar :
    WorkingMCFG Nonterminal α

  language_eq :
    grammar.StringLanguage =
      rules.Language

namespace CorrectedConcreteWorkingGrammarHypothesis

/-- Language interpretation of one compiled grammar hypothesis. -/
def Language
    (H :
      CorrectedConcreteWorkingGrammarHypothesis
        α M obs f) :
    Set (Word α) :=
  H.grammar.StringLanguage

/-- Number of rules in the finite learner object from which the grammar was
compiled. -/
def sourceRuleCount
    (H :
      CorrectedConcreteWorkingGrammarHypothesis
        α M obs f) :
    Nat :=
  H.rules.ruleCount

/-- Number of concrete grammar rules stored by the compiled `WorkingMCFG`. -/
def grammarRuleCount
    (H :
      CorrectedConcreteWorkingGrammarHypothesis
        α M obs f) :
    Nat :=
  H.grammar.startRules.length +
    H.grammar.terminalRules.length +
    H.grammar.binaryRules.length

/-- The stored grammar language is exactly the listed finite-object language. -/
theorem language_eq_rules
    (H :
      CorrectedConcreteWorkingGrammarHypothesis
        α M obs f) :
    H.Language =
      H.rules.Language :=
  H.language_eq

end CorrectedConcreteWorkingGrammarHypothesis

end CompiledWorkingGrammarHypothesis


section CompiledWorkingGrammarLearner

variable {α : Type u}
variable {M : Type v}
variable [Monoid M]

/-- Compile the canonical finite learner object on `K` into an actual
`WorkingMCFG`, using one selected dummy terminal. -/
noncomputable def correctedConcreteWorkingGrammarHypothesis
    (hα : Nonempty α)
    (obs : α → M)
    (f : Nat)
    (K : Finset (Word α)) :
    CorrectedConcreteWorkingGrammarHypothesis
      α M obs f := by

  let H :=
    correctedConcreteFiniteHypothesis
      K obs f

  let dummy :=
    Classical.choice hα

  exact
    { sample := K

      rules := H

      Nonterminal :=
        CorrectedConcreteCutGrammarNonterminal H

      grammar :=
        H.toCutWorkingMCFG dummy

      language_eq :=
        H.cutWorkingGrammar_language_eq
          dummy }

/-- Set-driven learner whose outputs are actual compiled working grammars. -/
noncomputable def correctedConcreteWorkingGrammarLearner
    (hα : Nonempty α)
    (obs : α → M)
    (f : Nat) :
    SetDrivenLearner α
      (CorrectedConcreteWorkingGrammarHypothesis
        α M obs f) :=
  fun K =>
    correctedConcreteWorkingGrammarHypothesis
      hα obs f K

/-- Language interpretation for the actual compiled grammar outputs. -/
def correctedConcreteWorkingGrammarHypLanguage
    (obs : α → M)
    (f : Nat) :
    HypLanguage α
      (CorrectedConcreteWorkingGrammarHypothesis
        α M obs f) :=
  fun H =>
    H.Language

@[simp] theorem correctedConcreteWorkingGrammarHypothesis_sample
    (hα : Nonempty α)
    (obs : α → M)
    (f : Nat)
    (K : Finset (Word α)) :
    (correctedConcreteWorkingGrammarHypothesis
      hα obs f K).sample =
        K :=
  rfl

@[simp] theorem correctedConcreteWorkingGrammarHypothesis_rules
    (hα : Nonempty α)
    (obs : α → M)
    (f : Nat)
    (K : Finset (Word α)) :
    (correctedConcreteWorkingGrammarHypothesis
      hα obs f K).rules =
        correctedConcreteFiniteHypothesis
          K obs f :=
  rfl

@[simp] theorem correctedConcreteWorkingGrammarLearner_sample
    (hα : Nonempty α)
    (obs : α → M)
    (f : Nat)
    (K : Finset (Word α)) :
    (correctedConcreteWorkingGrammarLearner
      hα obs f K).sample =
        K :=
  rfl

@[simp] theorem correctedConcreteWorkingGrammarLearner_rules
    (hα : Nonempty α)
    (obs : α → M)
    (f : Nat)
    (K : Finset (Word α)) :
    (correctedConcreteWorkingGrammarLearner
      hα obs f K).rules =
        correctedConcreteFiniteHypothesis
          K obs f :=
  rfl

@[simp] theorem correctedConcreteWorkingGrammarLearner_sourceRuleCount
    (hα : Nonempty α)
    (obs : α → M)
    (f : Nat)
    (K : Finset (Word α)) :
    (correctedConcreteWorkingGrammarLearner
      hα obs f K).sourceRuleCount =
        (correctedConcreteFiniteHypothesis
          K obs f).ruleCount :=
  rfl

/-- The actual compiled output grammar has exactly the listed finite-object
language. -/
theorem correctedConcreteWorkingGrammarHypLanguage_eq_finiteObject
    (hα : Nonempty α)
    (obs : α → M)
    (f : Nat)
    (K : Finset (Word α)) :
    correctedConcreteWorkingGrammarHypLanguage
        obs f
        (correctedConcreteWorkingGrammarLearner
          hα obs f K) =
      (correctedConcreteFiniteHypothesis
        K obs f).Language := by

  change
    ((correctedConcreteFiniteHypothesis
        K obs f).toCutWorkingMCFG
      (Classical.choice hα)).StringLanguage =
      (correctedConcreteFiniteHypothesis
        K obs f).Language

  exact
    correctedConcreteFiniteHypothesis_cutWorkingGrammar_language_eq
      (correctedConcreteFiniteHypothesis
        K obs f)
      (Classical.choice hα)

/-- Every compiled output grammar has exactly the corrected concrete canonical
learner language. -/
theorem correctedConcreteWorkingGrammarHypLanguage_apply
    (hα : Nonempty α)
    (obs : α → M)
    (f : Nat)
    (K : Finset (Word α)) :
    correctedConcreteWorkingGrammarHypLanguage
        obs f
        (correctedConcreteWorkingGrammarLearner
          hα obs f K) =
      CorrectedConcreteCanonicalLearnerLanguage
        K obs f := by

  calc
    correctedConcreteWorkingGrammarHypLanguage
          obs f
          (correctedConcreteWorkingGrammarLearner
            hα obs f K) =
        (correctedConcreteFiniteHypothesis
          K obs f).Language :=
      correctedConcreteWorkingGrammarHypLanguage_eq_finiteObject
        hα obs f K
    _ =
        CorrectedConcreteCanonicalLearnerLanguage
          K obs f :=
      CorrectedConcreteFiniteHypothesis.language_eq_corrected
        (correctedConcreteFiniteHypothesis
          K obs f)

/-- Every compiled output grammar also has exactly the exact-once reachable
sample language. -/
theorem correctedConcreteWorkingGrammarHypLanguage_eq_exactReachable
    (hα : Nonempty α)
    (obs : α → M)
    (f : Nat)
    (K : Finset (Word α)) :
    correctedConcreteWorkingGrammarHypLanguage
        obs f
        (correctedConcreteWorkingGrammarLearner
          hα obs f K) =
      ExactReachableSampleStringLanguage
        K obs f := by

  calc
    correctedConcreteWorkingGrammarHypLanguage
          obs f
          (correctedConcreteWorkingGrammarLearner
            hα obs f K) =
        (correctedConcreteFiniteHypothesis
          K obs f).Language :=
      correctedConcreteWorkingGrammarHypLanguage_eq_finiteObject
        hα obs f K
    _ =
        ExactReachableSampleStringLanguage
          K obs f :=
      CorrectedConcreteFiniteHypothesis.language_eq_exactReachable
        (correctedConcreteFiniteHypothesis
          K obs f)

/-- Expanded statement directly about the `StringLanguage` field of the
grammar returned on `K`. -/
theorem correctedConcreteWorkingGrammarLearner_stringLanguage_eq_corrected
    (hα : Nonempty α)
    (obs : α → M)
    (f : Nat)
    (K : Finset (Word α)) :
    (correctedConcreteWorkingGrammarLearner
      hα obs f K).grammar.StringLanguage =
      CorrectedConcreteCanonicalLearnerLanguage
        K obs f :=
  correctedConcreteWorkingGrammarHypLanguage_apply
    hα obs f K

end CompiledWorkingGrammarLearner


section CompiledLearnerStructure

variable {α : Type u}
variable {M : Type v}
variable [Monoid M]

/-- The compiled working-grammar learner contains every observed sample. -/
theorem correctedConcreteWorkingGrammarLearner_consistent
    (hα : Nonempty α)
    (obs : α → M)
    (f : Nat)
    (K : Finset (Word α)) :
    (K : Set (Word α)) ⊆
      correctedConcreteWorkingGrammarHypLanguage
        obs f
        (correctedConcreteWorkingGrammarLearner
          hα obs f K) := by

  rw [
    correctedConcreteWorkingGrammarHypLanguage_apply
  ]

  exact
    sample_subset_correctedConcreteCanonicalLearnerLanguage
      K obs f

/-- Output grammar languages are monotone under finite sample extension. -/
theorem correctedConcreteWorkingGrammarLearner_language_mono
    (hα : Nonempty α)
    (obs : α → M)
    (f : Nat)
    {S K : Finset (Word α)}
    (hSK :
      (S : Set (Word α)) ⊆
        (K : Set (Word α))) :
    correctedConcreteWorkingGrammarHypLanguage
        obs f
        (correctedConcreteWorkingGrammarLearner
          hα obs f S) ⊆
      correctedConcreteWorkingGrammarHypLanguage
        obs f
        (correctedConcreteWorkingGrammarLearner
          hα obs f K) := by

  rw [
    correctedConcreteWorkingGrammarHypLanguage_apply,
    correctedConcreteWorkingGrammarHypLanguage_apply
  ]

  exact
    correctedConcreteCanonicalLearnerLanguage_mono
      obs f hSK

/-- The compiled learner agrees sample-by-sample with the actual finite-object
learner. -/
theorem correctedConcreteWorkingGrammarLearner_eq_finiteObject_semantics
    (hα : Nonempty α)
    (obs : α → M)
    (f : Nat)
    (K : Finset (Word α)) :
    correctedConcreteWorkingGrammarHypLanguage
        obs f
        (correctedConcreteWorkingGrammarLearner
          hα obs f K) =
      correctedConcreteFiniteObjectHypLanguage
        obs f
        (correctedConcreteFiniteObjectLearner
          obs f K) := by

  rw [
    correctedConcreteWorkingGrammarHypLanguage_apply,
    correctedConcreteFiniteObjectHypLanguage_apply
  ]

/-- Consistency, language monotonicity, and exact samplewise compilation in one
package. -/
theorem correctedConcreteWorkingGrammarLearner_structural_package
    (hα : Nonempty α)
    (obs : α → M)
    (f : Nat) :
    (∀ K : Finset (Word α),
      (K : Set (Word α)) ⊆
        correctedConcreteWorkingGrammarHypLanguage
          obs f
          (correctedConcreteWorkingGrammarLearner
            hα obs f K)) ∧
    (∀ S K : Finset (Word α),
      (S : Set (Word α)) ⊆
          (K : Set (Word α)) →
      correctedConcreteWorkingGrammarHypLanguage
          obs f
          (correctedConcreteWorkingGrammarLearner
            hα obs f S) ⊆
        correctedConcreteWorkingGrammarHypLanguage
          obs f
          (correctedConcreteWorkingGrammarLearner
            hα obs f K)) ∧
    (∀ K : Finset (Word α),
      correctedConcreteWorkingGrammarHypLanguage
          obs f
          (correctedConcreteWorkingGrammarLearner
            hα obs f K) =
        CorrectedConcreteCanonicalLearnerLanguage
          K obs f) := by

  exact
    ⟨correctedConcreteWorkingGrammarLearner_consistent
        hα obs f,
      fun S K hSK =>
        correctedConcreteWorkingGrammarLearner_language_mono
          hα obs f hSK,
      correctedConcreteWorkingGrammarHypLanguage_apply
        hα obs f⟩

end CompiledLearnerStructure


section CharacteristicSampleTransfer

variable {α : Type u}
variable {M : Type v}
variable [Monoid M]
variable [DecidableEq α]

/-- Characteristic-sample statements for the actual working-grammar learner
are equivalent to the earlier corrected-concrete statements. -/
theorem correctedConcreteWorkingGrammar_characteristicSample_iff
    (hα : Nonempty α)
    (obs : α → M)
    (f : Nat)
    (S : Finset (Word α))
    (L : Set (Word α)) :
    CharacteristicSample
        (correctedConcreteWorkingGrammarHypLanguage
          obs f)
        (correctedConcreteWorkingGrammarLearner
          hα obs f)
        S L ↔
      CharacteristicSample
        (correctedConcreteCanonicalHypLanguage
          obs f)
        (correctedConcreteCanonicalLearner
          (α := α))
        S L := by
  constructor

  · intro h
    constructor

    · exact h.1

    · intro K hSK hKL

      have hK :=
        h.2 K hSK hKL

      rw [
        correctedConcreteWorkingGrammarHypLanguage_apply
      ] at hK

      exact hK

  · intro h
    constructor

    · exact h.1

    · intro K hSK hKL

      have hK :=
        h.2 K hSK hKL

      rw [
        correctedConcreteWorkingGrammarHypLanguage_apply
      ]

      exact hK

/-- Equivalent transfer through the finite-object learner facade. -/
theorem correctedConcreteWorkingGrammar_characteristicSample_iff_finiteObject
    (hα : Nonempty α)
    (obs : α → M)
    (f : Nat)
    (S : Finset (Word α))
    (L : Set (Word α)) :
    CharacteristicSample
        (correctedConcreteWorkingGrammarHypLanguage
          obs f)
        (correctedConcreteWorkingGrammarLearner
          hα obs f)
        S L ↔
      CharacteristicSample
        (correctedConcreteFiniteObjectHypLanguage
          obs f)
        (correctedConcreteFiniteObjectLearner
          obs f)
        S L := by

  rw [
    correctedConcreteWorkingGrammar_characteristicSample_iff,
    correctedConcreteFiniteObject_characteristicSample_iff
  ]

end CharacteristicSampleTransfer


section StartRootedWorkingGrammarClassTheorem

variable {α : Type u}
variable {M : Type v}
variable [Fintype M]
variable [DecidableEq α]
variable [DecidableEq M]
variable [Monoid M]
variable (hα : Nonempty α)
variable (obs : α → M)
variable (f : Nat)

/-- Every semantic start-rooted target has a finite characteristic sample for
the learner whose outputs are actual `WorkingMCFG` objects. -/
theorem correctedConcreteWorkingGrammarLearner_characteristicSample_for_startRootedTargetClass
    {L : Set (Word α)}
    (hL :
      L ∈ StartRootedCorrectedConcreteTargetClass
        (v := w) α M obs f) :
    ∃ S : Finset (Word α),
      CharacteristicSample
        (correctedConcreteWorkingGrammarHypLanguage
          obs f)
        (correctedConcreteWorkingGrammarLearner
          hα obs f)
        S L := by

  obtain ⟨S, hS⟩ :=
    correctedConcreteCanonicalLearner_characteristicSample_for_startRootedTargetClass
      (v := w) obs f hL

  exact
    ⟨S,
      (correctedConcreteWorkingGrammar_characteristicSample_iff
        hα obs f S L).2 hS⟩

/-- One uniform learner returning actual finite working grammars identifies the
entire semantic start-rooted target class. -/
theorem correctedConcreteWorkingGrammarLearner_identifies_startRootedTargetClass :
    IdentifiesClassFromPositiveData
      (correctedConcreteWorkingGrammarHypLanguage
        obs f)
      (correctedConcreteWorkingGrammarLearner
        hα obs f)
      (StartRootedCorrectedConcreteTargetClass
        (v := w) α M obs f) := by

  intro L hL

  obtain ⟨S, hS⟩ :=
    correctedConcreteWorkingGrammarLearner_characteristicSample_for_startRootedTargetClass
      (v := w) hα obs f hL

  intro T

  exact
    characteristicSample_eventual_correct_on_every_text
      (correctedConcreteWorkingGrammarHypLanguage
        obs f)
      (correctedConcreteWorkingGrammarLearner
        hα obs f)
      S hS T

/-- Expanded positive-text form of the actual-working-grammar class theorem. -/
theorem correctedConcreteWorkingGrammarLearner_identifies_every_startRooted_text :
    ∀ L : Set (Word α),
      L ∈ StartRootedCorrectedConcreteTargetClass
          (v := w) α M obs f →
      ∀ T : TextFor L,
        EventuallyCorrectOnText
          (correctedConcreteWorkingGrammarHypLanguage
            obs f)
          (correctedConcreteWorkingGrammarLearner
            hα obs f)
          T := by

  intro L hL T

  exact
    correctedConcreteWorkingGrammarLearner_identifies_startRootedTargetClass
      (v := w) hα obs f L hL T

end StartRootedWorkingGrammarClassTheorem


section SelectedStageWorkingGrammarExactness

variable {α : Type u}
variable {M : Type v}
variable [Fintype M]
variable [DecidableEq α]
variable [DecidableEq M]
variable [Monoid M]
variable (hα : Nonempty α)
variable (obs : α → M)
variable (f : Nat)

/-- After the selected start-rooted coverage stage, the actual output grammar
has exactly the target string language. -/
theorem correctedConcreteWorkingGrammarLearner_correct_after_startRootedCoverageStage
    {L : Set (Word α)}
    (hL :
      L ∈ StartRootedCorrectedConcreteTargetClass
        (v := w) α M obs f)
    (T : TextFor L)
    {n : Nat}
    (hn :
      startRootedCorrectedConcreteTargetCoverageStage
          (v := w) obs f hL T ≤ n) :
    (correctedConcreteWorkingGrammarLearner
        hα obs f
        (T.prefixSample n)).grammar.StringLanguage =
      L := by

  rw [
    correctedConcreteWorkingGrammarLearner_stringLanguage_eq_corrected
  ]

  exact
    correctedConcreteCanonicalLearner_correct_after_startRootedCoverageStage
      (v := w) obs f hL T hn

/-- At the selected coverage stage itself, the actual output `WorkingMCFG` is
already semantically exact. -/
theorem correctedConcreteWorkingGrammarLearner_correct_at_startRootedCoverageStage
    {L : Set (Word α)}
    (hL :
      L ∈ StartRootedCorrectedConcreteTargetClass
        (v := w) α M obs f)
    (T : TextFor L) :
    (correctedConcreteWorkingGrammarLearner
        hα obs f
        (T.prefixSample
          (startRootedCorrectedConcreteTargetCoverageStage
            (v := w) obs f hL T))).grammar.StringLanguage =
      L := by

  exact
    correctedConcreteWorkingGrammarLearner_correct_after_startRootedCoverageStage
      (v := w) hα obs f hL T
      (Nat.le_refl _)

/-- The actual working-grammar outputs are eventually language constant and
equal to the target. -/
theorem correctedConcreteWorkingGrammarLearner_eventually_language_constant
    {L : Set (Word α)}
    (hL :
      L ∈ StartRootedCorrectedConcreteTargetClass
        (v := w) α M obs f)
    (T : TextFor L) :
    ∃ n0 : Nat,
      ∀ n : Nat, n0 ≤ n →
        (correctedConcreteWorkingGrammarLearner
            hα obs f
            (T.prefixSample n)).grammar.StringLanguage =
          L := by

  refine
    ⟨startRootedCorrectedConcreteTargetCoverageStage
        (v := w) obs f hL T,
      ?_⟩

  intro n hn

  exact
    correctedConcreteWorkingGrammarLearner_correct_after_startRootedCoverageStage
      (v := w) hα obs f hL T hn

end SelectedStageWorkingGrammarExactness


section CompiledWorkingGrammarSize

variable {α : Type u}
variable {M : Type v}
variable [Monoid M]

/-- The source finite-rule object retained by every compiled grammar output
satisfies the explicit paper-facing size bound. -/
theorem correctedConcreteWorkingGrammarLearner_sourceRuleCount_le_explicit_paperPower
    (hα : Nonempty α)
    (obs : α → M)
    (f : Nat)
    (K : Finset (Word α)) :
    (correctedConcreteWorkingGrammarLearner
        hα obs f K).sourceRuleCount ≤
      (4 * (sampleLengthBudget K + f + 1)) ^
        (64 *
          (sampleLengthBudget K + f + 1) *
          (sampleLengthBudget K + f + 1)) := by

  exact
    correctedConcreteFiniteHypothesis_ruleCount_le_explicit_paperPower
      K obs f

/-- The same retained source-rule bound holds at every text prefix. -/
theorem correctedConcreteWorkingGrammarLearner_prefix_sourceRuleCount_le
    {L : Set (Word α)}
    [DecidableEq α]
    (hα : Nonempty α)
    (obs : α → M)
    (f : Nat)
    (T : TextFor L)
    (n : Nat) :
    (correctedConcreteWorkingGrammarLearner
        hα obs f
        (T.prefixSample n)).sourceRuleCount ≤
      (4 *
        (sampleLengthBudget
            (T.prefixSample n) +
          f + 1)) ^
        (64 *
          (sampleLengthBudget
              (T.prefixSample n) +
            f + 1) *
          (sampleLengthBudget
              (T.prefixSample n) +
            f + 1)) := by

  exact
    correctedConcreteWorkingGrammarLearner_sourceRuleCount_le_explicit_paperPower
      hα obs f (T.prefixSample n)

end CompiledWorkingGrammarSize


section FinalWorkingGrammarPackage

variable {α : Type u}
variable {M : Type v}
variable [Fintype M]
variable [DecidableEq α]
variable [DecidableEq M]
variable [Monoid M]
variable (hα : Nonempty α)
variable (obs : α → M)
variable (f : Nat)

/-- Paper-facing endpoint: one target-independent learner returns actual finite
`WorkingMCFG` objects, identifies every semantic start-rooted target, agrees
samplewise with the corrected concrete learner, is consistent and monotone,
and retains the explicit source-rule size bound. -/
theorem correctedConcreteWorkingGrammarLearner_class_conclusion_package :
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
            hα obs f K).sourceRuleCount ≤
          (4 * (sampleLengthBudget K + f + 1)) ^
            (64 *
              (sampleLengthBudget K + f + 1) *
              (sampleLengthBudget K + f + 1))) := by

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
      correctedConcreteWorkingGrammarLearner_sourceRuleCount_le_explicit_paperPower
        hα obs f⟩

/-- Selected-stage version of the final package: after one explicit finite
coverage stage, every actual grammar output is exact and its retained source
rule object satisfies the verified size estimate. -/
theorem correctedConcreteWorkingGrammarLearner_selectedStage_package :
    ∀ L : Set (Word α),
      L ∈ StartRootedCorrectedConcreteTargetClass
          (v := w) α M obs f →
      ∀ T : TextFor L,
        ∃ n0 : Nat,
          ∀ n : Nat, n0 ≤ n →
            (correctedConcreteWorkingGrammarLearner
                hα obs f
                (T.prefixSample n)).grammar.StringLanguage =
              L ∧
            (correctedConcreteWorkingGrammarLearner
                hα obs f
                (T.prefixSample n)).sourceRuleCount ≤
              (4 *
                (sampleLengthBudget
                    (T.prefixSample n) +
                  f + 1)) ^
                (64 *
                  (sampleLengthBudget
                      (T.prefixSample n) +
                    f + 1) *
                  (sampleLengthBudget
                      (T.prefixSample n) +
                    f + 1)) := by

  intro L hL T

  refine
    ⟨startRootedCorrectedConcreteTargetCoverageStage
        (v := w) obs f hL T,
      ?_⟩

  intro n hn

  exact
    ⟨correctedConcreteWorkingGrammarLearner_correct_after_startRootedCoverageStage
        (v := w) hα obs f hL T hn,
      correctedConcreteWorkingGrammarLearner_prefix_sourceRuleCount_le
        hα obs f T n⟩

end FinalWorkingGrammarPackage

end MCFG
