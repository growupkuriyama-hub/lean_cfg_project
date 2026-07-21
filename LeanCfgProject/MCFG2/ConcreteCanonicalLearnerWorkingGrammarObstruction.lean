/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG.ConcreteCanonicalLearnerFiniteObjectMonotone

/-!
# ConcreteCanonicalLearnerWorkingGrammarObstruction.lean

The natural next goal is to convert the actual finite learner object

```lean
correctedConcreteFiniteHypothesis K obs f
```

into a `WorkingMCFG` with exactly the same string language.

For the present lightweight grammar syntax, that conversion cannot exist
without an additional hypothesis on the terminal alphabet.

Every `DerivesTuple` proof contains a terminal-rule leaf.  Hence every
nonempty `WorkingMCFG` string language forces `Nonempty α`.  By contrast, the
finite-object learner always contains its sample, including the sample
consisting only of the empty word over the empty alphabet.

This file formalizes that obstruction.

Main results:

```lean
DerivesTuple.alphabet_nonempty
WorkingMCFG.stringLanguage_eq_empty_of_isEmpty

CorrectedConcreteFiniteObjectWorkingGrammarRealization
CorrectedConcreteFiniteObjectWorkingGrammarRealization.alphabet_nonempty_of_sample_nonempty

emptySampleWorkingGrammarRealization

emptyAlphabet_epsilonSample_not_represented
no_workingGrammarRealization_emptyAlphabet_epsilonSample.
```

Thus:

* an empty sample is representable by an empty `WorkingMCFG` over every
  alphabet;
* a nonempty sample can be represented only when the terminal alphabet is
  nonempty;
* the fully unconditional conversion theorem is false.

The following construction file may therefore legitimately assume
`[Nonempty α]` or split off the empty-sample case.

No `sorry`, `admit`, or `axiom` is used.
-/

namespace MCFG

universe u v w

section GrammarDerivationsNeedATerminal

variable {N : Type v}
variable {α : Type u}

namespace DerivesTuple

/-- Every grammar derivation contains a terminal-rule leaf and therefore
exhibits an actual terminal symbol. -/
theorem alphabet_nonempty
    {G : WorkingMCFG N α}
    {A : N}
    {x : Tuple α (G.arity A)}
    (h : DerivesTuple G A x) :
    Nonempty α := by
  induction h with

  | terminal hρ hwt =>
      exact ⟨ρ.terminal⟩

  | binary hρ hx hy ihx ihy =>
      exact ihx

  | start hρ hx hwt ih =>
      exact ih

/-- No tuple derivation exists over an empty terminal alphabet. -/
theorem false_of_isEmpty
    [IsEmpty α]
    {G : WorkingMCFG N α}
    {A : N}
    {x : Tuple α (G.arity A)}
    (h : DerivesTuple G A x) :
    False := by
  rcases h.alphabet_nonempty with ⟨a⟩
  exact isEmptyElim a

end DerivesTuple


namespace WorkingMCFG

/-- Every nonempty generated string language forces a nonempty terminal
alphabet. -/
theorem alphabet_nonempty_of_mem_stringLanguage
    (G : WorkingMCFG N α)
    {word : Word α}
    (hword : word ∈ G.StringLanguage) :
    Nonempty α := by
  rcases hword with ⟨hstart, hderives⟩
  exact hderives.alphabet_nonempty

/-- If the terminal alphabet is empty, every working grammar has empty string
language. -/
theorem stringLanguage_eq_empty_of_isEmpty
    [IsEmpty α]
    (G : WorkingMCFG N α) :
    G.StringLanguage = ∅ := by
  ext word
  constructor

  · intro hword
    rcases hword with ⟨hstart, hderives⟩
    exact (hderives.false_of_isEmpty).elim

  · simp

end WorkingMCFG

end GrammarDerivationsNeedATerminal


section CanonicalFiniteObjectContainsItsSample

variable {α : Type u}
variable {M : Type v} [Monoid M]

/-- The actual canonical finite rule object contains every observed sample
word in its listed language. -/
theorem sample_subset_correctedConcreteFiniteHypothesis_language
    (K : Finset (Word α))
    (obs : α → M)
    (f : Nat) :
    (K : Set (Word α)) ⊆
      (correctedConcreteFiniteHypothesis
        K obs f).Language := by
  rw [
    CorrectedConcreteFiniteHypothesis.language_eq_corrected
  ]
  exact
    sample_subset_correctedConcreteCanonicalLearnerLanguage
      K obs f

/-- A nonempty sample gives a nonempty finite-object language. -/
theorem correctedConcreteFiniteHypothesis_language_nonempty_of_sample_nonempty
    (K : Finset (Word α))
    (obs : α → M)
    (f : Nat)
    (hK : K.Nonempty) :
    (correctedConcreteFiniteHypothesis
      K obs f).Language.Nonempty := by
  rcases hK with ⟨word, hword⟩
  exact
    ⟨word,
      sample_subset_correctedConcreteFiniteHypothesis_language
        K obs f hword⟩

end CanonicalFiniteObjectContainsItsSample


section WorkingGrammarRealizationInterface

variable {α : Type u}
variable {M : Type v} [Monoid M]

/-- A genuine `WorkingMCFG` realization of the canonical finite learner object.

The nonterminal type is part of the realization.  The required equality is
with the listed-rule semantics of the actual finite object. -/
structure CorrectedConcreteFiniteObjectWorkingGrammarRealization
    (K : Finset (Word α))
    (obs : α → M)
    (f : Nat) where

  Nonterminal :
    Type w

  grammar :
    WorkingMCFG Nonterminal α

  language_eq :
    grammar.StringLanguage =
      (correctedConcreteFiniteHypothesis
        K obs f).Language

namespace CorrectedConcreteFiniteObjectWorkingGrammarRealization

variable {K : Finset (Word α)}
variable {obs : α → M}
variable {f : Nat}

/-- A realization of a nonempty sample necessarily supplies a terminal
symbol. -/
theorem alphabet_nonempty_of_sample_nonempty
    (R :
      CorrectedConcreteFiniteObjectWorkingGrammarRealization
        (w := w) K obs f)
    (hK : K.Nonempty) :
    Nonempty α := by

  rcases hK with ⟨word, hword⟩

  have hfinite :
      word ∈
        (correctedConcreteFiniteHypothesis
          K obs f).Language :=
    sample_subset_correctedConcreteFiniteHypothesis_language
      K obs f hword

  have hgrammar :
      word ∈ R.grammar.StringLanguage := by
    rw [R.language_eq]
    exact hfinite

  exact
    R.grammar.alphabet_nonempty_of_mem_stringLanguage
      hgrammar

/-- If the alphabet is empty, every realizable sample must itself be empty. -/
theorem sample_eq_empty_of_isEmpty
    [IsEmpty α]
    (R :
      CorrectedConcreteFiniteObjectWorkingGrammarRealization
        (w := w) K obs f) :
    K = ∅ := by
  classical

  by_contra hne

  have hK :
      K.Nonempty :=
    Finset.nonempty_iff_ne_empty.mpr hne

  rcases R.alphabet_nonempty_of_sample_nonempty hK with ⟨a⟩

  exact isEmptyElim a

end CorrectedConcreteFiniteObjectWorkingGrammarRealization

end WorkingGrammarRealizationInterface


section EmptySampleRealization

variable {α : Type u}
variable {M : Type v} [Monoid M]

/-- A concrete working grammar with no rules and therefore empty language. -/
def emptyLanguageWorkingMCFG :
    WorkingMCFG PUnit α where

  start :=
    PUnit.unit

  arity :=
    fun _ => 1

  arity_pos := by
    intro A
    omega

  startRules :=
    []

  terminalRules :=
    []

  binaryRules :=
    []

/-- The rule-free working grammar has no tuple derivations. -/
theorem emptyLanguageWorkingMCFG_no_derives
    {A : PUnit}
    {x : Tuple α (emptyLanguageWorkingMCFG.arity A)}
    (h :
      DerivesTuple
        (emptyLanguageWorkingMCFG (α := α))
        A x) :
    False := by
  induction h with

  | terminal hρ hwt =>
      simp [emptyLanguageWorkingMCFG] at hρ

  | binary hρ hx hy ihx ihy =>
      simp [emptyLanguageWorkingMCFG] at hρ

  | start hρ hx hwt ih =>
      simp [emptyLanguageWorkingMCFG] at hρ

/-- The rule-free working grammar has empty string language. -/
theorem emptyLanguageWorkingMCFG_stringLanguage_eq :
    (emptyLanguageWorkingMCFG (α := α)).StringLanguage =
      ∅ := by
  ext word
  constructor

  · intro hword
    rcases hword with ⟨hstart, hderives⟩
    exact
      (emptyLanguageWorkingMCFG_no_derives
        hderives).elim

  · simp

/-- The corrected concrete learner on the empty sample has empty language. -/
theorem correctedConcreteCanonicalLearnerLanguage_emptySample
    (obs : α → M)
    (f : Nat) :
    CorrectedConcreteCanonicalLearnerLanguage
        (∅ : Finset (Word α)) obs f =
      ∅ := by
  ext word
  constructor

  · intro hword
    rcases hword with
      ⟨startWord, start_mem, derives⟩
    simp at start_mem

  · simp

/-- The actual finite hypothesis object on the empty sample has empty
language. -/
theorem correctedConcreteFiniteHypothesis_language_emptySample
    (obs : α → M)
    (f : Nat) :
    (correctedConcreteFiniteHypothesis
        (∅ : Finset (Word α))
        obs f).Language =
      ∅ := by
  rw [
    CorrectedConcreteFiniteHypothesis.language_eq_corrected,
    correctedConcreteCanonicalLearnerLanguage_emptySample
  ]

/-- Empty samples are genuinely realizable over every terminal alphabet,
including an empty alphabet. -/
noncomputable def emptySampleWorkingGrammarRealization
    (obs : α → M)
    (f : Nat) :
    CorrectedConcreteFiniteObjectWorkingGrammarRealization
      (w := 0)
      (∅ : Finset (Word α))
      obs f where

  Nonterminal :=
    PUnit

  grammar :=
    emptyLanguageWorkingMCFG

  language_eq := by
    rw [
      emptyLanguageWorkingMCFG_stringLanguage_eq,
      correctedConcreteFiniteHypothesis_language_emptySample
    ]

end EmptySampleRealization


section EmptyAlphabetCounterexample

/-- The unique observation map from the empty alphabet to the trivial
monoid. -/
def emptyAlphabetObservation :
    Empty → PUnit :=
  fun a => nomatch a

/-- The one-element sample containing only the empty word over the empty
alphabet. -/
def emptyAlphabetEpsilonSample :
    Finset (Word Empty) :=
  {[]}

/-- The empty word belongs to that sample. -/
@[simp] theorem emptyWord_mem_emptyAlphabetEpsilonSample :
    ([] : Word Empty) ∈
      emptyAlphabetEpsilonSample := by
  simp [emptyAlphabetEpsilonSample]

/-- The finite learner object generates the empty word from the one-element
sample over the empty alphabet. -/
theorem emptyWord_mem_emptyAlphabetFiniteHypothesisLanguage
    (f : Nat) :
    ([] : Word Empty) ∈
      (correctedConcreteFiniteHypothesis
        emptyAlphabetEpsilonSample
        emptyAlphabetObservation
        f).Language := by
  exact
    sample_subset_correctedConcreteFiniteHypothesis_language
      emptyAlphabetEpsilonSample
      emptyAlphabetObservation
      f
      emptyWord_mem_emptyAlphabetEpsilonSample

/-- No working grammar over the empty alphabet can represent the finite learner
on the sample `{ε}`. -/
theorem emptyAlphabet_epsilonSample_not_represented
    {N : Type v}
    (G : WorkingMCFG N Empty)
    (f : Nat) :
    G.StringLanguage ≠
      (correctedConcreteFiniteHypothesis
        emptyAlphabetEpsilonSample
        emptyAlphabetObservation
        f).Language := by

  intro hEq

  have hfinite :
      ([] : Word Empty) ∈
        (correctedConcreteFiniteHypothesis
          emptyAlphabetEpsilonSample
          emptyAlphabetObservation
          f).Language :=
    emptyWord_mem_emptyAlphabetFiniteHypothesisLanguage
      f

  have hgrammar :
      ([] : Word Empty) ∈
        G.StringLanguage := by
    rw [hEq]
    exact hfinite

  rcases hgrammar with ⟨hstart, hderives⟩

  exact hderives.false_of_isEmpty

/-- There is no realization object, with any nonterminal type in universe
`w`, for the empty-alphabet sample `{ε}`. -/
theorem no_workingGrammarRealization_emptyAlphabet_epsilonSample
    (f : Nat) :
    ¬ Nonempty
      (CorrectedConcreteFiniteObjectWorkingGrammarRealization
        (w := w)
        emptyAlphabetEpsilonSample
        emptyAlphabetObservation
        f) := by

  intro hR
  rcases hR with ⟨R⟩

  exact
    emptyAlphabet_epsilonSample_not_represented
      R.grammar f R.language_eq

/-- The fully unconditional realization statement is false already for the
trivial monoid, empty terminal alphabet, and one-word sample `{ε}`. -/
theorem unconditional_workingGrammar_realization_is_false :
    ¬
      (∀ f : Nat,
        Nonempty
          (CorrectedConcreteFiniteObjectWorkingGrammarRealization
            (w := w)
            emptyAlphabetEpsilonSample
            emptyAlphabetObservation
            f)) := by

  intro h
  exact
    no_workingGrammarRealization_emptyAlphabet_epsilonSample
      (w := w) 0
      (h 0)

end EmptyAlphabetCounterexample


section CorrectCompilationDomain

variable {α : Type u}
variable {M : Type v} [Monoid M]

/-- Necessary domain condition for compilation into the present
`WorkingMCFG` syntax: either the sample is empty or the terminal alphabet is
nonempty. -/
def FiniteObjectWorkingGrammarCompilationDomain
    (K : Finset (Word α)) :
    Prop :=
  K = ∅ ∨ Nonempty α

/-- Every genuine working-grammar realization satisfies the necessary
compilation-domain condition. -/
theorem workingGrammarRealization_implies_compilationDomain
    {K : Finset (Word α)}
    {obs : α → M}
    {f : Nat}
    (R :
      CorrectedConcreteFiniteObjectWorkingGrammarRealization
        (w := w) K obs f) :
    FiniteObjectWorkingGrammarCompilationDomain
      K := by
  classical

  by_cases hK : K = ∅

  · exact Or.inl hK

  · exact
      Or.inr
        (R.alphabet_nonempty_of_sample_nonempty
          (Finset.nonempty_iff_ne_empty.mpr hK))

/-- Classical choice converts the mathematically necessary `Nonempty α`
witness into the `Inhabited α` instance needed by the forthcoming dummy-leaf
grammar construction. -/
noncomputable def inhabitedOfNonempty
    (hα : Nonempty α) :
    Inhabited α :=
  ⟨Classical.choice hα⟩

/-- Paper-facing obstruction and corrected-domain package. -/
theorem correctedConcreteFiniteObject_workingGrammar_obstruction_package :
    (∀ (G : WorkingMCFG PUnit Empty) (f : Nat),
      G.StringLanguage ≠
        (correctedConcreteFiniteHypothesis
          emptyAlphabetEpsilonSample
          emptyAlphabetObservation
          f).Language) ∧
    (∀ f : Nat,
      ¬ Nonempty
        (CorrectedConcreteFiniteObjectWorkingGrammarRealization
          (w := w)
          emptyAlphabetEpsilonSample
          emptyAlphabetObservation
          f)) ∧
    (∀ (K : Finset (Word α))
        (obs : α → M)
        (f : Nat),
      K.Nonempty →
      ∀ R :
        CorrectedConcreteFiniteObjectWorkingGrammarRealization
          (w := w) K obs f,
        Nonempty α) ∧
    (∀ (obs : α → M) (f : Nat),
      Nonempty
        (CorrectedConcreteFiniteObjectWorkingGrammarRealization
          (w := 0)
          (∅ : Finset (Word α))
          obs f)) := by

  exact
    ⟨fun G f =>
        emptyAlphabet_epsilonSample_not_represented
          G f,
      no_workingGrammarRealization_emptyAlphabet_epsilonSample
        (w := w),
      fun K obs f hK R =>
        R.alphabet_nonempty_of_sample_nonempty hK,
      fun obs f =>
        ⟨emptySampleWorkingGrammarRealization
          obs f⟩⟩

end CorrectCompilationDomain

end MCFG
