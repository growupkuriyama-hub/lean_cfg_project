/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG.ConcreteLearnerEvidence

/-!
# StartRuleSoundness.lean

Eleventh clean Lean experiment for the fixed-observation MCFG project.

The previous files proved soundness for sample-level learner derivations of
tuples.  This file packages the corresponding string-level statement.

A concrete learner has start rules from sample words.  Abstractly, we model a
string derivation as follows:

* choose a start word `w₀` from the positive sample `K`;
* derive the singleton tuple `(w)` from the singleton tuple `(w₀)` using
  `SampleLearnerDerives`.

The main theorem says that if `K` is positive for a target grammar `G` and the
target language satisfies the fixed-observation promise, then every such
derived string `w` belongs to `G.StringLanguage`.

No theorem here uses `sorry`.
-/

namespace MCFG

universe u v w

section UnaryContexts

variable {α : Type u}

/-- The one-hole identity named sentence context. -/
def unaryIdentityContext : NamedSentenceContext α 1 :=
  ⟨rawTwoSidedAsNamed ([] : Word α) ([] : Word α), by
    refine ⟨?_, ?_, ?_⟩
    · simp [rawTwoSidedAsNamed]
    · simp [rawTwoSidedAsNamed]
    · intro i
      fin_cases i
      simp [rawTwoSidedAsNamed, finOne]⟩

/-- Filling the one-hole identity context by a singleton tuple returns the
underlying word. -/
@[simp] theorem namedFill_unaryIdentityContext (word : Word α) :
    namedFill 1 unaryIdentityContext (singletonTuple word) = word := by
  change rawNamedFill
      (rawTwoSidedAsNamed ([] : Word α) ([] : Word α))
      (singletonTuple word) = word
  simp

/-- If a word belongs to a language, then the singleton tuple is accepted by the
identity named context. -/
theorem unaryIdentityContext_mem_of_word_mem
    {L : Set (Word α)} {word : Word α}
    (hword : word ∈ L) :
    namedFill 1 unaryIdentityContext (singletonTuple word) ∈ L := by
  simpa using hword

/-- Conversely, acceptance of the singleton tuple by the identity context is
word membership. -/
theorem word_mem_of_unaryIdentityContext_mem
    {L : Set (Word α)} {word : Word α}
    (hword : namedFill 1 unaryIdentityContext (singletonTuple word) ∈ L) :
    word ∈ L := by
  simpa using hword

end UnaryContexts


section SampleStringDerivation

variable {α : Type u} {M : Type v} [Monoid M]

/-- String-level sample learner derivation.

The start word is required to be present in the finite sample.  The tuple-level
derivation then starts from the singleton tuple of that sample word. -/
structure SampleStringDerives
    (K : Finset (Word α)) (obs : α → M) (f : Nat)
    (word : Word α) where
  startWord : Word α
  start_mem : startWord ∈ K
  derives : SampleLearnerDerives K obs f
    (singletonTuple startWord)
    (singletonTuple word)

namespace SampleStringDerives

/-- Build a trivial string derivation of any sample word. -/
def of_sample_word
    {K : Finset (Word α)} {obs : α → M} {f : Nat}
    {word : Word α}
    (hword : word ∈ K) :
    SampleStringDerives K obs f word :=
  { startWord := word,
    start_mem := hword,
    derives := SampleLearnerDerives.self (singletonTuple word) }

/-- String-level soundness for sample learner derivations.

If `K` is a positive sample for `G`, then every string derived from a sample
start word belongs to the target string language. -/
theorem sound_for_grammar
    {N : Type w}
    {K : Finset (Word α)} {obs : α → M} {f : Nat}
    (G : WorkingMCFG N α)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage)
    (hK : PositiveSample G K)
    {word : Word α}
    (D : SampleStringDerives K obs f word) :
    word ∈ G.StringLanguage := by
  have hstart :
      namedFill 1 unaryIdentityContext
        (singletonTuple D.startWord) ∈ G.StringLanguage := by
    exact unaryIdentityContext_mem_of_word_mem
      (hK D.startWord D.start_mem)
  have hderived :
      namedFill 1 unaryIdentityContext
        (singletonTuple word) ∈ G.StringLanguage :=
    SampleLearnerDerives.mem_right_for_grammar
      G hL hK D.derives hstart
  exact word_mem_of_unaryIdentityContext_mem hderived

/-- The trivial derivation of a positive sample word is sound. -/
theorem sound_of_sample_word
    {N : Type w}
    {K : Finset (Word α)} {obs : α → M} {f : Nat}
    (G : WorkingMCFG N α)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage)
    (hK : PositiveSample G K)
    {word : Word α}
    (hword : word ∈ K) :
    word ∈ G.StringLanguage :=
  (of_sample_word (K := K) (obs := obs) (f := f) hword).sound_for_grammar
    G hL hK

/-- A string derived from a sample start word has a singleton tuple with the
same observation type as the singleton tuple of the start word. -/
theorem singleton_tupleType_eq_for_grammar
    {N : Type w}
    {K : Finset (Word α)} {obs : α → M} {f : Nat}
    (G : WorkingMCFG N α)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage)
    (hK : PositiveSample G K)
    {word : Word α}
    (D : SampleStringDerives K obs f word) :
    tupleType obs (singletonTuple word) =
      tupleType obs (singletonTuple D.startWord) :=
  SampleLearnerDerives.tupleType_eq_for_grammar
    G hL hK D.derives

end SampleStringDerives

end SampleStringDerivation


section ConcreteSoundnessStatement

variable {N : Type w} {α : Type u} {M : Type v} [Monoid M]

/-- A compact string-level soundness theorem.

This is the current Lean approximation to the paper statement
`L(learner(K)) ⊆ L` for a positive sample `K`, phrased through the abstract
sample derivation relation. -/
theorem sample_string_soundness
    (G : WorkingMCFG N α)
    {K : Finset (Word α)} {obs : α → M} {f : Nat}
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage)
    (hK : PositiveSample G K)
    {word : Word α}
    (D : SampleStringDerives K obs f word) :
    word ∈ G.StringLanguage :=
  D.sound_for_grammar G hL hK

end ConcreteSoundnessStatement

end MCFG
