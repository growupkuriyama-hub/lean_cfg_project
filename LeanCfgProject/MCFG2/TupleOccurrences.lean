/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG.ConcreteTypedCharacteristicSample

/-!
# TupleOccurrences.lean

This file begins the concrete canonical learner construction.

For a finite sample `K`, an arity `d`, and a word-length bound, it constructs
actual finite sets of:

* words over the finite alphabet occurring in `K`;
* length-`d` tuple codes;
* well-formed named sentence contexts;
* tuple occurrences whose filling is a word of `K`;
* unit-rule pairs sharing one context and one observation type.

Every enumerated unit-rule pair is converted to the already verified
`SampleUnitEvidence`.

The construction is deliberately finite and target-independent.  It uses only
`K`, `obs`, `d`, and the explicit length bound.  The default occurrence and
unit-rule sets use the total length of the finite sample as their bound.

No target grammar is an input to any definition in this file.
-/

namespace MCFG

universe u v

section FiniteListCodes

variable {β : Type u}

/-- A list together with its statically recorded length. -/
structure FiniteListCode (β : Type u) (n : Nat) where
  entries : List β
  length_eq : entries.length = n

namespace FiniteListCode

/-- Read a fixed-length list as a function on `Fin n`. -/
def toFunction
    {n : Nat}
    (C : FiniteListCode β n) :
    Fin n → β :=
  fun i =>
    C.entries.get
      ⟨i.1, by
        rw [C.length_eq]
        exact i.2⟩

@[simp] theorem toFunction_apply
    {n : Nat}
    (C : FiniteListCode β n)
    (i : Fin n) :
    C.toFunction i =
      C.entries.get
        ⟨i.1, by
          rw [C.length_eq]
          exact i.2⟩ :=
  rfl

end FiniteListCode

/-- Enumerate every length-`n` list over a finite alphabet `A`. -/
noncomputable def finiteListsOver
    (A : Finset β) :
    (n : Nat) → Finset (FiniteListCode β n)
  | 0 => by
      classical
      exact {⟨[], rfl⟩}
  | n + 1 => by
      classical
      exact
        (A.product (finiteListsOver A n)).image
          (fun p =>
            { entries := p.1 :: p.2.entries
              length_eq := by
                simpa [p.2.length_eq] })

/-- Every enumerated fixed-length list has the advertised length. -/
theorem finiteListsOver_length
    (A : Finset β)
    {n : Nat}
    {C : FiniteListCode β n}
    (hC : C ∈ finiteListsOver A n) :
    C.entries.length = n :=
  C.length_eq

end FiniteListCodes


section FiniteWords

variable {α : Type u}

/-- Enumerate all words of exactly length `n` over a finite alphabet. -/
noncomputable def finiteWordsOfLength
    (A : Finset α)
    (n : Nat) :
    Finset (Word α) := by
  classical
  exact
    (finiteListsOver A n).image
      (fun C => C.entries)

/-- Enumerate all words of length at most `bound` over a finite alphabet. -/
noncomputable def finiteWordsUpTo
    (A : Finset α)
    (bound : Nat) :
    Finset (Word α) := by
  classical
  exact
    (Finset.range (bound + 1)).biUnion
      (fun n => finiteWordsOfLength A n)

/-- The finite alphabet actually appearing in a finite sample. -/
noncomputable def sampleAlphabet
    (K : Finset (Word α)) :
    Finset α := by
  classical
  exact K.biUnion (fun word => word.toFinset)

/-- A simple explicit length bound determined only by the finite sample. -/
def sampleLengthBudget
    (K : Finset (Word α)) :
    Nat :=
  ∑ word in K, word.length

/-- The finite set of candidate words used by the default learner
enumeration. -/
noncomputable def sampleBoundedWords
    (K : Finset (Word α)) :
    Finset (Word α) :=
  finiteWordsUpTo
    (sampleAlphabet K)
    (sampleLengthBudget K)

end FiniteWords


section TupleCodes

variable {α : Type u}

/-- Interpret a fixed list of words as an arity-indexed tuple. -/
def FiniteListCode.toTuple
    {d : Nat}
    (C : FiniteListCode (Word α) d) :
    Tuple α d :=
  C.toFunction

/-- Enumerate all arity-`d` tuple codes whose components belong to the finite
word set `W`. -/
noncomputable def finiteTupleCodes
    (W : Finset (Word α))
    (d : Nat) :
    Finset (FiniteListCode (Word α) d) :=
  finiteListsOver W d

end TupleCodes


section ContextCandidates

variable {α : Type u}

/-- Construct a raw named context from fixed-length chunk and hole codes. -/
def rawNamedContextOfCodes
    {d : Nat}
    (chunks : FiniteListCode (Word α) (d + 1))
    (holes : FiniteListCode (Fin d) d) :
    RawNamedSentenceContext α d where
  chunks := chunks.entries
  holes := holes.entries

/-- Enumerate raw named-context candidates whose chunks use words of bounded
length and whose hole list has length exactly `d`. -/
noncomputable def rawNamedContextCandidates
    (A : Finset α)
    (bound d : Nat) :
    Finset (RawNamedSentenceContext α d) := by
  classical
  let W := finiteWordsUpTo A bound
  exact
    ((finiteListsOver W (d + 1)).product
      (finiteListsOver
        (Finset.univ : Finset (Fin d)) d)).image
      (fun p => rawNamedContextOfCodes p.1 p.2)

/-- Enumerate the well-formed named sentence contexts among the raw
candidates. -/
noncomputable def namedContextCandidates
    (A : Finset α)
    (bound d : Nat) :
    Finset (NamedSentenceContext α d) := by
  classical
  let good :=
    (rawNamedContextCandidates A bound d).filter
      RawNamedSentenceContext.WellFormed
  exact
    good.attach.image
      (fun c =>
        ⟨c.1, (Finset.mem_filter.mp c.2).2⟩)

/-- Every enumerated context is well formed by construction. -/
theorem namedContextCandidate_wellFormed
    (A : Finset α)
    (bound d : Nat)
    {c : NamedSentenceContext α d}
    (hc : c ∈ namedContextCandidates A bound d) :
    c.1.WellFormed :=
  c.2

end ContextCandidates


section TupleOccurrences

variable {α : Type u}

/-- A finite-code candidate for one tuple occurrence in a named context. -/
structure FiniteTupleOccurrenceCandidate
    (α : Type u) (d : Nat) where
  context : NamedSentenceContext α d
  tupleCode : FiniteListCode (Word α) d

namespace FiniteTupleOccurrenceCandidate

/-- Tuple represented by an occurrence candidate. -/
def tuple
    {d : Nat}
    (O : FiniteTupleOccurrenceCandidate α d) :
    Tuple α d :=
  O.tupleCode.toTuple

/-- Word obtained by filling the candidate context with the candidate tuple. -/
def word
    {d : Nat}
    (O : FiniteTupleOccurrenceCandidate α d) :
    Word α :=
  namedFill d O.context O.tuple

@[simp] theorem word_eq_fill
    {d : Nat}
    (O : FiniteTupleOccurrenceCandidate α d) :
    O.word = namedFill d O.context O.tuple :=
  rfl

end FiniteTupleOccurrenceCandidate

/-- Enumerate all bounded tuple/context candidates. -/
noncomputable def tupleOccurrenceCandidatesUpTo
    (K : Finset (Word α))
    (d bound : Nat) :
    Finset (FiniteTupleOccurrenceCandidate α d) := by
  classical
  let A := sampleAlphabet K
  let W := finiteWordsUpTo A bound
  exact
    ((namedContextCandidates A bound d).product
      (finiteTupleCodes W d)).image
      (fun p =>
        { context := p.1
          tupleCode := p.2 })

/-- Keep exactly the bounded candidates whose filled word belongs to the
sample. -/
noncomputable def tupleOccurrencesUpTo
    (K : Finset (Word α))
    (d bound : Nat) :
    Finset (FiniteTupleOccurrenceCandidate α d) := by
  classical
  exact
    (tupleOccurrenceCandidatesUpTo K d bound).filter
      (fun O => O.word ∈ K)

/-- Default finite tuple-occurrence enumeration. -/
noncomputable def tupleOccurrences
    (K : Finset (Word α))
    (d : Nat) :
    Finset (FiniteTupleOccurrenceCandidate α d) :=
  tupleOccurrencesUpTo K d (sampleLengthBudget K)

/-- Membership in the bounded occurrence set exposes both candidate
enumeration and sample membership. -/
theorem mem_tupleOccurrencesUpTo_iff
    (K : Finset (Word α))
    (d bound : Nat)
    (O : FiniteTupleOccurrenceCandidate α d) :
    O ∈ tupleOccurrencesUpTo K d bound ↔
      O ∈ tupleOccurrenceCandidatesUpTo K d bound ∧
        O.word ∈ K := by
  classical
  simp [tupleOccurrencesUpTo]

/-- Every enumerated bounded occurrence fills to a sample word. -/
theorem tupleOccurrence_word_mem
    (K : Finset (Word α))
    (d bound : Nat)
    {O : FiniteTupleOccurrenceCandidate α d}
    (hO : O ∈ tupleOccurrencesUpTo K d bound) :
    O.word ∈ K :=
  ((mem_tupleOccurrencesUpTo_iff K d bound O).mp hO).2

/-- Every default occurrence fills to a sample word. -/
theorem tupleOccurrence_word_mem_default
    (K : Finset (Word α))
    (d : Nat)
    {O : FiniteTupleOccurrenceCandidate α d}
    (hO : O ∈ tupleOccurrences K d) :
    O.word ∈ K :=
  tupleOccurrence_word_mem
    K d (sampleLengthBudget K) hO

end TupleOccurrences


section ConcreteUnitRules

variable {α : Type u}
variable {M : Type v} [Monoid M]

/-- Finite bounded unit-rule enumeration.

A rule is a pair of enumerated tuple occurrences with the same named context
and the same componentwise observation type. -/
noncomputable def concreteUnitRulesUpTo
    (K : Finset (Word α))
    (obs : α → M)
    (d bound : Nat) :
    Finset
      (FiniteTupleOccurrenceCandidate α d ×
        FiniteTupleOccurrenceCandidate α d) := by
  classical
  let O := tupleOccurrencesUpTo K d bound
  exact
    (O.product O).filter
      (fun p =>
        p.1.context = p.2.context ∧
          tupleType obs p.1.tuple =
            tupleType obs p.2.tuple)

/-- Default finite unit-rule enumeration. -/
noncomputable def concreteUnitRules
    (K : Finset (Word α))
    (obs : α → M)
    (d : Nat) :
    Finset
      (FiniteTupleOccurrenceCandidate α d ×
        FiniteTupleOccurrenceCandidate α d) :=
  concreteUnitRulesUpTo
    K obs d (sampleLengthBudget K)

/-- Every enumerated bounded unit rule determines valid sample unit
evidence. -/
def sampleUnitEvidenceOfConcreteRuleUpTo
    (K : Finset (Word α))
    (obs : α → M)
    (d bound : Nat)
    (U :
      FiniteTupleOccurrenceCandidate α d ×
        FiniteTupleOccurrenceCandidate α d)
    (hU : U ∈ concreteUnitRulesUpTo K obs d bound) :
    SampleUnitEvidence K obs
      U.1.tuple U.2.tuple := by
  classical
  have hfilter := Finset.mem_filter.mp hU
  have hproduct := Finset.mem_product.mp hfilter.1
  have hleft :
      U.1.word ∈ K :=
    tupleOccurrence_word_mem K d bound hproduct.1
  have hright :
      U.2.word ∈ K :=
    tupleOccurrence_word_mem K d bound hproduct.2
  rcases hfilter.2 with ⟨hcontext, htype⟩
  exact
    { context := U.1.context
      type_eq := htype
      left_mem := by
        exact hleft
      right_mem := by
        change
          namedFill d U.1.context U.2.tuple ∈ K
        rw [hcontext]
        exact hright }

/-- Every default enumerated unit rule determines valid sample unit
evidence. -/
def sampleUnitEvidenceOfConcreteRule
    (K : Finset (Word α))
    (obs : α → M)
    (d : Nat)
    (U :
      FiniteTupleOccurrenceCandidate α d ×
        FiniteTupleOccurrenceCandidate α d)
    (hU : U ∈ concreteUnitRules K obs d) :
    SampleUnitEvidence K obs
      U.1.tuple U.2.tuple :=
  sampleUnitEvidenceOfConcreteRuleUpTo
    K obs d (sampleLengthBudget K) U hU

/-- An enumerated unit rule has two actual sample occurrences, one shared
context, and equal observed tuple types. -/
theorem concreteUnitRule_spec
    (K : Finset (Word α))
    (obs : α → M)
    (d bound : Nat)
    {U :
      FiniteTupleOccurrenceCandidate α d ×
        FiniteTupleOccurrenceCandidate α d}
    (hU : U ∈ concreteUnitRulesUpTo K obs d bound) :
    U.1.word ∈ K ∧
      U.2.word ∈ K ∧
      U.1.context = U.2.context ∧
      tupleType obs U.1.tuple =
        tupleType obs U.2.tuple := by
  classical
  have hfilter := Finset.mem_filter.mp hU
  have hproduct := Finset.mem_product.mp hfilter.1
  exact
    ⟨tupleOccurrence_word_mem K d bound hproduct.1,
      tupleOccurrence_word_mem K d bound hproduct.2,
      hfilter.2.1,
      hfilter.2.2⟩

end ConcreteUnitRules

end MCFG
