/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG.ConcreteCanonicalLearner

/-!
# TupleOccurrenceEnumerationCompleteness.lean

This file proves completeness of the finite enumerators introduced in
`TupleOccurrences.lean`, up to the explicit word-length bound.

The construction proceeds in layers:

* every fixed-length list over a finite alphabet occurs in `finiteListsOver`;
* every bounded word over a finite alphabet occurs in `finiteWordsUpTo`;
* every tuple whose components occur in a finite word set has a code in
  `finiteTupleCodes`;
* every well-formed named context whose chunks occur in the bounded word set
  occurs in `namedContextCandidates`;
* every bounded tuple occurrence filling to a sample word occurs in
  `tupleOccurrencesUpTo`;
* every bounded `SampleUnitEvidence` is represented by an actual member of
  `concreteUnitRulesUpTo`.

The final function `concreteUnitRuleOfEvidenceUpTo` uses classical choice only
after the corresponding finite-rule existence theorem has been proved.

This file does not yet prove that the chunks and tuple components of an
arbitrary sample occurrence are automatically bounded by
`sampleLengthBudget K`.  That is a separate structural theorem about
`namedFill`; its exact open statement is recorded at the end.
-/

namespace MCFG

universe u v

section FixedLengthListCompleteness

variable {β : Type u}

/-- Canonical fixed-length code of a list. -/
def FiniteListCode.ofList
    (entries : List β) :
    FiniteListCode β entries.length where
  entries := entries
  length_eq := rfl

@[simp] theorem FiniteListCode.ofList_entries
    (entries : List β) :
    (FiniteListCode.ofList entries).entries = entries :=
  rfl

/-- Every list whose entries belong to `A` occurs in the corresponding
fixed-length enumeration. -/
theorem finiteListsOver_complete_ofList
    (A : Finset β)
    (entries : List β)
    (hentries :
      ∀ b ∈ entries, b ∈ A) :
    FiniteListCode.ofList entries ∈
      finiteListsOver A entries.length := by
  classical
  induction entries with
  | nil =>
      simp [FiniteListCode.ofList, finiteListsOver]
  | cons b rest ih =>
      have hb : b ∈ A :=
        hentries b (by simp)
      have hrest :
          ∀ c ∈ rest, c ∈ A := by
        intro c hc
        exact hentries c (by simp [hc])
      have ih' := ih hrest
      apply Finset.mem_image.mpr
      refine
        ⟨(b, FiniteListCode.ofList rest),
          Finset.mem_product.mpr ⟨hb, ih'⟩,
          ?_⟩
      rfl

/-- Completeness for an arbitrary fixed-length code. -/
theorem finiteListsOver_complete
    (A : Finset β)
    {n : Nat}
    (C : FiniteListCode β n)
    (hentries :
      ∀ b ∈ C.entries, b ∈ A) :
    C ∈ finiteListsOver A n := by
  classical
  rcases C with ⟨entries, hlength⟩
  subst n
  simpa [FiniteListCode.ofList] using
    finiteListsOver_complete_ofList
      A entries hentries

end FixedLengthListCompleteness


section BoundedWordCompleteness

variable {α : Type u}

/-- Every word of the stated length over `A` occurs in
`finiteWordsOfLength`. -/
theorem finiteWordsOfLength_complete
    (A : Finset α)
    (word : Word α)
    (n : Nat)
    (hlength : word.length = n)
    (halphabet :
      ∀ a ∈ word, a ∈ A) :
    word ∈ finiteWordsOfLength A n := by
  classical
  let C : FiniteListCode α n :=
    { entries := word
      length_eq := hlength }
  apply Finset.mem_image.mpr
  refine ⟨C, ?_, rfl⟩
  exact finiteListsOver_complete
    A C halphabet

/-- Every word over `A` whose length is at most `bound` occurs in
`finiteWordsUpTo`. -/
theorem finiteWordsUpTo_complete
    (A : Finset α)
    (bound : Nat)
    (word : Word α)
    (hlength : word.length ≤ bound)
    (halphabet :
      ∀ a ∈ word, a ∈ A) :
    word ∈ finiteWordsUpTo A bound := by
  classical
  apply Finset.mem_biUnion.mpr
  refine ⟨word.length, ?_, ?_⟩
  · simp
    omega
  · exact finiteWordsOfLength_complete
      A word word.length rfl halphabet

/-- Every letter of a sample word belongs to the finite sample alphabet. -/
theorem mem_sampleAlphabet_of_mem_word
    (K : Finset (Word α))
    {word : Word α}
    (hword : word ∈ K)
    {a : α}
    (ha : a ∈ word) :
    a ∈ sampleAlphabet K := by
  classical
  simp [sampleAlphabet, hword, ha]

/-- Every sample word uses only letters of the finite sample alphabet. -/
theorem sample_word_alphabet_subset
    (K : Finset (Word α))
    {word : Word α}
    (hword : word ∈ K) :
    ∀ a ∈ word, a ∈ sampleAlphabet K := by
  intro a ha
  exact mem_sampleAlphabet_of_mem_word
    K hword ha

/-- The length of one sample word is bounded by the total sample length. -/
theorem sample_word_length_le_budget
    (K : Finset (Word α))
    {word : Word α}
    (hword : word ∈ K) :
    word.length ≤ sampleLengthBudget K := by
  classical
  unfold sampleLengthBudget
  have hsum :
      (∑ w in K.erase word, w.length) + word.length =
        ∑ w in K, w.length :=
    Finset.sum_erase_add _ hword
  rw [← hsum]
  exact Nat.le_add_left _ _

/-- Every sample word belongs to the default bounded word enumeration. -/
theorem sample_word_mem_sampleBoundedWords
    (K : Finset (Word α))
    {word : Word α}
    (hword : word ∈ K) :
    word ∈ sampleBoundedWords K := by
  exact finiteWordsUpTo_complete
    (sampleAlphabet K)
    (sampleLengthBudget K)
    word
    (sample_word_length_le_budget K hword)
    (sample_word_alphabet_subset K hword)

end BoundedWordCompleteness


section TupleCodeCompleteness

variable {α : Type u}

/-- Canonical fixed-list code of an arity-indexed tuple. -/
noncomputable def tupleCodeOfTuple
    {d : Nat}
    (x : Tuple α d) :
    FiniteListCode (Word α) d where
  entries := List.ofFn x
  length_eq := by simp

@[simp] theorem tupleCodeOfTuple_toTuple
    {d : Nat}
    (x : Tuple α d) :
    (tupleCodeOfTuple x).toTuple = x := by
  funext i
  simp [tupleCodeOfTuple,
    FiniteListCode.toTuple,
    FiniteListCode.toFunction]

/-- The canonical code of a tuple occurs in `finiteTupleCodes` whenever each
tuple component belongs to the finite component-word set. -/
theorem tupleCodeOfTuple_mem
    (W : Finset (Word α))
    {d : Nat}
    (x : Tuple α d)
    (hx :
      ∀ i : Fin d, x i ∈ W) :
    tupleCodeOfTuple x ∈
      finiteTupleCodes W d := by
  classical
  unfold finiteTupleCodes
  apply finiteListsOver_complete
  intro word hword
  change word ∈ List.ofFn x at hword
  rw [List.mem_ofFn] at hword
  rcases hword with ⟨i, rfl⟩
  exact hx i

end TupleCodeCompleteness


section ContextCandidateCompleteness

variable {α : Type u}

/-- Encode the actual chunk list of a named context as a fixed-length code,
given the expected length equation. -/
def namedContextChunksCode
    {d : Nat}
    (c : NamedSentenceContext α d)
    (hchunks : c.1.chunks.length = d + 1) :
    FiniteListCode (Word α) (d + 1) where
  entries := c.1.chunks
  length_eq := hchunks

/-- Encode the actual hole list of a named context as a fixed-length code,
given the expected length equation. -/
def namedContextHolesCode
    {d : Nat}
    (c : NamedSentenceContext α d)
    (hholes : c.1.holes.length = d) :
    FiniteListCode (Fin d) d where
  entries := c.1.holes
  length_eq := hholes

/-- Every well-formed named context whose chunk words occur in the bounded word
enumeration occurs in `namedContextCandidates`.

The length of the hole list is an explicit premise here.  It follows
mathematically from well-formedness (`Nodup` plus coverage of all `Fin d`) and
will be discharged by the subsequent structural context file. -/
theorem namedContextCandidates_complete_of_holesLength
    (A : Finset α)
    (bound d : Nat)
    (c : NamedSentenceContext α d)
    (hholes : c.1.holes.length = d)
    (hchunksBounded :
      ∀ word ∈ c.1.chunks,
        word ∈ finiteWordsUpTo A bound) :
    c ∈ namedContextCandidates A bound d := by
  classical
  have hchunks :
      c.1.chunks.length = d + 1 := by
    rw [c.2.1, hholes]

  let CC :=
    namedContextChunksCode c hchunks
  let HC :=
    namedContextHolesCode c hholes

  have hCC :
      CC ∈ finiteListsOver
        (finiteWordsUpTo A bound) (d + 1) := by
    exact finiteListsOver_complete
      (finiteWordsUpTo A bound)
      CC
      hchunksBounded

  have hHC :
      HC ∈ finiteListsOver
        (Finset.univ : Finset (Fin d)) d := by
    apply finiteListsOver_complete
    intro i hi
    simp

  have hraw :
      c.1 ∈ rawNamedContextCandidates
        A bound d := by
    unfold rawNamedContextCandidates
    apply Finset.mem_image.mpr
    refine
      ⟨(CC, HC),
        Finset.mem_product.mpr ⟨hCC, hHC⟩,
        ?_⟩
    rfl

  unfold namedContextCandidates
  apply Finset.mem_image.mpr
  let rawMember :
      { r : RawNamedSentenceContext α d //
        r ∈
          (rawNamedContextCandidates A bound d).filter
            RawNamedSentenceContext.WellFormed } :=
    ⟨c.1,
      Finset.mem_filter.mpr
        ⟨hraw, c.2⟩⟩
  refine ⟨rawMember, ?_, ?_⟩
  · simp
  · rfl

end ContextCandidateCompleteness


section TupleOccurrenceCompleteness

variable {α : Type u}

/-- Canonical finite occurrence candidate associated with an actual named
context and tuple. -/
noncomputable def tupleOccurrenceCandidateOf
    {d : Nat}
    (c : NamedSentenceContext α d)
    (x : Tuple α d) :
    FiniteTupleOccurrenceCandidate α d where
  context := c
  tupleCode := tupleCodeOfTuple x

@[simp] theorem tupleOccurrenceCandidateOf_context
    {d : Nat}
    (c : NamedSentenceContext α d)
    (x : Tuple α d) :
    (tupleOccurrenceCandidateOf c x).context = c :=
  rfl

@[simp] theorem tupleOccurrenceCandidateOf_tuple
    {d : Nat}
    (c : NamedSentenceContext α d)
    (x : Tuple α d) :
    (tupleOccurrenceCandidateOf c x).tuple = x :=
  tupleCodeOfTuple_toTuple x

@[simp] theorem tupleOccurrenceCandidateOf_word
    {d : Nat}
    (c : NamedSentenceContext α d)
    (x : Tuple α d) :
    (tupleOccurrenceCandidateOf c x).word =
      namedFill d c x := by
  simp [FiniteTupleOccurrenceCandidate.word]

/-- Completeness of the bounded tuple-occurrence enumeration. -/
theorem tupleOccurrenceCandidateOf_mem
    (K : Finset (Word α))
    (d bound : Nat)
    (c : NamedSentenceContext α d)
    (x : Tuple α d)
    (hholes : c.1.holes.length = d)
    (hchunks :
      ∀ word ∈ c.1.chunks,
        word ∈
          finiteWordsUpTo
            (sampleAlphabet K) bound)
    (hcomponents :
      ∀ i : Fin d,
        x i ∈
          finiteWordsUpTo
            (sampleAlphabet K) bound)
    (hfill :
      namedFill d c x ∈ K) :
    tupleOccurrenceCandidateOf c x ∈
      tupleOccurrencesUpTo K d bound := by
  classical
  apply
    (mem_tupleOccurrencesUpTo_iff
      K d bound
      (tupleOccurrenceCandidateOf c x)).2
  constructor
  · unfold tupleOccurrenceCandidatesUpTo
    apply Finset.mem_image.mpr
    refine
      ⟨(c, tupleCodeOfTuple x),
        Finset.mem_product.mpr ⟨?_, ?_⟩,
        rfl⟩
    · exact namedContextCandidates_complete_of_holesLength
        (sampleAlphabet K)
        bound d c hholes hchunks
    · exact tupleCodeOfTuple_mem
        (finiteWordsUpTo
          (sampleAlphabet K) bound)
        x hcomponents
  · simpa using hfill

end TupleOccurrenceCompleteness


section UnitRuleEnumerationCompleteness

variable {α : Type u}
variable {M : Type v} [Monoid M]

/-- Every bounded sample unit-evidence witness is represented by an actual
member of the finite bounded unit-rule enumeration. -/
theorem exists_concreteUnitRuleOfEvidenceUpTo
    (K : Finset (Word α))
    (obs : α → M)
    {d bound : Nat}
    {x y : Tuple α d}
    (U : SampleUnitEvidence K obs x y)
    (hholes :
      U.context.1.holes.length = d)
    (hchunks :
      ∀ word ∈ U.context.1.chunks,
        word ∈
          finiteWordsUpTo
            (sampleAlphabet K) bound)
    (hx :
      ∀ i : Fin d,
        x i ∈
          finiteWordsUpTo
            (sampleAlphabet K) bound)
    (hy :
      ∀ i : Fin d,
        y i ∈
          finiteWordsUpTo
            (sampleAlphabet K) bound) :
    ∃ Q :
        FiniteTupleOccurrenceCandidate α d ×
          FiniteTupleOccurrenceCandidate α d,
      Q ∈ concreteUnitRulesUpTo
          K obs d bound ∧
        Q.1.tuple = x ∧
        Q.2.tuple = y := by
  classical
  let OX :=
    tupleOccurrenceCandidateOf U.context x
  let OY :=
    tupleOccurrenceCandidateOf U.context y

  have hOX :
      OX ∈ tupleOccurrencesUpTo
        K d bound := by
    exact tupleOccurrenceCandidateOf_mem
      K d bound U.context x
      hholes hchunks hx U.left_mem

  have hOY :
      OY ∈ tupleOccurrencesUpTo
        K d bound := by
    exact tupleOccurrenceCandidateOf_mem
      K d bound U.context y
      hholes hchunks hy U.right_mem

  have hQ :
      (OX, OY) ∈ concreteUnitRulesUpTo
        K obs d bound := by
    unfold concreteUnitRulesUpTo
    apply Finset.mem_filter.mpr
    refine
      ⟨Finset.mem_product.mpr
          ⟨hOX, hOY⟩,
        ?_⟩
    refine ⟨rfl, ?_⟩
    simpa [OX, OY] using U.type_eq

  exact
    ⟨(OX, OY), hQ,
      by simp [OX],
      by simp [OY]⟩

/-- Select the concrete bounded unit rule only after its existence has been
proved. -/
noncomputable def concreteUnitRuleOfEvidenceUpTo
    (K : Finset (Word α))
    (obs : α → M)
    {d bound : Nat}
    {x y : Tuple α d}
    (U : SampleUnitEvidence K obs x y)
    (hholes :
      U.context.1.holes.length = d)
    (hchunks :
      ∀ word ∈ U.context.1.chunks,
        word ∈
          finiteWordsUpTo
            (sampleAlphabet K) bound)
    (hx :
      ∀ i : Fin d,
        x i ∈
          finiteWordsUpTo
            (sampleAlphabet K) bound)
    (hy :
      ∀ i : Fin d,
        y i ∈
          finiteWordsUpTo
            (sampleAlphabet K) bound) :
    (concreteUnitRulesUpTo K obs d bound).attach := by
  classical
  let hex :=
    exists_concreteUnitRuleOfEvidenceUpTo
      K obs U hholes hchunks hx hy
  exact
    ⟨Classical.choose hex,
      (Classical.choose_spec hex).1⟩

/-- The selected concrete rule has the original evidence source tuple. -/
theorem concreteUnitRuleOfEvidenceUpTo_source
    (K : Finset (Word α))
    (obs : α → M)
    {d bound : Nat}
    {x y : Tuple α d}
    (U : SampleUnitEvidence K obs x y)
    (hholes :
      U.context.1.holes.length = d)
    (hchunks :
      ∀ word ∈ U.context.1.chunks,
        word ∈
          finiteWordsUpTo
            (sampleAlphabet K) bound)
    (hx :
      ∀ i : Fin d,
        x i ∈
          finiteWordsUpTo
            (sampleAlphabet K) bound)
    (hy :
      ∀ i : Fin d,
        y i ∈
          finiteWordsUpTo
            (sampleAlphabet K) bound) :
    (concreteUnitRuleOfEvidenceUpTo
      K obs U hholes hchunks hx hy).1.1.tuple = x := by
  classical
  exact
    (Classical.choose_spec
      (exists_concreteUnitRuleOfEvidenceUpTo
        K obs U hholes hchunks hx hy)).2.1

/-- The selected concrete rule has the original evidence target tuple. -/
theorem concreteUnitRuleOfEvidenceUpTo_target
    (K : Finset (Word α))
    (obs : α → M)
    {d bound : Nat}
    {x y : Tuple α d}
    (U : SampleUnitEvidence K obs x y)
    (hholes :
      U.context.1.holes.length = d)
    (hchunks :
      ∀ word ∈ U.context.1.chunks,
        word ∈
          finiteWordsUpTo
            (sampleAlphabet K) bound)
    (hx :
      ∀ i : Fin d,
        x i ∈
          finiteWordsUpTo
            (sampleAlphabet K) bound)
    (hy :
      ∀ i : Fin d,
        y i ∈
          finiteWordsUpTo
            (sampleAlphabet K) bound) :
    (concreteUnitRuleOfEvidenceUpTo
      K obs U hholes hchunks hx hy).1.2.tuple = y := by
  classical
  exact
    (Classical.choose_spec
      (exists_concreteUnitRuleOfEvidenceUpTo
        K obs U hholes hchunks hx hy)).2.2

end UnitRuleEnumerationCompleteness


/-!
OPEN GOAL for the next file.

For every well-formed context and every tuple filling that belongs to the
sample, prove the automatic boundedness statements

```lean
theorem wellFormed_holes_length
    {d : Nat}
    (c : NamedSentenceContext α d) :
    c.1.holes.length = d

theorem namedFill_chunk_mem_sampleBoundedWords
    {K : Finset (Word α)}
    {d : Nat}
    (c : NamedSentenceContext α d)
    (x : Tuple α d)
    (hfill : namedFill d c x ∈ K) :
    ∀ word ∈ c.1.chunks,
      word ∈ sampleBoundedWords K

theorem namedFill_component_mem_sampleBoundedWords
    {K : Finset (Word α)}
    {d : Nat}
    (c : NamedSentenceContext α d)
    (x : Tuple α d)
    (hfill : namedFill d c x ∈ K) :
    ∀ i : Fin d,
      x i ∈ sampleBoundedWords K
```

These three theorems remove all boundedness premises from
`concreteUnitRuleOfEvidenceUpTo` and produce the default

```lean
ConcreteUnitRule K obs d
```

for every `SampleUnitEvidence K obs x y`.
-/

end MCFG
