/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG.TupleOccurrenceEnumerationCompleteness

/-!
# NamedFillEnumerationBounds.lean

This file discharges the structural boundedness obligations left by
`TupleOccurrenceEnumerationCompleteness.lean`.

For every well-formed named context it proves:

* the hole list has exactly the context arity;
* every terminal chunk occurs inside every filled word;
* every tuple component occurs inside every filled word;
* consequently every chunk and component of a sample occurrence belongs to
  the finite default word enumeration `sampleBoundedWords K`.

The proofs are direct inductions over `fillNamedAux`; no decomposition or
substring object is assumed.

As a result, every arbitrary

```lean
SampleUnitEvidence K obs x y
```

is converted to an actual member of the default finite set

```lean
concreteUnitRules K obs d
```

without any externally supplied length or alphabet bounds.

No `sorry`, `admit`, or `axiom` is used.
-/

namespace MCFG

universe u v

section WellFormedContextCardinality

variable {α : Type u}

/-- A well-formed arity-`d` named context contains exactly `d` holes.

Well-formedness says that the hole list is duplicate-free and contains every
element of `Fin d`; hence its finite set of entries is `univ`. -/
theorem wellFormed_holes_length
    {d : Nat}
    (c : NamedSentenceContext α d) :
    c.1.holes.length = d := by
  classical
  have hset :
      c.1.holes.toFinset =
        (Finset.univ : Finset (Fin d)) := by
    ext i
    simp [c.2.2.2 i]
  calc
    c.1.holes.length =
        c.1.holes.toFinset.card := by
      symm
      exact List.toFinset_card_of_nodup
        c.2.2.1
    _ = (Finset.univ : Finset (Fin d)).card := by
      rw [hset]
    _ = d := by
      simp

/-- A well-formed arity-`d` named context contains exactly `d + 1`
terminal chunks. -/
theorem wellFormed_chunks_length
    {d : Nat}
    (c : NamedSentenceContext α d) :
    c.1.chunks.length = d + 1 := by
  rw [c.2.1, wellFormed_holes_length c]

end WellFormedContextCardinality


section RawFillStructuralBounds

variable {α : Type u}

/-- Every terminal chunk has length at most the length of the filled word,
provided the chunk/hole lengths have the well-formed shape. -/
theorem fillNamedAux_chunk_length_le
    {d : Nat}
    (x : Tuple α d) :
    ∀ {holes : List (Fin d)}
      {chunks : List (Word α)}
      (hlen :
        chunks.length = holes.length + 1)
      {word : Word α},
      word ∈ chunks →
        word.length ≤
          (fillNamedAux x holes chunks).length := by
  intro holes
  induction holes with

  | nil =>
      intro chunks hlen word hword
      cases chunks with
      | nil =>
          simp at hlen
      | cons chunk rest =>
          have hrestLength :
              rest.length = 0 := by
            simp at hlen
            exact hlen
          have hrest :
              rest = [] :=
            List.length_eq_zero.mp hrestLength
          subst rest
          simp only [List.mem_singleton] at hword
          subst word
          simp [fillNamedAux]

  | cons hole holes ih =>
      intro chunks hlen word hword
      cases chunks with
      | nil =>
          simp at hlen
      | cons chunk rest =>
          have hlen' :
              rest.length =
                holes.length + 1 := by
            simp at hlen
            exact hlen
          rcases List.mem_cons.mp hword with
            rfl | hword'
          · simp [fillNamedAux]
          · have htail :
                word.length ≤
                  (fillNamedAux x holes rest).length :=
              ih hlen' hword'
            simp only [fillNamedAux,
              List.length_append]
            omega

/-- Every letter of a terminal chunk occurs in the filled word, provided the
chunk/hole lengths have the well-formed shape. -/
theorem fillNamedAux_mem_of_mem_chunk
    {d : Nat}
    (x : Tuple α d) :
    ∀ {holes : List (Fin d)}
      {chunks : List (Word α)}
      (hlen :
        chunks.length = holes.length + 1)
      {word : Word α}
      {a : α},
      word ∈ chunks →
      a ∈ word →
        a ∈ fillNamedAux x holes chunks := by
  intro holes
  induction holes with

  | nil =>
      intro chunks hlen word a hword ha
      cases chunks with
      | nil =>
          simp at hlen
      | cons chunk rest =>
          have hrestLength :
              rest.length = 0 := by
            simp at hlen
            exact hlen
          have hrest :
              rest = [] :=
            List.length_eq_zero.mp hrestLength
          subst rest
          simp only [List.mem_singleton] at hword
          subst word
          simpa [fillNamedAux] using ha

  | cons hole holes ih =>
      intro chunks hlen word a hword ha
      cases chunks with
      | nil =>
          simp at hlen
      | cons chunk rest =>
          have hlen' :
              rest.length =
                holes.length + 1 := by
            simp at hlen
            exact hlen
          rcases List.mem_cons.mp hword with
            rfl | hword'
          · simp [fillNamedAux, ha]
          · have htail :
                a ∈ fillNamedAux x holes rest :=
              ih hlen' hword' ha
            simp [fillNamedAux, htail]

/-- Every tuple component whose name occurs in the hole list has length at most
the length of the filled word. -/
theorem fillNamedAux_component_length_le
    {d : Nat}
    (x : Tuple α d) :
    ∀ {holes : List (Fin d)}
      {chunks : List (Word α)}
      (hlen :
        chunks.length = holes.length + 1)
      {i : Fin d},
      i ∈ holes →
        (x i).length ≤
          (fillNamedAux x holes chunks).length := by
  intro holes
  induction holes with

  | nil =>
      intro chunks hlen i hi
      simp at hi

  | cons hole holes ih =>
      intro chunks hlen i hi
      cases chunks with
      | nil =>
          simp at hlen
      | cons chunk rest =>
          have hlen' :
              rest.length =
                holes.length + 1 := by
            simp at hlen
            exact hlen
          rcases List.mem_cons.mp hi with
            rfl | hi'
          · simp [fillNamedAux]
          · have htail :
                (x i).length ≤
                  (fillNamedAux x holes rest).length :=
              ih hlen' hi'
            simp only [fillNamedAux,
              List.length_append]
            omega

/-- Every letter of a tuple component whose name occurs in the hole list
occurs in the filled word. -/
theorem fillNamedAux_mem_of_mem_component
    {d : Nat}
    (x : Tuple α d) :
    ∀ {holes : List (Fin d)}
      {chunks : List (Word α)}
      (hlen :
        chunks.length = holes.length + 1)
      {i : Fin d}
      {a : α},
      i ∈ holes →
      a ∈ x i →
        a ∈ fillNamedAux x holes chunks := by
  intro holes
  induction holes with

  | nil =>
      intro chunks hlen i a hi ha
      simp at hi

  | cons hole holes ih =>
      intro chunks hlen i a hi ha
      cases chunks with
      | nil =>
          simp at hlen
      | cons chunk rest =>
          have hlen' :
              rest.length =
                holes.length + 1 := by
            simp at hlen
            exact hlen
          rcases List.mem_cons.mp hi with
            rfl | hi'
          · simp [fillNamedAux, ha]
          · have htail :
                a ∈ fillNamedAux x holes rest :=
              ih hlen' hi' ha
            simp [fillNamedAux, htail]

end RawFillStructuralBounds


section NamedFillStructuralBounds

variable {α : Type u}

/-- Every chunk of a well-formed named context has length at most its filled
word. -/
theorem namedFill_chunk_length_le
    {d : Nat}
    (c : NamedSentenceContext α d)
    (x : Tuple α d)
    {word : Word α}
    (hword : word ∈ c.1.chunks) :
    word.length ≤
      (namedFill d c x).length := by
  simpa [namedFill, rawNamedFill] using
    fillNamedAux_chunk_length_le
      x c.2.1 hword

/-- Every letter of every context chunk occurs in the filled word. -/
theorem namedFill_mem_of_mem_chunk
    {d : Nat}
    (c : NamedSentenceContext α d)
    (x : Tuple α d)
    {word : Word α}
    {a : α}
    (hword : word ∈ c.1.chunks)
    (ha : a ∈ word) :
    a ∈ namedFill d c x := by
  simpa [namedFill, rawNamedFill] using
    fillNamedAux_mem_of_mem_chunk
      x c.2.1 hword ha

/-- Every tuple component of a well-formed named context has length at most
the filled word. -/
theorem namedFill_component_length_le
    {d : Nat}
    (c : NamedSentenceContext α d)
    (x : Tuple α d)
    (i : Fin d) :
    (x i).length ≤
      (namedFill d c x).length := by
  simpa [namedFill, rawNamedFill] using
    fillNamedAux_component_length_le
      x c.2.1 (c.2.2.2 i)

/-- Every letter of every tuple component occurs in the filled word. -/
theorem namedFill_mem_of_mem_component
    {d : Nat}
    (c : NamedSentenceContext α d)
    (x : Tuple α d)
    (i : Fin d)
    {a : α}
    (ha : a ∈ x i) :
    a ∈ namedFill d c x := by
  simpa [namedFill, rawNamedFill] using
    fillNamedAux_mem_of_mem_component
      x c.2.1 (c.2.2.2 i) ha

end NamedFillStructuralBounds


section AutomaticSampleBounds

variable {α : Type u}

/-- Every context chunk of a sample occurrence belongs to the default finite
sample-bounded word enumeration. -/
theorem namedFill_chunk_mem_sampleBoundedWords
    {K : Finset (Word α)}
    {d : Nat}
    (c : NamedSentenceContext α d)
    (x : Tuple α d)
    (hfill : namedFill d c x ∈ K) :
    ∀ word ∈ c.1.chunks,
      word ∈ sampleBoundedWords K := by
  intro word hword
  unfold sampleBoundedWords
  apply finiteWordsUpTo_complete
  · exact
      (namedFill_chunk_length_le
        c x hword).trans
        (sample_word_length_le_budget
          K hfill)
  · intro a ha
    exact mem_sampleAlphabet_of_mem_word
      K hfill
      (namedFill_mem_of_mem_chunk
        c x hword ha)

/-- Every tuple component of a sample occurrence belongs to the default finite
sample-bounded word enumeration. -/
theorem namedFill_component_mem_sampleBoundedWords
    {K : Finset (Word α)}
    {d : Nat}
    (c : NamedSentenceContext α d)
    (x : Tuple α d)
    (hfill : namedFill d c x ∈ K) :
    ∀ i : Fin d,
      x i ∈ sampleBoundedWords K := by
  intro i
  unfold sampleBoundedWords
  apply finiteWordsUpTo_complete
  · exact
      (namedFill_component_length_le
        c x i).trans
        (sample_word_length_le_budget
          K hfill)
  · intro a ha
    exact mem_sampleAlphabet_of_mem_word
      K hfill
      (namedFill_mem_of_mem_component
        c x i ha)

/-- Every actual sample occurrence is present in the default finite occurrence
enumeration. -/
theorem tupleOccurrenceCandidateOf_mem_default
    (K : Finset (Word α))
    {d : Nat}
    (c : NamedSentenceContext α d)
    (x : Tuple α d)
    (hfill : namedFill d c x ∈ K) :
    tupleOccurrenceCandidateOf c x ∈
      tupleOccurrences K d := by
  unfold tupleOccurrences
  exact tupleOccurrenceCandidateOf_mem
    K d (sampleLengthBudget K)
    c x
    (wellFormed_holes_length c)
    (by
      simpa [sampleBoundedWords] using
        namedFill_chunk_mem_sampleBoundedWords
          c x hfill)
    (by
      simpa [sampleBoundedWords] using
        namedFill_component_mem_sampleBoundedWords
          c x hfill)
    hfill

end AutomaticSampleBounds


section DefaultUnitRuleCompleteness

variable {α : Type u}
variable {M : Type v} [Monoid M]

/-- Every `SampleUnitEvidence` is represented by an actual member of the
default finite unit-rule set. -/
theorem exists_concreteUnitRuleOfEvidence
    (K : Finset (Word α))
    (obs : α → M)
    {d : Nat}
    {x y : Tuple α d}
    (U : SampleUnitEvidence K obs x y) :
    ∃ Q :
        FiniteTupleOccurrenceCandidate α d ×
          FiniteTupleOccurrenceCandidate α d,
      Q ∈ concreteUnitRules K obs d ∧
        Q.1.tuple = x ∧
        Q.2.tuple = y := by
  unfold concreteUnitRules
  exact exists_concreteUnitRuleOfEvidenceUpTo
    K obs U
    (wellFormed_holes_length U.context)
    (by
      simpa [sampleBoundedWords] using
        namedFill_chunk_mem_sampleBoundedWords
          U.context x U.left_mem)
    (by
      simpa [sampleBoundedWords] using
        namedFill_component_mem_sampleBoundedWords
          U.context x U.left_mem)
    (by
      simpa [sampleBoundedWords] using
        namedFill_component_mem_sampleBoundedWords
          U.context y U.right_mem)

/-- Select the concrete finite unit rule corresponding to arbitrary sample
unit evidence.  Choice is used only after
`exists_concreteUnitRuleOfEvidence` has proved existence. -/
noncomputable def concreteUnitRuleOfEvidence
    (K : Finset (Word α))
    (obs : α → M)
    {d : Nat}
    {x y : Tuple α d}
    (U : SampleUnitEvidence K obs x y) :
    ConcreteUnitRule K obs d := by
  classical
  let hex :=
    exists_concreteUnitRuleOfEvidence
      K obs U
  exact
    ⟨Classical.choose hex,
      (Classical.choose_spec hex).1⟩

/-- The selected concrete unit rule has the original evidence source. -/
theorem concreteUnitRuleOfEvidence_source
    (K : Finset (Word α))
    (obs : α → M)
    {d : Nat}
    {x y : Tuple α d}
    (U : SampleUnitEvidence K obs x y) :
    (concreteUnitRuleOfEvidence
      K obs U).source = x := by
  classical
  exact
    (Classical.choose_spec
      (exists_concreteUnitRuleOfEvidence
        K obs U)).2.1

/-- The selected concrete unit rule has the original evidence target. -/
theorem concreteUnitRuleOfEvidence_target
    (K : Finset (Word α))
    (obs : α → M)
    {d : Nat}
    {x y : Tuple α d}
    (U : SampleUnitEvidence K obs x y) :
    (concreteUnitRuleOfEvidence
      K obs U).target = y := by
  classical
  exact
    (Classical.choose_spec
      (exists_concreteUnitRuleOfEvidence
        K obs U)).2.2

/-- Every sample unit-evidence step can now be executed by the concrete
canonical learner. -/
theorem concreteCanonicalLearnerDerives_unit_of_evidence
    (K : Finset (Word α))
    (obs : α → M)
    (f : Nat)
    {d : Nat}
    {x y u : Tuple α d}
    (hd : d ≤ f)
    (hpos : 0 < d)
    (U : SampleUnitEvidence K obs x y)
    (hrest :
      ConcreteCanonicalLearnerDerives
        K obs f y u) :
    ConcreteCanonicalLearnerDerives
      K obs f x u := by
  let Q :=
    concreteUnitRuleOfEvidence K obs U
  have hsource :
      Q.source = x :=
    concreteUnitRuleOfEvidence_source
      K obs U
  have htarget :
      Q.target = y :=
    concreteUnitRuleOfEvidence_target
      K obs U
  rw [← hsource]
  apply ConcreteCanonicalLearnerDerives.unit
    hd hpos Q
  rw [htarget]
  exact hrest

end DefaultUnitRuleCompleteness


/-!
The unit-rule enumeration is now complete.

The remaining binary-rule direction needs the analogous construction for
`SampleBinaryEvidence`.  Before that construction, the default binary template
bound must be enlarged: a template word contains variable atoms in addition to
the terminal material visible in the filled sample word.  A safe bound is

```lean
sampleLengthBudget K + dB + dC
```

rather than `sampleLengthBudget K`.

The next file should introduce that corrected bound, prove completeness of the
finite exact-once template enumeration, and construct

```lean
concreteBinaryRuleOfEvidence :
  SampleBinaryEvidence K parent body x y →
  ConcreteBinaryRule K e dB dC
```

for exact-once bodies.
-/

end MCFG
