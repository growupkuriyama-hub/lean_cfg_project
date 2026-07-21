/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG.ConcreteCanonicalLearnerWorkingGrammarFiniteCodeUniverse

/-!
# ConcreteCanonicalLearnerWorkingGrammarFiniteDecodedSearch.lean

The preceding file constructs, at every sample-length level `n`, a finite list

```lean
correctedConcreteCompiledGrammarCheckedBitCodeUniverse n f
```

containing every Boolean code whose length is within the final paper-power
budget.

This file runs a fixed checked decoder over that finite code universe.

For an arbitrary decoder

```lean
decode : List Bool → Option β,
```

we define

```lean
successfulDecodePairs decode codes
```

to retain exactly the pairs `(bits, value)` for which

```lean
bits ∈ codes
and
decode bits = some value.
```

The central exact theorem is

```lean
mem_successfulDecodePairs_iff.
```

Thus the resulting list is simultaneously

* sound: every listed value has an accepted source code;
* complete: every accepted source code appears with its decoded value; and
* finite: its length is at most the source-code-list length.

At grammar budget level `(n,f)` we define

```lean
checkedBitDecodedCodeSearch decode n f
checkedBitDecodedValueSearch decode n f.
```

Their lengths are bounded by

```text
2 ^
  (correctedConcreteCompiledGrammarPaperPowerBitBound n f + 1).
```

For a fixed decoder these searches are monotone in the sample-length budget.

## Canonical learner search

For every finite sample `K`, the learner-specific search uses

```lean
correctedConcreteWorkingGrammarLearnerLogarithmicBitDecode hα obs f K
```

over the finite code universe at level `sampleLengthBudget K`.

The actual checked learner code and complete compiled presentation occur in the
search:

```lean
correctedConcreteWorkingGrammarLearner_actualCodePresentation_mem_decodedSearch
correctedConcreteWorkingGrammarLearner_actualPresentation_mem_decodedValueSearch.
```

Every candidate presentation returned by the search comes with a code in the
finite universe that the same learner decoder accepts.

## Target witnesses

Every checked bit-bounded target representation likewise occurs in the finite
decoded search associated with its own decoder.  Hence every semantic
start-rooted target has a finite positive sample, a finite decoded search, and
an accepted pair in that search representing the target's actual bounded
working grammar.

This is a finite exhaustive search theorem relative to a fixed checked decoder.
It does not assert that one global decoder enumerates all target languages.

No target grammar is supplied to the learner.
No `sorry`, `admit`, or `axiom` is used.
-/

namespace MCFG

universe u v w z


section GenericSuccessfulDecoderSearch

variable {β : Type z}

/-- Retain exactly the source-code / decoded-value pairs accepted by a decoder. -/
def successfulDecodePairs
    (decode : List Bool → Option β) :
    List (List Bool) →
      List (List Bool × β)

  | [] =>
      []

  | bits :: codes =>
      match decode bits with

      | none =>
          successfulDecodePairs decode codes

      | some value =>
          (bits, value) ::
            successfulDecodePairs decode codes

/-- Every retained successful pair has a source code in the original code list
and is accepted by the decoder. -/
theorem successfulDecodePairs_sound
    (decode : List Bool → Option β) :
    ∀
      {codes : List (List Bool)}
      {bits : List Bool}
      {value : β},
      (bits, value) ∈
          successfulDecodePairs decode codes →
        bits ∈ codes ∧
          decode bits = some value

  | [], bits, value, hmem => by
      simp [successfulDecodePairs] at hmem

  | code :: codes, bits, value, hmem => by
      cases hdecode :
          decode code with

      | none =>
          have htail :
              (bits, value) ∈
                successfulDecodePairs decode codes := by
            simpa [
              successfulDecodePairs,
              hdecode
            ] using hmem

          rcases
              successfulDecodePairs_sound
                decode htail with
            ⟨hbits, haccepted⟩

          exact
            ⟨by
                exact List.mem_cons_of_mem code hbits,
              haccepted⟩

      | some decoded =>
          have hcases :
              (bits, value) = (code, decoded) ∨
                (bits, value) ∈
                  successfulDecodePairs decode codes := by
            simpa [
              successfulDecodePairs,
              hdecode
            ] using hmem

          rcases hcases with
            hhead | htail

          · cases hhead

            exact
              ⟨by simp,
                hdecode⟩

          · rcases
                successfulDecodePairs_sound
                  decode htail with
              ⟨hbits, haccepted⟩

            exact
              ⟨by
                  exact List.mem_cons_of_mem code hbits,
                haccepted⟩

/-- Every source code accepted by the decoder contributes its successful pair
to the retained search list. -/
theorem successfulDecodePairs_complete
    (decode : List Bool → Option β) :
    ∀
      {codes : List (List Bool)}
      {bits : List Bool}
      {value : β},
      bits ∈ codes →
        decode bits = some value →
          (bits, value) ∈
            successfulDecodePairs decode codes

  | [], bits, value, hbits, hdecode => by
      simp at hbits

  | code :: codes, bits, value, hbits, hdecode => by
      rcases List.mem_cons.mp hbits with
        hhead | htail

      · subst bits

        simp [
          successfulDecodePairs,
          hdecode
        ]

      · cases hcode :
          decode code with

        | none =>
            have hrecursive :
                (bits, value) ∈
                  successfulDecodePairs decode codes :=
              successfulDecodePairs_complete
                decode htail hdecode

            simpa [
              successfulDecodePairs,
              hcode
            ] using hrecursive

        | some decoded =>
            have hrecursive :
                (bits, value) ∈
                  successfulDecodePairs decode codes :=
              successfulDecodePairs_complete
                decode htail hdecode

            exact
              List.mem_cons_of_mem
                (code, decoded)
                (by
                  simpa [
                    successfulDecodePairs,
                    hcode
                  ] using hrecursive)

/-- Exact successful-pair characterization. -/
@[simp] theorem mem_successfulDecodePairs_iff
    (decode : List Bool → Option β)
    (codes : List (List Bool))
    (bits : List Bool)
    (value : β) :
    (bits, value) ∈
        successfulDecodePairs decode codes ↔
      bits ∈ codes ∧
        decode bits = some value := by

  exact
    ⟨successfulDecodePairs_sound decode,
      fun h =>
        successfulDecodePairs_complete
          decode h.1 h.2⟩

/-- Running a decoder over a finite code list never creates more successful
pairs than source codes. -/
theorem successfulDecodePairs_length_le
    (decode : List Bool → Option β) :
    ∀ codes : List (List Bool),
      (successfulDecodePairs decode codes).length <=
        codes.length

  | [] => by
      simp [successfulDecodePairs]

  | code :: codes => by
      cases hdecode :
          decode code with

      | none =>
          have ih :=
            successfulDecodePairs_length_le
              decode codes

          simpa [
            successfulDecodePairs,
            hdecode
          ] using
            ih.trans
              (Nat.le_succ
                codes.length)

      | some value =>
          have ih :=
            successfulDecodePairs_length_le
              decode codes

          simp [
            successfulDecodePairs,
            hdecode
          ]

          exact
            Nat.succ_le_succ ih

/-- Values appearing in the successful-pair search, with their source codes
forgotten. -/
def successfulDecodedValues
    (decode : List Bool → Option β)
    (codes : List (List Bool)) :
    List β :=
  (successfulDecodePairs decode codes).map
    Prod.snd

/-- Exact value-level characterization: a value appears exactly when some
source code in the finite list decodes to it. -/
@[simp] theorem mem_successfulDecodedValues_iff
    (decode : List Bool → Option β)
    (codes : List (List Bool))
    (value : β) :
    value ∈
        successfulDecodedValues decode codes ↔
      ∃ bits,
        bits ∈ codes ∧
          decode bits = some value := by

  constructor

  · intro hvalue

    rcases List.mem_map.mp hvalue with
      ⟨pair, hpair, hpairValue⟩

    rcases pair with
      ⟨bits, decoded⟩

    simp only [Prod.snd] at hpairValue
    subst decoded

    rcases
        (mem_successfulDecodePairs_iff
          decode codes bits value).mp
          hpair with
      ⟨hbits, hdecode⟩

    exact
      ⟨bits, hbits, hdecode⟩

  · rintro
      ⟨bits, hbits, hdecode⟩

    apply List.mem_map.mpr

    exact
      ⟨(bits, value),
        (mem_successfulDecodePairs_iff
          decode codes bits value).mpr
          ⟨hbits, hdecode⟩,
        rfl⟩

/-- Forgetting source codes cannot increase the search-list length. -/
@[simp] theorem successfulDecodedValues_length
    (decode : List Bool → Option β)
    (codes : List (List Bool)) :
    (successfulDecodedValues decode codes).length =
      (successfulDecodePairs decode codes).length := by

  simp [successfulDecodedValues]

end GenericSuccessfulDecoderSearch


section BudgetedDecodedSearch

variable {β : Type z}

/-- Finite successful code/value search at grammar budget level `(n,f)`. -/
def checkedBitDecodedCodeSearch
    (decode : List Bool → Option β)
    (n f : Nat) :
    List (List Bool × β) :=
  successfulDecodePairs
    decode
    (correctedConcreteCompiledGrammarCheckedBitCodeUniverse
      n f)

/-- Finite decoded-value search at grammar budget level `(n,f)`. -/
def checkedBitDecodedValueSearch
    (decode : List Bool → Option β)
    (n f : Nat) :
    List β :=
  successfulDecodedValues
    decode
    (correctedConcreteCompiledGrammarCheckedBitCodeUniverse
      n f)

/-- Exact successful-pair characterization at a grammar budget level. -/
@[simp] theorem mem_checkedBitDecodedCodeSearch_iff
    (decode : List Bool → Option β)
    (n f : Nat)
    (bits : List Bool)
    (value : β) :
    (bits, value) ∈
        checkedBitDecodedCodeSearch decode n f ↔
      bits ∈
          correctedConcreteCompiledGrammarCheckedBitCodeUniverse
            n f ∧
        decode bits = some value := by

  simp [
    checkedBitDecodedCodeSearch
  ]

/-- Exact decoded-value characterization at a grammar budget level. -/
@[simp] theorem mem_checkedBitDecodedValueSearch_iff
    (decode : List Bool → Option β)
    (n f : Nat)
    (value : β) :
    value ∈
        checkedBitDecodedValueSearch decode n f ↔
      ∃ bits,
        bits ∈
            correctedConcreteCompiledGrammarCheckedBitCodeUniverse
              n f ∧
          decode bits = some value := by

  simp [
    checkedBitDecodedValueSearch
  ]

/-- Successful-pair search size is bounded by the finite source code universe. -/
theorem checkedBitDecodedCodeSearch_length_le_codeUniverse
    (decode : List Bool → Option β)
    (n f : Nat) :
    (checkedBitDecodedCodeSearch
        decode n f).length <=
      (correctedConcreteCompiledGrammarCheckedBitCodeUniverse
        n f).length := by

  exact
    successfulDecodePairs_length_le
      decode
      (correctedConcreteCompiledGrammarCheckedBitCodeUniverse
        n f)

/-- Successful decoded-value search size is bounded by the finite source code
universe. -/
theorem checkedBitDecodedValueSearch_length_le_codeUniverse
    (decode : List Bool → Option β)
    (n f : Nat) :
    (checkedBitDecodedValueSearch
        decode n f).length <=
      (correctedConcreteCompiledGrammarCheckedBitCodeUniverse
        n f).length := by

  rw [
    successfulDecodedValues_length
  ]

  exact
    checkedBitDecodedCodeSearch_length_le_codeUniverse
      decode n f

/-- Successful-pair search size is bounded by the explicit power-set estimate. -/
theorem checkedBitDecodedCodeSearch_length_le_two_pow
    (decode : List Bool → Option β)
    (n f : Nat) :
    (checkedBitDecodedCodeSearch
        decode n f).length <=
      2 ^
        (correctedConcreteCompiledGrammarPaperPowerBitBound
            n f +
          1) := by

  exact
    (checkedBitDecodedCodeSearch_length_le_codeUniverse
        decode n f).trans
      (correctedConcreteCompiledGrammarCheckedBitCodeUniverse_length_le
        n f)

/-- Successful decoded-value search size is bounded by the explicit power-set
estimate. -/
theorem checkedBitDecodedValueSearch_length_le_two_pow
    (decode : List Bool → Option β)
    (n f : Nat) :
    (checkedBitDecodedValueSearch
        decode n f).length <=
      2 ^
        (correctedConcreteCompiledGrammarPaperPowerBitBound
            n f +
          1) := by

  exact
    (checkedBitDecodedValueSearch_length_le_codeUniverse
        decode n f).trans
      (correctedConcreteCompiledGrammarCheckedBitCodeUniverse_length_le
        n f)

/-- For a fixed decoder, successful-pair search membership is monotone in the
sample-length budget. -/
theorem checkedBitDecodedCodeSearch_mem_mono
    (decode : List Bool → Option β)
    {n m f : Nat}
    (hnm : n <= m)
    {bits : List Bool}
    {value : β}
    (hpair :
      (bits, value) ∈
        checkedBitDecodedCodeSearch decode n f) :
    (bits, value) ∈
      checkedBitDecodedCodeSearch decode m f := by

  rcases
      (mem_checkedBitDecodedCodeSearch_iff
        decode n f bits value).mp
        hpair with
    ⟨hbits, hdecode⟩

  exact
    (mem_checkedBitDecodedCodeSearch_iff
      decode m f bits value).mpr
      ⟨correctedConcreteCompiledGrammarCheckedBitCodeUniverse_mem_mono
          hnm hbits,
        hdecode⟩

/-- For a fixed decoder, successful decoded-value search membership is monotone
in the sample-length budget. -/
theorem checkedBitDecodedValueSearch_mem_mono
    (decode : List Bool → Option β)
    {n m f : Nat}
    (hnm : n <= m)
    {value : β}
    (hvalue :
      value ∈
        checkedBitDecodedValueSearch decode n f) :
    value ∈
      checkedBitDecodedValueSearch decode m f := by

  rcases
      (mem_checkedBitDecodedValueSearch_iff
        decode n f value).mp
        hvalue with
    ⟨bits, hbits, hdecode⟩

  exact
    (mem_checkedBitDecodedValueSearch_iff
      decode m f value).mpr
      ⟨bits,
        correctedConcreteCompiledGrammarCheckedBitCodeUniverse_mem_mono
          hnm hbits,
        hdecode⟩

end BudgetedDecodedSearch


section CheckedRepresentationDecodedSearch

variable {α : Type u}

/-- Every checked bit-bounded representation's actual source-code /
presentation pair appears in the finite decoded search for its own decoder. -/
theorem
    CheckedBitBoundedCutCompiledWorkingGrammarRepresentation.actualPair_mem_decodedSearch
    {f n : Nat}
    {L : Set (Word α)}
    (R :
      CheckedBitBoundedCutCompiledWorkingGrammarRepresentation
        (w := w) (z := z) α f n L) :
    (R.bits, R.presentation) ∈
      checkedBitDecodedCodeSearch
        R.decode n f := by

  exact
    (mem_checkedBitDecodedCodeSearch_iff
      R.decode n f
      R.bits R.presentation).mpr
      ⟨R.bits_mem_codeUniverse,
        R.decode_bits⟩

/-- Every checked representation's presentation appears in the finite
decoded-value search for its own decoder. -/
theorem
    CheckedBitBoundedCutCompiledWorkingGrammarRepresentation.presentation_mem_decodedValueSearch
    {f n : Nat}
    {L : Set (Word α)}
    (R :
      CheckedBitBoundedCutCompiledWorkingGrammarRepresentation
        (w := w) (z := z) α f n L) :
    R.presentation ∈
      checkedBitDecodedValueSearch
        R.decode n f := by

  exact
    (mem_checkedBitDecodedValueSearch_iff
      R.decode n f R.presentation).mpr
      ⟨R.bits,
        R.bits_mem_codeUniverse,
        R.decode_bits⟩

/-- Every pair listed in a checked representation's decoded search is certified
by a bounded source code and successful decoding. -/
theorem
    CheckedBitBoundedCutCompiledWorkingGrammarRepresentation.decodedSearch_sound
    {f n : Nat}
    {L : Set (Word α)}
    (R :
      CheckedBitBoundedCutCompiledWorkingGrammarRepresentation
        (w := w) (z := z) α f n L)
    {bits : List Bool}
    {value : R.Presentation}
    (hpair :
      (bits, value) ∈
        checkedBitDecodedCodeSearch
          R.decode n f) :
    bits.length <=
        correctedConcreteCompiledGrammarPaperPowerBitBound
          n f ∧
      R.decode bits = some value := by

  rcases
      (mem_checkedBitDecodedCodeSearch_iff
        R.decode n f bits value).mp
        hpair with
    ⟨hbits, hdecode⟩

  exact
    ⟨(mem_correctedConcreteCompiledGrammarCheckedBitCodeUniverse_iff
        bits n f).mp hbits,
      hdecode⟩

/-- The finite decoded search associated with a checked representation has the
explicit universal size bound. -/
theorem
    CheckedBitBoundedCutCompiledWorkingGrammarRepresentation.decodedSearch_length_le
    {f n : Nat}
    {L : Set (Word α)}
    (R :
      CheckedBitBoundedCutCompiledWorkingGrammarRepresentation
        (w := w) (z := z) α f n L) :
    (checkedBitDecodedCodeSearch
        R.decode n f).length <=
      2 ^
        (correctedConcreteCompiledGrammarPaperPowerBitBound
            n f +
          1) := by

  exact
    checkedBitDecodedCodeSearch_length_le_two_pow
      R.decode n f

end CheckedRepresentationDecodedSearch


section CanonicalLearnerFiniteDecodedSearch

variable {α : Type u}
variable {M : Type v}
variable [Fintype M]
variable [DecidableEq α]
variable [DecidableEq M]
variable [Monoid M]

/-- Finite source-code / complete-presentation search for one canonical learner
sample. -/
noncomputable def
    correctedConcreteWorkingGrammarLearnerDecodedPresentationSearch
    (hα : Nonempty α)
    (obs : α → M)
    (f : Nat)
    (K : Finset (Word α)) :
    List
      (List Bool ×
        List
          (CorrectedConcreteCompiledGrammarPresentationEntry
            (correctedConcreteFiniteHypothesis K obs f))) :=
  checkedBitDecodedCodeSearch
    (correctedConcreteWorkingGrammarLearnerLogarithmicBitDecode
      hα obs f K)
    (sampleLengthBudget K)
    f

/-- Finite decoded complete-presentation search with source codes forgotten. -/
noncomputable def
    correctedConcreteWorkingGrammarLearnerDecodedPresentationValues
    (hα : Nonempty α)
    (obs : α → M)
    (f : Nat)
    (K : Finset (Word α)) :
    List
      (List
        (CorrectedConcreteCompiledGrammarPresentationEntry
          (correctedConcreteFiniteHypothesis K obs f))) :=
  checkedBitDecodedValueSearch
    (correctedConcreteWorkingGrammarLearnerLogarithmicBitDecode
      hα obs f K)
    (sampleLengthBudget K)
    f

/-- Exact characterization of one pair in the learner-specific finite decoded
search. -/
@[simp] theorem
    mem_correctedConcreteWorkingGrammarLearnerDecodedPresentationSearch_iff
    (hα : Nonempty α)
    (obs : α → M)
    (f : Nat)
    (K : Finset (Word α))
    (bits : List Bool)
    (presentation :
      List
        (CorrectedConcreteCompiledGrammarPresentationEntry
          (correctedConcreteFiniteHypothesis K obs f))) :
    (bits, presentation) ∈
        correctedConcreteWorkingGrammarLearnerDecodedPresentationSearch
          hα obs f K ↔
      bits ∈
          correctedConcreteCompiledGrammarCheckedBitCodeUniverse
            (sampleLengthBudget K)
            f ∧
        correctedConcreteWorkingGrammarLearnerLogarithmicBitDecode
            hα obs f K bits =
          some presentation := by

  simp [
    correctedConcreteWorkingGrammarLearnerDecodedPresentationSearch
  ]

/-- Exact characterization of one decoded presentation in the learner-specific
finite value search. -/
@[simp] theorem
    mem_correctedConcreteWorkingGrammarLearnerDecodedPresentationValues_iff
    (hα : Nonempty α)
    (obs : α → M)
    (f : Nat)
    (K : Finset (Word α))
    (presentation :
      List
        (CorrectedConcreteCompiledGrammarPresentationEntry
          (correctedConcreteFiniteHypothesis K obs f))) :
    presentation ∈
        correctedConcreteWorkingGrammarLearnerDecodedPresentationValues
          hα obs f K ↔
      ∃ bits,
        bits ∈
            correctedConcreteCompiledGrammarCheckedBitCodeUniverse
              (sampleLengthBudget K)
              f ∧
          correctedConcreteWorkingGrammarLearnerLogarithmicBitDecode
              hα obs f K bits =
            some presentation := by

  simp [
    correctedConcreteWorkingGrammarLearnerDecodedPresentationValues
  ]

/-- The actual learner code and complete compiled presentation occur together in
the finite decoded search. -/
theorem
    correctedConcreteWorkingGrammarLearner_actualCodePresentation_mem_decodedSearch
    (hα : Nonempty α)
    (obs : α → M)
    (f : Nat)
    (K : Finset (Word α)) :
    (correctedConcreteWorkingGrammarLearnerLogarithmicBitList
        hα obs f K,
      (correctedConcreteFiniteHypothesis K obs f).
        compiledGrammarPresentationEntries
          (Classical.choice hα)) ∈
      correctedConcreteWorkingGrammarLearnerDecodedPresentationSearch
        hα obs f K := by

  exact
    (mem_correctedConcreteWorkingGrammarLearnerDecodedPresentationSearch_iff
      hα obs f K
      (correctedConcreteWorkingGrammarLearnerLogarithmicBitList
        hα obs f K)
      ((correctedConcreteFiniteHypothesis K obs f).
        compiledGrammarPresentationEntries
          (Classical.choice hα))).mpr
      ⟨correctedConcreteWorkingGrammarLearnerLogarithmicBitList_mem_codeUniverse
          hα obs f K,
        correctedConcreteWorkingGrammarLearnerLogarithmicBitDecode_encode
          hα obs f K⟩

/-- The actual complete compiled presentation occurs in the finite decoded-value
search. -/
theorem
    correctedConcreteWorkingGrammarLearner_actualPresentation_mem_decodedValueSearch
    (hα : Nonempty α)
    (obs : α → M)
    (f : Nat)
    (K : Finset (Word α)) :
    (correctedConcreteFiniteHypothesis K obs f).
        compiledGrammarPresentationEntries
          (Classical.choice hα) ∈
      correctedConcreteWorkingGrammarLearnerDecodedPresentationValues
        hα obs f K := by

  exact
    (mem_correctedConcreteWorkingGrammarLearnerDecodedPresentationValues_iff
      hα obs f K
      ((correctedConcreteFiniteHypothesis K obs f).
        compiledGrammarPresentationEntries
          (Classical.choice hα))).mpr
      ⟨correctedConcreteWorkingGrammarLearnerLogarithmicBitList
          hα obs f K,
        correctedConcreteWorkingGrammarLearnerLogarithmicBitList_mem_codeUniverse
          hα obs f K,
        correctedConcreteWorkingGrammarLearnerLogarithmicBitDecode_encode
          hα obs f K⟩

/-- Every candidate pair in the learner-specific search is accepted by the
learner's fixed decoder and uses a code within the paper-power budget. -/
theorem
    correctedConcreteWorkingGrammarLearnerDecodedPresentationSearch_sound
    (hα : Nonempty α)
    (obs : α → M)
    (f : Nat)
    (K : Finset (Word α))
    {bits : List Bool}
    {presentation :
      List
        (CorrectedConcreteCompiledGrammarPresentationEntry
          (correctedConcreteFiniteHypothesis K obs f))}
    (hpair :
      (bits, presentation) ∈
        correctedConcreteWorkingGrammarLearnerDecodedPresentationSearch
          hα obs f K) :
    bits.length <=
        correctedConcreteCompiledGrammarPaperPowerBitBound
          (sampleLengthBudget K)
          f ∧
      correctedConcreteWorkingGrammarLearnerLogarithmicBitDecode
          hα obs f K bits =
        some presentation := by

  rcases
      (mem_correctedConcreteWorkingGrammarLearnerDecodedPresentationSearch_iff
        hα obs f K bits presentation).mp
        hpair with
    ⟨hbits, hdecode⟩

  exact
    ⟨(mem_correctedConcreteCompiledGrammarCheckedBitCodeUniverse_iff
        bits
        (sampleLengthBudget K)
        f).mp
        hbits,
      hdecode⟩

/-- The learner-specific source-code / presentation search is finite with the
explicit universal size estimate. -/
theorem
    correctedConcreteWorkingGrammarLearnerDecodedPresentationSearch_length_le
    (hα : Nonempty α)
    (obs : α → M)
    (f : Nat)
    (K : Finset (Word α)) :
    (correctedConcreteWorkingGrammarLearnerDecodedPresentationSearch
        hα obs f K).length <=
      2 ^
        (correctedConcreteCompiledGrammarPaperPowerBitBound
            (sampleLengthBudget K)
            f +
          1) := by

  exact
    checkedBitDecodedCodeSearch_length_le_two_pow
      (correctedConcreteWorkingGrammarLearnerLogarithmicBitDecode
        hα obs f K)
      (sampleLengthBudget K)
      f

/-- The learner-specific decoded-presentation value search is finite with the
same explicit universal size estimate. -/
theorem
    correctedConcreteWorkingGrammarLearnerDecodedPresentationValues_length_le
    (hα : Nonempty α)
    (obs : α → M)
    (f : Nat)
    (K : Finset (Word α)) :
    (correctedConcreteWorkingGrammarLearnerDecodedPresentationValues
        hα obs f K).length <=
      2 ^
        (correctedConcreteCompiledGrammarPaperPowerBitBound
            (sampleLengthBudget K)
            f +
          1) := by

  exact
    checkedBitDecodedValueSearch_length_le_two_pow
      (correctedConcreteWorkingGrammarLearnerLogarithmicBitDecode
        hα obs f K)
      (sampleLengthBudget K)
      f

/-- Compact finite exhaustive decoded-search package for one learner output. -/
theorem
    correctedConcreteWorkingGrammarLearner_finiteDecodedSearch_package
    (hα : Nonempty α)
    (obs : α → M)
    (f : Nat)
    (K : Finset (Word α)) :
    ((correctedConcreteWorkingGrammarLearnerDecodedPresentationSearch
        hα obs f K).length <=
      2 ^
        (correctedConcreteCompiledGrammarPaperPowerBitBound
            (sampleLengthBudget K)
            f +
          1)) ∧
      ((correctedConcreteWorkingGrammarLearnerLogarithmicBitList
          hα obs f K,
        (correctedConcreteFiniteHypothesis K obs f).
          compiledGrammarPresentationEntries
            (Classical.choice hα)) ∈
        correctedConcreteWorkingGrammarLearnerDecodedPresentationSearch
          hα obs f K) ∧
      (∀
        bits
        presentation,
        (bits, presentation) ∈
            correctedConcreteWorkingGrammarLearnerDecodedPresentationSearch
              hα obs f K →
          bits.length <=
              correctedConcreteCompiledGrammarPaperPowerBitBound
                (sampleLengthBudget K)
                f ∧
            correctedConcreteWorkingGrammarLearnerLogarithmicBitDecode
                hα obs f K bits =
              some presentation) := by

  exact
    ⟨correctedConcreteWorkingGrammarLearnerDecodedPresentationSearch_length_le
        hα obs f K,
      correctedConcreteWorkingGrammarLearner_actualCodePresentation_mem_decodedSearch
        hα obs f K,
      by
        intro bits presentation hpair

        exact
          correctedConcreteWorkingGrammarLearnerDecodedPresentationSearch_sound
            hα obs f K hpair⟩

end CanonicalLearnerFiniteDecodedSearch


section TargetFiniteDecodedSearch

variable {α : Type u}
variable {M : Type v}
variable [Fintype M]
variable [DecidableEq α]
variable [DecidableEq M]
variable [Monoid M]

/-- Every checked bit-bounded target witness's actual code/presentation pair
occurs in the finite decoded search for its stored decoder. -/
theorem
    CorrectedConcreteCheckedBitBoundedWorkingGrammarTargetWitness.actualPair_mem_finiteDecodedSearch
    {hα : Nonempty α}
    {obs : α → M}
    {f : Nat}
    {L : Set (Word α)}
    (W :
      CorrectedConcreteCheckedBitBoundedWorkingGrammarTargetWitness
        hα obs f L) :
    (W.representation.bits,
      W.representation.presentation) ∈
      checkedBitDecodedCodeSearch
        W.representation.decode
        (sampleLengthBudget W.sample)
        f := by

  exact
    W.representation.actualPair_mem_decodedSearch

/-- Every semantic start-rooted target has a finite positive sample and a finite
decoded search containing one accepted target-representation pair. -/
theorem
    startRootedTarget_exists_positive_finiteDecodedSearchWitness
    {L : Set (Word α)}
    (hα : Nonempty α)
    (obs : α → M)
    (f : Nat)
    (hL :
      L ∈ StartRootedCorrectedConcreteTargetClass
        (v := w) α M obs f) :
    ∃
      (S : Finset (Word α))
      (R :
        CheckedBitBoundedCutCompiledWorkingGrammarRepresentation
          (w := max u v)
          (z := max u v)
          α f
          (sampleLengthBudget S)
          L),
      (S : Set (Word α)) ⊆ L ∧
        (R.bits, R.presentation) ∈
          checkedBitDecodedCodeSearch
            R.decode
            (sampleLengthBudget S)
            f ∧
        (checkedBitDecodedCodeSearch
            R.decode
            (sampleLengthBudget S)
            f).length <=
          2 ^
            (correctedConcreteCompiledGrammarPaperPowerBitBound
                (sampleLengthBudget S)
                f +
              1) := by

  rcases
      correctedConcreteWorkingGrammarLearner_exists_checkedBitBoundedTargetWitness
        (v := w) hα obs f hL with
    ⟨W⟩

  exact
    ⟨W.sample,
      W.representation,
      W.sample_positive,
      W.representation.actualPair_mem_decodedSearch,
      W.representation.decodedSearch_length_le⟩

end TargetFiniteDecodedSearch


section FinalFiniteDecodedSearchPackage

variable {α : Type u}
variable {M : Type v}
variable [Fintype M]
variable [DecidableEq α]
variable [DecidableEq M]
variable [Monoid M]
variable (hα : Nonempty α)
variable (obs : α → M)
variable (f : Nat)

/-- Final identification plus finite exhaustive checked-decoder-search package. -/
theorem
    correctedConcreteWorkingGrammarLearner_identification_finiteDecodedSearch_package :
    IdentifiesClassFromPositiveData
        (correctedConcreteWorkingGrammarHypLanguage
          obs f)
        (correctedConcreteWorkingGrammarLearner
          hα obs f)
        (StartRootedCorrectedConcreteTargetClass
          (v := w) α M obs f) ∧
      (∀ K : Finset (Word α),
        (correctedConcreteWorkingGrammarLearnerDecodedPresentationSearch
            hα obs f K).length <=
          2 ^
            (correctedConcreteCompiledGrammarPaperPowerBitBound
                (sampleLengthBudget K)
                f +
              1)) ∧
      (∀ K : Finset (Word α),
        (correctedConcreteWorkingGrammarLearnerLogarithmicBitList
            hα obs f K,
          (correctedConcreteFiniteHypothesis K obs f).
            compiledGrammarPresentationEntries
              (Classical.choice hα)) ∈
          correctedConcreteWorkingGrammarLearnerDecodedPresentationSearch
            hα obs f K) ∧
      (∀ L : Set (Word α),
        L ∈ StartRootedCorrectedConcreteTargetClass
            (v := w) α M obs f →
        ∃
          (S : Finset (Word α))
          (R :
            CheckedBitBoundedCutCompiledWorkingGrammarRepresentation
              (w := max u v)
              (z := max u v)
              α f
              (sampleLengthBudget S)
              L),
          (S : Set (Word α)) ⊆ L ∧
            (R.bits, R.presentation) ∈
              checkedBitDecodedCodeSearch
                R.decode
                (sampleLengthBudget S)
                f ∧
            (checkedBitDecodedCodeSearch
                R.decode
                (sampleLengthBudget S)
                f).length <=
              2 ^
                (correctedConcreteCompiledGrammarPaperPowerBitBound
                    (sampleLengthBudget S)
                    f +
                  1) := by

  exact
    ⟨correctedConcreteWorkingGrammarLearner_identifies_startRootedTargetClass
        (v := w) hα obs f,
      correctedConcreteWorkingGrammarLearnerDecodedPresentationSearch_length_le
        hα obs f,
      correctedConcreteWorkingGrammarLearner_actualCodePresentation_mem_decodedSearch
        hα obs f,
      fun L hL =>
        startRootedTarget_exists_positive_finiteDecodedSearchWitness
          (v := w) hα obs f hL⟩

end FinalFiniteDecodedSearchPackage

end MCFG
