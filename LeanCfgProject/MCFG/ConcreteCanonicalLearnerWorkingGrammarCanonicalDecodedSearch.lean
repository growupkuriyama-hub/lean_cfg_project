/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG.ConcreteCanonicalLearnerWorkingGrammarFiniteDecodedSearch

/-!
# ConcreteCanonicalLearnerWorkingGrammarCanonicalDecodedSearch.lean

The preceding file exhaustively runs a fixed checked decoder over the finite
paper-power code universe.  A successful decoder pair only records

```text
decode bits = some presentation.
```

This file adds the converse canonicality check

```text
encode presentation = bits.
```

Thus a retained pair is simultaneously accepted by the decoder and reproduced
by the corresponding encoder.

## Presentation re-encoder

For any list of compiled presentation entries, define its complete logarithmic
bit serialization by

```text
encode the entry count;
encode every length-framed entry as natural fields;
encode the resulting natural list by the binary-tree bit codec.
```

On the actual complete presentation this is definitionally the existing
complete grammar bit serialization.

For any list consisting only of actually stored presentation entries, decoding
the new serialization returns that list.

## Generic canonical decoder search

For arbitrary functions

```lean
encode : β → List Bool
decode : List Bool → Option β,
```

the list

```lean
canonicalDecodePairs encode decode codes
```

retains exactly the triples of properties

```text
bits ∈ codes,
decode bits = some value,
encode value = bits.
```

We prove the exact membership theorem, soundness, completeness, a source-list
length bound, and uniqueness of the canonical source code for one decoded
value.

At grammar budget level `(n,f)` this gives finite canonical code/value searches
whose lengths are bounded by

```text
2 ^
  (correctedConcreteCompiledGrammarPaperPowerBitBound n f + 1).
```

For fixed encoder and decoder, search membership is monotone in `n`.

## Canonical learner search

For a sample `K`, use

```lean
correctedConcreteWorkingGrammarLearnerLogarithmicBitReencode hα obs f K
correctedConcreteWorkingGrammarLearnerLogarithmicBitDecode hα obs f K.
```

The actual learner bit list and complete presentation occur in the canonical
search.  Every retained candidate satisfies both checked decoding and exact
re-encoding, and one presentation has at most one canonical source code.

Along every positive text for a semantic target, after the usual coverage
stage, the finite canonical search contains the exact target learner output at
every later prefix.

This is the normalization layer requested after the finite decoded search.

No target grammar is supplied to the learner.
No `sorry`, `admit`, or `axiom` is used.
-/

namespace MCFG

universe u v w z


section CompletePresentationLogarithmicReencoder

variable {α : Type u}
variable {M : Type v} [Monoid M]
variable {K : Finset (Word α)}
variable {obs : α → M}
variable {f : Nat}

namespace CorrectedConcreteFiniteHypothesis

variable
  (H : CorrectedConcreteFiniteHypothesis K obs f)

/-- Complete logarithmic serialization of an arbitrary ordered list of compiled
presentation entries. -/
noncomputable def encodeCompiledGrammarPresentationLogarithmicBitList
    (dummy : α)
    (entries :
      List
        (CorrectedConcreteCompiledGrammarPresentationEntry H)) :
    List Bool :=
  encodeBinaryTreeNatListBits
    (entries.length ::
      H.encodeCompiledGrammarPresentationEntryStream
        dummy entries)

/-- Every list consisting only of actually stored entries round-trips through
the complete logarithmic presentation encoder and the existing checked grammar
decoder. -/
@[simp] theorem
    decodeCompiledWorkingGrammarLogarithmicBitList_encodePresentation_of_all_mem
    (dummy : α)
    (entries :
      List
        (CorrectedConcreteCompiledGrammarPresentationEntry H))
    (hstored :
      ∀ entry ∈ entries,
        entry ∈
          H.compiledGrammarPresentationEntries dummy) :
    H.decodeCompiledWorkingGrammarLogarithmicBitList dummy
        (H.encodeCompiledGrammarPresentationLogarithmicBitList
          dummy entries) =
      some entries := by

  classical

  unfold
    encodeCompiledGrammarPresentationLogarithmicBitList
    decodeCompiledWorkingGrammarLogarithmicBitList

  rw [
    decodeBinaryTreeNatListBits_encode
  ]

  unfold
    decodeCompiledWorkingGrammarNaturalList

  exact
    H.decodeCompiledGrammarPresentationEntryStreamExact_encode
      dummy entries hstored

/-- Re-encoding the actual complete presentation is exactly the existing
complete grammar logarithmic bit serialization. -/
@[simp] theorem
    encodeCompiledGrammarPresentationLogarithmicBitList_actual
    (dummy : α) :
    H.encodeCompiledGrammarPresentationLogarithmicBitList
        dummy
        (H.compiledGrammarPresentationEntries dummy) =
      H.encodeCompiledWorkingGrammarLogarithmicBitList
        dummy := by

  rfl

/-- The actual presentation is a fixed point of checked decoding followed by
the new presentation re-encoder. -/
theorem
    decode_reencode_actualCompiledGrammarPresentation
    (dummy : α) :
    H.decodeCompiledWorkingGrammarLogarithmicBitList dummy
        (H.encodeCompiledGrammarPresentationLogarithmicBitList
          dummy
          (H.compiledGrammarPresentationEntries dummy)) =
      some
        (H.compiledGrammarPresentationEntries dummy) := by

  exact
    H.decodeCompiledWorkingGrammarLogarithmicBitList_encodePresentation_of_all_mem
      dummy
      (H.compiledGrammarPresentationEntries dummy)
      (by
        intro entry hentry
        exact hentry)

end CorrectedConcreteFiniteHypothesis

end CompletePresentationLogarithmicReencoder


section GenericCanonicalDecoderSearch

variable {β : Type z}

/-- Retain exactly the successful decoder pairs whose decoded value re-encodes
to the original source code. -/
def canonicalDecodePairs
    (encode : β → List Bool)
    (decode : List Bool → Option β) :
    List (List Bool) →
      List (List Bool × β)

  | [] =>
      []

  | bits :: codes =>
      match decode bits with

      | none =>
          canonicalDecodePairs
            encode decode codes

      | some value =>
          if encode value = bits then
            (bits, value) ::
              canonicalDecodePairs
                encode decode codes
          else
            canonicalDecodePairs
              encode decode codes

/-- Every retained canonical pair has a source code in the original list,
decodes successfully, and re-encodes exactly to that source code. -/
theorem canonicalDecodePairs_sound
    (encode : β → List Bool)
    (decode : List Bool → Option β) :
    ∀
      {codes : List (List Bool)}
      {bits : List Bool}
      {value : β},
      (bits, value) ∈
          canonicalDecodePairs encode decode codes →
        bits ∈ codes ∧
          decode bits = some value ∧
          encode value = bits

  | [], bits, value, hmem => by
      simp [canonicalDecodePairs] at hmem

  | code :: codes, bits, value, hmem => by
      cases hdecode :
          decode code with

      | none =>
          have htail :
              (bits, value) ∈
                canonicalDecodePairs
                  encode decode codes := by

            simpa [
              canonicalDecodePairs,
              hdecode
            ] using hmem

          rcases
              canonicalDecodePairs_sound
                encode decode htail with
            ⟨hbits, haccepted, hcanonical⟩

          exact
            ⟨List.mem_cons_of_mem code hbits,
              haccepted,
              hcanonical⟩

      | some decoded =>
          by_cases hcanonical :
              encode decoded = code

          · have hcases :
                (bits, value) = (code, decoded) ∨
                  (bits, value) ∈
                    canonicalDecodePairs
                      encode decode codes := by

              simpa [
                canonicalDecodePairs,
                hdecode,
                hcanonical
              ] using hmem

            rcases hcases with
              hhead | htail

            · cases hhead

              exact
                ⟨by simp,
                  hdecode,
                  hcanonical⟩

            · rcases
                  canonicalDecodePairs_sound
                    encode decode htail with
                ⟨hbits, haccepted, hreencode⟩

              exact
                ⟨List.mem_cons_of_mem code hbits,
                  haccepted,
                  hreencode⟩

          · have htail :
                (bits, value) ∈
                  canonicalDecodePairs
                    encode decode codes := by

              simpa [
                canonicalDecodePairs,
                hdecode,
                hcanonical
              ] using hmem

            rcases
                canonicalDecodePairs_sound
                  encode decode htail with
              ⟨hbits, haccepted, hreencode⟩

            exact
              ⟨List.mem_cons_of_mem code hbits,
                haccepted,
                hreencode⟩

/-- Every source code that decodes successfully and is reproduced by re-encoding
contributes its canonical pair to the retained list. -/
theorem canonicalDecodePairs_complete
    (encode : β → List Bool)
    (decode : List Bool → Option β) :
    ∀
      {codes : List (List Bool)}
      {bits : List Bool}
      {value : β},
      bits ∈ codes →
        decode bits = some value →
          encode value = bits →
            (bits, value) ∈
              canonicalDecodePairs encode decode codes

  | [], bits, value, hbits, hdecode, hcanonical => by
      simp at hbits

  | code :: codes,
      bits,
      value,
      hbits,
      hdecode,
      hcanonical => by

      rcases List.mem_cons.mp hbits with
        hhead | htail

      · subst bits

        simp [
          canonicalDecodePairs,
          hdecode,
          hcanonical
        ]

      · cases hcode :
          decode code with

        | none =>
            have hrecursive :
                (bits, value) ∈
                  canonicalDecodePairs
                    encode decode codes :=
              canonicalDecodePairs_complete
                encode decode
                htail hdecode hcanonical

            simpa [
              canonicalDecodePairs,
              hcode
            ] using hrecursive

        | some decoded =>
            by_cases hcodeCanonical :
                encode decoded = code

            · have hrecursive :
                  (bits, value) ∈
                    canonicalDecodePairs
                      encode decode codes :=
                canonicalDecodePairs_complete
                  encode decode
                  htail hdecode hcanonical

              exact
                List.mem_cons_of_mem
                  (code, decoded)
                  (by
                    simpa [
                      canonicalDecodePairs,
                      hcode,
                      hcodeCanonical
                    ] using hrecursive)

            · have hrecursive :
                  (bits, value) ∈
                    canonicalDecodePairs
                      encode decode codes :=
                canonicalDecodePairs_complete
                  encode decode
                  htail hdecode hcanonical

              simpa [
                canonicalDecodePairs,
                hcode,
                hcodeCanonical
              ] using hrecursive

/-- Exact canonical-pair characterization. -/
@[simp] theorem mem_canonicalDecodePairs_iff
    (encode : β → List Bool)
    (decode : List Bool → Option β)
    (codes : List (List Bool))
    (bits : List Bool)
    (value : β) :
    (bits, value) ∈
        canonicalDecodePairs encode decode codes ↔
      bits ∈ codes ∧
        decode bits = some value ∧
        encode value = bits := by

  exact
    ⟨canonicalDecodePairs_sound
        encode decode,
      fun h =>
        canonicalDecodePairs_complete
          encode decode
          h.1 h.2.1 h.2.2⟩

/-- Canonical filtering never creates more pairs than source codes. -/
theorem canonicalDecodePairs_length_le
    (encode : β → List Bool)
    (decode : List Bool → Option β) :
    ∀ codes : List (List Bool),
      (canonicalDecodePairs
          encode decode codes).length <=
        codes.length

  | [] => by
      simp [canonicalDecodePairs]

  | code :: codes => by
      cases hdecode :
          decode code with

      | none =>
          have ih :=
            canonicalDecodePairs_length_le
              encode decode codes

          simpa [
            canonicalDecodePairs,
            hdecode
          ] using
            ih.trans
              (Nat.le_succ
                codes.length)

      | some value =>
          by_cases hcanonical :
              encode value = code

          · have ih :=
              canonicalDecodePairs_length_le
                encode decode codes

            simp [
              canonicalDecodePairs,
              hdecode,
              hcanonical
            ]

            exact
              Nat.succ_le_succ ih

          · have ih :=
              canonicalDecodePairs_length_le
                encode decode codes

            simpa [
              canonicalDecodePairs,
              hdecode,
              hcanonical
            ] using
              ih.trans
                (Nat.le_succ
                  codes.length)

/-- Canonically decoded values, with their unique canonical source-code field
forgotten. -/
def canonicalDecodedValues
    (encode : β → List Bool)
    (decode : List Bool → Option β)
    (codes : List (List Bool)) :
    List β :=
  (canonicalDecodePairs
      encode decode codes).map
    Prod.snd

/-- Exact value-level canonical-search characterization. -/
@[simp] theorem mem_canonicalDecodedValues_iff
    (encode : β → List Bool)
    (decode : List Bool → Option β)
    (codes : List (List Bool))
    (value : β) :
    value ∈
        canonicalDecodedValues
          encode decode codes ↔
      ∃ bits,
        bits ∈ codes ∧
          decode bits = some value ∧
          encode value = bits := by

  constructor

  · intro hvalue

    rcases List.mem_map.mp hvalue with
      ⟨pair, hpair, hpairValue⟩

    rcases pair with
      ⟨bits, decoded⟩

    simp only [Prod.snd] at hpairValue
    subst decoded

    rcases
        (mem_canonicalDecodePairs_iff
          encode decode codes bits value).mp
          hpair with
      ⟨hbits, hdecode, hcanonical⟩

    exact
      ⟨bits,
        hbits,
        hdecode,
        hcanonical⟩

  · rintro
      ⟨bits,
        hbits,
        hdecode,
        hcanonical⟩

    apply List.mem_map.mpr

    exact
      ⟨(bits, value),
        (mem_canonicalDecodePairs_iff
          encode decode codes bits value).mpr
          ⟨hbits,
            hdecode,
            hcanonical⟩,
        rfl⟩

/-- Forgetting source codes preserves the search-list length. -/
@[simp] theorem canonicalDecodedValues_length
    (encode : β → List Bool)
    (decode : List Bool → Option β)
    (codes : List (List Bool)) :
    (canonicalDecodedValues
        encode decode codes).length =
      (canonicalDecodePairs
        encode decode codes).length := by

  simp [canonicalDecodedValues]

/-- A canonical pair is a decoder fixed point after re-encoding. -/
theorem decode_encode_eq_of_mem_canonicalDecodePairs
    (encode : β → List Bool)
    (decode : List Bool → Option β)
    (codes : List (List Bool))
    {bits : List Bool}
    {value : β}
    (hpair :
      (bits, value) ∈
        canonicalDecodePairs
          encode decode codes) :
    decode (encode value) =
      some value := by

  rcases
      (mem_canonicalDecodePairs_iff
        encode decode codes bits value).mp
        hpair with
    ⟨hbits, hdecode, hcanonical⟩

  rw [hcanonical]

  exact hdecode

/-- One decoded value has at most one canonical source code. -/
theorem canonicalDecodePairs_code_unique
    (encode : β → List Bool)
    (decode : List Bool → Option β)
    (codes : List (List Bool))
    {bits₁ bits₂ : List Bool}
    {value : β}
    (h₁ :
      (bits₁, value) ∈
        canonicalDecodePairs
          encode decode codes)
    (h₂ :
      (bits₂, value) ∈
        canonicalDecodePairs
          encode decode codes) :
    bits₁ = bits₂ := by

  have hencode₁ :
      encode value = bits₁ :=
    ((mem_canonicalDecodePairs_iff
      encode decode codes bits₁ value).mp
      h₁).2.2

  have hencode₂ :
      encode value = bits₂ :=
    ((mem_canonicalDecodePairs_iff
      encode decode codes bits₂ value).mp
      h₂).2.2

  exact
    hencode₁.symm.trans
      hencode₂

/-- One source code cannot canonically decode to two different values. -/
theorem canonicalDecodePairs_value_unique
    (encode : β → List Bool)
    (decode : List Bool → Option β)
    (codes : List (List Bool))
    {bits : List Bool}
    {value₁ value₂ : β}
    (h₁ :
      (bits, value₁) ∈
        canonicalDecodePairs
          encode decode codes)
    (h₂ :
      (bits, value₂) ∈
        canonicalDecodePairs
          encode decode codes) :
    value₁ = value₂ := by

  have hdecode₁ :
      decode bits = some value₁ :=
    ((mem_canonicalDecodePairs_iff
      encode decode codes bits value₁).mp
      h₁).2.1

  have hdecode₂ :
      decode bits = some value₂ :=
    ((mem_canonicalDecodePairs_iff
      encode decode codes bits value₂).mp
      h₂).2.1

  rw [hdecode₂] at hdecode₁

  injection hdecode₁

end GenericCanonicalDecoderSearch


section BudgetedCanonicalDecodedSearch

variable {β : Type z}

/-- Finite canonical source-code / decoded-value search at budget level
`(n,f)`. -/
def checkedBitCanonicalDecodedCodeSearch
    (encode : β → List Bool)
    (decode : List Bool → Option β)
    (n f : Nat) :
    List (List Bool × β) :=
  canonicalDecodePairs
    encode decode
    (correctedConcreteCompiledGrammarCheckedBitCodeUniverse
      n f)

/-- Finite canonical decoded-value search at budget level `(n,f)`. -/
def checkedBitCanonicalDecodedValueSearch
    (encode : β → List Bool)
    (decode : List Bool → Option β)
    (n f : Nat) :
    List β :=
  canonicalDecodedValues
    encode decode
    (correctedConcreteCompiledGrammarCheckedBitCodeUniverse
      n f)

/-- Exact pair characterization at a grammar budget level. -/
@[simp] theorem
    mem_checkedBitCanonicalDecodedCodeSearch_iff
    (encode : β → List Bool)
    (decode : List Bool → Option β)
    (n f : Nat)
    (bits : List Bool)
    (value : β) :
    (bits, value) ∈
        checkedBitCanonicalDecodedCodeSearch
          encode decode n f ↔
      bits ∈
          correctedConcreteCompiledGrammarCheckedBitCodeUniverse
            n f ∧
        decode bits = some value ∧
        encode value = bits := by

  simp [
    checkedBitCanonicalDecodedCodeSearch
  ]

/-- Exact value characterization at a grammar budget level. -/
@[simp] theorem
    mem_checkedBitCanonicalDecodedValueSearch_iff
    (encode : β → List Bool)
    (decode : List Bool → Option β)
    (n f : Nat)
    (value : β) :
    value ∈
        checkedBitCanonicalDecodedValueSearch
          encode decode n f ↔
      ∃ bits,
        bits ∈
            correctedConcreteCompiledGrammarCheckedBitCodeUniverse
              n f ∧
          decode bits = some value ∧
          encode value = bits := by

  simp [
    checkedBitCanonicalDecodedValueSearch
  ]

/-- Canonical pair-search length is bounded by the finite code universe. -/
theorem
    checkedBitCanonicalDecodedCodeSearch_length_le_codeUniverse
    (encode : β → List Bool)
    (decode : List Bool → Option β)
    (n f : Nat) :
    (checkedBitCanonicalDecodedCodeSearch
        encode decode n f).length <=
      (correctedConcreteCompiledGrammarCheckedBitCodeUniverse
        n f).length := by

  exact
    canonicalDecodePairs_length_le
      encode decode
      (correctedConcreteCompiledGrammarCheckedBitCodeUniverse
        n f)

/-- Canonical decoded-value-search length is bounded by the finite code
universe. -/
theorem
    checkedBitCanonicalDecodedValueSearch_length_le_codeUniverse
    (encode : β → List Bool)
    (decode : List Bool → Option β)
    (n f : Nat) :
    (checkedBitCanonicalDecodedValueSearch
        encode decode n f).length <=
      (correctedConcreteCompiledGrammarCheckedBitCodeUniverse
        n f).length := by

  rw [
    canonicalDecodedValues_length
  ]

  exact
    checkedBitCanonicalDecodedCodeSearch_length_le_codeUniverse
      encode decode n f

/-- Canonical pair-search length satisfies the explicit universal estimate. -/
theorem
    checkedBitCanonicalDecodedCodeSearch_length_le_two_pow
    (encode : β → List Bool)
    (decode : List Bool → Option β)
    (n f : Nat) :
    (checkedBitCanonicalDecodedCodeSearch
        encode decode n f).length <=
      2 ^
        (correctedConcreteCompiledGrammarPaperPowerBitBound
            n f +
          1) := by

  exact
    (checkedBitCanonicalDecodedCodeSearch_length_le_codeUniverse
        encode decode n f).trans
      (correctedConcreteCompiledGrammarCheckedBitCodeUniverse_length_le
        n f)

/-- Canonical decoded-value-search length satisfies the explicit universal
estimate. -/
theorem
    checkedBitCanonicalDecodedValueSearch_length_le_two_pow
    (encode : β → List Bool)
    (decode : List Bool → Option β)
    (n f : Nat) :
    (checkedBitCanonicalDecodedValueSearch
        encode decode n f).length <=
      2 ^
        (correctedConcreteCompiledGrammarPaperPowerBitBound
            n f +
          1) := by

  exact
    (checkedBitCanonicalDecodedValueSearch_length_le_codeUniverse
        encode decode n f).trans
      (correctedConcreteCompiledGrammarCheckedBitCodeUniverse_length_le
        n f)

/-- For fixed encoder and decoder, canonical pair-search membership is monotone
in the sample-length budget. -/
theorem checkedBitCanonicalDecodedCodeSearch_mem_mono
    (encode : β → List Bool)
    (decode : List Bool → Option β)
    {n m f : Nat}
    (hnm : n <= m)
    {bits : List Bool}
    {value : β}
    (hpair :
      (bits, value) ∈
        checkedBitCanonicalDecodedCodeSearch
          encode decode n f) :
    (bits, value) ∈
      checkedBitCanonicalDecodedCodeSearch
        encode decode m f := by

  rcases
      (mem_checkedBitCanonicalDecodedCodeSearch_iff
        encode decode n f bits value).mp
        hpair with
    ⟨hbits, hdecode, hcanonical⟩

  exact
    (mem_checkedBitCanonicalDecodedCodeSearch_iff
      encode decode m f bits value).mpr
      ⟨correctedConcreteCompiledGrammarCheckedBitCodeUniverse_mem_mono
          hnm hbits,
        hdecode,
        hcanonical⟩

/-- For fixed encoder and decoder, canonical decoded-value-search membership is
monotone in the sample-length budget. -/
theorem checkedBitCanonicalDecodedValueSearch_mem_mono
    (encode : β → List Bool)
    (decode : List Bool → Option β)
    {n m f : Nat}
    (hnm : n <= m)
    {value : β}
    (hvalue :
      value ∈
        checkedBitCanonicalDecodedValueSearch
          encode decode n f) :
    value ∈
      checkedBitCanonicalDecodedValueSearch
        encode decode m f := by

  rcases
      (mem_checkedBitCanonicalDecodedValueSearch_iff
        encode decode n f value).mp
        hvalue with
    ⟨bits, hbits, hdecode, hcanonical⟩

  exact
    (mem_checkedBitCanonicalDecodedValueSearch_iff
      encode decode m f value).mpr
      ⟨bits,
        correctedConcreteCompiledGrammarCheckedBitCodeUniverse_mem_mono
          hnm hbits,
        hdecode,
        hcanonical⟩

end BudgetedCanonicalDecodedSearch


section CanonicalLearnerPresentationReencoder

variable {α : Type u}
variable {M : Type v}
variable [Fintype M]
variable [DecidableEq α]
variable [DecidableEq M]
variable [Monoid M]

/-- Re-encode one complete presentation candidate using the same dense tables,
dummy terminal, natural framing, and logarithmic bit codec as the actual
learner output. -/
noncomputable def
    correctedConcreteWorkingGrammarLearnerLogarithmicBitReencode
    (hα : Nonempty α)
    (obs : α → M)
    (f : Nat)
    (K : Finset (Word α))
    (presentation :
      List
        (CorrectedConcreteCompiledGrammarPresentationEntry
          (correctedConcreteFiniteHypothesis K obs f))) :
    List Bool :=
  (correctedConcreteFiniteHypothesis K obs f).
    encodeCompiledGrammarPresentationLogarithmicBitList
      (Classical.choice hα)
      presentation

/-- Re-encoding the actual complete learner presentation returns exactly the
actual checked learner bit list. -/
@[simp] theorem
    correctedConcreteWorkingGrammarLearnerLogarithmicBitReencode_actual
    (hα : Nonempty α)
    (obs : α → M)
    (f : Nat)
    (K : Finset (Word α)) :
    correctedConcreteWorkingGrammarLearnerLogarithmicBitReencode
        hα obs f K
        ((correctedConcreteFiniteHypothesis K obs f).
          compiledGrammarPresentationEntries
            (Classical.choice hα)) =
      correctedConcreteWorkingGrammarLearnerLogarithmicBitList
        hα obs f K := by

  exact
    (correctedConcreteFiniteHypothesis K obs f).
      encodeCompiledGrammarPresentationLogarithmicBitList_actual
        (Classical.choice hα)

/-- The actual complete learner presentation is a checked decoder/re-encoder
fixed point. -/
theorem
    correctedConcreteWorkingGrammarLearner_decode_reencode_actual
    (hα : Nonempty α)
    (obs : α → M)
    (f : Nat)
    (K : Finset (Word α)) :
    correctedConcreteWorkingGrammarLearnerLogarithmicBitDecode
        hα obs f K
        (correctedConcreteWorkingGrammarLearnerLogarithmicBitReencode
          hα obs f K
          ((correctedConcreteFiniteHypothesis K obs f).
            compiledGrammarPresentationEntries
              (Classical.choice hα))) =
      some
        ((correctedConcreteFiniteHypothesis K obs f).
          compiledGrammarPresentationEntries
            (Classical.choice hα)) := by

  rw [
    correctedConcreteWorkingGrammarLearnerLogarithmicBitReencode_actual
      hα obs f K
  ]

  exact
    correctedConcreteWorkingGrammarLearnerLogarithmicBitDecode_encode
      hα obs f K

end CanonicalLearnerPresentationReencoder


section CanonicalLearnerDecodedSearch

variable {α : Type u}
variable {M : Type v}
variable [Fintype M]
variable [DecidableEq α]
variable [DecidableEq M]
variable [Monoid M]

/-- Finite canonical source-code / complete-presentation search for one learner
sample. -/
noncomputable def
    correctedConcreteWorkingGrammarLearnerCanonicalDecodedPresentationSearch
    (hα : Nonempty α)
    (obs : α → M)
    (f : Nat)
    (K : Finset (Word α)) :
    List
      (List Bool ×
        List
          (CorrectedConcreteCompiledGrammarPresentationEntry
            (correctedConcreteFiniteHypothesis K obs f))) :=
  checkedBitCanonicalDecodedCodeSearch
    (correctedConcreteWorkingGrammarLearnerLogarithmicBitReencode
      hα obs f K)
    (correctedConcreteWorkingGrammarLearnerLogarithmicBitDecode
      hα obs f K)
    (sampleLengthBudget K)
    f

/-- Finite canonical decoded-presentation search with source codes forgotten. -/
noncomputable def
    correctedConcreteWorkingGrammarLearnerCanonicalDecodedPresentationValues
    (hα : Nonempty α)
    (obs : α → M)
    (f : Nat)
    (K : Finset (Word α)) :
    List
      (List
        (CorrectedConcreteCompiledGrammarPresentationEntry
          (correctedConcreteFiniteHypothesis K obs f))) :=
  checkedBitCanonicalDecodedValueSearch
    (correctedConcreteWorkingGrammarLearnerLogarithmicBitReencode
      hα obs f K)
    (correctedConcreteWorkingGrammarLearnerLogarithmicBitDecode
      hα obs f K)
    (sampleLengthBudget K)
    f

/-- Exact pair characterization in the learner-specific canonical search. -/
@[simp] theorem
    mem_correctedConcreteWorkingGrammarLearnerCanonicalDecodedPresentationSearch_iff
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
        correctedConcreteWorkingGrammarLearnerCanonicalDecodedPresentationSearch
          hα obs f K ↔
      bits ∈
          correctedConcreteCompiledGrammarCheckedBitCodeUniverse
            (sampleLengthBudget K)
            f ∧
        correctedConcreteWorkingGrammarLearnerLogarithmicBitDecode
            hα obs f K bits =
          some presentation ∧
        correctedConcreteWorkingGrammarLearnerLogarithmicBitReencode
            hα obs f K presentation =
          bits := by

  simp [
    correctedConcreteWorkingGrammarLearnerCanonicalDecodedPresentationSearch
  ]

/-- Exact value characterization in the learner-specific canonical search. -/
@[simp] theorem
    mem_correctedConcreteWorkingGrammarLearnerCanonicalDecodedPresentationValues_iff
    (hα : Nonempty α)
    (obs : α → M)
    (f : Nat)
    (K : Finset (Word α))
    (presentation :
      List
        (CorrectedConcreteCompiledGrammarPresentationEntry
          (correctedConcreteFiniteHypothesis K obs f))) :
    presentation ∈
        correctedConcreteWorkingGrammarLearnerCanonicalDecodedPresentationValues
          hα obs f K ↔
      ∃ bits,
        bits ∈
            correctedConcreteCompiledGrammarCheckedBitCodeUniverse
              (sampleLengthBudget K)
              f ∧
          correctedConcreteWorkingGrammarLearnerLogarithmicBitDecode
              hα obs f K bits =
            some presentation ∧
          correctedConcreteWorkingGrammarLearnerLogarithmicBitReencode
              hα obs f K presentation =
            bits := by

  simp [
    correctedConcreteWorkingGrammarLearnerCanonicalDecodedPresentationValues
  ]

/-- The actual learner code and complete actual presentation survive canonical
normalization. -/
theorem
    correctedConcreteWorkingGrammarLearner_actualCodePresentation_mem_canonicalSearch
    (hα : Nonempty α)
    (obs : α → M)
    (f : Nat)
    (K : Finset (Word α)) :
    (correctedConcreteWorkingGrammarLearnerLogarithmicBitList
        hα obs f K,
      (correctedConcreteFiniteHypothesis K obs f).
        compiledGrammarPresentationEntries
          (Classical.choice hα)) ∈
      correctedConcreteWorkingGrammarLearnerCanonicalDecodedPresentationSearch
        hα obs f K := by

  exact
    (mem_correctedConcreteWorkingGrammarLearnerCanonicalDecodedPresentationSearch_iff
      hα obs f K
      (correctedConcreteWorkingGrammarLearnerLogarithmicBitList
        hα obs f K)
      ((correctedConcreteFiniteHypothesis K obs f).
        compiledGrammarPresentationEntries
          (Classical.choice hα))).mpr
      ⟨correctedConcreteWorkingGrammarLearnerLogarithmicBitList_mem_codeUniverse
          hα obs f K,
        correctedConcreteWorkingGrammarLearnerLogarithmicBitDecode_encode
          hα obs f K,
        correctedConcreteWorkingGrammarLearnerLogarithmicBitReencode_actual
          hα obs f K⟩

/-- The actual complete presentation survives in the canonical value search. -/
theorem
    correctedConcreteWorkingGrammarLearner_actualPresentation_mem_canonicalValueSearch
    (hα : Nonempty α)
    (obs : α → M)
    (f : Nat)
    (K : Finset (Word α)) :
    (correctedConcreteFiniteHypothesis K obs f).
        compiledGrammarPresentationEntries
          (Classical.choice hα) ∈
      correctedConcreteWorkingGrammarLearnerCanonicalDecodedPresentationValues
        hα obs f K := by

  exact
    (mem_correctedConcreteWorkingGrammarLearnerCanonicalDecodedPresentationValues_iff
      hα obs f K
      ((correctedConcreteFiniteHypothesis K obs f).
        compiledGrammarPresentationEntries
          (Classical.choice hα))).mpr
      ⟨correctedConcreteWorkingGrammarLearnerLogarithmicBitList
          hα obs f K,
        correctedConcreteWorkingGrammarLearnerLogarithmicBitList_mem_codeUniverse
          hα obs f K,
        correctedConcreteWorkingGrammarLearnerLogarithmicBitDecode_encode
          hα obs f K,
        correctedConcreteWorkingGrammarLearnerLogarithmicBitReencode_actual
          hα obs f K⟩

/-- Every canonical search candidate satisfies bounded source length, checked
decoding, and exact re-encoding. -/
theorem
    correctedConcreteWorkingGrammarLearnerCanonicalDecodedPresentationSearch_sound
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
        correctedConcreteWorkingGrammarLearnerCanonicalDecodedPresentationSearch
          hα obs f K) :
    bits.length <=
        correctedConcreteCompiledGrammarPaperPowerBitBound
          (sampleLengthBudget K)
          f ∧
      correctedConcreteWorkingGrammarLearnerLogarithmicBitDecode
          hα obs f K bits =
        some presentation ∧
      correctedConcreteWorkingGrammarLearnerLogarithmicBitReencode
          hα obs f K presentation =
        bits := by

  rcases
      (mem_correctedConcreteWorkingGrammarLearnerCanonicalDecodedPresentationSearch_iff
        hα obs f K bits presentation).mp
        hpair with
    ⟨hbits, hdecode, hcanonical⟩

  exact
    ⟨(mem_correctedConcreteCompiledGrammarCheckedBitCodeUniverse_iff
        bits
        (sampleLengthBudget K)
        f).mp
        hbits,
      hdecode,
      hcanonical⟩

/-- Every canonical candidate is a decoder fixed point after re-encoding. -/
theorem
    correctedConcreteWorkingGrammarLearnerCanonicalDecodedPresentationSearch_decode_reencode
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
        correctedConcreteWorkingGrammarLearnerCanonicalDecodedPresentationSearch
          hα obs f K) :
    correctedConcreteWorkingGrammarLearnerLogarithmicBitDecode
        hα obs f K
        (correctedConcreteWorkingGrammarLearnerLogarithmicBitReencode
          hα obs f K presentation) =
      some presentation := by

  rcases
      correctedConcreteWorkingGrammarLearnerCanonicalDecodedPresentationSearch_sound
        hα obs f K hpair with
    ⟨hlength, hdecode, hcanonical⟩

  rw [hcanonical]

  exact hdecode

/-- One presentation has at most one source code in the learner-specific
canonical search. -/
theorem
    correctedConcreteWorkingGrammarLearnerCanonicalDecodedPresentationSearch_code_unique
    (hα : Nonempty α)
    (obs : α → M)
    (f : Nat)
    (K : Finset (Word α))
    {bits₁ bits₂ : List Bool}
    {presentation :
      List
        (CorrectedConcreteCompiledGrammarPresentationEntry
          (correctedConcreteFiniteHypothesis K obs f))}
    (h₁ :
      (bits₁, presentation) ∈
        correctedConcreteWorkingGrammarLearnerCanonicalDecodedPresentationSearch
          hα obs f K)
    (h₂ :
      (bits₂, presentation) ∈
        correctedConcreteWorkingGrammarLearnerCanonicalDecodedPresentationSearch
          hα obs f K) :
    bits₁ = bits₂ := by

  exact
    canonicalDecodePairs_code_unique
      (correctedConcreteWorkingGrammarLearnerLogarithmicBitReencode
        hα obs f K)
      (correctedConcreteWorkingGrammarLearnerLogarithmicBitDecode
        hα obs f K)
      (correctedConcreteCompiledGrammarCheckedBitCodeUniverse
        (sampleLengthBudget K)
        f)
      h₁ h₂

/-- One source code has at most one presentation in the learner-specific
canonical search. -/
theorem
    correctedConcreteWorkingGrammarLearnerCanonicalDecodedPresentationSearch_value_unique
    (hα : Nonempty α)
    (obs : α → M)
    (f : Nat)
    (K : Finset (Word α))
    {bits : List Bool}
    {presentation₁ presentation₂ :
      List
        (CorrectedConcreteCompiledGrammarPresentationEntry
          (correctedConcreteFiniteHypothesis K obs f))}
    (h₁ :
      (bits, presentation₁) ∈
        correctedConcreteWorkingGrammarLearnerCanonicalDecodedPresentationSearch
          hα obs f K)
    (h₂ :
      (bits, presentation₂) ∈
        correctedConcreteWorkingGrammarLearnerCanonicalDecodedPresentationSearch
          hα obs f K) :
    presentation₁ = presentation₂ := by

  exact
    canonicalDecodePairs_value_unique
      (correctedConcreteWorkingGrammarLearnerLogarithmicBitReencode
        hα obs f K)
      (correctedConcreteWorkingGrammarLearnerLogarithmicBitDecode
        hα obs f K)
      (correctedConcreteCompiledGrammarCheckedBitCodeUniverse
        (sampleLengthBudget K)
        f)
      h₁ h₂

/-- The learner-specific canonical search is finite with the explicit universal
size estimate. -/
theorem
    correctedConcreteWorkingGrammarLearnerCanonicalDecodedPresentationSearch_length_le
    (hα : Nonempty α)
    (obs : α → M)
    (f : Nat)
    (K : Finset (Word α)) :
    (correctedConcreteWorkingGrammarLearnerCanonicalDecodedPresentationSearch
        hα obs f K).length <=
      2 ^
        (correctedConcreteCompiledGrammarPaperPowerBitBound
            (sampleLengthBudget K)
            f +
          1) := by

  exact
    checkedBitCanonicalDecodedCodeSearch_length_le_two_pow
      (correctedConcreteWorkingGrammarLearnerLogarithmicBitReencode
        hα obs f K)
      (correctedConcreteWorkingGrammarLearnerLogarithmicBitDecode
        hα obs f K)
      (sampleLengthBudget K)
      f

/-- The learner-specific canonical value search satisfies the same finite size
estimate. -/
theorem
    correctedConcreteWorkingGrammarLearnerCanonicalDecodedPresentationValues_length_le
    (hα : Nonempty α)
    (obs : α → M)
    (f : Nat)
    (K : Finset (Word α)) :
    (correctedConcreteWorkingGrammarLearnerCanonicalDecodedPresentationValues
        hα obs f K).length <=
      2 ^
        (correctedConcreteCompiledGrammarPaperPowerBitBound
            (sampleLengthBudget K)
            f +
          1) := by

  exact
    checkedBitCanonicalDecodedValueSearch_length_le_two_pow
      (correctedConcreteWorkingGrammarLearnerLogarithmicBitReencode
        hα obs f K)
      (correctedConcreteWorkingGrammarLearnerLogarithmicBitDecode
        hα obs f K)
      (sampleLengthBudget K)
      f

/-- Compact finite normalized-search package for one learner output. -/
theorem
    correctedConcreteWorkingGrammarLearner_canonicalDecodedSearch_package
    (hα : Nonempty α)
    (obs : α → M)
    (f : Nat)
    (K : Finset (Word α)) :
    ((correctedConcreteWorkingGrammarLearnerCanonicalDecodedPresentationSearch
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
        correctedConcreteWorkingGrammarLearnerCanonicalDecodedPresentationSearch
          hα obs f K) ∧
      (∀
        bits
        presentation,
        (bits, presentation) ∈
            correctedConcreteWorkingGrammarLearnerCanonicalDecodedPresentationSearch
              hα obs f K →
          bits.length <=
              correctedConcreteCompiledGrammarPaperPowerBitBound
                (sampleLengthBudget K)
                f ∧
            correctedConcreteWorkingGrammarLearnerLogarithmicBitDecode
                hα obs f K bits =
              some presentation ∧
            correctedConcreteWorkingGrammarLearnerLogarithmicBitReencode
                hα obs f K presentation =
              bits) ∧
      (∀
        bits₁ bits₂
        presentation,
        (bits₁, presentation) ∈
            correctedConcreteWorkingGrammarLearnerCanonicalDecodedPresentationSearch
              hα obs f K →
        (bits₂, presentation) ∈
            correctedConcreteWorkingGrammarLearnerCanonicalDecodedPresentationSearch
              hα obs f K →
          bits₁ = bits₂) := by

  exact
    ⟨correctedConcreteWorkingGrammarLearnerCanonicalDecodedPresentationSearch_length_le
        hα obs f K,
      correctedConcreteWorkingGrammarLearner_actualCodePresentation_mem_canonicalSearch
        hα obs f K,
      by
        intro bits presentation hpair

        exact
          correctedConcreteWorkingGrammarLearnerCanonicalDecodedPresentationSearch_sound
            hα obs f K hpair,
      by
        intro bits₁ bits₂ presentation h₁ h₂

        exact
          correctedConcreteWorkingGrammarLearnerCanonicalDecodedPresentationSearch_code_unique
            hα obs f K h₁ h₂⟩

end CanonicalLearnerDecodedSearch


section EventualCanonicalDecodedSearch

variable {α : Type u}
variable {M : Type v}
variable [Fintype M]
variable [DecidableEq α]
variable [DecidableEq M]
variable [Monoid M]
variable (hα : Nonempty α)
variable (obs : α → M)
variable (f : Nat)

/-- After the usual target-coverage stage, every later finite canonical search
contains the exact target learner output as its canonical code/presentation
pair. -/
theorem
    correctedConcreteWorkingGrammarLearner_selectedStage_canonicalDecodedSearch_package :
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
            (correctedConcreteWorkingGrammarLearnerLogarithmicBitList
                hα obs f
                (T.prefixSample n),
              (correctedConcreteFiniteHypothesis
                  (T.prefixSample n) obs f).
                compiledGrammarPresentationEntries
                  (Classical.choice hα)) ∈
              correctedConcreteWorkingGrammarLearnerCanonicalDecodedPresentationSearch
                hα obs f
                (T.prefixSample n) ∧
            (correctedConcreteWorkingGrammarLearnerCanonicalDecodedPresentationSearch
                hα obs f
                (T.prefixSample n)).length <=
              2 ^
                (correctedConcreteCompiledGrammarPaperPowerBitBound
                    (sampleLengthBudget
                      (T.prefixSample n))
                    f +
                  1) := by

  intro L hL T

  refine
    ⟨startRootedCorrectedConcreteTargetCoverageStage
        (v := w) obs f hL T,
      ?_⟩

  intro n hn

  exact
    ⟨correctedConcreteWorkingGrammarLearner_correct_after_startRootedCoverageStage
        (v := w) hα obs f hL T hn,
      correctedConcreteWorkingGrammarLearner_actualCodePresentation_mem_canonicalSearch
        hα obs f
        (T.prefixSample n),
      correctedConcreteWorkingGrammarLearnerCanonicalDecodedPresentationSearch_length_le
        hα obs f
        (T.prefixSample n)⟩

/-- Final identification plus canonical finite-search normalization package. -/
theorem
    correctedConcreteWorkingGrammarLearner_identification_canonicalDecodedSearch_package :
    IdentifiesClassFromPositiveData
        (correctedConcreteWorkingGrammarHypLanguage
          obs f)
        (correctedConcreteWorkingGrammarLearner
          hα obs f)
        (StartRootedCorrectedConcreteTargetClass
          (v := w) α M obs f) ∧
      (∀ K : Finset (Word α),
        (correctedConcreteWorkingGrammarLearnerCanonicalDecodedPresentationSearch
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
          correctedConcreteWorkingGrammarLearnerCanonicalDecodedPresentationSearch
            hα obs f K) ∧
      (∀
        K : Finset (Word α),
        ∀
          bits
          presentation,
          (bits, presentation) ∈
              correctedConcreteWorkingGrammarLearnerCanonicalDecodedPresentationSearch
                hα obs f K →
            correctedConcreteWorkingGrammarLearnerLogarithmicBitDecode
                hα obs f K bits =
              some presentation ∧
            correctedConcreteWorkingGrammarLearnerLogarithmicBitReencode
                hα obs f K presentation =
              bits) ∧
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
                  (T.prefixSample n),
                (correctedConcreteFiniteHypothesis
                    (T.prefixSample n) obs f).
                  compiledGrammarPresentationEntries
                    (Classical.choice hα)) ∈
                correctedConcreteWorkingGrammarLearnerCanonicalDecodedPresentationSearch
                  hα obs f
                  (T.prefixSample n)) := by

  refine
    ⟨correctedConcreteWorkingGrammarLearner_identifies_startRootedTargetClass
        (v := w) hα obs f,
      correctedConcreteWorkingGrammarLearnerCanonicalDecodedPresentationSearch_length_le
        hα obs f,
      correctedConcreteWorkingGrammarLearner_actualCodePresentation_mem_canonicalSearch
        hα obs f,
      ?_,
      ?_⟩

  · intro K bits presentation hpair

    rcases
        correctedConcreteWorkingGrammarLearnerCanonicalDecodedPresentationSearch_sound
          hα obs f K hpair with
      ⟨hlength, hdecode, hcanonical⟩

    exact
      ⟨hdecode,
        hcanonical⟩

  · intro L hL T

    rcases
        correctedConcreteWorkingGrammarLearner_selectedStage_canonicalDecodedSearch_package
          (v := w) hα obs f L hL T with
      ⟨n0, hstage⟩

    exact
      ⟨n0,
        by
          intro n hn

          rcases hstage n hn with
            ⟨hlanguage, hpair, hlength⟩

          exact
            ⟨hlanguage,
              hpair⟩⟩

end EventualCanonicalDecodedSearch

end MCFG
