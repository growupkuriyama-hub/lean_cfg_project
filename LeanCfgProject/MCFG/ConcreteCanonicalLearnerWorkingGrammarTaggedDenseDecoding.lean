/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG.ConcreteCanonicalLearnerWorkingGrammarTaggedDenseEncoding

/-!
# ConcreteCanonicalLearnerWorkingGrammarTaggedDenseDecoding.lean

The preceding file constructed one collision-free global dense natural-number
code for all top-level entries of the actual cut-compiled grammar presentation.
Injectivity alone does not yet make the code an explicit finite codec: one also
needs a decoder and a round-trip theorem.

This file adds that missing decoding layer.  For a finite list, decoding is
ordinary `List.get?`, while encoding is the first-occurrence position.  We prove
three generic facts:

* every listed value decodes after it is encoded;
* every successful decoding returns a value contained in the list;
* every index below the list length successfully decodes.

These facts are then specialized to the complete tagged grammar-presentation
list.  The resulting endpoint says that the global tagged dense code is a
canonical finite codec for all actually stored presentation entries:

```lean
entry ∈ H.compiledGrammarPresentationEntries dummy
  -> H.compiledGrammarGlobalDenseDecode dummy
       (H.compiledGrammarGlobalDenseCode dummy entry)
       = some entry.
```

Moreover, decoding succeeds exactly on the finite index range below
`H.compiledGrammarPresentationItemCount`; in particular every code at or above
that bound decodes to `none`.

This closes the top-level finite-code layer before recursively serializing the
internal fields of terminal words and dependent binary templates.

No target grammar is supplied to the learner.
No `sorry`, `admit`, or `axiom` is used.
-/

namespace MCFG

universe u v

section GenericFirstOccurrenceDecoding

/-- Looking up the first-occurrence position of a listed value returns that
value. -/
theorem list_get?_listFirstIndex_of_mem
    {β : Type u}
    [DecidableEq β]
    (x : β) :
    ∀ (xs : List β),
      x ∈ xs →
      xs.get? (listFirstIndex x xs) = some x

  | [], hx => by
      simp at hx

  | y :: ys, hx => by
      by_cases hxy : x = y

      · subst y
        simp [listFirstIndex]

      · have hxTail : x ∈ ys := by
          simpa [hxy] using hx

        have hlookup :
            ys.get? (listFirstIndex x ys) = some x :=
          list_get?_listFirstIndex_of_mem x ys hxTail

        simpa [listFirstIndex, hxy] using hlookup

/-- A value returned by `List.get?` is a member of the source list. -/
theorem list_mem_of_get?_eq_some
    {β : Type u}
    (x : β) :
    ∀ (xs : List β) (n : Nat),
      xs.get? n = some x →
      x ∈ xs

  | [], n, h => by
      simp at h

  | y :: ys, 0, h => by
      have hyx : y = x := by
        simpa using h
      subst x
      simp

  | y :: ys, Nat.succ n, h => by
      have hTailLookup :
          ys.get? n = some x := by
        simpa using h

      have hxTail : x ∈ ys :=
        list_mem_of_get?_eq_some x ys n hTailLookup

      simp [hxTail]

/-- A successful lookup index is strictly below the list length. -/
theorem index_lt_length_of_get?_eq_some
    {β : Type u}
    (x : β) :
    ∀ (xs : List β) (n : Nat),
      xs.get? n = some x →
      n < xs.length

  | [], n, h => by
      simp at h

  | y :: ys, 0, h => by
      simp

  | y :: ys, Nat.succ n, h => by
      have hTailLookup :
          ys.get? n = some x := by
        simpa using h

      have hlt : n < ys.length :=
        index_lt_length_of_get?_eq_some
          x ys n hTailLookup

      simpa using Nat.succ_lt_succ hlt

/-- Every index strictly below the list length successfully decodes some list
entry. -/
theorem exists_get?_eq_some_of_lt_length
    {β : Type u} :
    ∀ (xs : List β) (n : Nat),
      n < xs.length →
      ∃ x, xs.get? n = some x

  | [], n, h => by
      simp at h

  | y :: ys, 0, h => by
      exact ⟨y, by simp⟩

  | y :: ys, Nat.succ n, h => by
      have hTail : n < ys.length := by
        simpa using h

      rcases
        exists_get?_eq_some_of_lt_length ys n hTail with
        ⟨x, hx⟩

      exact ⟨x, by simpa using hx⟩

/-- First-occurrence encoding together with list lookup is a canonical finite
codec on the values actually stored in a list. -/
structure FiniteStoredEntryCodec
    (β : Type u)
    (xs : List β) where

  encode : β → Nat

  decode : Nat → Option β

  encode_lt_of_mem :
    ∀ x ∈ xs,
      encode x < xs.length

  decode_encode_of_mem :
    ∀ x ∈ xs,
      decode (encode x) = some x

  decode_sound :
    ∀ n x,
      decode n = some x →
      x ∈ xs

  decode_complete :
    ∀ n,
      n < xs.length →
      ∃ x, decode n = some x

/-- Canonical codec attached to a finite list: encode by first occurrence and
decode by lookup. -/
noncomputable def listFirstOccurrenceCodec
    {β : Type u}
    [DecidableEq β]
    (xs : List β) :
    FiniteStoredEntryCodec β xs where

  encode := fun x =>
    listFirstIndex x xs

  decode := fun n =>
    xs.get? n

  encode_lt_of_mem := by
    intro x hx
    exact
      listFirstIndex_lt_length_of_mem
        x xs hx

  decode_encode_of_mem := by
    intro x hx
    exact
      list_get?_listFirstIndex_of_mem
        x xs hx

  decode_sound := by
    intro n x h
    exact
      list_mem_of_get?_eq_some
        x xs n h

  decode_complete := by
    intro n hn
    exact
      exists_get?_eq_some_of_lt_length
        xs n hn

end GenericFirstOccurrenceDecoding


section TaggedCompiledGrammarDecoder

variable {α : Type u}
variable {M : Type v} [Monoid M]
variable {K : Finset (Word α)}
variable {obs : α → M}
variable {f : Nat}

namespace CorrectedConcreteFiniteHypothesis

variable
  (H :
    CorrectedConcreteFiniteHypothesis
      K obs f)

/-- Decoder for the global tagged presentation code. -/
noncomputable def compiledGrammarGlobalDenseDecode
    (dummy : α)
    (code : Nat) :
    Option
      (CorrectedConcreteCompiledGrammarPresentationEntry H) :=
  (H.compiledGrammarPresentationEntries dummy).get? code

/-- The complete global tagged list carries the canonical first-occurrence
finite codec. -/
noncomputable def compiledGrammarTaggedDenseCodec
    (dummy : α) :
    FiniteStoredEntryCodec
      (CorrectedConcreteCompiledGrammarPresentationEntry H)
      (H.compiledGrammarPresentationEntries dummy) := by

  classical

  exact
    listFirstOccurrenceCodec
      (H.compiledGrammarPresentationEntries dummy)

@[simp] theorem compiledGrammarTaggedDenseCodec_encode
    (dummy : α)
    (entry :
      CorrectedConcreteCompiledGrammarPresentationEntry H) :
    (H.compiledGrammarTaggedDenseCodec dummy).encode entry =
      H.compiledGrammarGlobalDenseCode dummy entry := by

  rfl

@[simp] theorem compiledGrammarTaggedDenseCodec_decode
    (dummy : α)
    (code : Nat) :
    (H.compiledGrammarTaggedDenseCodec dummy).decode code =
      H.compiledGrammarGlobalDenseDecode dummy code := by

  rfl

/-- Main round-trip theorem: every actually stored tagged presentation entry is
recovered exactly after global dense encoding and decoding. -/
theorem compiledGrammarGlobalDenseDecode_encode_of_mem
    (dummy : α)
    (entry :
      CorrectedConcreteCompiledGrammarPresentationEntry H)
    (hentry :
      entry ∈ H.compiledGrammarPresentationEntries dummy) :
    H.compiledGrammarGlobalDenseDecode dummy
        (H.compiledGrammarGlobalDenseCode dummy entry) =
      some entry := by

  classical

  exact
    (H.compiledGrammarTaggedDenseCodec dummy).
      decode_encode_of_mem entry hentry

/-- Every successfully decoded tagged entry really occurs in the compiled
grammar presentation. -/
theorem compiledGrammarGlobalDenseDecode_sound
    (dummy : α)
    (code : Nat)
    (entry :
      CorrectedConcreteCompiledGrammarPresentationEntry H)
    (hdecode :
      H.compiledGrammarGlobalDenseDecode dummy code =
        some entry) :
    entry ∈ H.compiledGrammarPresentationEntries dummy := by

  classical

  exact
    (H.compiledGrammarTaggedDenseCodec dummy).
      decode_sound code entry hdecode

/-- Any successful global decoding uses a code below the complete presentation
item count. -/
theorem compiledGrammarGlobalDenseDecode_code_lt_presentationItemCount
    (dummy : α)
    (code : Nat)
    (entry :
      CorrectedConcreteCompiledGrammarPresentationEntry H)
    (hdecode :
      H.compiledGrammarGlobalDenseDecode dummy code =
        some entry) :
    code < H.compiledGrammarPresentationItemCount := by

  have hlt :
      code <
        (H.compiledGrammarPresentationEntries dummy).length :=
    index_lt_length_of_get?_eq_some
      entry
      (H.compiledGrammarPresentationEntries dummy)
      code
      hdecode

  simpa using hlt

/-- Every natural number below the complete presentation item count decodes to
some tagged entry. -/
theorem compiledGrammarGlobalDenseDecode_complete
    (dummy : α)
    (code : Nat)
    (hcode :
      code < H.compiledGrammarPresentationItemCount) :
    ∃ entry,
      H.compiledGrammarGlobalDenseDecode dummy code =
        some entry := by

  have hlt :
      code <
        (H.compiledGrammarPresentationEntries dummy).length := by
    simpa using hcode

  exact
    exists_get?_eq_some_of_lt_length
      (H.compiledGrammarPresentationEntries dummy)
      code hlt

/-- Codes outside the finite presentation range decode to `none`. -/
theorem compiledGrammarGlobalDenseDecode_eq_none_of_presentationItemCount_le
    (dummy : α)
    (code : Nat)
    (hcode :
      H.compiledGrammarPresentationItemCount ≤ code) :
    H.compiledGrammarGlobalDenseDecode dummy code = none := by

  cases hdecode :
      H.compiledGrammarGlobalDenseDecode dummy code with

  | none =>
      exact hdecode

  | some entry =>
      have hlt :
          code < H.compiledGrammarPresentationItemCount :=
        H.compiledGrammarGlobalDenseDecode_code_lt_presentationItemCount
          dummy code entry hdecode

      omega

/-- A compact package collecting the finite-code properties needed by later
structural serialization layers. -/
theorem compiledGrammarTaggedDenseCodec_package
    (dummy : α) :
    (∀ entry,
        entry ∈ H.compiledGrammarPresentationEntries dummy →
        H.compiledGrammarGlobalDenseDecode dummy
            (H.compiledGrammarGlobalDenseCode dummy entry) =
          some entry) ∧
      (∀ code entry,
        H.compiledGrammarGlobalDenseDecode dummy code = some entry →
        entry ∈ H.compiledGrammarPresentationEntries dummy) ∧
      (∀ code,
        code < H.compiledGrammarPresentationItemCount →
        ∃ entry,
          H.compiledGrammarGlobalDenseDecode dummy code = some entry) ∧
      (∀ code,
        H.compiledGrammarPresentationItemCount ≤ code →
        H.compiledGrammarGlobalDenseDecode dummy code = none) := by

  refine ⟨?_, ?_, ?_, ?_⟩

  · intro entry hentry
    exact
      H.compiledGrammarGlobalDenseDecode_encode_of_mem
        dummy entry hentry

  · intro code entry hdecode
    exact
      H.compiledGrammarGlobalDenseDecode_sound
        dummy code entry hdecode

  · intro code hcode
    exact
      H.compiledGrammarGlobalDenseDecode_complete
        dummy code hcode

  · intro code hcode
    exact
      H.compiledGrammarGlobalDenseDecode_eq_none_of_presentationItemCount_le
        dummy code hcode

end CorrectedConcreteFiniteHypothesis

end TaggedCompiledGrammarDecoder

end MCFG
