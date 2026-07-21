/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG2.ConcreteCanonicalLearnerWorkingGrammarBinaryRuleSerialization

/-!
# ConcreteCanonicalLearnerWorkingGrammarTerminalAlphabetEncoding.lean

The preceding file gives a checked structural codec for a complete compiled
binary rule, but terminal atoms still carry values of the ambient alphabet
`alpha`.  This file removes that remaining alphabet-valued payload at the token
level.

The actual cut-compiled grammar uses terminals from two finite sources:

* letters occurring in the positive sample `K`;
* the distinguished `dummy` terminal used by the seed construction.

We therefore use the finite augmented alphabet

```text
insert dummy (sampleAlphabet K)
```

and assign every listed terminal its first-occurrence dense natural code.  The
corresponding decoder is ordinary `List.get?`.  We prove exact decoding after
encoding, soundness of successful decoding, and the strict code bound by the
augmented alphabet cardinality.

We then replace every alphabet-valued terminal payload inside
`TemplateAtomStructuralToken alpha` by its dense natural code.  Left and right
variable indices were already natural numbers, so the resulting token type is
completely independent of `alpha`.  The construction is lifted to framed body
tokens and to complete framed token streams.  Round trips are proved whenever
the terminal payloads belong to the augmented finite alphabet.

This is the last alphabet-valued layer before serializing complete binary-rule
packets as natural-number data.

No target grammar is supplied to the learner.
No `sorry`, `admit`, or `axiom` is used.
-/

namespace MCFG

universe u v

section FiniteCompiledTerminalAlphabet

variable {α : Type u}

/-- The finite terminal alphabet needed by the cut-compiled grammar: all sample
letters together with the distinguished seed terminal. -/
noncomputable def compiledTerminalAlphabet
    (K : Finset (Word α))
    (dummy : α) :
    Finset α := by
  classical
  exact insert dummy (sampleAlphabet K)

/-- Canonical duplicate-free list underlying the finite compiled terminal
alphabet. -/
noncomputable def compiledTerminalAlphabetList
    (K : Finset (Word α))
    (dummy : α) :
    List α := by
  classical
  exact (compiledTerminalAlphabet K dummy).toList

/-- Every sample terminal belongs to the augmented compiled alphabet. -/
theorem mem_compiledTerminalAlphabet_of_mem_sampleAlphabet
    (K : Finset (Word α))
    (dummy : α)
    {a : α}
    (ha : a ∈ sampleAlphabet K) :
    a ∈ compiledTerminalAlphabet K dummy := by
  classical
  simp [compiledTerminalAlphabet, ha]

/-- The distinguished seed terminal belongs to the augmented compiled
alphabet. -/
@[simp] theorem dummy_mem_compiledTerminalAlphabet
    (K : Finset (Word α))
    (dummy : α) :
    dummy ∈ compiledTerminalAlphabet K dummy := by
  classical
  simp [compiledTerminalAlphabet]

/-- Membership in the canonical alphabet list is the same as membership in the
augmented finite alphabet. -/
@[simp] theorem mem_compiledTerminalAlphabetList_iff
    (K : Finset (Word α))
    (dummy a : α) :
    a ∈ compiledTerminalAlphabetList K dummy ↔
      a ∈ compiledTerminalAlphabet K dummy := by
  classical
  simp [compiledTerminalAlphabetList]

/-- The canonical alphabet-list length is exactly the augmented alphabet
cardinality. -/
@[simp] theorem compiledTerminalAlphabetList_length
    (K : Finset (Word α))
    (dummy : α) :
    (compiledTerminalAlphabetList K dummy).length =
      (compiledTerminalAlphabet K dummy).card := by
  classical
  simp [compiledTerminalAlphabetList]

/-- Dense natural code of one terminal relative to the augmented finite
alphabet. -/
noncomputable def compiledTerminalDenseCode
    (K : Finset (Word α))
    (dummy a : α) :
    Nat := by
  classical
  exact
    listFirstIndex a
      (compiledTerminalAlphabetList K dummy)

/-- Decode one dense terminal code by lookup in the augmented alphabet list. -/
noncomputable def compiledTerminalDenseDecode
    (K : Finset (Word α))
    (dummy : α)
    (code : Nat) :
    Option α := by
  classical
  exact
    (compiledTerminalAlphabetList K dummy).get? code

/-- Every terminal in the augmented finite alphabet survives dense encoding and
decoding exactly. -/
@[simp] theorem compiledTerminalDenseDecode_encode_of_mem
    (K : Finset (Word α))
    (dummy a : α)
    (ha : a ∈ compiledTerminalAlphabet K dummy) :
    compiledTerminalDenseDecode K dummy
        (compiledTerminalDenseCode K dummy a) =
      some a := by
  classical

  have hlist :
      a ∈ compiledTerminalAlphabetList K dummy := by
    simpa using ha

  exact
    list_get?_listFirstIndex_of_mem
      a
      (compiledTerminalAlphabetList K dummy)
      hlist

/-- Every sample terminal survives augmented dense encoding and decoding. -/
@[simp] theorem compiledTerminalDenseDecode_encode_of_mem_sampleAlphabet
    (K : Finset (Word α))
    (dummy a : α)
    (ha : a ∈ sampleAlphabet K) :
    compiledTerminalDenseDecode K dummy
        (compiledTerminalDenseCode K dummy a) =
      some a := by

  exact
    compiledTerminalDenseDecode_encode_of_mem
      K dummy a
      (mem_compiledTerminalAlphabet_of_mem_sampleAlphabet
        K dummy ha)

/-- The distinguished seed terminal survives augmented dense encoding and
decoding. -/
@[simp] theorem compiledTerminalDenseDecode_encode_dummy
    (K : Finset (Word α))
    (dummy : α) :
    compiledTerminalDenseDecode K dummy
        (compiledTerminalDenseCode K dummy dummy) =
      some dummy := by

  exact
    compiledTerminalDenseDecode_encode_of_mem
      K dummy dummy
      (dummy_mem_compiledTerminalAlphabet K dummy)

/-- A terminal occurring in the augmented alphabet receives a code strictly
below the augmented alphabet cardinality. -/
theorem compiledTerminalDenseCode_lt_card
    (K : Finset (Word α))
    (dummy a : α)
    (ha : a ∈ compiledTerminalAlphabet K dummy) :
    compiledTerminalDenseCode K dummy a <
      (compiledTerminalAlphabet K dummy).card := by
  classical

  have hlist :
      a ∈ compiledTerminalAlphabetList K dummy := by
    simpa using ha

  have hlt :
      listFirstIndex a
          (compiledTerminalAlphabetList K dummy) <
        (compiledTerminalAlphabetList K dummy).length :=
    listFirstIndex_lt_length_of_mem
      a
      (compiledTerminalAlphabetList K dummy)
      hlist

  simpa [compiledTerminalDenseCode] using hlt

/-- Successful dense terminal decoding always returns a terminal belonging to
the augmented finite alphabet. -/
theorem mem_compiledTerminalAlphabet_of_denseDecode_eq_some
    (K : Finset (Word α))
    (dummy a : α)
    (code : Nat)
    (hdecode :
      compiledTerminalDenseDecode K dummy code =
        some a) :
    a ∈ compiledTerminalAlphabet K dummy := by
  classical

  have hlist :
      a ∈ compiledTerminalAlphabetList K dummy :=
    list_mem_of_get?_eq_some
      a
      (compiledTerminalAlphabetList K dummy)
      code
      (by
        simpa [compiledTerminalDenseDecode] using hdecode)

  simpa using hlist

/-- Compact finite-terminal-codec package. -/
theorem compiledTerminalDenseCodec_package
    (K : Finset (Word α))
    (dummy a : α)
    (ha : a ∈ compiledTerminalAlphabet K dummy) :
    (compiledTerminalDenseDecode K dummy
        (compiledTerminalDenseCode K dummy a) =
      some a) ∧
      (compiledTerminalDenseCode K dummy a <
        (compiledTerminalAlphabet K dummy).card) := by

  constructor

  · exact
      compiledTerminalDenseDecode_encode_of_mem
        K dummy a ha

  · exact
      compiledTerminalDenseCode_lt_card
        K dummy a ha

end FiniteCompiledTerminalAlphabet


section AlphabetFreeTemplateTokens

variable {α : Type u}

/-- Alphabet-free structural token.  Terminal payloads are now dense natural
codes; child-variable payloads remain their ordinary natural indices. -/
inductive TemplateAtomNaturalToken where
  | terminalCode (code : Nat)
  | leftVar (index : Nat)
  | rightVar (index : Nat)
  deriving Repr, DecidableEq

/-- Predicate saying that every alphabet-valued payload of one structural token
belongs to a prescribed finite alphabet. -/
def TemplateAtomStructuralToken.TerminalsIn
    (A : Finset α) :
    TemplateAtomStructuralToken α → Prop

  | .terminal a =>
      a ∈ A

  | .leftVar _ =>
      True

  | .rightVar _ =>
      True

/-- Replace the terminal payload of one structural token by its dense natural
code. -/
noncomputable def encodeTemplateAtomNatural
    (K : Finset (Word α))
    (dummy : α) :
    TemplateAtomStructuralToken α →
      TemplateAtomNaturalToken

  | .terminal a =>
      .terminalCode
        (compiledTerminalDenseCode K dummy a)

  | .leftVar i =>
      .leftVar i

  | .rightVar j =>
      .rightVar j

/-- Decode one alphabet-free structural token.  Terminal codes are checked by
finite-list lookup; variable indices are passed unchanged to the later arity
checker. -/
noncomputable def decodeTemplateAtomNatural
    (K : Finset (Word α))
    (dummy : α) :
    TemplateAtomNaturalToken →
      Option (TemplateAtomStructuralToken α)

  | .terminalCode code =>
      match compiledTerminalDenseDecode K dummy code with
      | none =>
          none
      | some a =>
          some (.terminal a)

  | .leftVar i =>
      some (.leftVar i)

  | .rightVar j =>
      some (.rightVar j)

/-- Exact token-level round trip whenever the terminal payload belongs to the
augmented compiled alphabet. -/
@[simp] theorem decodeTemplateAtomNatural_encode
    (K : Finset (Word α))
    (dummy : α)
    (token : TemplateAtomStructuralToken α)
    (hterminal :
      token.TerminalsIn
        (compiledTerminalAlphabet K dummy)) :
    decodeTemplateAtomNatural K dummy
        (encodeTemplateAtomNatural K dummy token) =
      some token := by

  cases token with

  | terminal a =>
      simpa [
        TemplateAtomStructuralToken.TerminalsIn,
        encodeTemplateAtomNatural,
        decodeTemplateAtomNatural
      ] using
        compiledTerminalDenseDecode_encode_of_mem
          K dummy a hterminal

  | leftVar i =>
      rfl

  | rightVar j =>
      rfl


end AlphabetFreeTemplateTokens


section AlphabetFreeFramedTokens

variable {α : Type u}

/-- Alphabet-free framed body token. -/
inductive FramedTemplateBodyNaturalToken where
  | componentLength (length : Nat)
  | atom (token : TemplateAtomNaturalToken)
  deriving Repr, DecidableEq

/-- Terminal-membership predicate for one alphabet-valued framed body token. -/
def FramedTemplateBodyToken.TerminalsIn
    (A : Finset α) :
    FramedTemplateBodyToken α → Prop

  | .componentLength _ =>
      True

  | .atom token =>
      token.TerminalsIn A

/-- Remove alphabet-valued payloads from one framed body token. -/
noncomputable def encodeFramedTemplateBodyTokenNatural
    (K : Finset (Word α))
    (dummy : α) :
    FramedTemplateBodyToken α →
      FramedTemplateBodyNaturalToken

  | .componentLength n =>
      .componentLength n

  | .atom token =>
      .atom (encodeTemplateAtomNatural K dummy token)

/-- Checked reconstruction of one alphabet-valued framed body token. -/
noncomputable def decodeFramedTemplateBodyTokenNatural
    (K : Finset (Word α))
    (dummy : α) :
    FramedTemplateBodyNaturalToken →
      Option (FramedTemplateBodyToken α)

  | .componentLength n =>
      some (.componentLength n)

  | .atom encoded =>
      match decodeTemplateAtomNatural K dummy encoded with
      | none =>
          none
      | some token =>
          some (.atom token)

/-- Exact framed-token round trip under the finite terminal-alphabet condition. -/
@[simp] theorem decodeFramedTemplateBodyTokenNatural_encode
    (K : Finset (Word α))
    (dummy : α)
    (token : FramedTemplateBodyToken α)
    (hterminal :
      token.TerminalsIn
        (compiledTerminalAlphabet K dummy)) :
    decodeFramedTemplateBodyTokenNatural K dummy
        (encodeFramedTemplateBodyTokenNatural
          K dummy token) =
      some token := by

  cases token with

  | componentLength n =>
      rfl

  | atom token =>
      simpa [
        FramedTemplateBodyToken.TerminalsIn,
        encodeFramedTemplateBodyTokenNatural,
        decodeFramedTemplateBodyTokenNatural
      ] using
        decodeTemplateAtomNatural_encode
          K dummy token hterminal

/-- Encode a complete framed body stream with natural terminal payloads. -/
noncomputable def encodeFramedTemplateBodyNatural
    (K : Finset (Word α))
    (dummy : α)
    (tokens : List (FramedTemplateBodyToken α)) :
    List FramedTemplateBodyNaturalToken :=
  tokens.map
    (encodeFramedTemplateBodyTokenNatural K dummy)

/-- Decode a complete alphabet-free framed body stream. -/
noncomputable def decodeFramedTemplateBodyNatural
    (K : Finset (Word α))
    (dummy : α) :
    List FramedTemplateBodyNaturalToken →
      Option (List (FramedTemplateBodyToken α))

  | [] =>
      some []

  | encoded :: rest =>
      match
          decodeFramedTemplateBodyTokenNatural
            K dummy encoded with
      | none =>
          none
      | some token =>
          match
              decodeFramedTemplateBodyNatural
                K dummy rest with
          | none =>
              none
          | some tokens =>
              some (token :: tokens)

/-- Complete framed-stream round trip whenever every terminal payload belongs
to the augmented compiled alphabet. -/
@[simp] theorem decodeFramedTemplateBodyNatural_encode
    (K : Finset (Word α))
    (dummy : α) :
    ∀ (tokens : List (FramedTemplateBodyToken α)),
      (∀ token ∈ tokens,
        token.TerminalsIn
          (compiledTerminalAlphabet K dummy)) →
      decodeFramedTemplateBodyNatural K dummy
          (encodeFramedTemplateBodyNatural
            K dummy tokens) =
        some tokens

  | [], _ => by
      rfl

  | token :: rest, hterminals => by
      have hhead :
          token.TerminalsIn
            (compiledTerminalAlphabet K dummy) :=
        hterminals token (by simp)

      have htail :
          ∀ next ∈ rest,
            next.TerminalsIn
              (compiledTerminalAlphabet K dummy) := by
        intro next hnext
        exact hterminals next (by simp [hnext])

      simp [
        encodeFramedTemplateBodyNatural,
        decodeFramedTemplateBodyNatural,
        decodeFramedTemplateBodyTokenNatural_encode
          K dummy token hhead,
        decodeFramedTemplateBodyNatural_encode
          K dummy rest htail
      ]

/-- Natural terminal coding preserves the number of framed body tokens. -/
@[simp] theorem encodeFramedTemplateBodyNatural_length
    (K : Finset (Word α))
    (dummy : α)
    (tokens : List (FramedTemplateBodyToken α)) :
    (encodeFramedTemplateBodyNatural
        K dummy tokens).length =
      tokens.length := by

  simp [encodeFramedTemplateBodyNatural]

/-- Compact endpoint for an arbitrary finite-alphabet framed body stream. -/
theorem framedTemplateBodyNaturalCodec_package
    (K : Finset (Word α))
    (dummy : α)
    (tokens : List (FramedTemplateBodyToken α))
    (hterminals :
      ∀ token ∈ tokens,
        token.TerminalsIn
          (compiledTerminalAlphabet K dummy)) :
    (decodeFramedTemplateBodyNatural K dummy
        (encodeFramedTemplateBodyNatural
          K dummy tokens) =
      some tokens) ∧
      ((encodeFramedTemplateBodyNatural
          K dummy tokens).length =
        tokens.length) := by

  constructor

  · exact
      decodeFramedTemplateBodyNatural_encode
        K dummy tokens hterminals

  · exact
      encodeFramedTemplateBodyNatural_length
        K dummy tokens

end AlphabetFreeFramedTokens

end MCFG
