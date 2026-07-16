/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG.ConcreteCanonicalLearnerWorkingGrammarTemplateSerialization

/-!
# ConcreteCanonicalLearnerWorkingGrammarTemplateTupleFraming.lean

The preceding file serializes every atom and every individual output word of a
binary MCFG template, but it still represents a complete output tuple as a
function

```lean
Fin e → List (TemplateAtomStructuralToken α).
```

This file removes that remaining component-function interface.  Each output
component is framed by its token length, all framed components are concatenated,
and a checked decoder reconstructs the ordered component list.

The framing format is

```text
componentLength n, token₁, ..., tokenₙ,
componentLength m, token₁, ..., tokenₘ, ...
```

where the payload tokens are the nondependent structural tokens constructed in
the previous file.  The decoder therefore checks both kinds of internal
well-formedness:

* the declared component length is available in the flat stream;
* every left/right variable index is valid for the two child arities.

We prove exact round trips for arbitrary component lists, complete dependent
template tuples, and the body of every actual binary rule.  We also record the
exact flat-token count: one framing token per output component plus one token
per template atom.

No target grammar is supplied to the learner.
No `sorry`, `admit`, or `axiom` is used.
-/

namespace MCFG

universe u v

section ExactPrefixExtraction

variable {β : Type u}

/-- Extract exactly `n` leading entries, failing when the input is too short. -/
def takeExactly : Nat → List β → Option (List β × List β)
  | 0, xs =>
      some ([], xs)

  | _ + 1, [] =>
      none

  | n + 1, x :: xs =>
      match takeExactly n xs with
      | none =>
          none
      | some (prefix, suffix) =>
          some (x :: prefix, suffix)

/-- Extracting the length of an explicit prefix from `prefix ++ suffix`
recovers exactly that prefix and suffix. -/
@[simp] theorem takeExactly_length_append
    (prefix suffix : List β) :
    takeExactly prefix.length (prefix ++ suffix) =
      some (prefix, suffix) := by

  induction prefix with

  | nil =>
      rfl

  | cons x prefix ih =>
      simp [takeExactly, ih]

/-- A convenient variant with an externally supplied length equality. -/
theorem takeExactly_append_of_length
    {n : Nat}
    (prefix suffix : List β)
    (hlength : prefix.length = n) :
    takeExactly n (prefix ++ suffix) =
      some (prefix, suffix) := by

  subst n
  exact takeExactly_length_append prefix suffix

end ExactPrefixExtraction


section FramedTemplateComponents

variable {α : Type u}

/-- Flat tokens for a structurally serialized template tuple.  A component
header contains the exact number of following atom payload tokens. -/
inductive FramedTemplateBodyToken (α : Type u) where
  | componentLength (length : Nat)
  | atom (token : TemplateAtomStructuralToken α)
  deriving Repr

/-- Embed structural atom tokens into the flat framed-token alphabet. -/
def wrapStructuralAtomTokens
    (tokens : List (TemplateAtomStructuralToken α)) :
    List (FramedTemplateBodyToken α) :=
  tokens.map FramedTemplateBodyToken.atom

/-- Remove the atom wrapper from a payload.  A nested component header inside a
payload is rejected. -/
def unwrapStructuralAtomTokens :
    List (FramedTemplateBodyToken α) →
      Option (List (TemplateAtomStructuralToken α))

  | [] =>
      some []

  | .componentLength _ :: _ =>
      none

  | .atom token :: rest =>
      match unwrapStructuralAtomTokens rest with
      | none =>
          none
      | some tokens =>
          some (token :: tokens)

/-- Wrapping and then unwrapping a structural atom-token list is exact. -/
@[simp] theorem unwrapStructuralAtomTokens_wrap
    (tokens : List (TemplateAtomStructuralToken α)) :
    unwrapStructuralAtomTokens
        (wrapStructuralAtomTokens tokens) =
      some tokens := by

  induction tokens with

  | nil =>
      rfl

  | cons token tokens ih =>
      simp [
        wrapStructuralAtomTokens,
        unwrapStructuralAtomTokens,
        ih
      ]

/-- Atom wrapping preserves payload length. -/
@[simp] theorem wrapStructuralAtomTokens_length
    (tokens : List (TemplateAtomStructuralToken α)) :
    (wrapStructuralAtomTokens tokens).length =
      tokens.length := by

  simp [wrapStructuralAtomTokens]

/-- Frame one output component by prefixing its structural token count. -/
def frameTemplateWord
    {dB dC : Nat}
    (word : TemplateWord α dB dC) :
    List (FramedTemplateBodyToken α) :=
  .componentLength word.length ::
    wrapStructuralAtomTokens
      (encodeTemplateWordStructural word)

/-- One framed component uses exactly one header token plus one token per
original template atom. -/
@[simp] theorem frameTemplateWord_length
    {dB dC : Nat}
    (word : TemplateWord α dB dC) :
    (frameTemplateWord word).length =
      word.length + 1 := by

  simp [frameTemplateWord, Nat.add_comm]

/-- The exact prefix extractor recognizes the payload of a correctly framed
component even when another flat suffix follows it. -/
@[simp] theorem takeExactly_framedPayload_append
    {dB dC : Nat}
    (word : TemplateWord α dB dC)
    (suffix : List (FramedTemplateBodyToken α)) :
    takeExactly word.length
        (wrapStructuralAtomTokens
            (encodeTemplateWordStructural word) ++
          suffix) =
      some
        (wrapStructuralAtomTokens
            (encodeTemplateWordStructural word),
          suffix) := by

  apply takeExactly_append_of_length
  simp

/-- Checked decoding of one framed component, returning the unused suffix of
its flat token stream. -/
def decodeFramedTemplateWord
    (dB dC : Nat) :
    List (FramedTemplateBodyToken α) →
      Option
        (TemplateWord α dB dC ×
          List (FramedTemplateBodyToken α))

  | [] =>
      none

  | .atom _ :: _ =>
      none

  | .componentLength n :: rest =>
      match takeExactly n rest with
      | none =>
          none
      | some (payload, suffix) =>
          match unwrapStructuralAtomTokens payload with
          | none =>
              none
          | some atomTokens =>
              match
                  decodeTemplateWordStructural
                    dB dC atomTokens with
              | none =>
                  none
              | some word =>
                  some (word, suffix)

/-- A correctly framed component is recovered exactly and leaves an arbitrary
following suffix untouched. -/
@[simp] theorem decodeFramedTemplateWord_frame_append
    {dB dC : Nat}
    (word : TemplateWord α dB dC)
    (suffix : List (FramedTemplateBodyToken α)) :
    decodeFramedTemplateWord dB dC
        (frameTemplateWord word ++ suffix) =
      some (word, suffix) := by

  simp [
    decodeFramedTemplateWord,
    frameTemplateWord
  ]

/-- A flat stream beginning with an atom rather than a component header is
rejected. -/
@[simp] theorem decodeFramedTemplateWord_atomHead
    (dB dC : Nat)
    (token : TemplateAtomStructuralToken α)
    (rest : List (FramedTemplateBodyToken α)) :
    decodeFramedTemplateWord dB dC
        (.atom token :: rest) =
      none := by

  rfl

/-- Flatten an ordered list of output-component words. -/
def encodeFramedTemplateWords
    {dB dC : Nat} :
    List (TemplateWord α dB dC) →
      List (FramedTemplateBodyToken α)

  | [] =>
      []

  | word :: words =>
      frameTemplateWord word ++
        encodeFramedTemplateWords words

/-- Decode exactly `componentCount` framed output components and require the
flat stream to end at that point. -/
def decodeFramedTemplateWords
    (dB dC : Nat) :
    Nat →
      List (FramedTemplateBodyToken α) →
        Option (List (TemplateWord α dB dC))

  | 0, [] =>
      some []

  | 0, _ :: _ =>
      none

  | n + 1, tokens =>
      match decodeFramedTemplateWord dB dC tokens with
      | none =>
          none
      | some (word, suffix) =>
          match
              decodeFramedTemplateWords
                dB dC n suffix with
          | none =>
              none
          | some words =>
              some (word :: words)

/-- Arbitrary ordered component lists survive flattening and checked decoding
exactly. -/
@[simp] theorem decodeFramedTemplateWords_encode
    {dB dC : Nat}
    (words : List (TemplateWord α dB dC)) :
    decodeFramedTemplateWords dB dC
        words.length
        (encodeFramedTemplateWords words) =
      some words := by

  induction words with

  | nil =>
      rfl

  | cons word words ih =>
      simp [
        encodeFramedTemplateWords,
        decodeFramedTemplateWords,
        ih
      ]

/-- Exact token count of the flattened component-list representation. -/
@[simp] theorem encodeFramedTemplateWords_length
    {dB dC : Nat}
    (words : List (TemplateWord α dB dC)) :
    (encodeFramedTemplateWords words).length =
      words.length +
        (words.map List.length).sum := by

  induction words with

  | nil =>
      rfl

  | cons word words ih =>
      simp [
        encodeFramedTemplateWords,
        frameTemplateWord_length,
        ih,
        Nat.add_assoc,
        Nat.add_left_comm,
        Nat.add_comm
      ]

/-- Convert a dependent template tuple into its ordered output-component list. -/
def templateTupleStructuralWords
    {e dB dC : Nat}
    (body : TemplateTuple α e dB dC) :
    List (TemplateWord α dB dC) :=
  List.ofFn body

/-- Flat framed serialization of a complete dependent template tuple. -/
def encodeTemplateTupleFramed
    {e dB dC : Nat}
    (body : TemplateTuple α e dB dC) :
    List (FramedTemplateBodyToken α) :=
  encodeFramedTemplateWords
    (templateTupleStructuralWords body)

/-- A complete dependent template tuple is recovered as its canonical ordered
component list. -/
@[simp] theorem decodeTemplateTupleFramed_encode
    {e dB dC : Nat}
    (body : TemplateTuple α e dB dC) :
    decodeFramedTemplateWords dB dC e
        (encodeTemplateTupleFramed body) =
      some (templateTupleStructuralWords body) := by

  simpa [
    encodeTemplateTupleFramed,
    templateTupleStructuralWords
  ] using
    (decodeFramedTemplateWords_encode
      (templateTupleStructuralWords body))

/-- Exact token count of a complete framed template tuple. -/
@[simp] theorem encodeTemplateTupleFramed_length
    {e dB dC : Nat}
    (body : TemplateTuple α e dB dC) :
    (encodeTemplateTupleFramed body).length =
      e +
        ((templateTupleStructuralWords body).map
          List.length).sum := by

  simp [
    encodeTemplateTupleFramed,
    templateTupleStructuralWords
  ]

end FramedTemplateComponents


section BinaryRuleBodyFraming

variable {N : Type v}
variable {α : Type u}
variable {arity : N → Nat}

namespace BinaryRule

/-- Flat length-framed structural body stream of an actual dependent binary
rule. -/
def framedStructuralBodyTokens
    (ρ : BinaryRule N α arity) :
    List (FramedTemplateBodyToken α) :=
  encodeTemplateTupleFramed ρ.body

/-- The flat body stream of every actual binary rule decodes to the canonical
ordered list of all output components. -/
@[simp] theorem decode_framedStructuralBodyTokens
    (ρ : BinaryRule N α arity) :
    decodeFramedTemplateWords
        (arity ρ.left)
        (arity ρ.right)
        (arity ρ.lhs)
        ρ.framedStructuralBodyTokens =
      some (List.ofFn ρ.body) := by

  exact decodeTemplateTupleFramed_encode ρ.body

/-- Exact flat-token count for the body of an actual binary rule. -/
@[simp] theorem framedStructuralBodyTokens_length
    (ρ : BinaryRule N α arity) :
    ρ.framedStructuralBodyTokens.length =
      arity ρ.lhs +
        ((List.ofFn ρ.body).map List.length).sum := by

  exact encodeTemplateTupleFramed_length ρ.body

/-- Compact round-trip and token-count package for complete binary-rule body
framing. -/
theorem framedStructuralBodyTokens_roundTrip_package
    (ρ : BinaryRule N α arity) :
    (decodeFramedTemplateWords
        (arity ρ.left)
        (arity ρ.right)
        (arity ρ.lhs)
        ρ.framedStructuralBodyTokens =
      some (List.ofFn ρ.body)) ∧
      (ρ.framedStructuralBodyTokens.length =
        arity ρ.lhs +
          ((List.ofFn ρ.body).map List.length).sum) := by

  constructor

  · exact ρ.decode_framedStructuralBodyTokens

  · exact ρ.framedStructuralBodyTokens_length

end BinaryRule

end BinaryRuleBodyFraming

end MCFG
