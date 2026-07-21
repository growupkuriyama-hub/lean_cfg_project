/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG2.ConcreteCanonicalLearnerWorkingGrammarTaggedDenseDecoding

/-!
# ConcreteCanonicalLearnerWorkingGrammarTemplateSerialization.lean

The preceding files constructed a finite tagged codec for the top-level entries
of the actual cut-compiled grammar presentation.  A binary-rule entry, however,
still contains a dependent template body:

```lean
Fin (arity lhs) ->
  List (TemplateAtom α (arity left) (arity right)).
```

Before serializing a whole binary rule, the dependent `Fin` indices inside its
atoms must be turned into ordinary natural-number payloads.  This file performs
that first internal serialization step.

We introduce a nondependent tagged token type

```lean
terminal a | leftVar i | rightVar j
```

and define encoders and checked decoders for template atoms and template words.
The decoder checks the two child arity bounds before rebuilding `Fin` indices.
We prove exact round trips for:

* every template atom;
* every template word;
* every component of every template tuple;
* every component of the body of an actual dependent binary rule.

Invalid variable indices are rejected explicitly.  Thus the internal atom lists
of a binary rule now have a self-checking, nondependent structural
representation.  A later file can add output-component framing and the three
nonterminal header codes to obtain a complete whole-rule codec.

No target grammar is supplied to the learner.
No `sorry`, `admit`, or `axiom` is used.
-/

namespace MCFG

universe u v

section StructuralTemplateTokens

variable {α : Type u}

/-- A nondependent structural token for one binary-template atom.  Child
variables carry ordinary natural-number indices; the decoder restores the
required `Fin` proof after checking the relevant child arity. -/
inductive TemplateAtomStructuralToken (α : Type u) where
  | terminal (a : α)
  | leftVar (index : Nat)
  | rightVar (index : Nat)
  deriving Repr

/-- Forget the dependent child-arity indices of one template atom. -/
def encodeTemplateAtomStructural
    {dB dC : Nat} :
    TemplateAtom α dB dC →
      TemplateAtomStructuralToken α

  | .terminal a =>
      .terminal a

  | .leftVar i =>
      .leftVar i.1

  | .rightVar j =>
      .rightVar j.1

/-- Checked reconstruction of one dependent template atom from a structural
nondependent token. -/
def decodeTemplateAtomStructural
    (dB dC : Nat) :
    TemplateAtomStructuralToken α →
      Option (TemplateAtom α dB dC)

  | .terminal a =>
      some (.terminal a)

  | .leftVar i =>
      if hi : i < dB then
        some (.leftVar ⟨i, hi⟩)
      else
        none

  | .rightVar j =>
      if hj : j < dC then
        some (.rightVar ⟨j, hj⟩)
      else
        none

/-- Every dependent template atom is recovered exactly after structural
encoding and checked decoding. -/
@[simp] theorem decodeTemplateAtomStructural_encode
    {dB dC : Nat}
    (atom : TemplateAtom α dB dC) :
    decodeTemplateAtomStructural dB dC
        (encodeTemplateAtomStructural atom) =
      some atom := by

  cases atom with

  | terminal a =>
      rfl

  | leftVar i =>
      simp [
        encodeTemplateAtomStructural,
        decodeTemplateAtomStructural,
        i.2
      ]

  | rightVar j =>
      simp [
        encodeTemplateAtomStructural,
        decodeTemplateAtomStructural,
        j.2
      ]

/-- Successful atom decoding is structurally faithful: re-encoding the decoded
atom returns the original token. -/
theorem encodeTemplateAtomStructural_of_decode_eq_some
    {dB dC : Nat}
    (token : TemplateAtomStructuralToken α)
    (atom : TemplateAtom α dB dC)
    (hdecode :
      decodeTemplateAtomStructural dB dC token =
        some atom) :
    encodeTemplateAtomStructural atom = token := by

  cases token with

  | terminal a =>
      simp [decodeTemplateAtomStructural] at hdecode
      subst atom
      rfl

  | leftVar i =>
      by_cases hi : i < dB

      · simp [decodeTemplateAtomStructural, hi] at hdecode
        subst atom
        rfl

      · simp [decodeTemplateAtomStructural, hi] at hdecode

  | rightVar j =>
      by_cases hj : j < dC

      · simp [decodeTemplateAtomStructural, hj] at hdecode
        subst atom
        rfl

      · simp [decodeTemplateAtomStructural, hj] at hdecode

/-- An out-of-range left-variable token is rejected. -/
@[simp] theorem decodeTemplateAtomStructural_leftVar_eq_none_iff
    (dB dC i : Nat) :
    decodeTemplateAtomStructural (α := α) dB dC
        (.leftVar i) = none ↔
      dB ≤ i := by

  by_cases hi : i < dB

  · simp [decodeTemplateAtomStructural, hi,
      Nat.not_le_of_lt hi]

  · have hle : dB ≤ i :=
      Nat.le_of_not_gt hi

    simp [decodeTemplateAtomStructural, hi, hle]

/-- An out-of-range right-variable token is rejected. -/
@[simp] theorem decodeTemplateAtomStructural_rightVar_eq_none_iff
    (dB dC j : Nat) :
    decodeTemplateAtomStructural (α := α) dB dC
        (.rightVar j) = none ↔
      dC ≤ j := by

  by_cases hj : j < dC

  · simp [decodeTemplateAtomStructural, hj,
      Nat.not_le_of_lt hj]

  · have hle : dC ≤ j :=
      Nat.le_of_not_gt hj

    simp [decodeTemplateAtomStructural, hj, hle]

/-- Structural encoding of one complete template word. -/
def encodeTemplateWordStructural
    {dB dC : Nat}
    (word : TemplateWord α dB dC) :
    List (TemplateAtomStructuralToken α) :=
  word.map encodeTemplateAtomStructural

/-- Checked decoding of a structural token list into one dependent template
word. -/
def decodeTemplateWordStructural
    (dB dC : Nat) :
    List (TemplateAtomStructuralToken α) →
      Option (TemplateWord α dB dC)

  | [] =>
      some []

  | token :: rest =>
      match decodeTemplateAtomStructural dB dC token with
      | none =>
          none
      | some atom =>
          match decodeTemplateWordStructural dB dC rest with
          | none =>
              none
          | some word =>
              some (atom :: word)

/-- Exact word-level round trip. -/
@[simp] theorem decodeTemplateWordStructural_encode
    {dB dC : Nat}
    (word : TemplateWord α dB dC) :
    decodeTemplateWordStructural dB dC
        (encodeTemplateWordStructural word) =
      some word := by

  induction word with

  | nil =>
      rfl

  | cons atom rest ih =>
      simp [
        encodeTemplateWordStructural,
        decodeTemplateWordStructural,
        ih
      ]

/-- Structural word encoding does not change the number of atoms. -/
@[simp] theorem encodeTemplateWordStructural_length
    {dB dC : Nat}
    (word : TemplateWord α dB dC) :
    (encodeTemplateWordStructural word).length =
      word.length := by

  simp [encodeTemplateWordStructural]

/-- Successful word decoding is structurally faithful. -/
theorem encodeTemplateWordStructural_of_decode_eq_some
    (dB dC : Nat) :
    ∀ (tokens : List (TemplateAtomStructuralToken α))
      (word : TemplateWord α dB dC),
      decodeTemplateWordStructural dB dC tokens = some word →
      encodeTemplateWordStructural word = tokens

  | [], word, hdecode => by
      simp [decodeTemplateWordStructural] at hdecode
      subst word
      rfl

  | token :: rest, word, hdecode => by
      cases hatom :
          decodeTemplateAtomStructural dB dC token with

      | none =>
          simp [decodeTemplateWordStructural, hatom] at hdecode

      | some atom =>
          cases hrest :
              decodeTemplateWordStructural dB dC rest with

          | none =>
              simp [
                decodeTemplateWordStructural,
                hatom,
                hrest
              ] at hdecode

          | some decodedRest =>
              have hword :
                  word = atom :: decodedRest := by
                simpa [
                  decodeTemplateWordStructural,
                  hatom,
                  hrest
                ] using hdecode.symm

              subst word

              have hatomEncode :
                  encodeTemplateAtomStructural atom = token :=
                encodeTemplateAtomStructural_of_decode_eq_some
                  token atom hatom

              have hrestEncode :
                  encodeTemplateWordStructural decodedRest = rest :=
                encodeTemplateWordStructural_of_decode_eq_some
                  dB dC rest decodedRest hrest

              simp [
                encodeTemplateWordStructural,
                hatomEncode,
                hrestEncode
              ]

/-- Pointwise structural encoding of a complete template tuple.  The output
arity remains in the outer finite index, while all inner child-variable indices
have become ordinary natural numbers. -/
def encodeTemplateTupleStructural
    {e dB dC : Nat}
    (body : TemplateTuple α e dB dC) :
    Fin e → List (TemplateAtomStructuralToken α) :=
  fun i =>
    encodeTemplateWordStructural (body i)

/-- Every component of an encoded template tuple decodes exactly. -/
@[simp] theorem decodeTemplateTupleStructural_component
    {e dB dC : Nat}
    (body : TemplateTuple α e dB dC)
    (i : Fin e) :
    decodeTemplateWordStructural dB dC
        (encodeTemplateTupleStructural body i) =
      some (body i) := by

  exact
    decodeTemplateWordStructural_encode
      (body i)

/-- Every structurally encoded template tuple is componentwise valid for its
original child arities. -/
theorem encodeTemplateTupleStructural_componentwise_valid
    {e dB dC : Nat}
    (body : TemplateTuple α e dB dC) :
    ∀ i : Fin e,
      ∃ word : TemplateWord α dB dC,
        decodeTemplateWordStructural dB dC
            (encodeTemplateTupleStructural body i) =
          some word := by

  intro i
  exact ⟨body i, by simp⟩

end StructuralTemplateTokens


section BinaryRuleBodySerialization

variable {N : Type v}
variable {α : Type u}
variable {arity : N → Nat}

namespace BinaryRule

/-- Nondependent token representation of each output component of a dependent
binary-rule body. -/
def structuralBodyTokens
    (ρ : BinaryRule N α arity) :
    Fin (arity ρ.lhs) →
      List (TemplateAtomStructuralToken α) :=
  encodeTemplateTupleStructural ρ.body

/-- Every component of an actual binary-rule body is recovered exactly from its
structural token list. -/
@[simp] theorem decode_structuralBodyTokens_component
    (ρ : BinaryRule N α arity)
    (i : Fin (arity ρ.lhs)) :
    decodeTemplateWordStructural
        (arity ρ.left)
        (arity ρ.right)
        (ρ.structuralBodyTokens i) =
      some (ρ.body i) := by

  exact
    decodeTemplateTupleStructural_component
      ρ.body i

/-- The structural representation preserves the atom count of each output
component. -/
@[simp] theorem structuralBodyTokens_component_length
    (ρ : BinaryRule N α arity)
    (i : Fin (arity ρ.lhs)) :
    (ρ.structuralBodyTokens i).length =
      (ρ.body i).length := by

  exact
    encodeTemplateWordStructural_length
      (ρ.body i)

/-- All structurally serialized output components of a binary rule are checked
valid by the decoder at the rule's own child arities. -/
theorem structuralBodyTokens_componentwise_valid
    (ρ : BinaryRule N α arity) :
    ∀ i : Fin (arity ρ.lhs),
      ∃ word :
          TemplateWord α
            (arity ρ.left)
            (arity ρ.right),
        decodeTemplateWordStructural
            (arity ρ.left)
            (arity ρ.right)
            (ρ.structuralBodyTokens i) =
          some word := by

  intro i
  exact ⟨ρ.body i, by simp⟩

/-- Compact package for the internal template serialization of one dependent
binary rule. -/
theorem structuralBodyTokens_roundTrip_package
    (ρ : BinaryRule N α arity) :
    (∀ i : Fin (arity ρ.lhs),
      decodeTemplateWordStructural
          (arity ρ.left)
          (arity ρ.right)
          (ρ.structuralBodyTokens i) =
        some (ρ.body i)) ∧
      (∀ i : Fin (arity ρ.lhs),
        (ρ.structuralBodyTokens i).length =
          (ρ.body i).length) := by

  constructor

  · intro i
    exact ρ.decode_structuralBodyTokens_component i

  · intro i
    exact ρ.structuralBodyTokens_component_length i

end BinaryRule

end BinaryRuleBodySerialization

end MCFG
