/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG.ConcreteCanonicalLearnerWorkingGrammarTerminalAlphabetEncoding

/-!
# ConcreteCanonicalLearnerWorkingGrammarBinaryRuleNaturalSerialization.lean

The preceding file removes the last alphabet-valued payload from framed binary
rule bodies: every terminal is represented by a dense natural code in the
finite alphabet

```text
insert dummy (sampleAlphabet K).
```

This file completes the next serialization layer.  Every alphabet-free framed
body token is encoded by exactly two natural numbers:

```text
0, n    component-length header
1, c    terminal code
2, i    left-child variable index
3, j    right-child variable index.
```

A counted decoder parses exactly the prescribed number of token pairs and
returns the unconsumed suffix.  The exact decoder additionally requires that no
suffix remain.  We prove complete stream round trips and the exact length
formula

```text
encodedBody.length = 2 * bodyTokenCount.
```

We then combine this stream with the three global nonterminal codes of a
compiled binary rule.  A complete pure-natural representation is

```text
[lhsCode, leftCode, rightCode, bodyTokenCount] ++ encodedBody.
```

The checked decoder verifies the header shape, the declared token count, the
absence of trailing data, all terminal codes, all variable indices, the output
component framing, and all three nonterminal references before rebuilding the
dependent `BinaryRule`.

The main theorem is the complete natural-list round trip, under the precise
finite-terminal condition needed at this stage:

```lean
H.decodeCompiledBinaryRuleNaturalList dummy
    (H.encodeCompiledBinaryRuleNaturalList dummy rho)
  = some rho.
```

No target grammar is supplied to the learner.
No `sorry`, `admit`, or `axiom` is used.
-/

namespace MCFG

universe u v

section NaturalTokenPairCodec

/-- First natural field of one alphabet-free framed body token. -/
def framedTemplateBodyNaturalTokenTag :
    FramedTemplateBodyNaturalToken → Nat

  | .componentLength _ =>
      0

  | .atom (.terminalCode _) =>
      1

  | .atom (.leftVar _) =>
      2

  | .atom (.rightVar _) =>
      3

/-- Second natural field of one alphabet-free framed body token. -/
def framedTemplateBodyNaturalTokenPayload :
    FramedTemplateBodyNaturalToken → Nat

  | .componentLength n =>
      n

  | .atom (.terminalCode code) =>
      code

  | .atom (.leftVar index) =>
      index

  | .atom (.rightVar index) =>
      index

/-- Checked reconstruction of one alphabet-free framed body token from its two
natural fields. -/
def decodeFramedTemplateBodyNaturalTokenPair
    (tag payload : Nat) :
    Option FramedTemplateBodyNaturalToken :=

  match tag with

  | 0 =>
      some (.componentLength payload)

  | 1 =>
      some (.atom (.terminalCode payload))

  | 2 =>
      some (.atom (.leftVar payload))

  | 3 =>
      some (.atom (.rightVar payload))

  | _ =>
      none

/-- Every alphabet-free framed token survives its two-field natural codec. -/
@[simp] theorem decodeFramedTemplateBodyNaturalTokenPair_encode
    (token : FramedTemplateBodyNaturalToken) :
    decodeFramedTemplateBodyNaturalTokenPair
        (framedTemplateBodyNaturalTokenTag token)
        (framedTemplateBodyNaturalTokenPayload token) =
      some token := by

  cases token with

  | componentLength n =>
      rfl

  | atom atom =>
      cases atom <;> rfl

/-- Flatten a token list as consecutive `[tag, payload]` pairs. -/
def encodeFramedTemplateBodyNaturalStream :
    List FramedTemplateBodyNaturalToken → List Nat

  | [] =>
      []

  | token :: rest =>
      framedTemplateBodyNaturalTokenTag token ::
        framedTemplateBodyNaturalTokenPayload token ::
          encodeFramedTemplateBodyNaturalStream rest

/-- Parse exactly `tokenCount` natural token pairs, retaining the unconsumed
suffix. -/
def decodeFramedTemplateBodyNaturalStreamAux :
    Nat → List Nat →
      Option
        (List FramedTemplateBodyNaturalToken ×
          List Nat)

  | 0, codes =>
      some ([], codes)

  | Nat.succ tokenCount,
      tag :: payload :: rest =>
      match
          decodeFramedTemplateBodyNaturalTokenPair
            tag payload with

      | none =>
          none

      | some token =>
          match
              decodeFramedTemplateBodyNaturalStreamAux
                tokenCount rest with

          | none =>
              none

          | some (tokens, suffix) =>
              some (token :: tokens, suffix)

  | Nat.succ _, _ =>
      none

/-- Parsing an encoded token stream consumes precisely that stream and leaves
an arbitrary supplied suffix untouched. -/
@[simp] theorem decodeFramedTemplateBodyNaturalStreamAux_encode_append :
    ∀ (tokens : List FramedTemplateBodyNaturalToken)
      (suffix : List Nat),
      decodeFramedTemplateBodyNaturalStreamAux
          tokens.length
          (encodeFramedTemplateBodyNaturalStream tokens ++
            suffix) =
        some (tokens, suffix)

  | [], suffix => by
      rfl

  | token :: rest, suffix => by
      cases token with

      | componentLength n =>
          simp [
            encodeFramedTemplateBodyNaturalStream,
            decodeFramedTemplateBodyNaturalStreamAux,
            framedTemplateBodyNaturalTokenTag,
            framedTemplateBodyNaturalTokenPayload,
            decodeFramedTemplateBodyNaturalTokenPair,
            decodeFramedTemplateBodyNaturalStreamAux_encode_append
              rest suffix
          ]

      | atom atom =>
          cases atom <;>
            simp [
              encodeFramedTemplateBodyNaturalStream,
              decodeFramedTemplateBodyNaturalStreamAux,
              framedTemplateBodyNaturalTokenTag,
              framedTemplateBodyNaturalTokenPayload,
              decodeFramedTemplateBodyNaturalTokenPair,
              decodeFramedTemplateBodyNaturalStreamAux_encode_append
                rest suffix
            ]

/-- Exact token-stream decoder: parsing must consume all supplied natural data. -/
def decodeFramedTemplateBodyNaturalStreamExact
    (tokenCount : Nat)
    (codes : List Nat) :
    Option (List FramedTemplateBodyNaturalToken) :=

  match
      decodeFramedTemplateBodyNaturalStreamAux
        tokenCount codes with

  | some (tokens, []) =>
      some tokens

  | _ =>
      none

/-- Exact stream decoding after encoding is the identity. -/
@[simp] theorem decodeFramedTemplateBodyNaturalStreamExact_encode
    (tokens : List FramedTemplateBodyNaturalToken) :
    decodeFramedTemplateBodyNaturalStreamExact
        tokens.length
        (encodeFramedTemplateBodyNaturalStream tokens) =
      some tokens := by

  unfold decodeFramedTemplateBodyNaturalStreamExact

  rw [
    show
      encodeFramedTemplateBodyNaturalStream tokens =
        encodeFramedTemplateBodyNaturalStream tokens ++ [] by
        simp
  ]

  rw [
    decodeFramedTemplateBodyNaturalStreamAux_encode_append
      tokens []
  ]

/-- Every alphabet-free framed body token contributes exactly two natural
fields. -/
@[simp] theorem encodeFramedTemplateBodyNaturalStream_length :
    ∀ (tokens : List FramedTemplateBodyNaturalToken),
      (encodeFramedTemplateBodyNaturalStream tokens).length =
        2 * tokens.length

  | [] => by
      rfl

  | token :: rest => by
      simp [
        encodeFramedTemplateBodyNaturalStream,
        encodeFramedTemplateBodyNaturalStream_length rest,
        Nat.mul_succ,
        Nat.add_assoc,
        Nat.add_comm,
        Nat.add_left_comm
      ]

/-- Compact pair-stream codec endpoint. -/
theorem framedTemplateBodyNaturalStreamCodec_package
    (tokens : List FramedTemplateBodyNaturalToken) :
    (decodeFramedTemplateBodyNaturalStreamExact
        tokens.length
        (encodeFramedTemplateBodyNaturalStream tokens) =
      some tokens) ∧
      ((encodeFramedTemplateBodyNaturalStream tokens).length =
        2 * tokens.length) := by

  constructor

  · exact
      decodeFramedTemplateBodyNaturalStreamExact_encode
        tokens

  · exact
      encodeFramedTemplateBodyNaturalStream_length
        tokens

end NaturalTokenPairCodec


section CompleteBinaryRuleNaturalCodec

variable {α : Type u}
variable {M : Type v} [Monoid M]
variable {K : Finset (Word α)}
variable {obs : α → M}
variable {f : Nat}

/-- Alphabet-free packet for one complete compiled binary rule.  Its body still
has token structure, but all payloads are natural numbers. -/
structure CorrectedConcreteCompiledBinaryRuleNaturalPacket
    (H : CorrectedConcreteFiniteHypothesis K obs f) where

  lhsCode : Nat
  leftCode : Nat
  rightCode : Nat
  bodyTokens : List FramedTemplateBodyNaturalToken

namespace CorrectedConcreteFiniteHypothesis

variable
  (H : CorrectedConcreteFiniteHypothesis K obs f)

/-- Replace every terminal payload in a complete structural binary-rule packet
by its dense natural code. -/
noncomputable def encodeCompiledBinaryRuleNaturalPacket
    (dummy : α)
    (rho : BinaryRule
      (CorrectedConcreteCutGrammarNonterminal H)
      α
      (correctedConcreteCutGrammarArity H)) :
    CorrectedConcreteCompiledBinaryRuleNaturalPacket H := by

  let structural :=
    H.encodeCompiledBinaryRuleStructuralPacket dummy rho

  exact
    { lhsCode := structural.lhsCode
      leftCode := structural.leftCode
      rightCode := structural.rightCode
      bodyTokens :=
        encodeFramedTemplateBodyNatural
          K dummy structural.bodyTokens }

/-- Checked reconstruction of a dependent binary rule from an alphabet-free
natural packet. -/
noncomputable def decodeCompiledBinaryRuleNaturalPacket
    (dummy : α)
    (packet : CorrectedConcreteCompiledBinaryRuleNaturalPacket H) :
    Option
      (BinaryRule
        (CorrectedConcreteCutGrammarNonterminal H)
        α
        (correctedConcreteCutGrammarArity H)) :=

  match
      decodeFramedTemplateBodyNatural
        K dummy packet.bodyTokens with

  | none =>
      none

  | some bodyTokens =>
      H.decodeCompiledBinaryRuleStructuralPacket dummy
        { lhsCode := packet.lhsCode
          leftCode := packet.leftCode
          rightCode := packet.rightCode
          bodyTokens := bodyTokens }

/-- Natural-packet round trip, under the exact condition that all terminal
payloads of the rule occur in the augmented finite compiled alphabet. -/
@[simp] theorem decodeCompiledBinaryRuleNaturalPacket_encode
    (dummy : α)
    (rho : BinaryRule
      (CorrectedConcreteCutGrammarNonterminal H)
      α
      (correctedConcreteCutGrammarArity H))
    (hterminals :
      ∀ token ∈ rho.framedStructuralBodyTokens,
        token.TerminalsIn
          (compiledTerminalAlphabet K dummy)) :
    H.decodeCompiledBinaryRuleNaturalPacket dummy
        (H.encodeCompiledBinaryRuleNaturalPacket dummy rho) =
      some rho := by

  classical

  unfold
    decodeCompiledBinaryRuleNaturalPacket
    encodeCompiledBinaryRuleNaturalPacket

  dsimp [encodeCompiledBinaryRuleStructuralPacket]

  rw [
    decodeFramedTemplateBodyNatural_encode
      K dummy rho.framedStructuralBodyTokens hterminals
  ]

  exact
    H.decodeCompiledBinaryRuleStructuralPacket_encode
      dummy rho

/-- Serialize one alphabet-free natural packet to one pure list of natural
numbers.  The fourth header field declares the number of body tokens. -/
def serializeCompiledBinaryRuleNaturalPacket
    (packet : CorrectedConcreteCompiledBinaryRuleNaturalPacket H) :
    List Nat :=

  [ packet.lhsCode,
    packet.leftCode,
    packet.rightCode,
    packet.bodyTokens.length ] ++
      encodeFramedTemplateBodyNaturalStream
        packet.bodyTokens

/-- Checked inverse of the pure-natural packet serialization. -/
def deserializeCompiledBinaryRuleNaturalPacket
    (codes : List Nat) :
    Option (CorrectedConcreteCompiledBinaryRuleNaturalPacket H) :=

  match codes with

  | lhsCode :: leftCode :: rightCode ::
      bodyTokenCount :: payload =>
      match
          decodeFramedTemplateBodyNaturalStreamExact
            bodyTokenCount payload with

      | none =>
          none

      | some bodyTokens =>
          some
            { lhsCode := lhsCode
              leftCode := leftCode
              rightCode := rightCode
              bodyTokens := bodyTokens }

  | _ =>
      none

/-- Pure-natural serialization and deserialization are exact for every natural
packet. -/
@[simp] theorem deserializeCompiledBinaryRuleNaturalPacket_serialize
    (packet : CorrectedConcreteCompiledBinaryRuleNaturalPacket H) :
    H.deserializeCompiledBinaryRuleNaturalPacket
        (H.serializeCompiledBinaryRuleNaturalPacket packet) =
      some packet := by

  rcases packet with
    ⟨lhsCode, leftCode, rightCode, bodyTokens⟩

  simp [
    serializeCompiledBinaryRuleNaturalPacket,
    deserializeCompiledBinaryRuleNaturalPacket
  ]

/-- Complete pure-natural encoding of one dependent compiled binary rule. -/
noncomputable def encodeCompiledBinaryRuleNaturalList
    (dummy : α)
    (rho : BinaryRule
      (CorrectedConcreteCutGrammarNonterminal H)
      α
      (correctedConcreteCutGrammarArity H)) :
    List Nat :=

  H.serializeCompiledBinaryRuleNaturalPacket
    (H.encodeCompiledBinaryRuleNaturalPacket dummy rho)

/-- Complete checked decoder from a pure natural list to a dependent compiled
binary rule. -/
noncomputable def decodeCompiledBinaryRuleNaturalList
    (dummy : α)
    (codes : List Nat) :
    Option
      (BinaryRule
        (CorrectedConcreteCutGrammarNonterminal H)
        α
        (correctedConcreteCutGrammarArity H)) :=

  match
      H.deserializeCompiledBinaryRuleNaturalPacket codes with

  | none =>
      none

  | some packet =>
      H.decodeCompiledBinaryRuleNaturalPacket dummy packet

/-- Complete pure-natural-list round trip for one compiled binary rule. -/
@[simp] theorem decodeCompiledBinaryRuleNaturalList_encode
    (dummy : α)
    (rho : BinaryRule
      (CorrectedConcreteCutGrammarNonterminal H)
      α
      (correctedConcreteCutGrammarArity H))
    (hterminals :
      ∀ token ∈ rho.framedStructuralBodyTokens,
        token.TerminalsIn
          (compiledTerminalAlphabet K dummy)) :
    H.decodeCompiledBinaryRuleNaturalList dummy
        (H.encodeCompiledBinaryRuleNaturalList dummy rho) =
      some rho := by

  classical

  unfold
    encodeCompiledBinaryRuleNaturalList
    decodeCompiledBinaryRuleNaturalList

  rw [
    H.deserializeCompiledBinaryRuleNaturalPacket_serialize
  ]

  exact
    H.decodeCompiledBinaryRuleNaturalPacket_encode
      dummy rho hterminals

/-- Exact length of the pure-natural serialization of an arbitrary natural
packet. -/
@[simp] theorem serializeCompiledBinaryRuleNaturalPacket_length
    (packet : CorrectedConcreteCompiledBinaryRuleNaturalPacket H) :
    (H.serializeCompiledBinaryRuleNaturalPacket packet).length =
      4 + 2 * packet.bodyTokens.length := by

  simp [
    serializeCompiledBinaryRuleNaturalPacket,
    Nat.add_assoc,
    Nat.add_comm,
    Nat.add_left_comm
  ]

/-- Natural terminal coding preserves the body-token count of a complete binary
rule packet. -/
@[simp] theorem encodeCompiledBinaryRuleNaturalPacket_bodyTokens_length
    (dummy : α)
    (rho : BinaryRule
      (CorrectedConcreteCutGrammarNonterminal H)
      α
      (correctedConcreteCutGrammarArity H)) :
    (H.encodeCompiledBinaryRuleNaturalPacket dummy rho).
        bodyTokens.length =
      rho.framedStructuralBodyTokens.length := by

  simp [
    encodeCompiledBinaryRuleNaturalPacket,
    encodeCompiledBinaryRuleStructuralPacket
  ]

/-- Exact pure-natural field count of one complete binary rule. -/
@[simp] theorem encodeCompiledBinaryRuleNaturalList_length
    (dummy : α)
    (rho : BinaryRule
      (CorrectedConcreteCutGrammarNonterminal H)
      α
      (correctedConcreteCutGrammarArity H)) :
    (H.encodeCompiledBinaryRuleNaturalList dummy rho).length =
      4 +
        2 *
          (correctedConcreteCutGrammarArity H rho.lhs +
            ((List.ofFn rho.body).map List.length).sum) := by

  unfold encodeCompiledBinaryRuleNaturalList

  rw [
    H.serializeCompiledBinaryRuleNaturalPacket_length
  ]

  rw [
    H.encodeCompiledBinaryRuleNaturalPacket_bodyTokens_length
  ]

  rw [rho.framedStructuralBodyTokens_length]

/-- Compact endpoint collecting the complete pure-natural round trip and exact
serialized field count. -/
theorem compiledBinaryRuleNaturalListCodec_package
    (dummy : α)
    (rho : BinaryRule
      (CorrectedConcreteCutGrammarNonterminal H)
      α
      (correctedConcreteCutGrammarArity H))
    (hterminals :
      ∀ token ∈ rho.framedStructuralBodyTokens,
        token.TerminalsIn
          (compiledTerminalAlphabet K dummy)) :
    (H.decodeCompiledBinaryRuleNaturalList dummy
        (H.encodeCompiledBinaryRuleNaturalList dummy rho) =
      some rho) ∧
      ((H.encodeCompiledBinaryRuleNaturalList dummy rho).length =
        4 +
          2 *
            (correctedConcreteCutGrammarArity H rho.lhs +
              ((List.ofFn rho.body).map List.length).sum)) := by

  constructor

  · exact
      H.decodeCompiledBinaryRuleNaturalList_encode
        dummy rho hterminals

  · exact
      H.encodeCompiledBinaryRuleNaturalList_length
        dummy rho

end CorrectedConcreteFiniteHypothesis

end CompleteBinaryRuleNaturalCodec

end MCFG
