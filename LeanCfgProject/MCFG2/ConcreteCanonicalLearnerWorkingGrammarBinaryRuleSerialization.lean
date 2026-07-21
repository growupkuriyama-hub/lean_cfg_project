/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG2.ConcreteCanonicalLearnerWorkingGrammarTemplateTupleFraming

/-!
# ConcreteCanonicalLearnerWorkingGrammarBinaryRuleSerialization.lean

The preceding file serializes the dependent body of a binary MCFG rule as one
length-framed flat token stream.  A complete binary rule also contains three
nonterminal references:

```text
lhs, left child, right child.
```

This file combines those references with the framed body.  Each nonterminal is
encoded by the collision-free global tagged dense code of the complete compiled
grammar presentation.  A checked decoder then:

* decodes all three codes and requires them to be nonterminal entries;
* uses the recovered child arities to check every structural template token;
* uses the recovered left-hand-side arity to check the component framing;
* rebuilds the dependent `TemplateTuple` and hence the original `BinaryRule`.

The main theorem is the whole-rule round trip

```lean
H.decodeCompiledBinaryRuleStructuralPacket dummy
    (H.encodeCompiledBinaryRuleStructuralPacket dummy rho)
  = some rho.
```

Thus a binary rule is no longer treated as an opaque top-level object: its
nonterminal references and complete dependent template body now have an explicit
checked structural codec.  Terminal payloads are still carried as values of
`alpha`; assigning them finite natural-number codes is the next serialization
layer.

No target grammar is supplied to the learner.
No `sorry`, `admit`, or `axiom` is used.
-/

namespace MCFG

universe u v

section DecodedComponentCount

variable {α : Type u}

/-- Successful decoding of exactly `componentCount` framed template words
returns exactly that many output components. -/
theorem decodeFramedTemplateWords_length_of_eq_some
    (dB dC componentCount : Nat) :
    ∀ (tokens : List (FramedTemplateBodyToken α))
      (words : List (TemplateWord α dB dC)),
      decodeFramedTemplateWords
          dB dC componentCount tokens = some words →
      words.length = componentCount

  | tokens, words, hdecode => by
      induction componentCount generalizing tokens words with

      | zero =>
          cases tokens with

          | nil =>
              have hwords : words = [] := by
                simpa [decodeFramedTemplateWords] using hdecode.symm

              subst words
              rfl

          | cons token rest =>
              simp [decodeFramedTemplateWords] at hdecode

      | succ n ih =>
          cases hfirst :
              decodeFramedTemplateWord dB dC tokens with

          | none =>
              simp [decodeFramedTemplateWords, hfirst] at hdecode

          | some result =>
              rcases result with ⟨word, suffix⟩

              cases hrest :
                  decodeFramedTemplateWords dB dC n suffix with

              | none =>
                  simp [
                    decodeFramedTemplateWords,
                    hfirst,
                    hrest
                  ] at hdecode

              | some decodedRest =>
                  have hwords :
                      words = word :: decodedRest := by
                    simpa [
                      decodeFramedTemplateWords,
                      hfirst,
                      hrest
                    ] using hdecode.symm

                  subst words

                  have hlength :
                      decodedRest.length = n :=
                    ih suffix decodedRest hrest

                  simp [hlength]

/-- Rebuild a dependent template tuple from an ordered component list whose
length is exactly the required output arity. -/
def templateTupleOfExactLength
    {α : Type u}
    {e dB dC : Nat}
    (words : List (TemplateWord α dB dC))
    (hlength : words.length = e) :
    TemplateTuple α e dB dC :=
  fun i =>
    words.get
      ⟨i.1, by
        simpa [hlength] using i.2⟩

/-- Converting a dependent template tuple to `List.ofFn` and back is exact. -/
@[simp] theorem templateTupleOfExactLength_ofFn
    {α : Type u}
    {e dB dC : Nat}
    (body : TemplateTuple α e dB dC) :
    templateTupleOfExactLength
        (List.ofFn body)
        (by simp) =
      body := by

  funext i
  simp [templateTupleOfExactLength]

end DecodedComponentCount


section CompleteBinaryRuleStructuralCodec

variable {α : Type u}
variable {M : Type v} [Monoid M]
variable {K : Finset (Word α)}
variable {obs : α → M}
variable {f : Nat}

/-- Nondependent structural packet for one complete compiled binary rule.  The
three header fields use the global tagged presentation code; the body is the
length-framed structural token stream from the preceding file. -/
structure CorrectedConcreteCompiledBinaryRuleStructuralPacket
    (H : CorrectedConcreteFiniteHypothesis K obs f) where

  lhsCode : Nat
  leftCode : Nat
  rightCode : Nat
  bodyTokens : List (FramedTemplateBodyToken α)

namespace CorrectedConcreteFiniteHypothesis

variable
  (H : CorrectedConcreteFiniteHypothesis K obs f)

/-- Decode one global tagged presentation code, accepting only nonterminal
entries. -/
noncomputable def decodeCompiledNonterminalCode
    (dummy : α)
    (code : Nat) :
    Option (CorrectedConcreteCutGrammarNonterminal H) :=
  match H.compiledGrammarGlobalDenseDecode dummy code with
  | some (.nonterminal A) =>
      some A
  | _ =>
      none

/-- Every compiled nonterminal survives global tagged encoding followed by the
nonterminal-only decoder. -/
@[simp] theorem decodeCompiledNonterminalCode_encode
    (dummy : α)
    (A : CorrectedConcreteCutGrammarNonterminal H) :
    H.decodeCompiledNonterminalCode dummy
        (H.compiledGrammarGlobalDenseCode dummy
          (.nonterminal A)) =
      some A := by

  classical

  have hentry :
      CorrectedConcreteCompiledGrammarPresentationEntry.nonterminal A ∈
        H.compiledGrammarPresentationEntries dummy :=
    H.nonterminal_mem_compiledGrammarPresentationEntries
      dummy A (H.mem_compiledGrammarNonterminals A)

  unfold decodeCompiledNonterminalCode

  rw [
    H.compiledGrammarGlobalDenseDecode_encode_of_mem
      dummy (.nonterminal A) hentry
  ]

/-- Encode a complete dependent binary rule into its three global nonterminal
references and its flat framed structural body. -/
noncomputable def encodeCompiledBinaryRuleStructuralPacket
    (dummy : α)
    (rho : BinaryRule
      (CorrectedConcreteCutGrammarNonterminal H)
      α
      (correctedConcreteCutGrammarArity H)) :
    CorrectedConcreteCompiledBinaryRuleStructuralPacket H where

  lhsCode :=
    H.compiledGrammarGlobalDenseCode dummy
      (.nonterminal rho.lhs)

  leftCode :=
    H.compiledGrammarGlobalDenseCode dummy
      (.nonterminal rho.left)

  rightCode :=
    H.compiledGrammarGlobalDenseCode dummy
      (.nonterminal rho.right)

  bodyTokens :=
    rho.framedStructuralBodyTokens

/-- Checked reconstruction of a complete dependent binary rule from its
structural packet. -/
noncomputable def decodeCompiledBinaryRuleStructuralPacket
    (dummy : α)
    (packet : CorrectedConcreteCompiledBinaryRuleStructuralPacket H) :
    Option
      (BinaryRule
        (CorrectedConcreteCutGrammarNonterminal H)
        α
        (correctedConcreteCutGrammarArity H)) :=

  match
      H.decodeCompiledNonterminalCode
        dummy packet.lhsCode with

  | none =>
      none

  | some lhs =>
      match
          H.decodeCompiledNonterminalCode
            dummy packet.leftCode with

      | none =>
          none

      | some left =>
          match
              H.decodeCompiledNonterminalCode
                dummy packet.rightCode with

          | none =>
              none

          | some right =>
              match hbody :
                  decodeFramedTemplateWords
                    (correctedConcreteCutGrammarArity H left)
                    (correctedConcreteCutGrammarArity H right)
                    (correctedConcreteCutGrammarArity H lhs)
                    packet.bodyTokens with

              | none =>
                  none

              | some words =>
                  some
                    { lhs := lhs
                      left := left
                      right := right
                      body :=
                        templateTupleOfExactLength words
                          (decodeFramedTemplateWords_length_of_eq_some
                            (correctedConcreteCutGrammarArity H left)
                            (correctedConcreteCutGrammarArity H right)
                            (correctedConcreteCutGrammarArity H lhs)
                            packet.bodyTokens words hbody) }

/-- Whole-rule exact round trip: the checked decoder reconstructs every binary
rule after structural packet encoding. -/
@[simp] theorem decodeCompiledBinaryRuleStructuralPacket_encode
    (dummy : α)
    (rho : BinaryRule
      (CorrectedConcreteCutGrammarNonterminal H)
      α
      (correctedConcreteCutGrammarArity H)) :
    H.decodeCompiledBinaryRuleStructuralPacket dummy
        (H.encodeCompiledBinaryRuleStructuralPacket dummy rho) =
      some rho := by

  classical

  simp [
    decodeCompiledBinaryRuleStructuralPacket,
    encodeCompiledBinaryRuleStructuralPacket,
    templateTupleOfExactLength_ofFn
  ]

/-- Exact number of framed body tokens stored by the complete structural packet. -/
@[simp] theorem encodeCompiledBinaryRuleStructuralPacket_bodyTokens_length
    (dummy : α)
    (rho : BinaryRule
      (CorrectedConcreteCutGrammarNonterminal H)
      α
      (correctedConcreteCutGrammarArity H)) :
    (H.encodeCompiledBinaryRuleStructuralPacket dummy rho).
        bodyTokens.length =
      correctedConcreteCutGrammarArity H rho.lhs +
        ((List.ofFn rho.body).map List.length).sum := by

  exact rho.framedStructuralBodyTokens_length

/-- Structural field count of one complete encoded binary rule: three header
codes plus all framed body tokens. -/
def compiledBinaryRuleStructuralFieldCount
    (dummy : α)
    (rho : BinaryRule
      (CorrectedConcreteCutGrammarNonterminal H)
      α
      (correctedConcreteCutGrammarArity H)) :
    Nat :=
  3 +
    (H.encodeCompiledBinaryRuleStructuralPacket dummy rho).
      bodyTokens.length

/-- Exact complete field count after expanding the framed body length. -/
@[simp] theorem compiledBinaryRuleStructuralFieldCount_eq
    (dummy : α)
    (rho : BinaryRule
      (CorrectedConcreteCutGrammarNonterminal H)
      α
      (correctedConcreteCutGrammarArity H)) :
    H.compiledBinaryRuleStructuralFieldCount dummy rho =
      3 +
        correctedConcreteCutGrammarArity H rho.lhs +
        ((List.ofFn rho.body).map List.length).sum := by

  simp [
    compiledBinaryRuleStructuralFieldCount,
    Nat.add_assoc
  ]

/-- Compact endpoint collecting whole-rule decoding and the exact structural
field count. -/
theorem compiledBinaryRuleStructuralCodec_package
    (dummy : α)
    (rho : BinaryRule
      (CorrectedConcreteCutGrammarNonterminal H)
      α
      (correctedConcreteCutGrammarArity H)) :
    (H.decodeCompiledBinaryRuleStructuralPacket dummy
        (H.encodeCompiledBinaryRuleStructuralPacket dummy rho) =
      some rho) ∧
      (H.compiledBinaryRuleStructuralFieldCount dummy rho =
        3 +
          correctedConcreteCutGrammarArity H rho.lhs +
          ((List.ofFn rho.body).map List.length).sum) := by

  constructor

  · exact
      H.decodeCompiledBinaryRuleStructuralPacket_encode
        dummy rho

  · exact
      H.compiledBinaryRuleStructuralFieldCount_eq
        dummy rho

end CorrectedConcreteFiniteHypothesis

end CompleteBinaryRuleStructuralCodec

end MCFG
