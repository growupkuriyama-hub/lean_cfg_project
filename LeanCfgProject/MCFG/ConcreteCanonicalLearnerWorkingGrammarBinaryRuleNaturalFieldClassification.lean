/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG.ConcreteCanonicalLearnerWorkingGrammarNaturalFieldEntryBounds

/-!
# ConcreteCanonicalLearnerWorkingGrammarBinaryRuleNaturalFieldClassification.lean

The preceding file reduces every top-level presentation-entry field to explicit
dense-code ranges, except for the local natural-value bound of a complete
binary-rule payload.

This file opens that final opaque top-level payload.

Every alphabet-free framed body token contributes exactly two natural fields:

```text
[tag, payload].
```

The tag is one of `0`, `1`, `2`, or `3`, and the payload is respectively

* an output-component length;
* a dense terminal code;
* a left-child variable index; or
* a right-child variable index.

We first prove an exact classification of every natural field in a flattened
body-token stream.  We then define the maximum token-local value and prove that
it bounds every field in that stream.

A complete binary-rule natural serialization has the exact shape

```text
[lhsCode, leftCode, rightCode, bodyTokenCount] ++ encodedBody.
```

Accordingly, every field is exactly one of

* the dense code of the left-hand-side nonterminal;
* the dense code of the left child;
* the dense code of the right child;
* the body-token count;
* a body-token tag; or
* a body-token payload.

The three nonterminal codes are bounded by the complete presentation-item
count.  This yields the explicit binary-rule bound

```text
max binaryNaturalFieldCount
  (max 4
    (max presentationItemCount
      (max bodyTokenCount maximumBodyTokenValue))).
```

The previous opaque quantity

```lean
H.compiledBinaryRuleNaturalValueBound dummy rho
```

is proved below this structural bound.

After this file, the only remaining binary-payload quantity is the maximum
token payload itself.  Its four constructors can be handled independently in
the next layer using component lengths, terminal-alphabet cardinality, and the
two child arities.

No target grammar is supplied to the learner.
No `sorry`, `admit`, or `axiom` is used.
-/

namespace MCFG

universe u v

section NaturalBodyTokenFieldClassification

/-- Exact classification of one natural field contributed by one framed body
token. -/
def FramedTemplateBodyNaturalToken.NaturalFieldClass
    (token : FramedTemplateBodyNaturalToken)
    (n : Nat) :
    Prop :=
  n = framedTemplateBodyNaturalTokenTag token ∨
    n = framedTemplateBodyNaturalTokenPayload token

/-- One-token classification is exactly membership in its two-field natural
serialization. -/
@[simp] theorem
    framedTemplateBodyNaturalToken_naturalFieldClass_iff_mem
    (token : FramedTemplateBodyNaturalToken)
    (n : Nat) :
    token.NaturalFieldClass n ↔
      n ∈
        [framedTemplateBodyNaturalTokenTag token,
          framedTemplateBodyNaturalTokenPayload token] := by

  simp [
    FramedTemplateBodyNaturalToken.NaturalFieldClass,
    or_assoc
  ]

/-- Exact source classification of a field in a flattened body-token stream. -/
def FramedTemplateBodyNaturalStreamFieldClass
    (tokens : List FramedTemplateBodyNaturalToken)
    (n : Nat) :
    Prop :=
  ∃ token,
    token ∈ tokens ∧
      token.NaturalFieldClass n

/-- Every classified token-stream field occurs in the flattened natural
stream. -/
theorem
    mem_encodeFramedTemplateBodyNaturalStream_of_fieldClass :
    ∀
      (tokens : List FramedTemplateBodyNaturalToken)
      (n : Nat),
      FramedTemplateBodyNaturalStreamFieldClass tokens n →
        n ∈ encodeFramedTemplateBodyNaturalStream tokens

  | [], n, hclass => by
      simp [
        FramedTemplateBodyNaturalStreamFieldClass
      ] at hclass

  | token :: tokens, n, hclass => by
      rcases hclass with
        ⟨source, hsource, hfield⟩

      rcases List.mem_cons.mp hsource with
        rfl | htail

      · rcases hfield with htag | hpayload

        · subst n

          simp [
            encodeFramedTemplateBodyNaturalStream
          ]

        · subst n

          simp [
            encodeFramedTemplateBodyNaturalStream
          ]

      · have htailClass :
            FramedTemplateBodyNaturalStreamFieldClass
              tokens n :=
          ⟨source, htail, hfield⟩

        have htailMem :
            n ∈
              encodeFramedTemplateBodyNaturalStream
                tokens :=
          mem_encodeFramedTemplateBodyNaturalStream_of_fieldClass
            tokens n htailClass

        simp [
          encodeFramedTemplateBodyNaturalStream,
          htailMem
        ]

/-- Every field occurring in a flattened token stream has one of the exact
token-local sources. -/
theorem
    fieldClass_of_mem_encodeFramedTemplateBodyNaturalStream :
    ∀
      (tokens : List FramedTemplateBodyNaturalToken)
      (n : Nat),
      n ∈ encodeFramedTemplateBodyNaturalStream tokens →
        FramedTemplateBodyNaturalStreamFieldClass tokens n

  | [], n, hmem => by
      simp [
        encodeFramedTemplateBodyNaturalStream
      ] at hmem

  | token :: tokens, n, hmem => by
      simp [
        encodeFramedTemplateBodyNaturalStream
      ] at hmem

      rcases hmem with
        htag | hpayload | htail

      · exact
          ⟨token,
            by simp,
            Or.inl htag⟩

      · exact
          ⟨token,
            by simp,
            Or.inr hpayload⟩

      · rcases
          fieldClass_of_mem_encodeFramedTemplateBodyNaturalStream
            tokens n htail with
        ⟨source, hsource, hfield⟩

        exact
          ⟨source,
            by simp [hsource],
            hfield⟩

/-- Exact flattened-token-stream field classification. -/
@[simp] theorem
    framedTemplateBodyNaturalStreamFieldClass_iff_mem
    (tokens : List FramedTemplateBodyNaturalToken)
    (n : Nat) :
    FramedTemplateBodyNaturalStreamFieldClass tokens n ↔
      n ∈ encodeFramedTemplateBodyNaturalStream tokens := by

  constructor

  · exact
      mem_encodeFramedTemplateBodyNaturalStream_of_fieldClass
        tokens n

  · exact
      fieldClass_of_mem_encodeFramedTemplateBodyNaturalStream
        tokens n

end NaturalBodyTokenFieldClassification


section NaturalBodyTokenValueBounds

/-- Natural-value bound of one framed body token. -/
def framedTemplateBodyNaturalTokenValueBound
    (token : FramedTemplateBodyNaturalToken) :
    Nat :=
  max
    (framedTemplateBodyNaturalTokenTag token)
    (framedTemplateBodyNaturalTokenPayload token)

/-- The tag field of a body token is below its local value bound. -/
theorem framedTemplateBodyNaturalTokenTag_le_valueBound
    (token : FramedTemplateBodyNaturalToken) :
    framedTemplateBodyNaturalTokenTag token <=
      framedTemplateBodyNaturalTokenValueBound token := by

  exact
    Nat.le_max_left
      (framedTemplateBodyNaturalTokenTag token)
      (framedTemplateBodyNaturalTokenPayload token)

/-- The payload field of a body token is below its local value bound. -/
theorem framedTemplateBodyNaturalTokenPayload_le_valueBound
    (token : FramedTemplateBodyNaturalToken) :
    framedTemplateBodyNaturalTokenPayload token <=
      framedTemplateBodyNaturalTokenValueBound token := by

  exact
    Nat.le_max_right
      (framedTemplateBodyNaturalTokenTag token)
      (framedTemplateBodyNaturalTokenPayload token)

/-- Every classified field of one token is below its local value bound. -/
theorem framedTemplateBodyNaturalTokenField_le_valueBound
    (token : FramedTemplateBodyNaturalToken)
    {n : Nat}
    (hclass : token.NaturalFieldClass n) :
    n <= framedTemplateBodyNaturalTokenValueBound token := by

  rcases hclass with htag | hpayload

  · subst n
    exact
      framedTemplateBodyNaturalTokenTag_le_valueBound
        token

  · subst n
    exact
      framedTemplateBodyNaturalTokenPayload_le_valueBound
        token

/-- Maximum token-local natural value in a finite body-token list. -/
def maximumFramedTemplateBodyNaturalTokenValueBound
    (tokens : List FramedTemplateBodyNaturalToken) :
    Nat :=
  maximumNaturalFieldValue
    (tokens.map
      framedTemplateBodyNaturalTokenValueBound)

/-- Every token-local bound is below the maximum over its containing token
list. -/
theorem
    framedTemplateBodyNaturalTokenValueBound_le_maximum_of_mem
    (token : FramedTemplateBodyNaturalToken)
    (tokens : List FramedTemplateBodyNaturalToken)
    (htoken : token ∈ tokens) :
    framedTemplateBodyNaturalTokenValueBound token <=
      maximumFramedTemplateBodyNaturalTokenValueBound tokens := by

  unfold
    maximumFramedTemplateBodyNaturalTokenValueBound

  apply
    nat_le_maximumNaturalFieldValue_of_mem

  exact
    List.mem_map.mpr
      ⟨token, htoken, rfl⟩

/-- Every natural field in a flattened token stream is below the maximum
token-local value. -/
theorem
    framedTemplateBodyNaturalStreamField_le_maximum_of_mem
    (tokens : List FramedTemplateBodyNaturalToken)
    {n : Nat}
    (hn :
      n ∈ encodeFramedTemplateBodyNaturalStream tokens) :
    n <=
      maximumFramedTemplateBodyNaturalTokenValueBound
        tokens := by

  rcases
      (framedTemplateBodyNaturalStreamFieldClass_iff_mem
        tokens n).mpr hn with
    ⟨token, htoken, hfield⟩

  exact
    (framedTemplateBodyNaturalTokenField_le_valueBound
        token hfield).trans
      (framedTemplateBodyNaturalTokenValueBound_le_maximum_of_mem
        token tokens htoken)

/-- The maximum field of the flattened token stream is below the maximum
token-local value. -/
theorem
    maximumNaturalFieldValue_encodeFramedTemplateBodyNaturalStream_le
    (tokens : List FramedTemplateBodyNaturalToken) :
    maximumNaturalFieldValue
        (encodeFramedTemplateBodyNaturalStream tokens) <=
      maximumFramedTemplateBodyNaturalTokenValueBound
        tokens := by

  apply
    maximumNaturalFieldValue_le_of_forall_mem

  intro n hn

  exact
    framedTemplateBodyNaturalStreamField_le_maximum_of_mem
      tokens hn

/-- The body-token tags are uniformly at most three. -/
theorem framedTemplateBodyNaturalTokenTag_le_three
    (token : FramedTemplateBodyNaturalToken) :
    framedTemplateBodyNaturalTokenTag token <= 3 := by

  cases token with

  | componentLength length =>
      simp [framedTemplateBodyNaturalTokenTag]

  | atom atom =>
      cases atom <;>
        simp [framedTemplateBodyNaturalTokenTag]

/-- A token-local value bound can equivalently be bounded by tag bound three
and its payload. -/
theorem framedTemplateBodyNaturalTokenValueBound_le_three_max_payload
    (token : FramedTemplateBodyNaturalToken) :
    framedTemplateBodyNaturalTokenValueBound token <=
      max 3
        (framedTemplateBodyNaturalTokenPayload token) := by

  unfold framedTemplateBodyNaturalTokenValueBound

  apply max_le

  · exact
      (framedTemplateBodyNaturalTokenTag_le_three
        token).trans
        (Nat.le_max_left
          3
          (framedTemplateBodyNaturalTokenPayload token))

  · exact
      Nat.le_max_right
        3
        (framedTemplateBodyNaturalTokenPayload token)

/-- Compact token-stream classification and maximum package. -/
theorem framedTemplateBodyNaturalStreamFieldClassification_package
    (tokens : List FramedTemplateBodyNaturalToken) :
    (∀ n : Nat,
      FramedTemplateBodyNaturalStreamFieldClass tokens n ↔
        n ∈ encodeFramedTemplateBodyNaturalStream tokens) ∧
      (∀ n ∈ encodeFramedTemplateBodyNaturalStream tokens,
        n <=
          maximumFramedTemplateBodyNaturalTokenValueBound
            tokens) ∧
      (maximumNaturalFieldValue
          (encodeFramedTemplateBodyNaturalStream tokens) <=
        maximumFramedTemplateBodyNaturalTokenValueBound
          tokens) := by

  exact
    ⟨by
        intro n
        exact
          framedTemplateBodyNaturalStreamFieldClass_iff_mem
            tokens n,
      by
        intro n hn
        exact
          framedTemplateBodyNaturalStreamField_le_maximum_of_mem
            tokens hn,
      maximumNaturalFieldValue_encodeFramedTemplateBodyNaturalStream_le
        tokens⟩

end NaturalBodyTokenValueBounds


section BinaryRulePacketNaturalFieldClassification

variable {α : Type u}
variable {M : Type v} [Monoid M]
variable {K : Finset (Word α)}
variable {obs : α → M}
variable {f : Nat}

/-- Exact source classification of one natural field in a serialized complete
binary-rule packet. -/
def CorrectedConcreteCompiledBinaryRuleNaturalPacket.NaturalFieldClass
    {H : CorrectedConcreteFiniteHypothesis K obs f}
    (packet : CorrectedConcreteCompiledBinaryRuleNaturalPacket H)
    (n : Nat) :
    Prop :=
  n = packet.lhsCode ∨
    n = packet.leftCode ∨
    n = packet.rightCode ∨
    n = packet.bodyTokens.length ∨
    FramedTemplateBodyNaturalStreamFieldClass
      packet.bodyTokens n

namespace CorrectedConcreteFiniteHypothesis

variable
  (H : CorrectedConcreteFiniteHypothesis K obs f)

/-- Packet field classification is exactly membership in the serialized
pure-natural packet. -/
@[simp] theorem
    compiledBinaryRuleNaturalPacket_fieldClass_iff_mem
    (packet :
      CorrectedConcreteCompiledBinaryRuleNaturalPacket H)
    (n : Nat) :
    packet.NaturalFieldClass n ↔
      n ∈
        H.serializeCompiledBinaryRuleNaturalPacket packet := by

  simp [
    CorrectedConcreteCompiledBinaryRuleNaturalPacket.NaturalFieldClass,
    serializeCompiledBinaryRuleNaturalPacket,
    framedTemplateBodyNaturalStreamFieldClass_iff_mem,
    or_assoc
  ]

/-- Exact source classification of one natural field in the complete encoded
binary rule. -/
noncomputable def CompiledBinaryRuleNaturalFieldClass
    (dummy : α)
    (rho : BinaryRule
      (CorrectedConcreteCutGrammarNonterminal H)
      α
      (correctedConcreteCutGrammarArity H))
    (n : Nat) :
    Prop :=
  (H.encodeCompiledBinaryRuleNaturalPacket dummy rho).
    NaturalFieldClass n

/-- Complete binary-rule field classification is exact. -/
@[simp] theorem compiledBinaryRuleNaturalFieldClass_iff_mem
    (dummy : α)
    (rho : BinaryRule
      (CorrectedConcreteCutGrammarNonterminal H)
      α
      (correctedConcreteCutGrammarArity H))
    (n : Nat) :
    H.CompiledBinaryRuleNaturalFieldClass dummy rho n ↔
      n ∈ H.encodeCompiledBinaryRuleNaturalList dummy rho := by

  unfold
    CompiledBinaryRuleNaturalFieldClass
    encodeCompiledBinaryRuleNaturalList

  exact
    H.compiledBinaryRuleNaturalPacket_fieldClass_iff_mem
      (H.encodeCompiledBinaryRuleNaturalPacket dummy rho)
      n

/-- Expanded exact source form for every complete binary-rule natural field. -/
theorem compiledBinaryRuleNaturalField_classification
    (dummy : α)
    (rho : BinaryRule
      (CorrectedConcreteCutGrammarNonterminal H)
      α
      (correctedConcreteCutGrammarArity H))
    {n : Nat}
    (hn :
      n ∈ H.encodeCompiledBinaryRuleNaturalList dummy rho) :
    n =
        (H.encodeCompiledBinaryRuleNaturalPacket dummy rho).
          lhsCode ∨
      n =
        (H.encodeCompiledBinaryRuleNaturalPacket dummy rho).
          leftCode ∨
      n =
        (H.encodeCompiledBinaryRuleNaturalPacket dummy rho).
          rightCode ∨
      n =
        (H.encodeCompiledBinaryRuleNaturalPacket dummy rho).
          bodyTokens.length ∨
      FramedTemplateBodyNaturalStreamFieldClass
        (H.encodeCompiledBinaryRuleNaturalPacket dummy rho).
          bodyTokens
        n := by

  exact
    (H.compiledBinaryRuleNaturalFieldClass_iff_mem
      dummy rho n).mpr hn

end CorrectedConcreteFiniteHypothesis

end BinaryRulePacketNaturalFieldClassification


section ExplicitBinaryRuleNaturalFieldBound

variable {α : Type u}
variable {M : Type v} [Monoid M]
variable {K : Finset (Word α)}
variable {obs : α → M}
variable {f : Nat}

namespace CorrectedConcreteFiniteHypothesis

variable
  (H : CorrectedConcreteFiniteHypothesis K obs f)

/-- Maximum token-local value in the alphabet-free framed body of one compiled
binary rule. -/
noncomputable def compiledBinaryRuleMaximumBodyTokenNaturalValueBound
    (dummy : α)
    (rho : BinaryRule
      (CorrectedConcreteCutGrammarNonterminal H)
      α
      (correctedConcreteCutGrammarArity H)) :
    Nat :=
  maximumFramedTemplateBodyNaturalTokenValueBound
    (H.encodeCompiledBinaryRuleNaturalPacket dummy rho).
      bodyTokens

/-- Explicit structural natural-value bound for one complete compiled binary
rule. -/
noncomputable def compiledBinaryRuleExplicitNaturalValueBound
    (dummy : α)
    (rho : BinaryRule
      (CorrectedConcreteCutGrammarNonterminal H)
      α
      (correctedConcreteCutGrammarArity H)) :
    Nat :=
  max
    (H.encodeCompiledBinaryRuleNaturalList dummy rho).length
    (max 4
      (max
        H.compiledGrammarPresentationItemCount
        (max
          (H.encodeCompiledBinaryRuleNaturalPacket dummy rho).
            bodyTokens.length
          (H.compiledBinaryRuleMaximumBodyTokenNaturalValueBound
            dummy rho))))

/-- The encoded binary-rule field count is below its explicit structural
bound. -/
theorem compiledBinaryRuleNaturalFieldCount_le_explicitBound
    (dummy : α)
    (rho : BinaryRule
      (CorrectedConcreteCutGrammarNonterminal H)
      α
      (correctedConcreteCutGrammarArity H)) :
    (H.encodeCompiledBinaryRuleNaturalList dummy rho).length <=
      H.compiledBinaryRuleExplicitNaturalValueBound
        dummy rho := by

  exact
    Nat.le_max_left
      (H.encodeCompiledBinaryRuleNaturalList dummy rho).length
      (max 4
        (max
          H.compiledGrammarPresentationItemCount
          (max
            (H.encodeCompiledBinaryRuleNaturalPacket dummy rho).
              bodyTokens.length
            (H.compiledBinaryRuleMaximumBodyTokenNaturalValueBound
              dummy rho))))

/-- The left-hand-side nonterminal code of an encoded binary rule is below the
complete presentation-item count. -/
theorem encodeCompiledBinaryRuleNaturalPacket_lhsCode_le
    (dummy : α)
    (rho : BinaryRule
      (CorrectedConcreteCutGrammarNonterminal H)
      α
      (correctedConcreteCutGrammarArity H)) :
    (H.encodeCompiledBinaryRuleNaturalPacket dummy rho).lhsCode <=
      H.compiledGrammarPresentationItemCount := by

  simpa [
    encodeCompiledBinaryRuleNaturalPacket,
    encodeCompiledBinaryRuleStructuralPacket
  ] using
    H.compiledNonterminalGlobalDenseCode_le_presentationItemCount
      dummy rho.lhs

/-- The left-child nonterminal code of an encoded binary rule is below the
complete presentation-item count. -/
theorem encodeCompiledBinaryRuleNaturalPacket_leftCode_le
    (dummy : α)
    (rho : BinaryRule
      (CorrectedConcreteCutGrammarNonterminal H)
      α
      (correctedConcreteCutGrammarArity H)) :
    (H.encodeCompiledBinaryRuleNaturalPacket dummy rho).leftCode <=
      H.compiledGrammarPresentationItemCount := by

  simpa [
    encodeCompiledBinaryRuleNaturalPacket,
    encodeCompiledBinaryRuleStructuralPacket
  ] using
    H.compiledNonterminalGlobalDenseCode_le_presentationItemCount
      dummy rho.left

/-- The right-child nonterminal code of an encoded binary rule is below the
complete presentation-item count. -/
theorem encodeCompiledBinaryRuleNaturalPacket_rightCode_le
    (dummy : α)
    (rho : BinaryRule
      (CorrectedConcreteCutGrammarNonterminal H)
      α
      (correctedConcreteCutGrammarArity H)) :
    (H.encodeCompiledBinaryRuleNaturalPacket dummy rho).rightCode <=
      H.compiledGrammarPresentationItemCount := by

  simpa [
    encodeCompiledBinaryRuleNaturalPacket,
    encodeCompiledBinaryRuleStructuralPacket
  ] using
    H.compiledNonterminalGlobalDenseCode_le_presentationItemCount
      dummy rho.right

/-- Every natural field in one complete binary-rule serialization is below its
explicit structural bound. -/
theorem compiledBinaryRuleNaturalField_le_explicitBound_of_mem
    (dummy : α)
    (rho : BinaryRule
      (CorrectedConcreteCutGrammarNonterminal H)
      α
      (correctedConcreteCutGrammarArity H))
    {n : Nat}
    (hn :
      n ∈ H.encodeCompiledBinaryRuleNaturalList dummy rho) :
    n <=
      H.compiledBinaryRuleExplicitNaturalValueBound
        dummy rho := by

  rcases
      H.compiledBinaryRuleNaturalField_classification
        dummy rho hn with
    hlhs | hleft | hright | hcount | hbody

  · subst n

    exact
      (H.encodeCompiledBinaryRuleNaturalPacket_lhsCode_le
          dummy rho).trans
        ((Nat.le_max_left
            H.compiledGrammarPresentationItemCount
            (max
              (H.encodeCompiledBinaryRuleNaturalPacket dummy rho).
                bodyTokens.length
              (H.compiledBinaryRuleMaximumBodyTokenNaturalValueBound
                dummy rho))).trans
          ((Nat.le_max_right
              4
              (max
                H.compiledGrammarPresentationItemCount
                (max
                  (H.encodeCompiledBinaryRuleNaturalPacket dummy rho).
                    bodyTokens.length
                  (H.compiledBinaryRuleMaximumBodyTokenNaturalValueBound
                    dummy rho)))).trans
            (Nat.le_max_right
              (H.encodeCompiledBinaryRuleNaturalList dummy rho).length
              (max 4
                (max
                  H.compiledGrammarPresentationItemCount
                  (max
                    (H.encodeCompiledBinaryRuleNaturalPacket dummy rho).
                      bodyTokens.length
                    (H.compiledBinaryRuleMaximumBodyTokenNaturalValueBound
                      dummy rho))))))

  · subst n

    exact
      (H.encodeCompiledBinaryRuleNaturalPacket_leftCode_le
          dummy rho).trans
        ((Nat.le_max_left
            H.compiledGrammarPresentationItemCount
            (max
              (H.encodeCompiledBinaryRuleNaturalPacket dummy rho).
                bodyTokens.length
              (H.compiledBinaryRuleMaximumBodyTokenNaturalValueBound
                dummy rho))).trans
          ((Nat.le_max_right
              4
              (max
                H.compiledGrammarPresentationItemCount
                (max
                  (H.encodeCompiledBinaryRuleNaturalPacket dummy rho).
                    bodyTokens.length
                  (H.compiledBinaryRuleMaximumBodyTokenNaturalValueBound
                    dummy rho)))).trans
            (Nat.le_max_right
              (H.encodeCompiledBinaryRuleNaturalList dummy rho).length
              (max 4
                (max
                  H.compiledGrammarPresentationItemCount
                  (max
                    (H.encodeCompiledBinaryRuleNaturalPacket dummy rho).
                      bodyTokens.length
                    (H.compiledBinaryRuleMaximumBodyTokenNaturalValueBound
                      dummy rho))))))

  · subst n

    exact
      (H.encodeCompiledBinaryRuleNaturalPacket_rightCode_le
          dummy rho).trans
        ((Nat.le_max_left
            H.compiledGrammarPresentationItemCount
            (max
              (H.encodeCompiledBinaryRuleNaturalPacket dummy rho).
                bodyTokens.length
              (H.compiledBinaryRuleMaximumBodyTokenNaturalValueBound
                dummy rho))).trans
          ((Nat.le_max_right
              4
              (max
                H.compiledGrammarPresentationItemCount
                (max
                  (H.encodeCompiledBinaryRuleNaturalPacket dummy rho).
                    bodyTokens.length
                  (H.compiledBinaryRuleMaximumBodyTokenNaturalValueBound
                    dummy rho)))).trans
            (Nat.le_max_right
              (H.encodeCompiledBinaryRuleNaturalList dummy rho).length
              (max 4
                (max
                  H.compiledGrammarPresentationItemCount
                  (max
                    (H.encodeCompiledBinaryRuleNaturalPacket dummy rho).
                      bodyTokens.length
                    (H.compiledBinaryRuleMaximumBodyTokenNaturalValueBound
                      dummy rho))))))

  · subst n

    exact
      (Nat.le_max_left
          (H.encodeCompiledBinaryRuleNaturalPacket dummy rho).
            bodyTokens.length
          (H.compiledBinaryRuleMaximumBodyTokenNaturalValueBound
            dummy rho)).trans
        ((Nat.le_max_right
            H.compiledGrammarPresentationItemCount
            (max
              (H.encodeCompiledBinaryRuleNaturalPacket dummy rho).
                bodyTokens.length
              (H.compiledBinaryRuleMaximumBodyTokenNaturalValueBound
                dummy rho))).trans
          ((Nat.le_max_right
              4
              (max
                H.compiledGrammarPresentationItemCount
                (max
                  (H.encodeCompiledBinaryRuleNaturalPacket dummy rho).
                    bodyTokens.length
                  (H.compiledBinaryRuleMaximumBodyTokenNaturalValueBound
                    dummy rho)))).trans
            (Nat.le_max_right
              (H.encodeCompiledBinaryRuleNaturalList dummy rho).length
              (max 4
                (max
                  H.compiledGrammarPresentationItemCount
                  (max
                    (H.encodeCompiledBinaryRuleNaturalPacket dummy rho).
                      bodyTokens.length
                    (H.compiledBinaryRuleMaximumBodyTokenNaturalValueBound
                      dummy rho))))))

  · have hbodyBound :
        n <=
          H.compiledBinaryRuleMaximumBodyTokenNaturalValueBound
            dummy rho := by

      exact
        framedTemplateBodyNaturalStreamField_le_maximum_of_mem
          (H.encodeCompiledBinaryRuleNaturalPacket dummy rho).
            bodyTokens
          ((framedTemplateBodyNaturalStreamFieldClass_iff_mem
              (H.encodeCompiledBinaryRuleNaturalPacket dummy rho).
                bodyTokens
              n).mp hbody)

    exact
      hbodyBound.trans
        ((Nat.le_max_right
            (H.encodeCompiledBinaryRuleNaturalPacket dummy rho).
              bodyTokens.length
            (H.compiledBinaryRuleMaximumBodyTokenNaturalValueBound
              dummy rho)).trans
          ((Nat.le_max_right
              H.compiledGrammarPresentationItemCount
              (max
                (H.encodeCompiledBinaryRuleNaturalPacket dummy rho).
                  bodyTokens.length
                (H.compiledBinaryRuleMaximumBodyTokenNaturalValueBound
                  dummy rho))).trans
            ((Nat.le_max_right
                4
                (max
                  H.compiledGrammarPresentationItemCount
                  (max
                    (H.encodeCompiledBinaryRuleNaturalPacket dummy rho).
                      bodyTokens.length
                    (H.compiledBinaryRuleMaximumBodyTokenNaturalValueBound
                      dummy rho)))).trans
              (Nat.le_max_right
                (H.encodeCompiledBinaryRuleNaturalList dummy rho).length
                (max 4
                  (max
                    H.compiledGrammarPresentationItemCount
                    (max
                      (H.encodeCompiledBinaryRuleNaturalPacket dummy rho).
                        bodyTokens.length
                      (H.compiledBinaryRuleMaximumBodyTokenNaturalValueBound
                        dummy rho))))))

/-- The previous opaque binary-rule `naturalFieldValueBound` is below the
explicit structural bound. -/
theorem compiledBinaryRuleNaturalValueBound_le_explicitBound
    (dummy : α)
    (rho : BinaryRule
      (CorrectedConcreteCutGrammarNonterminal H)
      α
      (correctedConcreteCutGrammarArity H)) :
    H.compiledBinaryRuleNaturalValueBound dummy rho <=
      H.compiledBinaryRuleExplicitNaturalValueBound
        dummy rho := by

  unfold compiledBinaryRuleNaturalValueBound

  apply
    naturalFieldValueBound_le_of_count_le_of_all_le

  · exact
      H.compiledBinaryRuleNaturalFieldCount_le_explicitBound
        dummy rho

  · intro n hn

    exact
      H.compiledBinaryRuleNaturalField_le_explicitBound_of_mem
        dummy rho hn

/-- Expanded body-token count in the explicit binary-rule bound. -/
@[simp] theorem
    encodeCompiledBinaryRuleNaturalPacket_bodyTokenCount_eq
    (dummy : α)
    (rho : BinaryRule
      (CorrectedConcreteCutGrammarNonterminal H)
      α
      (correctedConcreteCutGrammarArity H)) :
    (H.encodeCompiledBinaryRuleNaturalPacket dummy rho).
        bodyTokens.length =
      correctedConcreteCutGrammarArity H rho.lhs +
        ((List.ofFn rho.body).map List.length).sum := by

  exact
    H.encodeCompiledBinaryRuleNaturalPacket_bodyTokens_length
      dummy rho

/-- Compact complete binary-rule field-classification and explicit-bound
package. -/
theorem compiledBinaryRuleNaturalFieldClassification_package
    (dummy : α)
    (rho : BinaryRule
      (CorrectedConcreteCutGrammarNonterminal H)
      α
      (correctedConcreteCutGrammarArity H)) :
    (∀ n : Nat,
      H.CompiledBinaryRuleNaturalFieldClass dummy rho n ↔
        n ∈ H.encodeCompiledBinaryRuleNaturalList dummy rho) ∧
      (∀ n ∈ H.encodeCompiledBinaryRuleNaturalList dummy rho,
        n <=
          H.compiledBinaryRuleExplicitNaturalValueBound
            dummy rho) ∧
      (H.compiledBinaryRuleNaturalValueBound dummy rho <=
        H.compiledBinaryRuleExplicitNaturalValueBound
          dummy rho) ∧
      ((H.encodeCompiledBinaryRuleNaturalPacket dummy rho).
          bodyTokens.length =
        correctedConcreteCutGrammarArity H rho.lhs +
          ((List.ofFn rho.body).map List.length).sum) := by

  exact
    ⟨by
        intro n
        exact
          H.compiledBinaryRuleNaturalFieldClass_iff_mem
            dummy rho n,
      by
        intro n hn
        exact
          H.compiledBinaryRuleNaturalField_le_explicitBound_of_mem
            dummy rho hn,
      H.compiledBinaryRuleNaturalValueBound_le_explicitBound
        dummy rho,
      H.encodeCompiledBinaryRuleNaturalPacket_bodyTokenCount_eq
        dummy rho⟩

end CorrectedConcreteFiniteHypothesis

end ExplicitBinaryRuleNaturalFieldBound


section StoredBinaryRuleExplicitBounds

variable {α : Type u}
variable {M : Type v} [Monoid M]
variable {K : Finset (Word α)}
variable {obs : α → M}
variable {f : Nat}

namespace CorrectedConcreteFiniteHypothesis

variable
  (H : CorrectedConcreteFiniteHypothesis K obs f)

/-- Maximum explicit binary-rule natural-value bound among all actually stored
binary rules. -/
noncomputable def
    compiledWorkingGrammarMaximumBinaryRuleExplicitNaturalValueBound
    (dummy : α) :
    Nat :=
  maximumNaturalFieldValue
    ((H.toCutWorkingMCFG dummy).binaryRules.map
      (fun rho =>
        H.compiledBinaryRuleExplicitNaturalValueBound
          dummy rho))

/-- Every stored binary rule's explicit bound is below the maximum stored
binary-rule bound. -/
theorem
    compiledBinaryRuleExplicitNaturalValueBound_le_storedMaximum
    (dummy : α)
    (rho : BinaryRule
      (CorrectedConcreteCutGrammarNonterminal H)
      α
      (correctedConcreteCutGrammarArity H))
    (hrho :
      rho ∈ (H.toCutWorkingMCFG dummy).binaryRules) :
    H.compiledBinaryRuleExplicitNaturalValueBound dummy rho <=
      H.compiledWorkingGrammarMaximumBinaryRuleExplicitNaturalValueBound
        dummy := by

  unfold
    compiledWorkingGrammarMaximumBinaryRuleExplicitNaturalValueBound

  apply
    nat_le_maximumNaturalFieldValue_of_mem

  exact
    List.mem_map.mpr
      ⟨rho, hrho, rfl⟩

/-- Every stored binary rule's previous local natural-value bound is below the
maximum explicit stored-binary-rule bound. -/
theorem
    compiledBinaryRuleNaturalValueBound_le_storedExplicitMaximum
    (dummy : α)
    (rho : BinaryRule
      (CorrectedConcreteCutGrammarNonterminal H)
      α
      (correctedConcreteCutGrammarArity H))
    (hrho :
      rho ∈ (H.toCutWorkingMCFG dummy).binaryRules) :
    H.compiledBinaryRuleNaturalValueBound dummy rho <=
      H.compiledWorkingGrammarMaximumBinaryRuleExplicitNaturalValueBound
        dummy := by

  exact
    (H.compiledBinaryRuleNaturalValueBound_le_explicitBound
        dummy rho).trans
      (H.compiledBinaryRuleExplicitNaturalValueBound_le_storedMaximum
        dummy rho hrho)

end CorrectedConcreteFiniteHypothesis

end StoredBinaryRuleExplicitBounds

end MCFG
