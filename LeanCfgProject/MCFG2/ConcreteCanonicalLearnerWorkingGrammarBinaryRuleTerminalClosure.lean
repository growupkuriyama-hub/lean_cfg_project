/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG2.ConcreteCanonicalLearnerWorkingGrammarBinaryRuleNaturalSerialization

/-!
# ConcreteCanonicalLearnerWorkingGrammarBinaryRuleTerminalClosure.lean

The preceding file gives a complete pure-`Nat` list codec for an arbitrary
compiled binary rule, but its round-trip theorem still assumes explicitly that
every terminal token of the rule belongs to

```text
insert dummy (sampleAlphabet K).
```

This file discharges that assumption for every binary rule that actually occurs
in the cut-compiled `WorkingMCFG`.

There are three binary-rule families.

* A control constant rule emits the tuple stored by one finite control code.
  We prove that every letter in every control tuple belongs to the sample
  alphabet by decomposing the six sources of the finite control set:
  sample words, unit sources, unit targets, binary parents, binary left
  children, and binary right children.
* A lifted corrected binary rule comes from an actual sample witness.  Every
  literal terminal in its template therefore occurs in the witnessed parent
  sample word.
* A saturated cut rule is a left-identity template and contains no literal
  terminals.

A generic support layer transports terminal membership through structural atom
encoding, component framing, tuple framing, and
`BinaryRule.framedStructuralBodyTokens`.

The main endpoint removes the last external terminal-support premise from the
natural-list codec for stored compiled binary rules:

```lean
H.decodeCompiledBinaryRuleNaturalList dummy
    (H.encodeCompiledBinaryRuleNaturalList dummy rho)
  = some rho
```

whenever

```lean
rho ∈ (H.toCutWorkingMCFG dummy).binaryRules.
```

No target grammar is supplied to the learner.
No `sorry`, `admit`, or `axiom` is used.
-/

namespace MCFG

universe u v

section TemplateTerminalSupport

variable {α : Type u}

/-- Literal-terminal support of one dependent template atom. -/
def TemplateAtom.TerminalsIn
    {dB dC : Nat}
    (A : Finset α) :
    TemplateAtom α dB dC → Prop

  | .terminal a =>
      a ∈ A

  | .leftVar _ =>
      True

  | .rightVar _ =>
      True

/-- Literal-terminal support of one dependent template word. -/
def TemplateWord.TerminalsIn
    {dB dC : Nat}
    (A : Finset α)
    (word : TemplateWord α dB dC) :
    Prop :=
  ∀ atom ∈ word,
    atom.TerminalsIn A

/-- Literal-terminal support of one dependent template tuple. -/
def TemplateTuple.TerminalsIn
    {e dB dC : Nat}
    (A : Finset α)
    (body : TemplateTuple α e dB dC) :
    Prop :=
  ∀ i : Fin e,
    (body i).TerminalsIn A

/-- Structural atom serialization preserves terminal support. -/
theorem encodeTemplateAtomStructural_terminalsIn
    {dB dC : Nat}
    (A : Finset α)
    (atom : TemplateAtom α dB dC)
    (hterminal : atom.TerminalsIn A) :
    (encodeTemplateAtomStructural atom).TerminalsIn A := by

  cases atom with

  | terminal a =>
      simpa [
        TemplateAtom.TerminalsIn,
        TemplateAtomStructuralToken.TerminalsIn,
        encodeTemplateAtomStructural
      ] using hterminal

  | leftVar i =>
      trivial

  | rightVar j =>
      trivial

/-- Structural word serialization preserves terminal support pointwise. -/
theorem encodeTemplateWordStructural_terminalsIn
    {dB dC : Nat}
    (A : Finset α)
    (word : TemplateWord α dB dC)
    (hword : word.TerminalsIn A) :
    ∀ token ∈ encodeTemplateWordStructural word,
      token.TerminalsIn A := by

  intro token htoken

  rcases List.mem_map.mp htoken with
    ⟨atom, hatom, rfl⟩

  exact
    encodeTemplateAtomStructural_terminalsIn
      A atom
      (hword atom hatom)

/-- Framing one template component preserves terminal support. -/
theorem frameTemplateWord_terminalsIn
    {dB dC : Nat}
    (A : Finset α)
    (word : TemplateWord α dB dC)
    (hword : word.TerminalsIn A) :
    ∀ token ∈ frameTemplateWord word,
      token.TerminalsIn A := by

  intro token htoken

  change
    token ∈
      FramedTemplateBodyToken.componentLength word.length ::
        wrapStructuralAtomTokens
          (encodeTemplateWordStructural word)
    at htoken

  rcases List.mem_cons.mp htoken with
    hheader | hpayload

  · subst token
    trivial

  · unfold wrapStructuralAtomTokens at hpayload

    rcases List.mem_map.mp hpayload with
      ⟨structural, hstructural, rfl⟩

    exact
      encodeTemplateWordStructural_terminalsIn
        A word hword structural hstructural

/-- Framing an ordered component list preserves terminal support. -/
theorem encodeFramedTemplateWords_terminalsIn
    {dB dC : Nat}
    (A : Finset α) :
    ∀ words : List (TemplateWord α dB dC),
      (∀ word ∈ words,
        word.TerminalsIn A) →
      ∀ token ∈ encodeFramedTemplateWords words,
        token.TerminalsIn A

  | [], _ => by
      intro token htoken
      simp [encodeFramedTemplateWords] at htoken

  | word :: words, hwords => by
      intro token htoken

      have hhead :
          word.TerminalsIn A :=
        hwords word (by simp)

      have htail :
          ∀ next ∈ words,
            next.TerminalsIn A := by
        intro next hnext
        exact hwords next (by simp [hnext])

      change
        token ∈
          frameTemplateWord word ++
            encodeFramedTemplateWords words
        at htoken

      rcases List.mem_append.mp htoken with
        hframe | hrest

      · exact
          frameTemplateWord_terminalsIn
            A word hhead token hframe

      · exact
          encodeFramedTemplateWords_terminalsIn
            A words htail token hrest

/-- Complete tuple framing preserves terminal support. -/
theorem encodeTemplateTupleFramed_terminalsIn
    {e dB dC : Nat}
    (A : Finset α)
    (body : TemplateTuple α e dB dC)
    (hbody : body.TerminalsIn A) :
    ∀ token ∈ encodeTemplateTupleFramed body,
      token.TerminalsIn A := by

  apply
    encodeFramedTemplateWords_terminalsIn
      A
      (templateTupleStructuralWords body)

  intro word hword

  change word ∈ List.ofFn body at hword
  rw [List.mem_ofFn] at hword

  rcases hword with ⟨i, rfl⟩

  exact hbody i

namespace BinaryRule

variable {N : Type v}
variable {arity : N → Nat}

/-- Terminal support of a dependent rule body implies support of every token in
its flat framed structural stream. -/
theorem framedStructuralBodyTokens_terminalsIn
    (A : Finset α)
    (rho : BinaryRule N α arity)
    (hbody : rho.body.TerminalsIn A) :
    ∀ token ∈ rho.framedStructuralBodyTokens,
      token.TerminalsIn A := by

  exact
    encodeTemplateTupleFramed_terminalsIn
      A rho.body hbody

end BinaryRule

end TemplateTerminalSupport


section ElementaryTemplateSupport

variable {α : Type u}

/-- A literal terminal word is supported whenever all of its letters are. -/
theorem terminalTemplateWord_terminalsIn
    {dB dC : Nat}
    (A : Finset α)
    (word : Word α)
    (hword :
      ∀ a ∈ word,
        a ∈ A) :
    (terminalTemplateWord
      (dB := dB) (dC := dC) word).TerminalsIn A := by

  intro atom hatom

  unfold terminalTemplateWord at hatom

  rcases List.mem_map.mp hatom with
    ⟨a, ha, rfl⟩

  exact hword a ha

/-- A constant tuple template is supported whenever each stored tuple component
is supported. -/
theorem constantTupleTemplate_terminalsIn
    {d : Nat}
    (A : Finset α)
    (x : Tuple α d)
    (hx :
      ∀ i : Fin d,
        ∀ a ∈ x i,
          a ∈ A) :
    (constantTupleTemplate x).TerminalsIn A := by

  intro i

  exact
    terminalTemplateWord_terminalsIn
      A (x i) (hx i)

/-- A left-identity template contains no literal terminals. -/
theorem leftIdentityTupleTemplate_terminalsIn
    {e d : Nat}
    (A : Finset α)
    (h : e = d) :
    (leftIdentityTupleTemplate
      (α := α) h).TerminalsIn A := by

  intro i atom hatom

  simp [
    leftIdentityTupleTemplate,
    TemplateWord.TerminalsIn,
    TemplateAtom.TerminalsIn
  ] at hatom ⊢

end ElementaryTemplateSupport


section SampleTupleTerminalSupport

variable {α : Type u}

/-- Every letter in a tuple component exposed inside a sample word belongs to
the finite sample alphabet. -/
theorem mem_sampleAlphabet_of_namedFill_component
    {K : Finset (Word α)}
    {d : Nat}
    {context : NamedSentenceContext α d}
    {x : Tuple α d}
    (hfill :
      namedFill d context x ∈ K)
    (i : Fin d)
    {a : α}
    (ha : a ∈ x i) :
    a ∈ sampleAlphabet K := by

  exact
    mem_sampleAlphabet_of_mem_word
      K hfill
      (namedFill_mem_of_mem_component
        context x i ha)

end SampleTupleTerminalSupport


section ControlCodeTerminalSupport

variable {α : Type u}
variable {M : Type v} [Monoid M]
variable {K : Finset (Word α)}
variable {obs : α → M}
variable {f : Nat}

namespace CorrectedConcreteFiniteHypothesis

variable
  (H : CorrectedConcreteFiniteHypothesis K obs f)

/-- Every letter in every component of every finite control tuple belongs to the
sample alphabet. -/
theorem controlCode_tuple_terminalsIn_sampleAlphabet
    {X : FiniteObjectTupleCode α}
    (hX : H.IsControlCode X) :
    ∀ i : Fin X.arity,
      ∀ a ∈ X.tuple i,
        a ∈ sampleAlphabet K := by

  classical

  unfold IsControlCode at hX
  unfold controlCodes at hX

  rcases Finset.mem_union.mp hX with
    hword | hrest

  · rcases Finset.mem_image.mp hword with
      ⟨word, hword, rfl⟩

    intro i a ha

    exact
      mem_sampleAlphabet_of_mem_word
        K hword
        (by simpa using ha)

  · rcases Finset.mem_union.mp hrest with
      hunitSource | hrest

    · rcases Finset.mem_image.mp hunitSource with
        ⟨U, hU, rfl⟩

      intro i a ha

      change a ∈ U.source i at ha

      exact
        mem_sampleAlphabet_of_namedFill_component
          U.rule.evidence.left_mem i ha

    · rcases Finset.mem_union.mp hrest with
        hunitTarget | hrest

      · rcases Finset.mem_image.mp hunitTarget with
          ⟨U, hU, rfl⟩

        intro i a ha

        change a ∈ U.target i at ha

        exact
          mem_sampleAlphabet_of_namedFill_component
            U.rule.evidence.right_mem i ha

      · rcases Finset.mem_union.mp hrest with
          hbinarySource | hrest

        · rcases Finset.mem_image.mp hbinarySource with
            ⟨B, hB, rfl⟩

          intro i a ha

          change a ∈ B.source i at ha

          exact
            mem_sampleAlphabet_of_mem_word
              K
              B.rule.witness.parent.word_mem
              (namedFill_mem_of_mem_component
                B.rule.witness.parent.1.context
                B.rule.witness.parent.1.tuple
                i
                (by simpa using ha))

        · rcases Finset.mem_union.mp hrest with
            hbinaryLeft | hbinaryRight

          · rcases Finset.mem_image.mp hbinaryLeft with
              ⟨B, hB, rfl⟩

            intro i a ha

            change a ∈ B.leftSource i at ha

            exact
              mem_sampleAlphabet_of_mem_word
                K
                B.rule.witness.left.word_mem
                (namedFill_mem_of_mem_component
                  B.rule.witness.left.1.context
                  B.rule.witness.left.1.tuple
                  i
                  (by simpa using ha))

          · rcases Finset.mem_image.mp hbinaryRight with
              ⟨B, hB, rfl⟩

            intro i a ha

            change a ∈ B.rightSource i at ha

            exact
              mem_sampleAlphabet_of_mem_word
                K
                B.rule.witness.right.word_mem
                (namedFill_mem_of_mem_component
                  B.rule.witness.right.1.context
                  B.rule.witness.right.1.tuple
                  i
                  (by simpa using ha))

end CorrectedConcreteFiniteHypothesis

end ControlCodeTerminalSupport


section CompiledRuleFamilyTerminalSupport

variable {α : Type u}
variable {M : Type v} [Monoid M]
variable {K : Finset (Word α)}
variable {obs : α → M}
variable {f : Nat}

namespace CorrectedConcreteFiniteHypothesis

variable
  (H : CorrectedConcreteFiniteHypothesis K obs f)
variable
  (dummy : α)

/-- Every control constant rule uses only terminals from the augmented compiled
alphabet. -/
theorem cutConstantRule_body_terminalsIn
    (X : H.controlCodes.attach) :
    (correctedConcreteCutConstantRule H X).body.TerminalsIn
      (compiledTerminalAlphabet K dummy) := by

  change
    (constantTupleTemplate X.1.tuple).TerminalsIn
      (compiledTerminalAlphabet K dummy)

  apply
    constantTupleTemplate_terminalsIn

  intro i a ha

  exact
    mem_compiledTerminalAlphabet_of_mem_sampleAlphabet
      K dummy
      (H.controlCode_tuple_terminalsIn_sampleAlphabet
        X.2 i a ha)

/-- Every lifted corrected binary rule uses only terminals visible in its
sample parent witness. -/
theorem cutLiftedBinaryRule_body_terminalsIn
    (B : H.binaryRuleCodes.attach) :
    (correctedConcreteCutLiftedBinaryRule H B).body.TerminalsIn
      (compiledTerminalAlphabet K dummy) := by

  change
    B.1.body.TerminalsIn
      (compiledTerminalAlphabet K dummy)

  intro o atom hatom

  cases atom with

  | terminal a =>
      exact
        mem_compiledTerminalAlphabet_of_mem_sampleAlphabet
          K dummy
          (terminal_mem_sampleAlphabet_of_binary_parent_mem
            B.1.rule.evidence.parent_mem
            o
            hatom)

  | leftVar i =>
      trivial

  | rightVar j =>
      trivial

/-- Every saturated cut rule is terminal-free. -/
theorem cutSaturationRule_body_terminalsIn
    (p : H.cutPairs.attach) :
    (correctedConcreteCutSaturationRule H p).body.TerminalsIn
      (compiledTerminalAlphabet K dummy) := by

  change
    (leftIdentityTupleTemplate
      (α := α)
      (H.cutPairArityEq p)).TerminalsIn
        (compiledTerminalAlphabet K dummy)

  exact
    leftIdentityTupleTemplate_terminalsIn
      (compiledTerminalAlphabet K dummy)
      (H.cutPairArityEq p)

/-- Framed terminal support for a control constant rule. -/
theorem cutConstantRule_framedTokens_terminalsIn
    (X : H.controlCodes.attach) :
    ∀ token ∈
        (correctedConcreteCutConstantRule H X).
          framedStructuralBodyTokens,
      token.TerminalsIn
        (compiledTerminalAlphabet K dummy) := by

  exact
    BinaryRule.framedStructuralBodyTokens_terminalsIn
      (compiledTerminalAlphabet K dummy)
      (correctedConcreteCutConstantRule H X)
      (H.cutConstantRule_body_terminalsIn
        dummy X)

/-- Framed terminal support for one lifted corrected sample rule. -/
theorem cutLiftedBinaryRule_framedTokens_terminalsIn
    (B : H.binaryRuleCodes.attach) :
    ∀ token ∈
        (correctedConcreteCutLiftedBinaryRule H B).
          framedStructuralBodyTokens,
      token.TerminalsIn
        (compiledTerminalAlphabet K dummy) := by

  exact
    BinaryRule.framedStructuralBodyTokens_terminalsIn
      (compiledTerminalAlphabet K dummy)
      (correctedConcreteCutLiftedBinaryRule H B)
      (H.cutLiftedBinaryRule_body_terminalsIn
        dummy B)

/-- Framed terminal support for one saturated cut rule. -/
theorem cutSaturationRule_framedTokens_terminalsIn
    (p : H.cutPairs.attach) :
    ∀ token ∈
        (correctedConcreteCutSaturationRule H p).
          framedStructuralBodyTokens,
      token.TerminalsIn
        (compiledTerminalAlphabet K dummy) := by

  exact
    BinaryRule.framedStructuralBodyTokens_terminalsIn
      (compiledTerminalAlphabet K dummy)
      (correctedConcreteCutSaturationRule H p)
      (H.cutSaturationRule_body_terminalsIn
        dummy p)

end CorrectedConcreteFiniteHypothesis

end CompiledRuleFamilyTerminalSupport


section ActualCompiledBinaryRuleTerminalClosure

variable {α : Type u}
variable {M : Type v} [Monoid M]
variable {K : Finset (Word α)}
variable {obs : α → M}
variable {f : Nat}

namespace CorrectedConcreteFiniteHypothesis

variable
  (H : CorrectedConcreteFiniteHypothesis K obs f)
variable
  (dummy : α)

/-- Every binary rule actually stored in the cut-compiled grammar uses only the
augmented finite terminal alphabet. -/
theorem cutWorkingGrammar_binaryRule_framedTokens_terminalsIn
    (rho : BinaryRule
      (CorrectedConcreteCutGrammarNonterminal H)
      α
      (correctedConcreteCutGrammarArity H))
    (hrho :
      rho ∈
        (H.toCutWorkingMCFG dummy).binaryRules) :
    ∀ token ∈ rho.framedStructuralBodyTokens,
      token.TerminalsIn
        (compiledTerminalAlphabet K dummy) := by

  change
    rho ∈
      H.controlCodes.attach.toList.map
          (correctedConcreteCutConstantRule H) ++
        H.binaryRuleCodes.attach.toList.map
            (correctedConcreteCutLiftedBinaryRule H) ++
          H.cutPairs.attach.toList.map
            (correctedConcreteCutSaturationRule H)
    at hrho

  rcases List.mem_append.mp hrho with
    hconstant | hrest

  · rcases List.mem_map.mp hconstant with
      ⟨X, hX, rfl⟩

    exact
      H.cutConstantRule_framedTokens_terminalsIn
        dummy X

  · rcases List.mem_append.mp hrest with
      hlifted | hsaturated

    · rcases List.mem_map.mp hlifted with
        ⟨B, hB, rfl⟩

      exact
        H.cutLiftedBinaryRule_framedTokens_terminalsIn
          dummy B

    · rcases List.mem_map.mp hsaturated with
        ⟨p, hp, rfl⟩

      exact
        H.cutSaturationRule_framedTokens_terminalsIn
          dummy p

/-- The pure-natural-list binary-rule codec is unconditional for every rule
actually stored in the cut-compiled grammar. -/
@[simp] theorem decodeCompiledBinaryRuleNaturalList_encode_of_mem
    (rho : BinaryRule
      (CorrectedConcreteCutGrammarNonterminal H)
      α
      (correctedConcreteCutGrammarArity H))
    (hrho :
      rho ∈
        (H.toCutWorkingMCFG dummy).binaryRules) :
    H.decodeCompiledBinaryRuleNaturalList dummy
        (H.encodeCompiledBinaryRuleNaturalList dummy rho) =
      some rho := by

  exact
    H.decodeCompiledBinaryRuleNaturalList_encode
      dummy rho
      (H.cutWorkingGrammar_binaryRule_framedTokens_terminalsIn
        dummy rho hrho)

/-- Compact stored-rule codec endpoint: unconditional round trip together with
the exact pure-natural field count. -/
theorem compiledBinaryRuleNaturalListCodec_of_mem_package
    (rho : BinaryRule
      (CorrectedConcreteCutGrammarNonterminal H)
      α
      (correctedConcreteCutGrammarArity H))
    (hrho :
      rho ∈
        (H.toCutWorkingMCFG dummy).binaryRules) :
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
      H.decodeCompiledBinaryRuleNaturalList_encode_of_mem
        dummy rho hrho

  · exact
      H.encodeCompiledBinaryRuleNaturalList_length
        dummy rho

end CorrectedConcreteFiniteHypothesis

end ActualCompiledBinaryRuleTerminalClosure

end MCFG
