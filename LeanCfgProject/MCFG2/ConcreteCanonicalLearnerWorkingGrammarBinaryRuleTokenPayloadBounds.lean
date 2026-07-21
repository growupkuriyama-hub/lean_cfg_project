/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG2.ConcreteCanonicalLearnerWorkingGrammarBinaryRuleNaturalFieldClassification

/-!
# ConcreteCanonicalLearnerWorkingGrammarBinaryRuleTokenPayloadBounds.lean

The preceding file classifies every natural field in a complete compiled binary
rule and isolates one final local quantity:

```lean
H.compiledBinaryRuleMaximumBodyTokenNaturalValueBound dummy rho.
```

This file removes that quantity for every binary rule actually stored in the
cut-compiled grammar.

A framed structural body token comes from one of two sources.

* A component header stores the length of one output component.
* An atom token stores a terminal, left-variable, or right-variable payload.

We first prove exact source lemmas for the framing construction:

```text
componentLength n occurs
  ⇒ n is the length of one output component;

atom token occurs
  ⇒ token occurs in the structural encoding of one output component.
```

For a stored compiled binary rule, the four natural payload cases are then
bounded as follows.

```text
component length
  ≤ bodyTokenCount;

terminal code
  < compiledTerminalAlphabet.card;

left-variable index
  < arity left
  ≤ max 1 f;

right-variable index
  < arity right
  ≤ max 1 f.
```

The common body-token payload bound is therefore

```lean
max bodyTokenCount
  (max compiledTerminalAlphabet.card (max 1 f)).
```

Since every token tag is at most three, the maximum complete token value is
bounded by

```text
max 3 commonPayloadBound.
```

This yields a fully explicit bound for every stored binary-rule natural
serialization:

```text
max binaryNaturalFieldCount
  (max 4
    (max presentationItemCount
      (max 3
        (max bodyTokenCount
          (max terminalAlphabetCard (max 1 f)))))).
```

No token-local or variable-index maximum remains.  The only quantities left are
already structural: field count, presentation-item count, body-token count,
terminal-alphabet cardinality, and the fixed fan-out parameter.

No target grammar is supplied to the learner.
No `sorry`, `admit`, or `axiom` is used.
-/

namespace MCFG

universe u v

section FramedStructuralTokenSources

variable {α : Type u}

/-- A component header occurring in a framed component list stores the length
of one of the original component words. -/
theorem componentLength_mem_componentLengths_of_mem_encodeFramedTemplateWords
    {dB dC : Nat} :
    ∀
      (words : List (TemplateWord α dB dC))
      (n : Nat),
      FramedTemplateBodyToken.componentLength n ∈
          encodeFramedTemplateWords words →
        n ∈ words.map List.length

  | [], n, hmem => by
      simp [encodeFramedTemplateWords] at hmem

  | word :: words, n, hmem => by
      simp [
        encodeFramedTemplateWords,
        frameTemplateWord,
        wrapStructuralAtomTokens
      ] at hmem ⊢

      rcases hmem with hhead | htail

      · exact Or.inl hhead

      · exact
          Or.inr
            (componentLength_mem_componentLengths_of_mem_encodeFramedTemplateWords
              words n htail)

/-- An atom token occurring in a framed component list comes from the structural
encoding of one of the original component words. -/
theorem atom_mem_component_of_mem_encodeFramedTemplateWords
    {dB dC : Nat} :
    ∀
      (words : List (TemplateWord α dB dC))
      (token : TemplateAtomStructuralToken α),
      FramedTemplateBodyToken.atom token ∈
          encodeFramedTemplateWords words →
        ∃ word,
          word ∈ words ∧
            token ∈ encodeTemplateWordStructural word

  | [], token, hmem => by
      simp [encodeFramedTemplateWords] at hmem

  | word :: words, token, hmem => by
      simp [
        encodeFramedTemplateWords,
        frameTemplateWord,
        wrapStructuralAtomTokens
      ] at hmem

      rcases hmem with hhead | htail

      · exact
          ⟨word,
            by simp,
            hhead⟩

      · rcases
          atom_mem_component_of_mem_encodeFramedTemplateWords
            words token htail with
        ⟨sourceWord, hsourceWord, htoken⟩

        exact
          ⟨sourceWord,
            by simp [hsourceWord],
            htoken⟩

/-- A component header in an actual binary-rule body is the length of one of
that body's output components. -/
theorem BinaryRule.componentLength_mem_bodyComponentLengths
    {N : Type v}
    {arity : N → Nat}
    (rho : BinaryRule N α arity)
    (n : Nat)
    (hmem :
      FramedTemplateBodyToken.componentLength n ∈
        rho.framedStructuralBodyTokens) :
    n ∈
      (List.ofFn rho.body).map List.length := by

  unfold BinaryRule.framedStructuralBodyTokens at hmem
  unfold encodeTemplateTupleFramed at hmem
  unfold templateTupleStructuralWords at hmem

  exact
    componentLength_mem_componentLengths_of_mem_encodeFramedTemplateWords
      (List.ofFn rho.body)
      n
      hmem

/-- A structural atom token in an actual binary-rule body comes from one of
the body's dependent template atoms. -/
theorem BinaryRule.atom_mem_bodyComponent
    {N : Type v}
    {arity : N → Nat}
    (rho : BinaryRule N α arity)
    (token : TemplateAtomStructuralToken α)
    (hmem :
      FramedTemplateBodyToken.atom token ∈
        rho.framedStructuralBodyTokens) :
    ∃ word,
      word ∈ List.ofFn rho.body ∧
        token ∈ encodeTemplateWordStructural word := by

  unfold BinaryRule.framedStructuralBodyTokens at hmem
  unfold encodeTemplateTupleFramed at hmem
  unfold templateTupleStructuralWords at hmem

  exact
    atom_mem_component_of_mem_encodeFramedTemplateWords
      (List.ofFn rho.body)
      token
      hmem

end FramedStructuralTokenSources


section NaturalSumMembership

/-- Every member of a finite natural list is at most its sum. -/
theorem nat_le_list_sum_of_mem
    (n : Nat) :
    ∀ values : List Nat,
      n ∈ values →
        n <= values.sum

  | [], hmem => by
      simp at hmem

  | value :: values, hmem => by
      rcases List.mem_cons.mp hmem with
        hhead | htail

      · subst value
        exact
          Nat.le_add_right
            n
            values.sum

      · exact
          (nat_le_list_sum_of_mem
              n values htail).trans
            (Nat.le_add_left
              values.sum
              value)

/-- The maximum natural value of a finite list is at most its sum. -/
theorem maximumNaturalFieldValue_le_sum
    (values : List Nat) :
    maximumNaturalFieldValue values <=
      values.sum := by

  apply
    maximumNaturalFieldValue_le_of_forall_mem

  intro n hn

  exact
    nat_le_list_sum_of_mem
      n values hn

end NaturalSumMembership


section StructuralVariableIndexBounds

variable {α : Type u}

/-- A structurally encoded left-variable token retains an index below the left
child arity. -/
theorem leftVar_index_lt_of_mem_encodeTemplateWordStructural
    {dB dC : Nat}
    (word : TemplateWord α dB dC)
    (index : Nat)
    (hmem :
      TemplateAtomStructuralToken.leftVar index ∈
        encodeTemplateWordStructural word) :
    index < dB := by

  unfold encodeTemplateWordStructural at hmem

  rcases List.mem_map.mp hmem with
    ⟨atom, hatom, hencode⟩

  cases atom with

  | terminal a =>
      simp [encodeTemplateAtomStructural] at hencode

  | leftVar i =>
      simp [encodeTemplateAtomStructural] at hencode
      subst index
      exact i.2

  | rightVar j =>
      simp [encodeTemplateAtomStructural] at hencode

/-- A structurally encoded right-variable token retains an index below the
right child arity. -/
theorem rightVar_index_lt_of_mem_encodeTemplateWordStructural
    {dB dC : Nat}
    (word : TemplateWord α dB dC)
    (index : Nat)
    (hmem :
      TemplateAtomStructuralToken.rightVar index ∈
        encodeTemplateWordStructural word) :
    index < dC := by

  unfold encodeTemplateWordStructural at hmem

  rcases List.mem_map.mp hmem with
    ⟨atom, hatom, hencode⟩

  cases atom with

  | terminal a =>
      simp [encodeTemplateAtomStructural] at hencode

  | leftVar i =>
      simp [encodeTemplateAtomStructural] at hencode

  | rightVar j =>
      simp [encodeTemplateAtomStructural] at hencode
      subst index
      exact j.2

/-- Every left-variable index occurring in an actual binary-rule framed body is
below the left child arity. -/
theorem BinaryRule.leftVar_index_lt_of_mem_framedStructuralBodyTokens
    {N : Type v}
    {arity : N → Nat}
    (rho : BinaryRule N α arity)
    (index : Nat)
    (hmem :
      FramedTemplateBodyToken.atom
          (.leftVar index) ∈
        rho.framedStructuralBodyTokens) :
    index < arity rho.left := by

  rcases rho.atom_mem_bodyComponent
      (.leftVar index) hmem with
    ⟨word, hword, htoken⟩

  exact
    leftVar_index_lt_of_mem_encodeTemplateWordStructural
      word index htoken

/-- Every right-variable index occurring in an actual binary-rule framed body
is below the right child arity. -/
theorem BinaryRule.rightVar_index_lt_of_mem_framedStructuralBodyTokens
    {N : Type v}
    {arity : N → Nat}
    (rho : BinaryRule N α arity)
    (index : Nat)
    (hmem :
      FramedTemplateBodyToken.atom
          (.rightVar index) ∈
        rho.framedStructuralBodyTokens) :
    index < arity rho.right := by

  rcases rho.atom_mem_bodyComponent
      (.rightVar index) hmem with
    ⟨word, hword, htoken⟩

  exact
    rightVar_index_lt_of_mem_encodeTemplateWordStructural
      word index htoken

end StructuralVariableIndexBounds


section StoredBinaryRuleBodyPayloadClasses

variable {α : Type u}
variable {M : Type v} [Monoid M]
variable {K : Finset (Word α)}
variable {obs : α → M}
variable {f : Nat}

namespace CorrectedConcreteFiniteHypothesis

variable
  (H : CorrectedConcreteFiniteHypothesis K obs f)

/-- Common explicit payload bound for every alphabet-free framed body token of
one compiled binary rule.

The component-length case is bounded by the total body-token count; terminal
codes are bounded by the augmented terminal alphabet cardinality; variable
indices are bounded by the compiled grammar fan-out `max 1 f`. -/
noncomputable def compiledBinaryRuleBodyTokenPayloadBound
    (dummy : α)
    (rho : BinaryRule
      (CorrectedConcreteCutGrammarNonterminal H)
      α
      (correctedConcreteCutGrammarArity H)) :
    Nat :=
  max
    (H.encodeCompiledBinaryRuleNaturalPacket dummy rho).
      bodyTokens.length
    (max
      (compiledTerminalAlphabet K dummy).card
      (max 1 f))

/-- The natural packet body is exactly the pointwise natural encoding of the
rule's structural framed body. -/
theorem encodeCompiledBinaryRuleNaturalPacket_bodyTokens_eq
    (dummy : α)
    (rho : BinaryRule
      (CorrectedConcreteCutGrammarNonterminal H)
      α
      (correctedConcreteCutGrammarArity H)) :
    (H.encodeCompiledBinaryRuleNaturalPacket dummy rho).
        bodyTokens =
      encodeFramedTemplateBodyNatural
        K dummy rho.framedStructuralBodyTokens := by

  rfl

/-- Every component length occurring in a binary-rule body is at most the total
number of framed body tokens. -/
theorem componentLength_le_framedStructuralBodyTokenCount
    (rho : BinaryRule
      (CorrectedConcreteCutGrammarNonterminal H)
      α
      (correctedConcreteCutGrammarArity H))
    (length : Nat)
    (hmem :
      FramedTemplateBodyToken.componentLength length ∈
        rho.framedStructuralBodyTokens) :
    length <= rho.framedStructuralBodyTokens.length := by

  have hlength :
      length ∈
        (List.ofFn rho.body).map List.length :=
    rho.componentLength_mem_bodyComponentLengths
      length hmem

  have hsum :
      length <=
        ((List.ofFn rho.body).map List.length).sum :=
    nat_le_list_sum_of_mem
      length
      ((List.ofFn rho.body).map List.length)
      hlength

  rw [rho.framedStructuralBodyTokens_length]

  exact
    hsum.trans
      (Nat.le_add_left
        ((List.ofFn rho.body).map List.length).sum
        (correctedConcreteCutGrammarArity H rho.lhs))

/-- Every component-length payload in the natural body encoding is below the
common body-token payload bound. -/
theorem encoded_componentLength_payload_le
    (dummy : α)
    (rho : BinaryRule
      (CorrectedConcreteCutGrammarNonterminal H)
      α
      (correctedConcreteCutGrammarArity H))
    (length : Nat)
    (hmem :
      FramedTemplateBodyToken.componentLength length ∈
        rho.framedStructuralBodyTokens) :
    length <=
      H.compiledBinaryRuleBodyTokenPayloadBound
        dummy rho := by

  have hlength :
      length <=
        (H.encodeCompiledBinaryRuleNaturalPacket dummy rho).
          bodyTokens.length := by

    rw [
      H.encodeCompiledBinaryRuleNaturalPacket_bodyTokens_length
        dummy rho
    ]

    exact
      H.componentLength_le_framedStructuralBodyTokenCount
        rho length hmem

  exact
    hlength.trans
      (Nat.le_max_left
        (H.encodeCompiledBinaryRuleNaturalPacket dummy rho).
          bodyTokens.length
        (max
          (compiledTerminalAlphabet K dummy).card
          (max 1 f)))

/-- Every terminal-code payload in a stored binary rule is below the common
body-token payload bound. -/
theorem encoded_terminalCode_payload_le_of_mem
    (dummy : α)
    (rho : BinaryRule
      (CorrectedConcreteCutGrammarNonterminal H)
      α
      (correctedConcreteCutGrammarArity H))
    (hrho :
      rho ∈ (H.toCutWorkingMCFG dummy).binaryRules)
    (a : α)
    (hmem :
      FramedTemplateBodyToken.atom
          (.terminal a) ∈
        rho.framedStructuralBodyTokens) :
    compiledTerminalDenseCode K dummy a <=
      H.compiledBinaryRuleBodyTokenPayloadBound
        dummy rho := by

  have hterminal :
      a ∈ compiledTerminalAlphabet K dummy := by

    have hsupport :=
      H.cutWorkingGrammar_binaryRule_framedTokens_terminalsIn
        dummy rho hrho
        (FramedTemplateBodyToken.atom
          (.terminal a))
        hmem

    simpa [
      FramedTemplateBodyToken.TerminalsIn,
      TemplateAtomStructuralToken.TerminalsIn
    ] using hsupport

  have hcode :
      compiledTerminalDenseCode K dummy a <=
        (compiledTerminalAlphabet K dummy).card :=
    Nat.le_of_lt
      (compiledTerminalDenseCode_lt_card
        K dummy a hterminal)

  exact
    hcode.trans
      ((Nat.le_max_left
          (compiledTerminalAlphabet K dummy).card
          (max 1 f)).trans
        (Nat.le_max_right
          (H.encodeCompiledBinaryRuleNaturalPacket dummy rho).
            bodyTokens.length
          (max
            (compiledTerminalAlphabet K dummy).card
            (max 1 f))))

/-- Every left-variable payload in a stored compiled binary rule is below the
common body-token payload bound. -/
theorem encoded_leftVar_payload_le
    (dummy : α)
    (rho : BinaryRule
      (CorrectedConcreteCutGrammarNonterminal H)
      α
      (correctedConcreteCutGrammarArity H))
    (index : Nat)
    (hmem :
      FramedTemplateBodyToken.atom
          (.leftVar index) ∈
        rho.framedStructuralBodyTokens) :
    index <=
      H.compiledBinaryRuleBodyTokenPayloadBound
        dummy rho := by

  have hindex :
      index <=
        correctedConcreteCutGrammarArity H rho.left :=
    Nat.le_of_lt
      (rho.leftVar_index_lt_of_mem_framedStructuralBodyTokens
        index hmem)

  have harity :
      correctedConcreteCutGrammarArity H rho.left <=
        max 1 f :=
    H.toCutWorkingMCFG_fanoutAtMost_max
      dummy rho.left

  exact
    (hindex.trans harity).trans
      ((Nat.le_max_right
          (compiledTerminalAlphabet K dummy).card
          (max 1 f)).trans
        (Nat.le_max_right
          (H.encodeCompiledBinaryRuleNaturalPacket dummy rho).
            bodyTokens.length
          (max
            (compiledTerminalAlphabet K dummy).card
            (max 1 f))))

/-- Every right-variable payload in a stored compiled binary rule is below the
common body-token payload bound. -/
theorem encoded_rightVar_payload_le
    (dummy : α)
    (rho : BinaryRule
      (CorrectedConcreteCutGrammarNonterminal H)
      α
      (correctedConcreteCutGrammarArity H))
    (index : Nat)
    (hmem :
      FramedTemplateBodyToken.atom
          (.rightVar index) ∈
        rho.framedStructuralBodyTokens) :
    index <=
      H.compiledBinaryRuleBodyTokenPayloadBound
        dummy rho := by

  have hindex :
      index <=
        correctedConcreteCutGrammarArity H rho.right :=
    Nat.le_of_lt
      (rho.rightVar_index_lt_of_mem_framedStructuralBodyTokens
        index hmem)

  have harity :
      correctedConcreteCutGrammarArity H rho.right <=
        max 1 f :=
    H.toCutWorkingMCFG_fanoutAtMost_max
      dummy rho.right

  exact
    (hindex.trans harity).trans
      ((Nat.le_max_right
          (compiledTerminalAlphabet K dummy).card
          (max 1 f)).trans
        (Nat.le_max_right
          (H.encodeCompiledBinaryRuleNaturalPacket dummy rho).
            bodyTokens.length
          (max
            (compiledTerminalAlphabet K dummy).card
            (max 1 f))))

/-- Every natural payload field of every body token in a stored compiled binary
rule is below the common explicit payload bound. -/
theorem compiledBinaryRuleBodyToken_payload_le_of_mem
    (dummy : α)
    (rho : BinaryRule
      (CorrectedConcreteCutGrammarNonterminal H)
      α
      (correctedConcreteCutGrammarArity H))
    (hrho :
      rho ∈ (H.toCutWorkingMCFG dummy).binaryRules)
    (token : FramedTemplateBodyNaturalToken)
    (htoken :
      token ∈
        (H.encodeCompiledBinaryRuleNaturalPacket dummy rho).
          bodyTokens) :
    framedTemplateBodyNaturalTokenPayload token <=
      H.compiledBinaryRuleBodyTokenPayloadBound
        dummy rho := by

  rw [
    H.encodeCompiledBinaryRuleNaturalPacket_bodyTokens_eq
      dummy rho
  ] at htoken

  unfold encodeFramedTemplateBodyNatural at htoken

  rcases List.mem_map.mp htoken with
    ⟨source, hsource, rfl⟩

  cases source with

  | componentLength length =>
      exact
        H.encoded_componentLength_payload_le
          dummy rho length hsource

  | atom structural =>
      cases structural with

      | terminal a =>
          exact
            H.encoded_terminalCode_payload_le_of_mem
              dummy rho hrho a hsource

      | leftVar index =>
          exact
            H.encoded_leftVar_payload_le
              dummy rho index hsource

      | rightVar index =>
          exact
            H.encoded_rightVar_payload_le
              dummy rho index hsource

/-- Every complete token-local value is below three joined with the common
payload bound. -/
theorem compiledBinaryRuleBodyToken_valueBound_le_of_mem
    (dummy : α)
    (rho : BinaryRule
      (CorrectedConcreteCutGrammarNonterminal H)
      α
      (correctedConcreteCutGrammarArity H))
    (hrho :
      rho ∈ (H.toCutWorkingMCFG dummy).binaryRules)
    (token : FramedTemplateBodyNaturalToken)
    (htoken :
      token ∈
        (H.encodeCompiledBinaryRuleNaturalPacket dummy rho).
          bodyTokens) :
    framedTemplateBodyNaturalTokenValueBound token <=
      max 3
        (H.compiledBinaryRuleBodyTokenPayloadBound
          dummy rho) := by

  unfold framedTemplateBodyNaturalTokenValueBound

  apply max_le

  · exact
      (framedTemplateBodyNaturalTokenTag_le_three
          token).trans
        (Nat.le_max_left
          3
          (H.compiledBinaryRuleBodyTokenPayloadBound
            dummy rho))

  · exact
      (H.compiledBinaryRuleBodyToken_payload_le_of_mem
          dummy rho hrho token htoken).trans
        (Nat.le_max_right
          3
          (H.compiledBinaryRuleBodyTokenPayloadBound
            dummy rho))

/-- The maximum token-local natural value of a stored binary rule is bounded by
the explicit tag/payload maximum. -/
theorem
    compiledBinaryRuleMaximumBodyTokenNaturalValueBound_le_payloadBound
    (dummy : α)
    (rho : BinaryRule
      (CorrectedConcreteCutGrammarNonterminal H)
      α
      (correctedConcreteCutGrammarArity H))
    (hrho :
      rho ∈ (H.toCutWorkingMCFG dummy).binaryRules) :
    H.compiledBinaryRuleMaximumBodyTokenNaturalValueBound
        dummy rho <=
      max 3
        (H.compiledBinaryRuleBodyTokenPayloadBound
          dummy rho) := by

  unfold
    compiledBinaryRuleMaximumBodyTokenNaturalValueBound
    maximumFramedTemplateBodyNaturalTokenValueBound

  apply
    maximumNaturalFieldValue_le_of_forall_mem

  intro localBound hlocalBound

  rcases List.mem_map.mp hlocalBound with
    ⟨token, htoken, rfl⟩

  exact
    H.compiledBinaryRuleBodyToken_valueBound_le_of_mem
      dummy rho hrho token htoken

end CorrectedConcreteFiniteHypothesis

end StoredBinaryRuleBodyPayloadClasses


section FullyExplicitStoredBinaryRuleBound

variable {α : Type u}
variable {M : Type v} [Monoid M]
variable {K : Finset (Word α)}
variable {obs : α → M}
variable {f : Nat}

namespace CorrectedConcreteFiniteHypothesis

variable
  (H : CorrectedConcreteFiniteHypothesis K obs f)

/-- Fully explicit natural-value bound for one stored compiled binary rule.

No maximum over token payloads or variable indices remains. -/
noncomputable def compiledBinaryRuleFullyExplicitNaturalValueBound
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
        (max 3
          (H.compiledBinaryRuleBodyTokenPayloadBound
            dummy rho))))

/-- The previous token-maximum-based binary-rule bound is below the fully
explicit bound for every actually stored binary rule. -/
theorem
    compiledBinaryRuleExplicitNaturalValueBound_le_fullyExplicit_of_mem
    (dummy : α)
    (rho : BinaryRule
      (CorrectedConcreteCutGrammarNonterminal H)
      α
      (correctedConcreteCutGrammarArity H))
    (hrho :
      rho ∈ (H.toCutWorkingMCFG dummy).binaryRules) :
    H.compiledBinaryRuleExplicitNaturalValueBound dummy rho <=
      H.compiledBinaryRuleFullyExplicitNaturalValueBound
        dummy rho := by

  unfold
    compiledBinaryRuleExplicitNaturalValueBound
    compiledBinaryRuleFullyExplicitNaturalValueBound

  apply max_le

  · exact
      Nat.le_max_left
        (H.encodeCompiledBinaryRuleNaturalList dummy rho).length
        (max 4
          (max
            H.compiledGrammarPresentationItemCount
            (max 3
              (H.compiledBinaryRuleBodyTokenPayloadBound
                dummy rho))))

  · apply max_le

    · exact
        (Nat.le_max_left
            4
            (max
              H.compiledGrammarPresentationItemCount
              (max 3
                (H.compiledBinaryRuleBodyTokenPayloadBound
                  dummy rho)))).trans
          (Nat.le_max_right
            (H.encodeCompiledBinaryRuleNaturalList dummy rho).length
            (max 4
              (max
                H.compiledGrammarPresentationItemCount
                (max 3
                  (H.compiledBinaryRuleBodyTokenPayloadBound
                    dummy rho)))))

    · apply max_le

      · exact
          (Nat.le_max_left
              H.compiledGrammarPresentationItemCount
              (max 3
                (H.compiledBinaryRuleBodyTokenPayloadBound
                  dummy rho))).trans
            ((Nat.le_max_right
                4
                (max
                  H.compiledGrammarPresentationItemCount
                  (max 3
                    (H.compiledBinaryRuleBodyTokenPayloadBound
                      dummy rho)))).trans
              (Nat.le_max_right
                (H.encodeCompiledBinaryRuleNaturalList dummy rho).length
                (max 4
                  (max
                    H.compiledGrammarPresentationItemCount
                    (max 3
                      (H.compiledBinaryRuleBodyTokenPayloadBound
                        dummy rho))))))

      · apply max_le

        · have hcount :
              (H.encodeCompiledBinaryRuleNaturalPacket dummy rho).
                  bodyTokens.length <=
                H.compiledBinaryRuleBodyTokenPayloadBound
                  dummy rho :=
            Nat.le_max_left
              (H.encodeCompiledBinaryRuleNaturalPacket dummy rho).
                bodyTokens.length
              (max
                (compiledTerminalAlphabet K dummy).card
                (max 1 f))

          exact
            hcount.trans
              ((Nat.le_max_right
                  3
                  (H.compiledBinaryRuleBodyTokenPayloadBound
                    dummy rho)).trans
                ((Nat.le_max_right
                    H.compiledGrammarPresentationItemCount
                    (max 3
                      (H.compiledBinaryRuleBodyTokenPayloadBound
                        dummy rho))).trans
                  ((Nat.le_max_right
                      4
                      (max
                        H.compiledGrammarPresentationItemCount
                        (max 3
                          (H.compiledBinaryRuleBodyTokenPayloadBound
                            dummy rho)))).trans
                    (Nat.le_max_right
                      (H.encodeCompiledBinaryRuleNaturalList dummy rho).length
                      (max 4
                        (max
                          H.compiledGrammarPresentationItemCount
                          (max 3
                            (H.compiledBinaryRuleBodyTokenPayloadBound
                              dummy rho)))))))

        · exact
            (H.compiledBinaryRuleMaximumBodyTokenNaturalValueBound_le_payloadBound
                dummy rho hrho).trans
              ((Nat.le_max_right
                  H.compiledGrammarPresentationItemCount
                  (max 3
                    (H.compiledBinaryRuleBodyTokenPayloadBound
                      dummy rho))).trans
                ((Nat.le_max_right
                    4
                    (max
                      H.compiledGrammarPresentationItemCount
                      (max 3
                        (H.compiledBinaryRuleBodyTokenPayloadBound
                          dummy rho)))).trans
                  (Nat.le_max_right
                    (H.encodeCompiledBinaryRuleNaturalList dummy rho).length
                    (max 4
                      (max
                        H.compiledGrammarPresentationItemCount
                        (max 3
                          (H.compiledBinaryRuleBodyTokenPayloadBound
                            dummy rho))))))

/-- The original binary-rule natural-value bound is below the fully explicit
stored-rule bound. -/
theorem
    compiledBinaryRuleNaturalValueBound_le_fullyExplicit_of_mem
    (dummy : α)
    (rho : BinaryRule
      (CorrectedConcreteCutGrammarNonterminal H)
      α
      (correctedConcreteCutGrammarArity H))
    (hrho :
      rho ∈ (H.toCutWorkingMCFG dummy).binaryRules) :
    H.compiledBinaryRuleNaturalValueBound dummy rho <=
      H.compiledBinaryRuleFullyExplicitNaturalValueBound
        dummy rho := by

  exact
    (H.compiledBinaryRuleNaturalValueBound_le_explicitBound
        dummy rho).trans
      (H.compiledBinaryRuleExplicitNaturalValueBound_le_fullyExplicit_of_mem
        dummy rho hrho)

/-- Expanded form of the common body-token payload bound. -/
theorem compiledBinaryRuleBodyTokenPayloadBound_eq
    (dummy : α)
    (rho : BinaryRule
      (CorrectedConcreteCutGrammarNonterminal H)
      α
      (correctedConcreteCutGrammarArity H)) :
    H.compiledBinaryRuleBodyTokenPayloadBound dummy rho =
      max
        (correctedConcreteCutGrammarArity H rho.lhs +
          ((List.ofFn rho.body).map List.length).sum)
        (max
          (compiledTerminalAlphabet K dummy).card
          (max 1 f)) := by

  unfold compiledBinaryRuleBodyTokenPayloadBound

  rw [
    H.encodeCompiledBinaryRuleNaturalPacket_bodyTokenCount_eq
      dummy rho
  ]

/-- Expanded form of the fully explicit binary-rule bound. -/
theorem compiledBinaryRuleFullyExplicitNaturalValueBound_eq
    (dummy : α)
    (rho : BinaryRule
      (CorrectedConcreteCutGrammarNonterminal H)
      α
      (correctedConcreteCutGrammarArity H)) :
    H.compiledBinaryRuleFullyExplicitNaturalValueBound dummy rho =
      max
        (4 +
          2 *
            (correctedConcreteCutGrammarArity H rho.lhs +
              ((List.ofFn rho.body).map List.length).sum))
        (max 4
          (max
            H.compiledGrammarPresentationItemCount
            (max 3
              (max
                (correctedConcreteCutGrammarArity H rho.lhs +
                  ((List.ofFn rho.body).map List.length).sum)
                (max
                  (compiledTerminalAlphabet K dummy).card
                  (max 1 f)))))) := by

  unfold compiledBinaryRuleFullyExplicitNaturalValueBound

  rw [
    H.encodeCompiledBinaryRuleNaturalList_length
      dummy rho
  ]

  rw [
    H.compiledBinaryRuleBodyTokenPayloadBound_eq
      dummy rho
  ]

/-- Compact final package for one stored binary rule. -/
theorem compiledBinaryRuleTokenPayloadBounds_package
    (dummy : α)
    (rho : BinaryRule
      (CorrectedConcreteCutGrammarNonterminal H)
      α
      (correctedConcreteCutGrammarArity H))
    (hrho :
      rho ∈ (H.toCutWorkingMCFG dummy).binaryRules) :
    (∀ token ∈
        (H.encodeCompiledBinaryRuleNaturalPacket dummy rho).
          bodyTokens,
      framedTemplateBodyNaturalTokenPayload token <=
        H.compiledBinaryRuleBodyTokenPayloadBound
          dummy rho) ∧
      (H.compiledBinaryRuleMaximumBodyTokenNaturalValueBound
          dummy rho <=
        max 3
          (H.compiledBinaryRuleBodyTokenPayloadBound
            dummy rho)) ∧
      (H.compiledBinaryRuleExplicitNaturalValueBound dummy rho <=
        H.compiledBinaryRuleFullyExplicitNaturalValueBound
          dummy rho) ∧
      (H.compiledBinaryRuleNaturalValueBound dummy rho <=
        H.compiledBinaryRuleFullyExplicitNaturalValueBound
          dummy rho) := by

  exact
    ⟨by
        intro token htoken
        exact
          H.compiledBinaryRuleBodyToken_payload_le_of_mem
            dummy rho hrho token htoken,
      H.compiledBinaryRuleMaximumBodyTokenNaturalValueBound_le_payloadBound
        dummy rho hrho,
      H.compiledBinaryRuleExplicitNaturalValueBound_le_fullyExplicit_of_mem
        dummy rho hrho,
      H.compiledBinaryRuleNaturalValueBound_le_fullyExplicit_of_mem
        dummy rho hrho⟩

end CorrectedConcreteFiniteHypothesis

end FullyExplicitStoredBinaryRuleBound

end MCFG
