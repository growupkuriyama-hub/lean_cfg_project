/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG.ConcreteCanonicalLearnerWorkingGrammarCutSaturation

/-!
# ConcreteCanonicalLearnerWorkingGrammarConstruction.lean

This file constructs the finite `WorkingMCFG` syntax attached to the saturated
finite learner object.

A terminal symbol `dummy : α` is used only to provide terminal leaves.  The
grammar has:

* one fresh start nonterminal;
* one seed nonterminal with the terminal rule `seed → dummy`;
* one control nonterminal for every tuple code in `H.controlCodes`.

Its finite binary-rule list contains three families:

1. a constant rule for every control tuple;
2. one lifted rule for every listed corrected binary rule;
3. one left-identity rule for every saturated cut pair.

The constant and cut rules may ignore their seed child.  Therefore this
constructed grammar is a concrete `WorkingMCFG` in the lightweight syntax, but
it is not claimed to satisfy the paper's nondeleting or exact-once side
conditions.

The main theorem is:

```lean
correctedConcreteFiniteHypothesis_language_subset_cutWorkingGrammar.
```

Every listed finite-object derivation is first normalized using
`CutNormalizedListedFiniteDerives` and then translated to an actual
`DerivesTuple` proof of the constructed grammar.

The reverse inclusion is handled in the following equivalence file.

No target grammar occurs in the construction.
No `sorry`, `admit`, or `axiom` is used.
-/

namespace MCFG

universe u v

section ControlArity

variable {α : Type u}
variable {M : Type v} [Monoid M]
variable {K : Finset (Word α)}
variable {obs : α → M}
variable {f : Nat}

/-- Every tuple code in the finite control set has positive arity. -/
theorem CorrectedConcreteFiniteHypothesis.controlCode_arity_pos
    (H :
      CorrectedConcreteFiniteHypothesis
        K obs f)
    {X : FiniteObjectTupleCode α}
    (hX : H.IsControlCode X) :
    0 < X.arity := by
  classical

  unfold CorrectedConcreteFiniteHypothesis.IsControlCode at hX
  unfold CorrectedConcreteFiniteHypothesis.controlCodes at hX

  rcases Finset.mem_union.mp hX with hword | hrest

  · rcases Finset.mem_image.mp hword with
      ⟨word, hword, rfl⟩
    omega

  · rcases Finset.mem_union.mp hrest with hunitSource | hrest

    · rcases Finset.mem_image.mp hunitSource with
        ⟨U, hU, rfl⟩
      exact U.arity_pos

    · rcases Finset.mem_union.mp hrest with hunitTarget | hrest

      · rcases Finset.mem_image.mp hunitTarget with
          ⟨U, hU, rfl⟩
        exact U.arity_pos

      · rcases Finset.mem_union.mp hrest with hbinarySource | hrest

        · rcases Finset.mem_image.mp hbinarySource with
            ⟨B, hB, rfl⟩
          exact B.parentArity_pos

        · rcases Finset.mem_union.mp hrest with hbinaryLeft | hbinaryRight

          · rcases Finset.mem_image.mp hbinaryLeft with
              ⟨B, hB, rfl⟩
            exact B.leftArity_pos

          · rcases Finset.mem_image.mp hbinaryRight with
              ⟨B, hB, rfl⟩
            exact B.rightArity_pos

end ControlArity


section GrammarNonterminals

variable {α : Type u}
variable {M : Type v} [Monoid M]
variable {K : Finset (Word α)}
variable {obs : α → M}
variable {f : Nat}

/-- A control tuple code bundled with its control-set membership proof. -/
abbrev FiniteObjectControlCode
    (H :
      CorrectedConcreteFiniteHypothesis
        K obs f) :=
  {X : FiniteObjectTupleCode α //
    H.IsControlCode X}

/-- Nonterminals of the concrete cut-saturated grammar. -/
inductive CorrectedConcreteCutGrammarNonterminal
    (H :
      CorrectedConcreteFiniteHypothesis
        K obs f) where

  | start

  | seed

  | control
      (X : FiniteObjectControlCode H)

/-- Arity function of the cut-saturated grammar. -/
def correctedConcreteCutGrammarArity
    (H :
      CorrectedConcreteFiniteHypothesis
        K obs f) :
    CorrectedConcreteCutGrammarNonterminal H →
      Nat

  | .start =>
      1

  | .seed =>
      1

  | .control X =>
      X.1.arity

/-- Canonical control nonterminal attached to one controlled tuple code. -/
def correctedConcreteControlNode
    (H :
      CorrectedConcreteFiniteHypothesis
        K obs f)
    (X : FiniteObjectTupleCode α)
    (hX : H.IsControlCode X) :
    CorrectedConcreteCutGrammarNonterminal H :=
  .control ⟨X, hX⟩

@[simp] theorem correctedConcreteCutGrammarArity_start
    (H :
      CorrectedConcreteFiniteHypothesis
        K obs f) :
    correctedConcreteCutGrammarArity H
        (.start :
          CorrectedConcreteCutGrammarNonterminal H) =
      1 :=
  rfl

@[simp] theorem correctedConcreteCutGrammarArity_seed
    (H :
      CorrectedConcreteFiniteHypothesis
        K obs f) :
    correctedConcreteCutGrammarArity H
        (.seed :
          CorrectedConcreteCutGrammarNonterminal H) =
      1 :=
  rfl

@[simp] theorem correctedConcreteCutGrammarArity_control
    (H :
      CorrectedConcreteFiniteHypothesis
        K obs f)
    (X : FiniteObjectControlCode H) :
    correctedConcreteCutGrammarArity H
        (.control X) =
      X.1.arity :=
  rfl

@[simp] theorem correctedConcreteCutGrammarArity_controlNode
    (H :
      CorrectedConcreteFiniteHypothesis
        K obs f)
    (X : FiniteObjectTupleCode α)
    (hX : H.IsControlCode X) :
    correctedConcreteCutGrammarArity H
        (correctedConcreteControlNode H X hX) =
      X.arity :=
  rfl

/-- Proof fields do not affect the control nonterminal. -/
theorem correctedConcreteControlNode_proof_irrel
    (H :
      CorrectedConcreteFiniteHypothesis
        K obs f)
    (X : FiniteObjectTupleCode α)
    (hX hX' : H.IsControlCode X) :
    correctedConcreteControlNode H X hX =
      correctedConcreteControlNode H X hX' := by
  apply congrArg
    CorrectedConcreteCutGrammarNonterminal.control
  apply Subtype.ext
  rfl

end GrammarNonterminals


section ConstantAndIdentityTemplates

variable {α : Type u}

/-- A template word consisting only of literal terminal atoms. -/
def terminalTemplateWord
    {dB dC : Nat}
    (word : Word α) :
    TemplateWord α dB dC :=
  word.map TemplateAtom.terminal

/-- Evaluating a literal terminal template returns the original word. -/
theorem eval_terminalTemplateWord
    {dB dC : Nat}
    (word : Word α)
    (x : Tuple α dB)
    (y : Tuple α dC) :
    evalTemplateWord x y
        (terminalTemplateWord word) =
      word := by
  induction word with

  | nil =>
      rfl

  | cons a rest ih =>
      simp [
        terminalTemplateWord,
        evalTemplateWord,
        evalTemplateAtom,
        ih
      ]

/-- A binary template that returns one fixed tuple and ignores both children. -/
def constantTupleTemplate
    {d : Nat}
    (x : Tuple α d) :
    TemplateTuple α d 1 1 :=
  fun i =>
    terminalTemplateWord (x i)

/-- Evaluation of a constant tuple template. -/
theorem eval_constantTupleTemplate
    {d : Nat}
    (x : Tuple α d)
    (left right : Tuple α 1) :
    evalTemplateTuple
        (constantTupleTemplate x)
        left right =
      x := by
  funext i
  exact
    eval_terminalTemplateWord
      (x i) left right

/-- Left-identity template across an equality of output and child arities. -/
def leftIdentityTupleTemplate
    {e d : Nat}
    (h : e = d) :
    TemplateTuple α e d 1 :=
  fun i =>
    [TemplateAtom.leftVar
      (Fin.cast h i)]

/-- Evaluation of the left-identity template. -/
theorem eval_leftIdentityTupleTemplate
    {e d : Nat}
    (h : e = d)
    (x : Tuple α d)
    (seed : Tuple α 1) :
    evalTemplateTuple
        (leftIdentityTupleTemplate
          (α := α) h)
        x seed =
      castTuple h.symm x := by
  subst h
  funext i
  simp [
    leftIdentityTupleTemplate,
    evalTemplateTuple,
    evalTemplateWord,
    evalTemplateAtom
  ]

/-- Casting a tuple along any self-equality is the identity. -/
theorem castTuple_self
    {d : Nat}
    (h : d = d)
    (x : Tuple α d) :
    castTuple h x = x := by
  have hh :
      h = rfl :=
    Subsingleton.elim _ _
  subst hh
  rfl

end ConstantAndIdentityTemplates


section SaturatedCutWitnesses

variable {α : Type u}
variable {M : Type v} [Monoid M]
variable {K : Finset (Word α)}
variable {obs : α → M}
variable {f : Nat}

/-- Equality of the two arities stored by a saturated cut pair. -/
noncomputable def CorrectedConcreteFiniteHypothesis.cutPairArityEq
    (H :
      CorrectedConcreteFiniteHypothesis
        K obs f)
    (p :
      {p :
        FiniteObjectTupleCode α ×
          FiniteObjectTupleCode α //
        p ∈ H.cutPairs}) :
    p.1.1.arity =
      p.1.2.arity :=
  Classical.choose
    (H.cutPair_admissible p.2)

/-- Listed derivation witness stored semantically by a saturated cut pair. -/
theorem CorrectedConcreteFiniteHypothesis.cutPairDerives
    (H :
      CorrectedConcreteFiniteHypothesis
        K obs f)
    (p :
      {p :
        FiniteObjectTupleCode α ×
          FiniteObjectTupleCode α //
        p ∈ H.cutPairs}) :
    ListedFiniteCorrectedConcreteLearnerDerives
      K obs f H
      p.1.1.tuple
      (castTuple
        (H.cutPairArityEq p).symm
        p.1.2.tuple) :=
  Classical.choose_spec
    (H.cutPair_admissible p.2)

end SaturatedCutWitnesses


section LiftedGrammarRules

variable {α : Type u}
variable {M : Type v} [Monoid M]
variable {K : Finset (Word α)}
variable {obs : α → M}
variable {f : Nat}

/-- Start rule corresponding to one observed sample word. -/
def correctedConcreteCutStartRule
    (H :
      CorrectedConcreteFiniteHypothesis
        K obs f)
    (w : K.attach) :
    StartRule
      (CorrectedConcreteCutGrammarNonterminal H) where

  child :=
    correctedConcreteControlNode H
      (FiniteObjectTupleCode.ofWord w.1)
      (H.word_control w.2)

/-- The unique terminal rule used for dummy leaves. -/
def correctedConcreteCutSeedRule
    (H :
      CorrectedConcreteFiniteHypothesis
        K obs f)
    (dummy : α) :
    TerminalRule
      (CorrectedConcreteCutGrammarNonterminal H)
      α where

  lhs :=
    .seed

  terminal :=
    dummy

/-- Constant rule generating the tuple carried by one control code. -/
def correctedConcreteCutConstantRule
    (H :
      CorrectedConcreteFiniteHypothesis
        K obs f)
    (X : H.controlCodes.attach) :
    BinaryRule
      (CorrectedConcreteCutGrammarNonterminal H)
      α
      (correctedConcreteCutGrammarArity H) where

  lhs :=
    .control X

  left :=
    .seed

  right :=
    .seed

  body :=
    constantTupleTemplate X.1.tuple

/-- Lift one listed corrected binary rule to the cut-saturated grammar. -/
def correctedConcreteCutLiftedBinaryRule
    (H :
      CorrectedConcreteFiniteHypothesis
        K obs f)
    (B : H.binaryRuleCodes.attach) :
    BinaryRule
      (CorrectedConcreteCutGrammarNonterminal H)
      α
      (correctedConcreteCutGrammarArity H) where

  lhs :=
    correctedConcreteControlNode H
      B.1.sourceCode
      (H.binarySource_control
        B.1 B.2)

  left :=
    correctedConcreteControlNode H
      B.1.leftSourceCode
      (H.binaryLeftSource_control
        B.1 B.2)

  right :=
    correctedConcreteControlNode H
      B.1.rightSourceCode
      (H.binaryRightSource_control
        B.1 B.2)

  body :=
    B.1.body

/-- Lift one saturated cut pair to a binary left-identity rule. -/
noncomputable def correctedConcreteCutSaturationRule
    (H :
      CorrectedConcreteFiniteHypothesis
        K obs f)
    (p : H.cutPairs.attach) :
    BinaryRule
      (CorrectedConcreteCutGrammarNonterminal H)
      α
      (correctedConcreteCutGrammarArity H) where

  lhs :=
    correctedConcreteControlNode H
      p.1.1
      (H.cutPair_source_control p.2)

  left :=
    correctedConcreteControlNode H
      p.1.2
      (H.cutPair_target_control p.2)

  right :=
    .seed

  body :=
    leftIdentityTupleTemplate
      (α := α)
      (H.cutPairArityEq p)

@[simp] theorem correctedConcreteCutConstantRule_apply
    (H :
      CorrectedConcreteFiniteHypothesis
        K obs f)
    (X : H.controlCodes.attach)
    (left right : Tuple α 1) :
    (correctedConcreteCutConstantRule
      H X).apply left right =
      X.1.tuple := by
  exact
    eval_constantTupleTemplate
      X.1.tuple left right

@[simp] theorem correctedConcreteCutLiftedBinaryRule_apply
    (H :
      CorrectedConcreteFiniteHypothesis
        K obs f)
    (B : H.binaryRuleCodes.attach)
    (left : Tuple α B.1.leftArity)
    (right : Tuple α B.1.rightArity) :
    (correctedConcreteCutLiftedBinaryRule
      H B).apply left right =
      evalTemplateTuple B.1.body
        left right :=
  rfl

@[simp] theorem correctedConcreteCutSaturationRule_apply
    (H :
      CorrectedConcreteFiniteHypothesis
        K obs f)
    (p : H.cutPairs.attach)
    (x : Tuple α p.1.2.arity)
    (seed : Tuple α 1) :
    (correctedConcreteCutSaturationRule
      H p).apply x seed =
      castTuple
        (H.cutPairArityEq p).symm
        x := by
  exact
    eval_leftIdentityTupleTemplate
      (H.cutPairArityEq p)
      x seed

end LiftedGrammarRules


section ConcreteCutGrammar

variable {α : Type u}
variable {M : Type v} [Monoid M]
variable {K : Finset (Word α)}
variable {obs : α → M}
variable {f : Nat}

/-- Concrete finite `WorkingMCFG` generated from one complete finite learner
object and a dummy terminal symbol. -/
noncomputable def CorrectedConcreteFiniteHypothesis.toCutWorkingMCFG
    (H :
      CorrectedConcreteFiniteHypothesis
        K obs f)
    (dummy : α) :
    WorkingMCFG
      (CorrectedConcreteCutGrammarNonterminal H)
      α where

  start :=
    .start

  arity :=
    correctedConcreteCutGrammarArity H

  arity_pos := by
    intro A
    cases A with

    | start =>
        omega

    | seed =>
        omega

    | control X =>
        exact
          H.controlCode_arity_pos
            X.2

  startRules :=
    K.attach.toList.map
      (correctedConcreteCutStartRule H)

  terminalRules :=
    [correctedConcreteCutSeedRule
      H dummy]

  binaryRules :=
    H.controlCodes.attach.toList.map
        (correctedConcreteCutConstantRule H) ++
      H.binaryRuleCodes.attach.toList.map
        (correctedConcreteCutLiftedBinaryRule H) ++
      H.cutPairs.attach.toList.map
        (correctedConcreteCutSaturationRule H)

namespace CorrectedConcreteFiniteHypothesis

variable
  (H :
    CorrectedConcreteFiniteHypothesis
      K obs f)
variable
  (dummy : α)

/-- Every sample start rule occurs in the concrete grammar. -/
theorem cutStartRule_mem
    (w : K.attach) :
    correctedConcreteCutStartRule H w ∈
      (H.toCutWorkingMCFG
        dummy).startRules := by
  simp [
    CorrectedConcreteFiniteHypothesis.toCutWorkingMCFG
  ]

/-- The seed terminal rule occurs in the concrete grammar. -/
theorem cutSeedRule_mem :
    correctedConcreteCutSeedRule
        H dummy ∈
      (H.toCutWorkingMCFG
        dummy).terminalRules := by
  simp [
    CorrectedConcreteFiniteHypothesis.toCutWorkingMCFG
  ]

/-- Every control constant rule occurs in the concrete grammar. -/
theorem cutConstantRule_mem
    (X : H.controlCodes.attach) :
    correctedConcreteCutConstantRule H X ∈
      (H.toCutWorkingMCFG
        dummy).binaryRules := by
  simp [
    CorrectedConcreteFiniteHypothesis.toCutWorkingMCFG
  ]

/-- Every listed binary rule occurs in the concrete grammar. -/
theorem cutLiftedBinaryRule_mem
    (B : H.binaryRuleCodes.attach) :
    correctedConcreteCutLiftedBinaryRule H B ∈
      (H.toCutWorkingMCFG
        dummy).binaryRules := by
  simp [
    CorrectedConcreteFiniteHypothesis.toCutWorkingMCFG
  ]

/-- Every saturated cut rule occurs in the concrete grammar. -/
theorem cutSaturationRule_mem
    (p : H.cutPairs.attach) :
    correctedConcreteCutSaturationRule H p ∈
      (H.toCutWorkingMCFG
        dummy).binaryRules := by
  simp [
    CorrectedConcreteFiniteHypothesis.toCutWorkingMCFG
  ]

/-- The fresh grammar start has arity one. -/
@[simp] theorem toCutWorkingMCFG_start_arity :
    (H.toCutWorkingMCFG
      dummy).arity
        (H.toCutWorkingMCFG
          dummy).start =
      1 :=
  rfl

end CorrectedConcreteFiniteHypothesis

end ConcreteCutGrammar


section BasicGrammarDerivations

variable {α : Type u}
variable {M : Type v} [Monoid M]
variable {K : Finset (Word α)}
variable {obs : α → M}
variable {f : Nat}
variable
  (H :
    CorrectedConcreteFiniteHypothesis
      K obs f)
variable
  (dummy : α)

/-- Tuple generated by the dummy seed terminal. -/
def correctedConcreteCutSeedTuple :
    Tuple α 1 :=
  singletonTuple [dummy]

/-- The seed nonterminal derives its dummy singleton tuple. -/
theorem correctedConcreteCutSeed_derives :
    DerivesTuple
      (H.toCutWorkingMCFG dummy)
      (.seed :
        CorrectedConcreteCutGrammarNonterminal H)
      (correctedConcreteCutSeedTuple dummy) := by

  have h :=
    DerivesTuple.terminal
      (H.cutSeedRule_mem dummy)
      (rfl :
        (H.toCutWorkingMCFG dummy).arity
            (correctedConcreteCutSeedRule
              H dummy).lhs =
          1)

  simpa [
    correctedConcreteCutSeedTuple,
    correctedConcreteCutSeedRule
  ] using h

/-- Every control nonterminal derives its own stored tuple via its constant
rule. -/
theorem correctedConcreteCutControl_self_derives
    (X : H.controlCodes.attach) :
    DerivesTuple
      (H.toCutWorkingMCFG dummy)
      (.control X :
        CorrectedConcreteCutGrammarNonterminal H)
      X.1.tuple := by

  have h :=
    DerivesTuple.binary
      (H.cutConstantRule_mem dummy X)
      (correctedConcreteCutSeed_derives
        H dummy)
      (correctedConcreteCutSeed_derives
        H dummy)

  simpa using h

end BasicGrammarDerivations


section CutNormalEmbedding

variable {α : Type u}
variable {M : Type v} [Monoid M]
variable {K : Finset (Word α)}
variable {obs : α → M}
variable {f : Nat}
variable
  {H :
    CorrectedConcreteFiniteHypothesis
      K obs f}

namespace CutNormalizedListedFiniteDerives

/-- Every cut-normal finite-object derivation is a derivation of the concrete
cut-saturated working grammar. -/
theorem toCutWorkingMCFG
    (dummy : α)
    {d : Nat}
    {x y : Tuple α d}
    (h :
      CutNormalizedListedFiniteDerives
        H x y) :
    DerivesTuple
      (H.toCutWorkingMCFG dummy)
      (correctedConcreteControlNode H
        (FiniteObjectTupleCode.mk x)
        h.source_control)
      y := by

  induction h with

  | self x hx =>
      let X :
          H.controlCodes.attach :=
        ⟨FiniteObjectTupleCode.mk x, hx⟩

      have hself :=
        correctedConcreteCutControl_self_derives
          H dummy X

      simpa [
        X,
        correctedConcreteControlNode
      ] using hself

  | binary B hB hleft hright ihleft ihright =>
      let B' :
          H.binaryRuleCodes.attach :=
        ⟨B, hB⟩

      have hstep :=
        DerivesTuple.binary
          (H.cutLiftedBinaryRule_mem
            dummy B')
          ihleft
          ihright

      simpa [
        B',
        correctedConcreteCutLiftedBinaryRule,
        correctedConcreteControlNode
      ] using hstep

  | cut hx hy hxy hyz ihyz =>
      have hadmissible :
          H.CutAdmissible
            (FiniteObjectTupleCode.mk x)
            (FiniteObjectTupleCode.mk y) := by
        refine ⟨rfl, ?_⟩
        simpa using hxy

      have hpair :
          (FiniteObjectTupleCode.mk x,
            FiniteObjectTupleCode.mk y) ∈
            H.cutPairs :=
        H.mem_cutPairs_of_control_admissible
          hx hy hadmissible

      let p :
          H.cutPairs.attach :=
        ⟨(FiniteObjectTupleCode.mk x,
          FiniteObjectTupleCode.mk y),
          hpair⟩

      have hstep :=
        DerivesTuple.binary
          (H.cutSaturationRule_mem
            dummy p)
          ihyz
          (correctedConcreteCutSeed_derives
            H dummy)

      have hcast :
          castTuple
              (H.cutPairArityEq p).symm
              y =
            y :=
        castTuple_self
          (H.cutPairArityEq p).symm
          y

      simpa [
        p,
        correctedConcreteCutSaturationRule,
        correctedConcreteControlNode,
        hcast
      ] using hstep

end CutNormalizedListedFiniteDerives

end CutNormalEmbedding


section StringLanguageEmbedding

variable {α : Type u}
variable {M : Type v} [Monoid M]
variable {K : Finset (Word α)}
variable {obs : α → M}
variable {f : Nat}

/-- Every word of the listed finite-object language is generated by the
concrete cut-saturated working grammar. -/
theorem correctedConcreteFiniteHypothesis_language_subset_cutWorkingGrammar
    (H :
      CorrectedConcreteFiniteHypothesis
        K obs f)
    (dummy : α) :
    H.Language ⊆
      (H.toCutWorkingMCFG
        dummy).StringLanguage := by

  intro word hword

  rcases
      (correctedConcreteFiniteHypothesis_language_iff_cutNormalized
        H word).mp hword with
    ⟨startWord, hstart, hderives⟩

  let w :
      K.attach :=
    ⟨startWord, hstart⟩

  have hchild :=
    hderives.toCutWorkingMCFG
      dummy

  have hstartDerives :=
    DerivesTuple.start
      (H.cutStartRule_mem dummy w)
      hchild
      (rfl :
        (H.toCutWorkingMCFG dummy).arity
            (correctedConcreteCutStartRule
              H w).child =
          (H.toCutWorkingMCFG dummy).arity
            (H.toCutWorkingMCFG dummy).start)

  refine ⟨rfl, ?_⟩

  simpa [
    w,
    correctedConcreteCutStartRule,
    correctedConcreteControlNode
  ] using hstartDerives

/-- Canonical finite learner object version of the forward compilation
theorem. -/
theorem correctedConcreteCanonicalFiniteHypothesis_language_subset_cutWorkingGrammar
    (K : Finset (Word α))
    (obs : α → M)
    (f : Nat)
    (dummy : α) :
    (correctedConcreteFiniteHypothesis
        K obs f).Language ⊆
      ((correctedConcreteFiniteHypothesis
          K obs f).toCutWorkingMCFG
        dummy).StringLanguage :=
  correctedConcreteFiniteHypothesis_language_subset_cutWorkingGrammar
    (correctedConcreteFiniteHypothesis
      K obs f)
    dummy

/-- Paper-facing construction package: the grammar is finite by construction,
has one seed terminal rule, and contains the finite-object language. -/
theorem correctedConcreteFiniteHypothesis_cutWorkingGrammar_construction_package
    (H :
      CorrectedConcreteFiniteHypothesis
        K obs f)
    (dummy : α) :
    (H.toCutWorkingMCFG dummy).terminalRules =
        [correctedConcreteCutSeedRule
          H dummy] ∧
      H.Language ⊆
        (H.toCutWorkingMCFG
          dummy).StringLanguage := by
  exact
    ⟨rfl,
      correctedConcreteFiniteHypothesis_language_subset_cutWorkingGrammar
        H dummy⟩

end StringLanguageEmbedding

end MCFG
