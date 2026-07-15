/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG.ConcreteCanonicalLearnerWorkingGrammarPresentationSize

/-!
# ConcreteCanonicalLearnerWorkingGrammarStructuralConditions.lean

The cut-saturated compiler produces an actual finite `WorkingMCFG`, and the
preceding files prove exact language equivalence and explicit size bounds.

This file records exactly which working-grammar side conditions the compiled
grammar satisfies.

The positive results are:

* every control nonterminal has arity at most `max 1 f`;
* the compiled grammar has fan-out at most `max 1 f`;
* if `1 ≤ f`, it has fan-out at most `f`;
* the fresh start has arity one;
* all start rules are well-typed;
* the unique seed terminal rule is well-typed.

The negative result is equally important.

Constant control rules and saturated cut rules use dummy seed children.
In particular, every constant control rule ignores both children.  Therefore,
as soon as the control set is nonempty, the compiled grammar does not satisfy
the nondeleting condition from `BasicWorkingConditions`.  A nonempty sample
always gives a nonempty control set, so:

```lean
K.Nonempty →
  ¬ (H.toCutWorkingMCFG dummy).BasicWorkingConditions
```

and hence also:

```lean
K.Nonempty →
  ¬ (H.toCutWorkingMCFG dummy).ExactWorkingConditions.
```

This does not affect the verified language equivalence or Gold identification.
It identifies the precise status of the compiled grammar:

* it is a finite, bounded-fan-out, well-typed semantic compilation target;
* it is not itself an exact-once/nondeleting working grammar in the paper's
  restricted normal form.

A later normal-form construction would need to remove the dummy-child
erasure, rather than merely repackage these rules.

No target grammar occurs in the construction.
No `sorry`, `admit`, or `axiom` is used.
-/

namespace MCFG

universe u v w

section ControlCodeFanout

variable {α : Type u}
variable {M : Type v} [Monoid M]
variable {K : Finset (Word α)}
variable {obs : α → M}
variable {f : Nat}

/-- Every finite control tuple code has arity at most `max 1 f`.  Sample
singleton codes contribute the possible arity-one case; all rule-derived
control codes have arity at most `f`. -/
theorem CorrectedConcreteFiniteHypothesis.controlCode_arity_le_max
    (H :
      CorrectedConcreteFiniteHypothesis
        K obs f)
    {X : FiniteObjectTupleCode α}
    (hX : H.IsControlCode X) :
    X.arity ≤ max 1 f := by
  classical

  unfold CorrectedConcreteFiniteHypothesis.IsControlCode at hX
  unfold CorrectedConcreteFiniteHypothesis.controlCodes at hX

  rcases Finset.mem_union.mp hX with hword | hrest

  · rcases Finset.mem_image.mp hword with
      ⟨word, hword, rfl⟩
    exact Nat.le_max_left 1 f

  · rcases Finset.mem_union.mp hrest with hunitSource | hrest

    · rcases Finset.mem_image.mp hunitSource with
        ⟨U, hU, rfl⟩
      exact
        U.arity_le.trans
          (Nat.le_max_right 1 f)

    · rcases Finset.mem_union.mp hrest with hunitTarget | hrest

      · rcases Finset.mem_image.mp hunitTarget with
          ⟨U, hU, rfl⟩
        exact
          U.arity_le.trans
            (Nat.le_max_right 1 f)

      · rcases Finset.mem_union.mp hrest with hbinarySource | hrest

        · rcases Finset.mem_image.mp hbinarySource with
            ⟨B, hB, rfl⟩
          exact
            B.parentArity_le.trans
              (Nat.le_max_right 1 f)

        · rcases Finset.mem_union.mp hrest with hbinaryLeft | hbinaryRight

          · rcases Finset.mem_image.mp hbinaryLeft with
              ⟨B, hB, rfl⟩
            exact
              B.leftArity_le.trans
                (Nat.le_max_right 1 f)

          · rcases Finset.mem_image.mp hbinaryRight with
              ⟨B, hB, rfl⟩
            exact
              B.rightArity_le.trans
                (Nat.le_max_right 1 f)

/-- If the fixed fan-out bound is positive, every finite control tuple code has
arity at most `f` itself. -/
theorem CorrectedConcreteFiniteHypothesis.controlCode_arity_le
    (H :
      CorrectedConcreteFiniteHypothesis
        K obs f)
    (hf : 1 ≤ f)
    {X : FiniteObjectTupleCode α}
    (hX : H.IsControlCode X) :
    X.arity ≤ f := by

  have h :=
    H.controlCode_arity_le_max hX

  rw [max_eq_right hf] at h

  exact h

end ControlCodeFanout


section CompiledGrammarFanout

variable {α : Type u}
variable {M : Type v} [Monoid M]
variable {K : Finset (Word α)}
variable {obs : α → M}
variable {f : Nat}

/-- The concrete cut-saturated grammar has fan-out at most `max 1 f`. -/
theorem CorrectedConcreteFiniteHypothesis.toCutWorkingMCFG_fanoutAtMost_max
    (H :
      CorrectedConcreteFiniteHypothesis
        K obs f)
    (dummy : α) :
    (H.toCutWorkingMCFG
      dummy).FanoutAtMost
        (max 1 f) := by

  intro A

  cases A with

  | start =>
      exact Nat.le_max_left 1 f

  | seed =>
      exact Nat.le_max_left 1 f

  | control X =>
      exact
        H.controlCode_arity_le_max
          X.2

/-- Under the natural positive fan-out assumption, the compiler preserves the
original bound `f`. -/
theorem CorrectedConcreteFiniteHypothesis.toCutWorkingMCFG_fanoutAtMost
    (H :
      CorrectedConcreteFiniteHypothesis
        K obs f)
    (dummy : α)
    (hf : 1 ≤ f) :
    (H.toCutWorkingMCFG
      dummy).FanoutAtMost f := by

  have h :=
    H.toCutWorkingMCFG_fanoutAtMost_max
      dummy

  rw [max_eq_right hf] at h

  exact h

/-- Every actual learner output has fan-out at most `max 1 f`. -/
theorem correctedConcreteWorkingGrammarLearner_fanoutAtMost_max
    (hα : Nonempty α)
    (obs : α → M)
    (f : Nat)
    (K : Finset (Word α)) :
    (correctedConcreteWorkingGrammarLearner
      hα obs f K).grammar.FanoutAtMost
        (max 1 f) := by

  change
    ((correctedConcreteFiniteHypothesis
      K obs f).toCutWorkingMCFG
        (Classical.choice hα)).FanoutAtMost
          (max 1 f)

  exact
    (correctedConcreteFiniteHypothesis
      K obs f).toCutWorkingMCFG_fanoutAtMost_max
        (Classical.choice hα)

/-- Positive fixed fan-out is preserved by every actual learner output. -/
theorem correctedConcreteWorkingGrammarLearner_fanoutAtMost
    (hα : Nonempty α)
    (obs : α → M)
    (f : Nat)
    (hf : 1 ≤ f)
    (K : Finset (Word α)) :
    (correctedConcreteWorkingGrammarLearner
      hα obs f K).grammar.FanoutAtMost f := by

  change
    ((correctedConcreteFiniteHypothesis
      K obs f).toCutWorkingMCFG
        (Classical.choice hα)).FanoutAtMost f

  exact
    (correctedConcreteFiniteHypothesis
      K obs f).toCutWorkingMCFG_fanoutAtMost
        (Classical.choice hα) hf

end CompiledGrammarFanout


section CompiledGrammarTyping

variable {α : Type u}
variable {M : Type v} [Monoid M]
variable {K : Finset (Word α)}
variable {obs : α → M}
variable {f : Nat}

/-- The fresh start symbol has arity one. -/
theorem CorrectedConcreteFiniteHypothesis.toCutWorkingMCFG_startArityOne
    (H :
      CorrectedConcreteFiniteHypothesis
        K obs f)
    (dummy : α) :
    (H.toCutWorkingMCFG
      dummy).StartArityOne := by
  rfl

/-- Every start rule introduced from a sample word is well-typed. -/
theorem CorrectedConcreteFiniteHypothesis.toCutWorkingMCFG_startRulesWellTyped
    (H :
      CorrectedConcreteFiniteHypothesis
        K obs f)
    (dummy : α) :
    (H.toCutWorkingMCFG
      dummy).StartRulesWellTyped := by

  intro ρ hρ

  change
    ρ ∈
      K.attach.toList.map
        (correctedConcreteCutStartRule H)
      at hρ

  rcases List.mem_map.mp hρ with
    ⟨sampleWord, hsampleWord, rfl⟩

  rfl

/-- The unique dummy seed terminal rule is well-typed. -/
theorem CorrectedConcreteFiniteHypothesis.toCutWorkingMCFG_terminalRulesWellTyped
    (H :
      CorrectedConcreteFiniteHypothesis
        K obs f)
    (dummy : α) :
    (H.toCutWorkingMCFG
      dummy).TerminalRulesWellTyped := by

  intro ρ hρ

  change
    ρ ∈
      [correctedConcreteCutSeedRule
        H dummy]
      at hρ

  simp only [List.mem_singleton] at hρ

  subst ρ

  rfl

/-- The positive syntactic conditions actually preserved by the cut compiler.

This deliberately omits nondeleting/exact-once conditions. -/
def WorkingMCFG.CutCompiledConditions
    {N : Type v}
    (G : WorkingMCFG N α)
    (f : Nat) :
    Prop :=
  G.StartArityOne ∧
    G.StartRulesWellTyped ∧
    G.TerminalRulesWellTyped ∧
    G.FanoutAtMost (max 1 f)

/-- Every cut-saturated grammar satisfies the exact positive compiler
conditions. -/
theorem CorrectedConcreteFiniteHypothesis.toCutWorkingMCFG_cutCompiledConditions
    (H :
      CorrectedConcreteFiniteHypothesis
        K obs f)
    (dummy : α) :
    (H.toCutWorkingMCFG
      dummy).CutCompiledConditions f := by

  exact
    ⟨H.toCutWorkingMCFG_startArityOne
        dummy,
      H.toCutWorkingMCFG_startRulesWellTyped
        dummy,
      H.toCutWorkingMCFG_terminalRulesWellTyped
        dummy,
      H.toCutWorkingMCFG_fanoutAtMost_max
        dummy⟩

/-- Every learner output satisfies the positive compiler conditions. -/
theorem correctedConcreteWorkingGrammarLearner_cutCompiledConditions
    (hα : Nonempty α)
    (obs : α → M)
    (f : Nat)
    (K : Finset (Word α)) :
    (correctedConcreteWorkingGrammarLearner
      hα obs f K).grammar.CutCompiledConditions f := by

  change
    ((correctedConcreteFiniteHypothesis
      K obs f).toCutWorkingMCFG
        (Classical.choice hα)).CutCompiledConditions f

  exact
    (correctedConcreteFiniteHypothesis
      K obs f).toCutWorkingMCFG_cutCompiledConditions
        (Classical.choice hα)

end CompiledGrammarTyping


section ConstantRuleErasure

variable {α : Type u}

/-- A constant tuple template with two arity-one children is not nondeleting:
its body contains no left-child variable. -/
theorem constantTupleTemplate_not_nondeleting
    {d : Nat}
    (x : Tuple α d) :
    ¬ TemplateTuple.Nondeleting
      (constantTupleTemplate x) := by

  intro hnondeleting

  rcases hnondeleting.1
      (0 : Fin 1) with
    ⟨o, ho⟩

  change
    TemplateAtom.leftVar
        (0 : Fin 1) ∈
      (x o).map TemplateAtom.terminal
    at ho

  simpa using ho

end ConstantRuleErasure


section CompiledGrammarNondeletingFailure

variable {α : Type u}
variable {M : Type v} [Monoid M]
variable {K : Finset (Word α)}
variable {obs : α → M}
variable {f : Nat}

/-- Every constant control rule violates the nondeleting side condition. -/
theorem correctedConcreteCutConstantRule_not_nondeleting
    (H :
      CorrectedConcreteFiniteHypothesis
        K obs f)
    (X : H.controlCodes.attach) :
    ¬
      (correctedConcreteCutConstantRule
        H X).Nondeleting := by

  unfold BinaryRule.Nondeleting

  exact
    constantTupleTemplate_not_nondeleting
      X.1.tuple

/-- A nonempty control set forces failure of the grammar-wide nondeleting
condition. -/
theorem CorrectedConcreteFiniteHypothesis.toCutWorkingMCFG_not_binaryRulesNondeleting_of_controlCodes_nonempty
    (H :
      CorrectedConcreteFiniteHypothesis
        K obs f)
    (dummy : α)
    (hcontrol :
      H.controlCodes.Nonempty) :
    ¬
      (H.toCutWorkingMCFG
        dummy).BinaryRulesNondeleting := by

  intro hnondeleting

  rcases hcontrol with
    ⟨X, hX⟩

  let Xcode :
      H.controlCodes.attach :=
    ⟨X, hX⟩

  have hrule :
      correctedConcreteCutConstantRule
          H Xcode ∈
        (H.toCutWorkingMCFG
          dummy).binaryRules :=
    H.cutConstantRule_mem
      dummy Xcode

  exact
    correctedConcreteCutConstantRule_not_nondeleting
      H Xcode
      (hnondeleting
        (correctedConcreteCutConstantRule
          H Xcode)
        hrule)

/-- A nonempty sample always supplies at least one finite control code. -/
theorem CorrectedConcreteFiniteHypothesis.controlCodes_nonempty_of_sample_nonempty
    (H :
      CorrectedConcreteFiniteHypothesis
        K obs f)
    (hK : K.Nonempty) :
    H.controlCodes.Nonempty := by

  rcases hK with
    ⟨word, hword⟩

  refine
    ⟨FiniteObjectTupleCode.ofWord word,
      ?_⟩

  exact
    H.word_control hword

/-- The cut-saturated compiler does not satisfy grammar-wide nondeleting when
the input sample is nonempty. -/
theorem CorrectedConcreteFiniteHypothesis.toCutWorkingMCFG_not_binaryRulesNondeleting_of_sample_nonempty
    (H :
      CorrectedConcreteFiniteHypothesis
        K obs f)
    (dummy : α)
    (hK : K.Nonempty) :
    ¬
      (H.toCutWorkingMCFG
        dummy).BinaryRulesNondeleting := by

  exact
    H.toCutWorkingMCFG_not_binaryRulesNondeleting_of_controlCodes_nonempty
      dummy
      (H.controlCodes_nonempty_of_sample_nonempty
        hK)

/-- Therefore a compiled grammar from a nonempty sample does not satisfy the
paper's basic working conditions. -/
theorem CorrectedConcreteFiniteHypothesis.toCutWorkingMCFG_not_basicWorkingConditions_of_sample_nonempty
    (H :
      CorrectedConcreteFiniteHypothesis
        K obs f)
    (dummy : α)
    (hK : K.Nonempty) :
    ¬
      (H.toCutWorkingMCFG
        dummy).BasicWorkingConditions := by

  intro hbasic

  exact
    H.toCutWorkingMCFG_not_binaryRulesNondeleting_of_sample_nonempty
      dummy hK
      hbasic.2.2.2

/-- Consequently the stronger exact working conditions also fail for every
nonempty input sample. -/
theorem CorrectedConcreteFiniteHypothesis.toCutWorkingMCFG_not_exactWorkingConditions_of_sample_nonempty
    (H :
      CorrectedConcreteFiniteHypothesis
        K obs f)
    (dummy : α)
    (hK : K.Nonempty) :
    ¬
      (H.toCutWorkingMCFG
        dummy).ExactWorkingConditions := by

  intro hexact

  exact
    H.toCutWorkingMCFG_not_basicWorkingConditions_of_sample_nonempty
      dummy hK
      hexact.basic

/-- Learner-output form of the nondeleting obstruction. -/
theorem correctedConcreteWorkingGrammarLearner_not_binaryRulesNondeleting_of_sample_nonempty
    (hα : Nonempty α)
    (obs : α → M)
    (f : Nat)
    (K : Finset (Word α))
    (hK : K.Nonempty) :
    ¬
      (correctedConcreteWorkingGrammarLearner
        hα obs f K).grammar.BinaryRulesNondeleting := by

  change
    ¬
      ((correctedConcreteFiniteHypothesis
        K obs f).toCutWorkingMCFG
          (Classical.choice hα)).BinaryRulesNondeleting

  exact
    (correctedConcreteFiniteHypothesis
      K obs f).toCutWorkingMCFG_not_binaryRulesNondeleting_of_sample_nonempty
        (Classical.choice hα)
        hK

/-- Learner-output form of failure of the basic working conditions. -/
theorem correctedConcreteWorkingGrammarLearner_not_basicWorkingConditions_of_sample_nonempty
    (hα : Nonempty α)
    (obs : α → M)
    (f : Nat)
    (K : Finset (Word α))
    (hK : K.Nonempty) :
    ¬
      (correctedConcreteWorkingGrammarLearner
        hα obs f K).grammar.BasicWorkingConditions := by

  change
    ¬
      ((correctedConcreteFiniteHypothesis
        K obs f).toCutWorkingMCFG
          (Classical.choice hα)).BasicWorkingConditions

  exact
    (correctedConcreteFiniteHypothesis
      K obs f).toCutWorkingMCFG_not_basicWorkingConditions_of_sample_nonempty
        (Classical.choice hα)
        hK

/-- Learner-output form of failure of exact working conditions. -/
theorem correctedConcreteWorkingGrammarLearner_not_exactWorkingConditions_of_sample_nonempty
    (hα : Nonempty α)
    (obs : α → M)
    (f : Nat)
    (K : Finset (Word α))
    (hK : K.Nonempty) :
    ¬
      (correctedConcreteWorkingGrammarLearner
        hα obs f K).grammar.ExactWorkingConditions := by

  change
    ¬
      ((correctedConcreteFiniteHypothesis
        K obs f).toCutWorkingMCFG
          (Classical.choice hα)).ExactWorkingConditions

  exact
    (correctedConcreteFiniteHypothesis
      K obs f).toCutWorkingMCFG_not_exactWorkingConditions_of_sample_nonempty
        (Classical.choice hα)
        hK

end CompiledGrammarNondeletingFailure


section StructuralBoundaryPackages

variable {α : Type u}
variable {M : Type v} [Monoid M]

/-- Exact positive and negative structural status of one compiled grammar. -/
theorem correctedConcreteFiniteHypothesis_cutWorkingGrammar_structural_package
    (K : Finset (Word α))
    (obs : α → M)
    (f : Nat)
    (dummy : α) :
    ((correctedConcreteFiniteHypothesis
        K obs f).toCutWorkingMCFG
          dummy).CutCompiledConditions f ∧
      ((correctedConcreteFiniteHypothesis
        K obs f).toCutWorkingMCFG
          dummy).StringLanguage =
        (correctedConcreteFiniteHypothesis
          K obs f).Language ∧
      (K.Nonempty →
        ¬
          ((correctedConcreteFiniteHypothesis
            K obs f).toCutWorkingMCFG
              dummy).BasicWorkingConditions) ∧
      (K.Nonempty →
        ¬
          ((correctedConcreteFiniteHypothesis
            K obs f).toCutWorkingMCFG
              dummy).ExactWorkingConditions) := by

  exact
    ⟨(correctedConcreteFiniteHypothesis
        K obs f).toCutWorkingMCFG_cutCompiledConditions
          dummy,
      correctedConcreteFiniteHypothesis_cutWorkingGrammar_language_eq
        (correctedConcreteFiniteHypothesis
          K obs f)
        dummy,
      (correctedConcreteFiniteHypothesis
        K obs f).toCutWorkingMCFG_not_basicWorkingConditions_of_sample_nonempty
          dummy,
      (correctedConcreteFiniteHypothesis
        K obs f).toCutWorkingMCFG_not_exactWorkingConditions_of_sample_nonempty
          dummy⟩

/-- Actual learner package: exact semantics, bounded fan-out, well-typed
start/terminal structure, and the precise nondeleting obstruction. -/
theorem correctedConcreteWorkingGrammarLearner_structuralBoundary_package
    (hα : Nonempty α)
    (obs : α → M)
    (f : Nat)
    (K : Finset (Word α)) :
    (correctedConcreteWorkingGrammarLearner
        hα obs f K).grammar.CutCompiledConditions f ∧
      (correctedConcreteWorkingGrammarLearner
        hα obs f K).grammar.StringLanguage =
          CorrectedConcreteCanonicalLearnerLanguage
            K obs f ∧
      (K.Nonempty →
        ¬
          (correctedConcreteWorkingGrammarLearner
            hα obs f K).grammar.BasicWorkingConditions) ∧
      (K.Nonempty →
        ¬
          (correctedConcreteWorkingGrammarLearner
            hα obs f K).grammar.ExactWorkingConditions) := by

  exact
    ⟨correctedConcreteWorkingGrammarLearner_cutCompiledConditions
        hα obs f K,
      correctedConcreteWorkingGrammarLearner_stringLanguage_eq_corrected
        hα obs f K,
      correctedConcreteWorkingGrammarLearner_not_basicWorkingConditions_of_sample_nonempty
        hα obs f K,
      correctedConcreteWorkingGrammarLearner_not_exactWorkingConditions_of_sample_nonempty
        hα obs f K⟩

end StructuralBoundaryPackages


section ClassLevelStructuralPackage

variable {α : Type u}
variable {M : Type v}
variable [Fintype M]
variable [DecidableEq α]
variable [DecidableEq M]
variable [Monoid M]
variable (hα : Nonempty α)
variable (obs : α → M)
variable (f : Nat)

/-- Paper-facing class-level package: the actual grammar-valued learner
identifies the start-rooted class and every output has the verified positive
compiler conditions, while nonempty-sample outputs provably lie outside the
paper's exact working normal form. -/
theorem correctedConcreteWorkingGrammarLearner_class_structuralBoundary_package :
    IdentifiesClassFromPositiveData
        (correctedConcreteWorkingGrammarHypLanguage
          obs f)
        (correctedConcreteWorkingGrammarLearner
          hα obs f)
        (StartRootedCorrectedConcreteTargetClass
          (v := w) α M obs f) ∧
      (∀ K : Finset (Word α),
        (correctedConcreteWorkingGrammarLearner
          hα obs f K).grammar.CutCompiledConditions f) ∧
      (∀ K : Finset (Word α),
        (correctedConcreteWorkingGrammarLearner
          hα obs f K).grammar.StringLanguage =
            CorrectedConcreteCanonicalLearnerLanguage
              K obs f) ∧
      (∀ K : Finset (Word α),
        K.Nonempty →
          ¬
            (correctedConcreteWorkingGrammarLearner
              hα obs f K).grammar.ExactWorkingConditions) := by

  exact
    ⟨correctedConcreteWorkingGrammarLearner_identifies_startRootedTargetClass
        (v := w) hα obs f,
      correctedConcreteWorkingGrammarLearner_cutCompiledConditions
        hα obs f,
      correctedConcreteWorkingGrammarLearner_stringLanguage_eq_corrected
        hα obs f,
      fun K hK =>
        correctedConcreteWorkingGrammarLearner_not_exactWorkingConditions_of_sample_nonempty
          hα obs f K hK⟩

end ClassLevelStructuralPackage

end MCFG
