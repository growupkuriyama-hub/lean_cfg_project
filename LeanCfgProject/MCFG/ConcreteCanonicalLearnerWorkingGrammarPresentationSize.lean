/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG.ConcreteCanonicalLearnerWorkingGrammarSize

/-!
# ConcreteCanonicalLearnerWorkingGrammarPresentationSize.lean

The preceding file counts every rule stored in the compiled `WorkingMCFG`.
This file adds an explicit finite enumeration of its nonterminals and bounds
the total finite presentation size.

For a finite learner object `H`, the compiler has exactly three kinds of
nonterminal:

```text
fresh start
dummy seed
one control node for every element of H.controlCodes.
```

The list

```lean
H.compiledGrammarNonterminals
```

contains all of them and has length

```lean
H.controlCodes.card + 2.
```

Combining this with the structural rule-count estimate gives

```lean
nonterminal entries + rule entries ≤
  (K.card + 3 * H.ruleCount + 3) ^ 2.
```

For the canonical learner object, substitution of the verified source-rule
bound yields the fully explicit estimate

```lean
(sampleLengthBudget K +
    3 *
      ((4 * (sampleLengthBudget K + f + 1)) ^
        (64 *
          (sampleLengthBudget K + f + 1) *
          (sampleLengthBudget K + f + 1))) +
    4) ^ 2.
```

This is an item-count bound for the actual compiled presentation:

* every nonterminal entry;
* every start rule;
* every terminal rule;
* every binary rule.

It is not yet a bit-length bound for words and templates stored inside those
entries.

No target grammar occurs in the bound.
No `sorry`, `admit`, or `axiom` is used.
-/

namespace MCFG

universe u v w

section ExplicitNonterminalEnumeration

variable {α : Type u}
variable {M : Type v} [Monoid M]
variable {K : Finset (Word α)}
variable {obs : α → M}
variable {f : Nat}

/-- Explicit finite enumeration of all nonterminals used by the cut-saturated
working grammar. -/
noncomputable def CorrectedConcreteFiniteHypothesis.compiledGrammarNonterminals
    (H :
      CorrectedConcreteFiniteHypothesis
        K obs f) :
    List
      (CorrectedConcreteCutGrammarNonterminal H) :=
  [CorrectedConcreteCutGrammarNonterminal.start,
    CorrectedConcreteCutGrammarNonterminal.seed] ++
    H.controlCodes.attach.toList.map
      CorrectedConcreteCutGrammarNonterminal.control

namespace CorrectedConcreteFiniteHypothesis

variable
  (H :
    CorrectedConcreteFiniteHypothesis
      K obs f)

/-- The fresh start nonterminal occurs in the explicit enumeration. -/
theorem start_mem_compiledGrammarNonterminals :
    (CorrectedConcreteCutGrammarNonterminal.start :
      CorrectedConcreteCutGrammarNonterminal H) ∈
      H.compiledGrammarNonterminals := by
  simp [
    CorrectedConcreteFiniteHypothesis.compiledGrammarNonterminals
  ]

/-- The dummy seed nonterminal occurs in the explicit enumeration. -/
theorem seed_mem_compiledGrammarNonterminals :
    (CorrectedConcreteCutGrammarNonterminal.seed :
      CorrectedConcreteCutGrammarNonterminal H) ∈
      H.compiledGrammarNonterminals := by
  simp [
    CorrectedConcreteFiniteHypothesis.compiledGrammarNonterminals
  ]

/-- Every control nonterminal occurs in the explicit enumeration. -/
theorem control_mem_compiledGrammarNonterminals
    (X : FiniteObjectControlCode H) :
    CorrectedConcreteCutGrammarNonterminal.control X ∈
      H.compiledGrammarNonterminals := by
  simp [
    CorrectedConcreteFiniteHypothesis.compiledGrammarNonterminals
  ]

/-- Every nonterminal of the constructed grammar occurs in the explicit
enumeration. -/
theorem mem_compiledGrammarNonterminals
    (A :
      CorrectedConcreteCutGrammarNonterminal H) :
    A ∈ H.compiledGrammarNonterminals := by
  cases A with

  | start =>
      exact
        H.start_mem_compiledGrammarNonterminals

  | seed =>
      exact
        H.seed_mem_compiledGrammarNonterminals

  | control X =>
      exact
        H.control_mem_compiledGrammarNonterminals
          X

/-- Exact length of the explicit nonterminal enumeration. -/
@[simp] theorem compiledGrammarNonterminals_length :
    H.compiledGrammarNonterminals.length =
      H.controlCodes.card + 2 := by
  simp [
    CorrectedConcreteFiniteHypothesis.compiledGrammarNonterminals,
    Nat.add_comm,
    Nat.add_left_comm,
    Nat.add_assoc
  ]

/-- Every nonterminal used by the actual grammar object is covered by the
explicit finite enumeration. -/
theorem toCutWorkingMCFG_nonterminal_covered
    (dummy : α)
    (A :
      CorrectedConcreteCutGrammarNonterminal H) :
    A ∈ H.compiledGrammarNonterminals :=
  H.mem_compiledGrammarNonterminals A

end CorrectedConcreteFiniteHypothesis

end ExplicitNonterminalEnumeration


section NonterminalCount

variable {α : Type u}
variable {M : Type v} [Monoid M]
variable {K : Finset (Word α)}
variable {obs : α → M}
variable {f : Nat}

/-- Number of entries in the explicit nonterminal enumeration. -/
def CorrectedConcreteFiniteHypothesis.compiledGrammarNonterminalCount
    (H :
      CorrectedConcreteFiniteHypothesis
        K obs f) :
    Nat :=
  H.compiledGrammarNonterminals.length

namespace CorrectedConcreteFiniteHypothesis

variable
  (H :
    CorrectedConcreteFiniteHypothesis
      K obs f)

/-- Exact nonterminal-entry count. -/
theorem compiledGrammarNonterminalCount_eq :
    H.compiledGrammarNonterminalCount =
      H.controlCodes.card + 2 := by
  unfold compiledGrammarNonterminalCount
  exact H.compiledGrammarNonterminals_length

/-- The nonterminal-entry count is controlled by sample size and source finite
rule count. -/
theorem compiledGrammarNonterminalCount_le_sample_rule
    :
    H.compiledGrammarNonterminalCount ≤
      K.card + 3 * H.ruleCount + 2 := by

  rw [
    H.compiledGrammarNonterminalCount_eq
  ]

  exact
    Nat.add_le_add_right
      H.controlCodes_card_le_sample_add_three_ruleCount
      2

/-- The nonterminal-entry count is at most the structural compiler scale. -/
theorem compiledGrammarNonterminalCount_le_scale :
    H.compiledGrammarNonterminalCount ≤
      H.compiledGrammarScale := by

  simpa [
    CorrectedConcreteFiniteHypothesis.compiledGrammarScale
  ] using
    H.compiledGrammarNonterminalCount_le_sample_rule

end CorrectedConcreteFiniteHypothesis

end NonterminalCount


section PresentationItemCount

variable {α : Type u}
variable {M : Type v} [Monoid M]
variable {K : Finset (Word α)}
variable {obs : α → M}
variable {f : Nat}

/-- Total number of top-level entries in the compiled finite presentation:
nonterminal entries plus rule entries. -/
def CorrectedConcreteFiniteHypothesis.compiledGrammarPresentationItemCount
    (H :
      CorrectedConcreteFiniteHypothesis
        K obs f) :
    Nat :=
  H.compiledGrammarNonterminalCount +
    H.compiledGrammarRuleCount

/-- Structural square bound for the full compiled presentation. -/
def CorrectedConcreteFiniteHypothesis.compiledGrammarPresentationBound
    (H :
      CorrectedConcreteFiniteHypothesis
        K obs f) :
    Nat :=
  (H.compiledGrammarScale + 1) ^ 2

namespace CorrectedConcreteFiniteHypothesis

variable
  (H :
    CorrectedConcreteFiniteHypothesis
      K obs f)

/-- The complete presentation item count is at most one compiler scale plus
the square of that scale. -/
theorem compiledGrammarPresentationItemCount_le_scale_add_square :
    H.compiledGrammarPresentationItemCount ≤
      H.compiledGrammarScale +
        H.compiledGrammarScale ^ 2 := by

  unfold compiledGrammarPresentationItemCount

  exact
    Nat.add_le_add
      H.compiledGrammarNonterminalCount_le_scale
      H.compiledGrammarRuleCount_le_quadratic

/-- The complete finite presentation is bounded by the square of one plus the
compiler scale. -/
theorem compiledGrammarPresentationItemCount_le_bound :
    H.compiledGrammarPresentationItemCount ≤
      H.compiledGrammarPresentationBound := by

  have h :=
    H.compiledGrammarPresentationItemCount_le_scale_add_square

  unfold compiledGrammarPresentationBound

  calc
    H.compiledGrammarPresentationItemCount ≤
        H.compiledGrammarScale +
          H.compiledGrammarScale ^ 2 :=
      h
    _ ≤
        (H.compiledGrammarScale + 1) ^ 2 := by
      ring_nf
      omega

/-- Expanded structural form of the presentation-item bound. -/
theorem compiledGrammarPresentationItemCount_le_structuralSquare :
    H.compiledGrammarPresentationItemCount ≤
      (K.card + 3 * H.ruleCount + 3) ^ 2 := by

  simpa [
    CorrectedConcreteFiniteHypothesis.compiledGrammarPresentationBound,
    CorrectedConcreteFiniteHypothesis.compiledGrammarScale,
    Nat.add_assoc
  ] using
    H.compiledGrammarPresentationItemCount_le_bound

end CorrectedConcreteFiniteHypothesis

end PresentationItemCount


section ActualGrammarPresentationCount

variable {α : Type u}
variable {M : Type v} [Monoid M]
variable {K : Finset (Word α)}
variable {obs : α → M}
variable {f : Nat}

/-- Top-level item count read directly from the actual compiled grammar:
explicit nonterminal enumeration plus all three rule lists. -/
def CorrectedConcreteFiniteHypothesis.toCutWorkingMCFGPresentationItemCount
    (H :
      CorrectedConcreteFiniteHypothesis
        K obs f)
    (dummy : α) :
    Nat :=
  H.compiledGrammarNonterminals.length +
    (H.toCutWorkingMCFG dummy).startRules.length +
    (H.toCutWorkingMCFG dummy).terminalRules.length +
    (H.toCutWorkingMCFG dummy).binaryRules.length

namespace CorrectedConcreteFiniteHypothesis

variable
  (H :
    CorrectedConcreteFiniteHypothesis
      K obs f)

/-- The directly read grammar count equals the abstract finite-presentation
item count. -/
theorem toCutWorkingMCFGPresentationItemCount_eq
    (dummy : α) :
    H.toCutWorkingMCFGPresentationItemCount
        dummy =
      H.compiledGrammarPresentationItemCount := by

  unfold
    toCutWorkingMCFGPresentationItemCount
    compiledGrammarPresentationItemCount
    compiledGrammarNonterminalCount

  rw [
    H.toCutWorkingMCFG_totalRuleCount_eq
  ]

/-- The directly read actual grammar presentation satisfies the structural
square bound. -/
theorem toCutWorkingMCFGPresentationItemCount_le_structuralSquare
    (dummy : α) :
    H.toCutWorkingMCFGPresentationItemCount
        dummy ≤
      (K.card + 3 * H.ruleCount + 3) ^ 2 := by

  rw [
    H.toCutWorkingMCFGPresentationItemCount_eq
  ]

  exact
    H.compiledGrammarPresentationItemCount_le_structuralSquare

end CorrectedConcreteFiniteHypothesis

end ActualGrammarPresentationCount


section PaperFacingPresentationBound

variable {α : Type u}
variable {M : Type v} [Monoid M]

/-- Paper-facing bound for the number of nonterminal and rule entries in the
compiled grammar presentation. -/
def correctedConcreteCompiledGrammarPresentationItemBound
    (sampleLength f : Nat) :
    Nat :=
  (sampleLength +
      3 *
        correctedLearnerPaperRuleCountBound
          sampleLength f +
      4) ^ 2

/-- The canonical finite learner object satisfies the paper-facing complete
presentation-item bound. -/
theorem correctedConcreteFiniteHypothesis_presentationItemCount_le_paperBound
    (K : Finset (Word α))
    (obs : α → M)
    (f : Nat) :
    (correctedConcreteFiniteHypothesis
        K obs f).compiledGrammarPresentationItemCount ≤
      correctedConcreteCompiledGrammarPresentationItemBound
        (sampleLengthBudget K) f := by

  let H :=
    correctedConcreteFiniteHypothesis
      K obs f

  let sourceBound :=
    correctedLearnerPaperRuleCountBound
      (sampleLengthBudget K) f

  have hstructural :
      H.compiledGrammarPresentationItemCount ≤
        (K.card + 3 * H.ruleCount + 3) ^ 2 := by
    exact
      H.compiledGrammarPresentationItemCount_le_structuralSquare

  have hsample :
      K.card ≤
        sampleLengthBudget K + 1 :=
    card_sample_le_lengthBudget_add_one
      K

  have hsource :
      H.ruleCount ≤
        sourceBound := by
    dsimp [H, sourceBound]
    exact
      correctedConcreteFiniteHypothesis_ruleCount_le_paperBound
        K obs f

  have hscale :
      K.card + 3 * H.ruleCount + 3 ≤
        sampleLengthBudget K +
          3 * sourceBound + 4 := by
    omega

  calc
    H.compiledGrammarPresentationItemCount ≤
        (K.card + 3 * H.ruleCount + 3) ^ 2 :=
      hstructural
    _ ≤
        (sampleLengthBudget K +
            3 * sourceBound + 4) ^ 2 :=
      Nat.pow_le_pow_left
        hscale 2
    _ =
        correctedConcreteCompiledGrammarPresentationItemBound
          (sampleLengthBudget K) f := by
      rfl

/-- Fully expanded complete-presentation item-count bound. -/
theorem correctedConcreteFiniteHypothesis_presentationItemCount_le_explicit
    (K : Finset (Word α))
    (obs : α → M)
    (f : Nat) :
    (correctedConcreteFiniteHypothesis
        K obs f).compiledGrammarPresentationItemCount ≤
      (sampleLengthBudget K +
          3 *
            ((4 *
                (sampleLengthBudget K +
                  f + 1)) ^
              (64 *
                (sampleLengthBudget K +
                  f + 1) *
                (sampleLengthBudget K +
                  f + 1))) +
          4) ^ 2 := by

  simpa [
    correctedConcreteCompiledGrammarPresentationItemBound,
    correctedLearnerPaperRuleCountBound,
    correctedLearnerPaperBase,
    correctedLearnerPaperExponent,
    correctedLearnerPaperScale
  ] using
    correctedConcreteFiniteHypothesis_presentationItemCount_le_paperBound
      K obs f

end PaperFacingPresentationBound


section WorkingGrammarLearnerPresentationSize

variable {α : Type u}
variable {M : Type v} [Monoid M]

/-- Number of nonterminal entries in the explicit enumeration attached to an
actual learner output. -/
def CorrectedConcreteWorkingGrammarHypothesis.nonterminalCount
    (H :
      CorrectedConcreteWorkingGrammarHypothesis
        α M obs f) :
    Nat :=
  H.rules.compiledGrammarNonterminalCount

/-- Total nonterminal-plus-rule item count attached to an actual learner
output. -/
def CorrectedConcreteWorkingGrammarHypothesis.presentationItemCount
    (H :
      CorrectedConcreteWorkingGrammarHypothesis
        α M obs f) :
    Nat :=
  H.rules.compiledGrammarPresentationItemCount

@[simp] theorem correctedConcreteWorkingGrammarLearner_nonterminalCount_eq
    (hα : Nonempty α)
    (obs : α → M)
    (f : Nat)
    (K : Finset (Word α)) :
    (correctedConcreteWorkingGrammarLearner
        hα obs f K).nonterminalCount =
      (correctedConcreteFiniteHypothesis
        K obs f).compiledGrammarNonterminalCount :=
  rfl

@[simp] theorem correctedConcreteWorkingGrammarLearner_presentationItemCount_eq
    (hα : Nonempty α)
    (obs : α → M)
    (f : Nat)
    (K : Finset (Word α)) :
    (correctedConcreteWorkingGrammarLearner
        hα obs f K).presentationItemCount =
      (correctedConcreteFiniteHypothesis
        K obs f).compiledGrammarPresentationItemCount :=
  rfl

/-- Structural nonterminal-count bound for the actual output grammar. -/
theorem correctedConcreteWorkingGrammarLearner_nonterminalCount_le
    (hα : Nonempty α)
    (obs : α → M)
    (f : Nat)
    (K : Finset (Word α)) :
    (correctedConcreteWorkingGrammarLearner
        hα obs f K).nonterminalCount ≤
      K.card +
        3 *
          (correctedConcreteWorkingGrammarLearner
            hα obs f K).sourceRuleCount +
        2 := by

  change
    (correctedConcreteFiniteHypothesis
        K obs f).compiledGrammarNonterminalCount ≤
      K.card +
        3 *
          (correctedConcreteFiniteHypothesis
            K obs f).ruleCount +
        2

  exact
    (correctedConcreteFiniteHypothesis
      K obs f).compiledGrammarNonterminalCount_le_sample_rule

/-- Paper-facing complete-presentation size bound for the actual working
grammar learner. -/
theorem correctedConcreteWorkingGrammarLearner_presentationItemCount_le_paperBound
    (hα : Nonempty α)
    (obs : α → M)
    (f : Nat)
    (K : Finset (Word α)) :
    (correctedConcreteWorkingGrammarLearner
        hα obs f K).presentationItemCount ≤
      correctedConcreteCompiledGrammarPresentationItemBound
        (sampleLengthBudget K) f := by

  rw [
    correctedConcreteWorkingGrammarLearner_presentationItemCount_eq
  ]

  exact
    correctedConcreteFiniteHypothesis_presentationItemCount_le_paperBound
      K obs f

/-- Fully expanded complete-presentation size bound for the actual working
grammar learner. -/
theorem correctedConcreteWorkingGrammarLearner_presentationItemCount_le_explicit
    (hα : Nonempty α)
    (obs : α → M)
    (f : Nat)
    (K : Finset (Word α)) :
    (correctedConcreteWorkingGrammarLearner
        hα obs f K).presentationItemCount ≤
      (sampleLengthBudget K +
          3 *
            ((4 *
                (sampleLengthBudget K +
                  f + 1)) ^
              (64 *
                (sampleLengthBudget K +
                  f + 1) *
                (sampleLengthBudget K +
                  f + 1))) +
          4) ^ 2 := by

  rw [
    correctedConcreteWorkingGrammarLearner_presentationItemCount_eq
  ]

  exact
    correctedConcreteFiniteHypothesis_presentationItemCount_le_explicit
      K obs f

/-- Prefix form of the full actual presentation-size estimate. -/
theorem correctedConcreteWorkingGrammarLearner_prefix_presentationItemCount_le
    {L : Set (Word α)}
    [DecidableEq α]
    (hα : Nonempty α)
    (obs : α → M)
    (f : Nat)
    (T : TextFor L)
    (n : Nat) :
    (correctedConcreteWorkingGrammarLearner
        hα obs f
        (T.prefixSample n)).presentationItemCount ≤
      correctedConcreteCompiledGrammarPresentationItemBound
        (sampleLengthBudget
          (T.prefixSample n))
        f := by

  exact
    correctedConcreteWorkingGrammarLearner_presentationItemCount_le_paperBound
      hα obs f
      (T.prefixSample n)

end WorkingGrammarLearnerPresentationSize


section PresentationSizeSemanticPackage

variable {α : Type u}
variable {M : Type v}
variable [Fintype M]
variable [DecidableEq α]
variable [DecidableEq M]
variable [Monoid M]
variable (hα : Nonempty α)
variable (obs : α → M)
variable (f : Nat)

/-- Final package combining actual working-grammar output, exact semantics,
Gold identification, source-rule count, compiled rule count, nonterminal
enumeration, and complete top-level presentation size. -/
theorem correctedConcreteWorkingGrammarLearner_presentationSize_semantic_package :
    IdentifiesClassFromPositiveData
        (correctedConcreteWorkingGrammarHypLanguage
          obs f)
        (correctedConcreteWorkingGrammarLearner
          hα obs f)
        (StartRootedCorrectedConcreteTargetClass
          (v := w) α M obs f) ∧
      (∀ K : Finset (Word α),
        (correctedConcreteWorkingGrammarLearner
            hα obs f K).grammar.StringLanguage =
          CorrectedConcreteCanonicalLearnerLanguage
            K obs f) ∧
      (∀ K : Finset (Word α),
        (correctedConcreteWorkingGrammarLearner
            hα obs f K).sourceRuleCount ≤
          correctedLearnerPaperRuleCountBound
            (sampleLengthBudget K) f) ∧
      (∀ K : Finset (Word α),
        (correctedConcreteWorkingGrammarLearner
            hα obs f K).grammarRuleCount ≤
          correctedConcreteCompiledGrammarRuleCountBound
            (sampleLengthBudget K) f) ∧
      (∀ K : Finset (Word α),
        (correctedConcreteWorkingGrammarLearner
            hα obs f K).presentationItemCount ≤
          correctedConcreteCompiledGrammarPresentationItemBound
            (sampleLengthBudget K) f) := by

  exact
    ⟨correctedConcreteWorkingGrammarLearner_identifies_startRootedTargetClass
        (v := w) hα obs f,
      correctedConcreteWorkingGrammarLearner_stringLanguage_eq_corrected
        hα obs f,
      fun K =>
        correctedConcreteFiniteHypothesis_ruleCount_le_paperBound
          K obs f,
      correctedConcreteWorkingGrammarLearner_grammarRuleCount_le_paperBound
        hα obs f,
      correctedConcreteWorkingGrammarLearner_presentationItemCount_le_paperBound
        hα obs f⟩

/-- Selected-stage complete-presentation package. -/
theorem correctedConcreteWorkingGrammarLearner_selectedStage_presentationSize_package :
    ∀ L : Set (Word α),
      L ∈ StartRootedCorrectedConcreteTargetClass
          (v := w) α M obs f →
      ∀ T : TextFor L,
        ∃ n0 : Nat,
          ∀ n : Nat, n0 ≤ n →
            (correctedConcreteWorkingGrammarLearner
                hα obs f
                (T.prefixSample n)).grammar.StringLanguage =
              L ∧
            (correctedConcreteWorkingGrammarLearner
                hα obs f
                (T.prefixSample n)).presentationItemCount ≤
              correctedConcreteCompiledGrammarPresentationItemBound
                (sampleLengthBudget
                  (T.prefixSample n))
                f := by

  intro L hL T

  refine
    ⟨startRootedCorrectedConcreteTargetCoverageStage
        (v := w) obs f hL T,
      ?_⟩

  intro n hn

  exact
    ⟨correctedConcreteWorkingGrammarLearner_correct_after_startRootedCoverageStage
        (v := w) hα obs f hL T hn,
      correctedConcreteWorkingGrammarLearner_prefix_presentationItemCount_le
        hα obs f T n⟩

end PresentationSizeSemanticPackage

end MCFG
