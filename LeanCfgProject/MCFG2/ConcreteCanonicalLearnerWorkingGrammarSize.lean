/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG.ConcreteCanonicalLearnerWorkingGrammarIdentification

/-!
# ConcreteCanonicalLearnerWorkingGrammarSize.lean

The actual compiled learner now returns a finite `WorkingMCFG`.  This file
counts the rules stored by that grammar.

For a finite learner object `H`, write

```lean
R = H.ruleCount.
```

The cut compiler uses:

* `K.card` start rules;
* one seed terminal rule;
* one constant rule for each control code;
* one lifted rule for each corrected binary rule;
* one saturation rule for each admissible cut pair.

The finite control set contains sample singleton codes, two codes for each
unit rule, and three codes for each binary rule.  Hence

```lean
H.controlCodes.card ≤ K.card + 3 * R.
```

The cut-pair set is a filtered subset of the square of the control set, so

```lean
H.cutPairs.card ≤ H.controlCodes.card ^ 2.
```

Combining these estimates gives the compact structural bound

```lean
compiled grammar rule count ≤
  (K.card + 3 * H.ruleCount + 2) ^ 2.
```

For the canonical hypothesis, the previously verified source-rule estimate is
then substituted.  The final explicit theorem is

```lean
correctedConcreteWorkingGrammarLearner_grammarRuleCount_le_explicit.
```

Its bound depends only on total sample length and the fixed fan-out parameter.

The count in this file is the actual list length stored in the compiled
`WorkingMCFG`, including the auxiliary seed, constant, and saturation rules.
It is therefore distinct from the earlier source finite-object rule count.

No target grammar occurs in the bound.
No `sorry`, `admit`, or `axiom` is used.
-/

namespace MCFG

universe u v w

section FinsetCardinalityHelpers

variable {β : Type u}

/-- The cardinality of a union of six finite sets is bounded by the sum of
their cardinalities. -/
theorem card_union_six_le
    [DecidableEq β]
    (A B C D E F : Finset β) :
    (((((A ∪ B) ∪ C) ∪ D) ∪ E) ∪ F).card ≤
      A.card + B.card + C.card +
        D.card + E.card + F.card := by

  calc
    (((((A ∪ B) ∪ C) ∪ D) ∪ E) ∪ F).card ≤
        ((((A ∪ B) ∪ C) ∪ D) ∪ E).card +
          F.card :=
      Finset.card_union_le _ _
    _ ≤
        (((A ∪ B) ∪ C) ∪ D).card +
          E.card + F.card := by
      exact
        Nat.add_le_add_right
          (Finset.card_union_le _ _)
          F.card
    _ ≤
        ((A ∪ B) ∪ C).card +
          D.card + E.card + F.card := by
      have h :=
        Finset.card_union_le
          ((A ∪ B) ∪ C) D
      omega
    _ ≤
        (A ∪ B).card +
          C.card + D.card + E.card + F.card := by
      have h :=
        Finset.card_union_le
          (A ∪ B) C
      omega
    _ ≤
        A.card + B.card +
          C.card + D.card + E.card + F.card := by
      have h :=
        Finset.card_union_le A B
      omega

end FinsetCardinalityHelpers


section SampleCardinality

variable {α : Type u}

/-- A finite set of words has cardinality at most its total length plus the
possible exceptional empty word. -/
theorem card_sample_le_lengthBudget_add_emptyIndicator
    (K : Finset (Word α)) :
    K.card ≤
      sampleLengthBudget K +
        (if ([] : Word α) ∈ K then 1 else 0) := by
  classical

  induction K using Finset.induction_on with

  | empty =>
      simp [sampleLengthBudget]

  | @insert word K hword ih =>
      rw [
        Finset.card_insert_of_not_mem hword
      ]

      simp only [sampleLengthBudget] at ih ⊢

      rw [
        Finset.sum_insert hword
      ]

      by_cases hw : word = []

      · subst word

        simp [hword] at ih ⊢

        omega

      · have hlength :
            1 ≤ word.length := by
          cases word with

          | nil =>
              simp at hw

          | cons a rest =>
              simp

        by_cases hempty :
          ([] : Word α) ∈ K

        · simp [hw, hempty] at ih ⊢
          omega

        · simp [hw, hempty] at ih ⊢
          omega

/-- Simpler sample-cardinality estimate used by the paper-facing grammar-size
bound. -/
theorem card_sample_le_lengthBudget_add_one
    (K : Finset (Word α)) :
    K.card ≤
      sampleLengthBudget K + 1 := by
  classical

  have h :=
    card_sample_le_lengthBudget_add_emptyIndicator
      K

  by_cases hempty :
    ([] : Word α) ∈ K

  · simp [hempty] at h
    exact h

  · simp [hempty] at h
    omega

end SampleCardinality


section ControlCodeCardinality

variable {α : Type u}
variable {M : Type v} [Monoid M]
variable {K : Finset (Word α)}
variable {obs : α → M}
variable {f : Nat}

/-- Raw componentwise cardinality estimate for the finite control set. -/
theorem CorrectedConcreteFiniteHypothesis.controlCodes_card_le_components
    (H :
      CorrectedConcreteFiniteHypothesis
        K obs f) :
    H.controlCodes.card ≤
      K.card +
        2 * H.unitRuleCodes.card +
        3 * H.binaryRuleCodes.card := by
  classical

  have hunion :
      H.controlCodes.card ≤
        (K.image
            FiniteObjectTupleCode.ofWord).card +
          (H.unitRuleCodes.image
              CorrectedConcreteUnitRuleCode.sourceCode).card +
          (H.unitRuleCodes.image
              CorrectedConcreteUnitRuleCode.targetCode).card +
          (H.binaryRuleCodes.image
              CorrectedConcreteBinaryRuleCode.sourceCode).card +
          (H.binaryRuleCodes.image
              CorrectedConcreteBinaryRuleCode.leftSourceCode).card +
          (H.binaryRuleCodes.image
              CorrectedConcreteBinaryRuleCode.rightSourceCode).card := by

    unfold
      CorrectedConcreteFiniteHypothesis.controlCodes

    exact
      card_union_six_le
        (K.image
          FiniteObjectTupleCode.ofWord)
        (H.unitRuleCodes.image
          CorrectedConcreteUnitRuleCode.sourceCode)
        (H.unitRuleCodes.image
          CorrectedConcreteUnitRuleCode.targetCode)
        (H.binaryRuleCodes.image
          CorrectedConcreteBinaryRuleCode.sourceCode)
        (H.binaryRuleCodes.image
          CorrectedConcreteBinaryRuleCode.leftSourceCode)
        (H.binaryRuleCodes.image
          CorrectedConcreteBinaryRuleCode.rightSourceCode)

  have hword :
      (K.image
        FiniteObjectTupleCode.ofWord).card ≤
          K.card :=
    Finset.card_image_le

  have hunitSource :
      (H.unitRuleCodes.image
        CorrectedConcreteUnitRuleCode.sourceCode).card ≤
          H.unitRuleCodes.card :=
    Finset.card_image_le

  have hunitTarget :
      (H.unitRuleCodes.image
        CorrectedConcreteUnitRuleCode.targetCode).card ≤
          H.unitRuleCodes.card :=
    Finset.card_image_le

  have hbinarySource :
      (H.binaryRuleCodes.image
        CorrectedConcreteBinaryRuleCode.sourceCode).card ≤
          H.binaryRuleCodes.card :=
    Finset.card_image_le

  have hbinaryLeft :
      (H.binaryRuleCodes.image
        CorrectedConcreteBinaryRuleCode.leftSourceCode).card ≤
          H.binaryRuleCodes.card :=
    Finset.card_image_le

  have hbinaryRight :
      (H.binaryRuleCodes.image
        CorrectedConcreteBinaryRuleCode.rightSourceCode).card ≤
          H.binaryRuleCodes.card :=
    Finset.card_image_le

  omega

/-- The control-set cardinality is bounded by the sample size plus three times
the total finite-object rule count. -/
theorem CorrectedConcreteFiniteHypothesis.controlCodes_card_le_sample_add_three_ruleCount
    (H :
      CorrectedConcreteFiniteHypothesis
        K obs f) :
    H.controlCodes.card ≤
      K.card + 3 * H.ruleCount := by

  have h :=
    H.controlCodes_card_le_components

  unfold
    CorrectedConcreteFiniteHypothesis.ruleCount

  omega

end ControlCodeCardinality


section CutPairCardinality

variable {α : Type u}
variable {M : Type v} [Monoid M]
variable {K : Finset (Word α)}
variable {obs : α → M}
variable {f : Nat}

/-- The finite cut saturation is a filtered subset of the square of the
control-code set. -/
theorem CorrectedConcreteFiniteHypothesis.cutPairs_card_le_controlCodes_square
    (H :
      CorrectedConcreteFiniteHypothesis
        K obs f) :
    H.cutPairs.card ≤
      H.controlCodes.card *
        H.controlCodes.card := by
  classical

  unfold
    CorrectedConcreteFiniteHypothesis.cutPairs

  calc
    ((H.controlCodes.product
        H.controlCodes).filter
          (fun p =>
            H.CutAdmissible p.1 p.2)).card ≤
        (H.controlCodes.product
          H.controlCodes).card :=
      Finset.card_le_card
        (Finset.filter_subset _ _)
    _ =
        H.controlCodes.card *
          H.controlCodes.card := by
      simp

/-- Cut saturation is bounded by the square of the sample-plus-rule control
bound. -/
theorem CorrectedConcreteFiniteHypothesis.cutPairs_card_le_sample_rule_square
    (H :
      CorrectedConcreteFiniteHypothesis
        K obs f) :
    H.cutPairs.card ≤
      (K.card + 3 * H.ruleCount) *
        (K.card + 3 * H.ruleCount) := by

  calc
    H.cutPairs.card ≤
        H.controlCodes.card *
          H.controlCodes.card :=
      H.cutPairs_card_le_controlCodes_square
    _ ≤
        (K.card + 3 * H.ruleCount) *
          (K.card + 3 * H.ruleCount) :=
      Nat.mul_le_mul
        H.controlCodes_card_le_sample_add_three_ruleCount
        H.controlCodes_card_le_sample_add_three_ruleCount

end CutPairCardinality


section ExactCompiledGrammarCounts

variable {α : Type u}
variable {M : Type v} [Monoid M]
variable {K : Finset (Word α)}
variable {obs : α → M}
variable {f : Nat}

/-- Exact number of start rules in the cut-saturated grammar. -/
@[simp] theorem CorrectedConcreteFiniteHypothesis.toCutWorkingMCFG_startRules_length
    (H :
      CorrectedConcreteFiniteHypothesis
        K obs f)
    (dummy : α) :
    (H.toCutWorkingMCFG
      dummy).startRules.length =
        K.card := by

  simp [
    CorrectedConcreteFiniteHypothesis.toCutWorkingMCFG
  ]

/-- Exact number of terminal rules in the cut-saturated grammar. -/
@[simp] theorem CorrectedConcreteFiniteHypothesis.toCutWorkingMCFG_terminalRules_length
    (H :
      CorrectedConcreteFiniteHypothesis
        K obs f)
    (dummy : α) :
    (H.toCutWorkingMCFG
      dummy).terminalRules.length =
        1 := by

  simp [
    CorrectedConcreteFiniteHypothesis.toCutWorkingMCFG
  ]

/-- Exact number of binary rules in the cut-saturated grammar. -/
@[simp] theorem CorrectedConcreteFiniteHypothesis.toCutWorkingMCFG_binaryRules_length
    (H :
      CorrectedConcreteFiniteHypothesis
        K obs f)
    (dummy : α) :
    (H.toCutWorkingMCFG
      dummy).binaryRules.length =
        H.controlCodes.card +
          H.binaryRuleCodes.card +
          H.cutPairs.card := by

  simp [
    CorrectedConcreteFiniteHypothesis.toCutWorkingMCFG,
    List.length_append,
    Nat.add_assoc
  ]

/-- Exact total rule count of the concrete compiled grammar, expressed through
the finite control and cut-saturation sets. -/
def CorrectedConcreteFiniteHypothesis.compiledGrammarRuleCount
    (H :
      CorrectedConcreteFiniteHypothesis
        K obs f) :
    Nat :=
  K.card + 1 +
    (H.controlCodes.card +
      H.binaryRuleCodes.card +
      H.cutPairs.card)

/-- Exact list-length identity for the concrete compiled grammar. -/
theorem CorrectedConcreteFiniteHypothesis.toCutWorkingMCFG_totalRuleCount_eq
    (H :
      CorrectedConcreteFiniteHypothesis
        K obs f)
    (dummy : α) :
    (H.toCutWorkingMCFG
        dummy).startRules.length +
      (H.toCutWorkingMCFG
        dummy).terminalRules.length +
      (H.toCutWorkingMCFG
        dummy).binaryRules.length =
      H.compiledGrammarRuleCount := by

  unfold
    CorrectedConcreteFiniteHypothesis.compiledGrammarRuleCount

  rw [
    H.toCutWorkingMCFG_startRules_length,
    H.toCutWorkingMCFG_terminalRules_length,
    H.toCutWorkingMCFG_binaryRules_length
  ]

end ExactCompiledGrammarCounts


section StructuralCompiledGrammarBound

variable {α : Type u}
variable {M : Type v} [Monoid M]
variable {K : Finset (Word α)}
variable {obs : α → M}
variable {f : Nat}

/-- Natural scale controlling all auxiliary rules introduced by the
cut-saturation compiler. -/
def CorrectedConcreteFiniteHypothesis.compiledGrammarScale
    (H :
      CorrectedConcreteFiniteHypothesis
        K obs f) :
    Nat :=
  K.card + 3 * H.ruleCount + 2

/-- Structural quadratic rule-count bound for the concrete compiled grammar. -/
def CorrectedConcreteFiniteHypothesis.compiledGrammarQuadraticBound
    (H :
      CorrectedConcreteFiniteHypothesis
        K obs f) :
    Nat :=
  H.compiledGrammarScale ^ 2

/-- The exact compiled grammar rule count is bounded quadratically in the
sample size and the source finite-object rule count. -/
theorem CorrectedConcreteFiniteHypothesis.compiledGrammarRuleCount_le_quadratic
    (H :
      CorrectedConcreteFiniteHypothesis
        K obs f) :
    H.compiledGrammarRuleCount ≤
      H.compiledGrammarQuadraticBound := by

  let N :=
    K.card

  let R :=
    H.ruleCount

  let C :=
    H.controlCodes.card

  let B :=
    H.binaryRuleCodes.card

  let Q :=
    H.cutPairs.card

  let T :=
    N + 3 * R

  have hC :
      C ≤ T := by
    dsimp [C, T, N, R]
    exact
      H.controlCodes_card_le_sample_add_three_ruleCount

  have hB :
      B ≤ R := by
    dsimp [B, R]
    unfold
      CorrectedConcreteFiniteHypothesis.ruleCount
    omega

  have hQ0 :
      Q ≤ C * C := by
    dsimp [Q, C]
    exact
      H.cutPairs_card_le_controlCodes_square

  have hQ :
      Q ≤ T * T :=
    hQ0.trans
      (Nat.mul_le_mul hC hC)

  have hlinear :
      N + 1 + T + R ≤
        4 * T + 4 := by
    dsimp [T]
    omega

  unfold
    CorrectedConcreteFiniteHypothesis.compiledGrammarRuleCount
    CorrectedConcreteFiniteHypothesis.compiledGrammarQuadraticBound
    CorrectedConcreteFiniteHypothesis.compiledGrammarScale

  change
    N + 1 + (C + B + Q) ≤
      (N + 3 * R + 2) ^ 2

  calc
    N + 1 + (C + B + Q) ≤
        N + 1 + (T + R + T * T) := by
      omega
    _ =
        T * T +
          (N + 1 + T + R) := by
      ring
    _ ≤
        T * T +
          (4 * T + 4) :=
      Nat.add_le_add_left
        hlinear
        (T * T)
    _ =
        (N + 3 * R + 2) ^ 2 := by
      dsimp [T]
      ring

/-- The actual list length of every compiled grammar satisfies the structural
quadratic bound. -/
theorem CorrectedConcreteFiniteHypothesis.toCutWorkingMCFG_totalRuleCount_le_quadratic
    (H :
      CorrectedConcreteFiniteHypothesis
        K obs f)
    (dummy : α) :
    (H.toCutWorkingMCFG
        dummy).startRules.length +
      (H.toCutWorkingMCFG
        dummy).terminalRules.length +
      (H.toCutWorkingMCFG
        dummy).binaryRules.length ≤
      H.compiledGrammarQuadraticBound := by

  rw [
    H.toCutWorkingMCFG_totalRuleCount_eq
  ]

  exact
    H.compiledGrammarRuleCount_le_quadratic

end StructuralCompiledGrammarBound


section PaperFacingCompiledGrammarBound

variable {α : Type u}
variable {M : Type v} [Monoid M]

/-- Explicit grammar-rule bound obtained by substituting the previously proved
source finite-object bound into the structural quadratic compiler bound. -/
def correctedConcreteCompiledGrammarRuleCountBound
    (sampleLength f : Nat) :
    Nat :=
  (sampleLength +
      3 *
        correctedLearnerPaperRuleCountBound
          sampleLength f +
      3) ^ 2

/-- The canonical finite hypothesis satisfies the paper-facing compiled
grammar rule-count bound. -/
theorem correctedConcreteFiniteHypothesis_compiledGrammarRuleCount_le_paperBound
    (K : Finset (Word α))
    (obs : α → M)
    (f : Nat) :
    (correctedConcreteFiniteHypothesis
        K obs f).compiledGrammarRuleCount ≤
      correctedConcreteCompiledGrammarRuleCountBound
        (sampleLengthBudget K) f := by

  let H :=
    correctedConcreteFiniteHypothesis
      K obs f

  let sourceBound :=
    correctedLearnerPaperRuleCountBound
      (sampleLengthBudget K) f

  have hquadratic :
      H.compiledGrammarRuleCount ≤
        (K.card + 3 * H.ruleCount + 2) ^ 2 := by
    simpa [
      CorrectedConcreteFiniteHypothesis.compiledGrammarQuadraticBound,
      CorrectedConcreteFiniteHypothesis.compiledGrammarScale
    ] using
      H.compiledGrammarRuleCount_le_quadratic

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
      K.card + 3 * H.ruleCount + 2 ≤
        sampleLengthBudget K +
          3 * sourceBound + 3 := by
    omega

  calc
    H.compiledGrammarRuleCount ≤
        (K.card + 3 * H.ruleCount + 2) ^ 2 :=
      hquadratic
    _ ≤
        (sampleLengthBudget K +
            3 * sourceBound + 3) ^ 2 :=
      Nat.pow_le_pow_left
        hscale 2
    _ =
        correctedConcreteCompiledGrammarRuleCountBound
          (sampleLengthBudget K) f := by
      rfl

/-- Fully expanded paper-facing bound for the canonical compiled grammar. -/
theorem correctedConcreteFiniteHypothesis_compiledGrammarRuleCount_le_explicit
    (K : Finset (Word α))
    (obs : α → M)
    (f : Nat) :
    (correctedConcreteFiniteHypothesis
        K obs f).compiledGrammarRuleCount ≤
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
          3) ^ 2 := by

  simpa [
    correctedConcreteCompiledGrammarRuleCountBound,
    correctedLearnerPaperRuleCountBound,
    correctedLearnerPaperBase,
    correctedLearnerPaperExponent,
    correctedLearnerPaperScale
  ] using
    correctedConcreteFiniteHypothesis_compiledGrammarRuleCount_le_paperBound
      K obs f

end PaperFacingCompiledGrammarBound


section WorkingGrammarLearnerCounts

variable {α : Type u}
variable {M : Type v} [Monoid M]

/-- Exact connection between the learner-output `grammarRuleCount` field and
the compiler's finite combinatorial count. -/
@[simp] theorem correctedConcreteWorkingGrammarLearner_grammarRuleCount_eq
    (hα : Nonempty α)
    (obs : α → M)
    (f : Nat)
    (K : Finset (Word α)) :
    (correctedConcreteWorkingGrammarLearner
        hα obs f K).grammarRuleCount =
      (correctedConcreteFiniteHypothesis
        K obs f).compiledGrammarRuleCount := by

  change
    ((correctedConcreteFiniteHypothesis
        K obs f).toCutWorkingMCFG
          (Classical.choice hα)).startRules.length +
      ((correctedConcreteFiniteHypothesis
        K obs f).toCutWorkingMCFG
          (Classical.choice hα)).terminalRules.length +
      ((correctedConcreteFiniteHypothesis
        K obs f).toCutWorkingMCFG
          (Classical.choice hα)).binaryRules.length =
      (correctedConcreteFiniteHypothesis
        K obs f).compiledGrammarRuleCount

  exact
    CorrectedConcreteFiniteHypothesis.toCutWorkingMCFG_totalRuleCount_eq
      (correctedConcreteFiniteHypothesis
        K obs f)
      (Classical.choice hα)

/-- Structural quadratic count for the actual `WorkingMCFG` returned by the
learner. -/
theorem correctedConcreteWorkingGrammarLearner_grammarRuleCount_le_quadratic
    (hα : Nonempty α)
    (obs : α → M)
    (f : Nat)
    (K : Finset (Word α)) :
    (correctedConcreteWorkingGrammarLearner
        hα obs f K).grammarRuleCount ≤
      (K.card +
          3 *
            (correctedConcreteWorkingGrammarLearner
              hα obs f K).sourceRuleCount +
          2) ^ 2 := by

  rw [
    correctedConcreteWorkingGrammarLearner_grammarRuleCount_eq
  ]

  change
    (correctedConcreteFiniteHypothesis
        K obs f).compiledGrammarRuleCount ≤
      (K.card +
          3 *
            (correctedConcreteFiniteHypothesis
              K obs f).ruleCount +
          2) ^ 2

  simpa [
    CorrectedConcreteFiniteHypothesis.compiledGrammarQuadraticBound,
    CorrectedConcreteFiniteHypothesis.compiledGrammarScale
  ] using
    (correctedConcreteFiniteHypothesis
      K obs f).compiledGrammarRuleCount_le_quadratic

/-- Paper-facing bound for the actual grammar-rule list returned by the
learner. -/
theorem correctedConcreteWorkingGrammarLearner_grammarRuleCount_le_paperBound
    (hα : Nonempty α)
    (obs : α → M)
    (f : Nat)
    (K : Finset (Word α)) :
    (correctedConcreteWorkingGrammarLearner
        hα obs f K).grammarRuleCount ≤
      correctedConcreteCompiledGrammarRuleCountBound
        (sampleLengthBudget K) f := by

  rw [
    correctedConcreteWorkingGrammarLearner_grammarRuleCount_eq
  ]

  exact
    correctedConcreteFiniteHypothesis_compiledGrammarRuleCount_le_paperBound
      K obs f

/-- Fully expanded rule-count bound for the actual compiled `WorkingMCFG`
returned by the learner. -/
theorem correctedConcreteWorkingGrammarLearner_grammarRuleCount_le_explicit
    (hα : Nonempty α)
    (obs : α → M)
    (f : Nat)
    (K : Finset (Word α)) :
    (correctedConcreteWorkingGrammarLearner
        hα obs f K).grammarRuleCount ≤
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
          3) ^ 2 := by

  rw [
    correctedConcreteWorkingGrammarLearner_grammarRuleCount_eq
  ]

  exact
    correctedConcreteFiniteHypothesis_compiledGrammarRuleCount_le_explicit
      K obs f

/-- Prefix form of the actual compiled grammar-size theorem. -/
theorem correctedConcreteWorkingGrammarLearner_prefix_grammarRuleCount_le
    {L : Set (Word α)}
    [DecidableEq α]
    (hα : Nonempty α)
    (obs : α → M)
    (f : Nat)
    (T : TextFor L)
    (n : Nat) :
    (correctedConcreteWorkingGrammarLearner
        hα obs f
        (T.prefixSample n)).grammarRuleCount ≤
      correctedConcreteCompiledGrammarRuleCountBound
        (sampleLengthBudget
          (T.prefixSample n))
        f := by

  exact
    correctedConcreteWorkingGrammarLearner_grammarRuleCount_le_paperBound
      hα obs f
      (T.prefixSample n)

end WorkingGrammarLearnerCounts


section WorkingGrammarSizeSemanticPackage

variable {α : Type u}
variable {M : Type v}
variable [Fintype M]
variable [DecidableEq α]
variable [DecidableEq M]
variable [Monoid M]
variable (hα : Nonempty α)
variable (obs : α → M)
variable (f : Nat)

/-- Final package combining actual grammar output, exact language semantics,
Gold identification, and bounds for both the source finite rule object and the
compiled grammar rule lists. -/
theorem correctedConcreteWorkingGrammarLearner_size_semantic_package :
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
        hα obs f⟩

/-- Selected-stage package: after the characteristic-sample coverage stage,
the actual output grammar is exact and both source and compiled grammar counts
satisfy their verified bounds. -/
theorem correctedConcreteWorkingGrammarLearner_selectedStage_size_package :
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
                (T.prefixSample n)).sourceRuleCount ≤
              correctedLearnerPaperRuleCountBound
                (sampleLengthBudget
                  (T.prefixSample n))
                f ∧
            (correctedConcreteWorkingGrammarLearner
                hα obs f
                (T.prefixSample n)).grammarRuleCount ≤
              correctedConcreteCompiledGrammarRuleCountBound
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
      correctedConcreteFiniteHypothesis_ruleCount_le_paperBound
        (T.prefixSample n) obs f,
      correctedConcreteWorkingGrammarLearner_prefix_grammarRuleCount_le
        hα obs f T n⟩

end WorkingGrammarSizeSemanticPackage

end MCFG
