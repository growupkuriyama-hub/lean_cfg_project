/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG.ConcreteCanonicalLearnerWorkingGrammarUniformNaturalFieldBound

/-!
# ConcreteCanonicalLearnerWorkingGrammarBinaryRuleFamilyBodyBounds.lean

The preceding file reduces the complete natural-field and bit-size analysis to
one compiler-specific quantity:

```lean
H.compiledWorkingGrammarMaximumBinaryRuleBodyTokenCount dummy.
```

This file evaluates that quantity from the finite sample length and the fixed
fan-out bound.

The cut-compiled grammar has exactly three binary-rule families.

## Constant control rules

A constant control rule has one output component for every component of its
stored control tuple.  Every control tuple component occurs inside a sample
word, hence its length is at most

```lean
sampleLengthBudget K.
```

The control arity is at most `max 1 f`.  Therefore its framed body has at most

```text
max 1 f + (max 1 f) * sampleLengthBudget K
```

tokens.

## Lifted sample binary rules

A lifted rule has parent, left, and right arities at most `f`.  Exact-once
linearity gives, componentwise,

```text
template component length
  ≤ evaluated parent component length + left arity + right arity.
```

The evaluated parent component occurs inside a sample word, so its length is at
most `sampleLengthBudget K`.  Consequently its framed body has at most

```text
max 1 f
  + (max 1 f) *
      (sampleLengthBudget K + 2 * max 1 f)
```

tokens.

## Saturated cut rules

A saturation rule is a left-identity template.  Every output component consists
of exactly one left-variable atom.  Its framed body therefore has at most

```text
2 * max 1 f
```

tokens.

A single deliberately roomy common bound is

```lean
compiledWorkingGrammarBinaryRuleBodyTokenCountSampleFanoutBound K f
```

defined as

```text
2 * max 1 f
  + (max 1 f) *
      (sampleLengthBudget K + 2 * max 1 f).
```

We prove that every stored binary rule satisfies this bound and hence

```lean
H.compiledWorkingGrammarMaximumBinaryRuleBodyTokenCount dummy
  ≤
compiledWorkingGrammarBinaryRuleBodyTokenCountSampleFanoutBound K f.
```

After this file the maximum stored body-token count is no longer an independent
quantity.  The next layer can substitute this sample/fan-out expression into
the uniform natural-field and logarithmic bit-size bounds.

No target grammar is supplied to the learner.
No `sorry`, `admit`, or `axiom` is used.
-/

namespace MCFG

universe u v

section FiniteListSumBounds

/-- If every element of a finite natural list is at most `bound`, then its sum
is at most its length times `bound`. -/
theorem list_sum_le_length_mul_of_forall_mem_le :
    ∀
      (values : List Nat)
      (bound : Nat),
      (∀ n ∈ values, n <= bound) →
        values.sum <= values.length * bound

  | [], bound, hall => by
      simp

  | value :: values, bound, hall => by
      have hhead :
          value <= bound :=
        hall value (by simp)

      have htail :
          ∀ n ∈ values,
            n <= bound := by
        intro n hn
        exact
          hall n (by simp [hn])

      have ih :
          values.sum <= values.length * bound :=
        list_sum_le_length_mul_of_forall_mem_le
          values bound htail

      calc
        (value :: values).sum =
            value + values.sum := by
              simp
        _ <=
            bound + values.length * bound :=
          Nat.add_le_add hhead ih
        _ =
            (value :: values).length * bound := by
          simp [
            Nat.succ_mul,
            Nat.add_comm,
            Nat.add_left_comm,
            Nat.add_assoc
          ]

end FiniteListSumBounds


section TemplateTupleComponentSumBounds

variable {α : Type u}

/-- A componentwise template-word length bound gives a total component-length
sum bound. -/
theorem templateTuple_componentLengthSum_le
    {e dB dC : Nat}
    (body : TemplateTuple α e dB dC)
    (bound : Nat)
    (hcomponent :
      ∀ i : Fin e,
        (body i).length <= bound) :
    ((List.ofFn body).map List.length).sum <=
      e * bound := by

  apply
    list_sum_le_length_mul_of_forall_mem_le
      ((List.ofFn body).map List.length)
      bound

  intro length hlength

  rcases List.mem_map.mp hlength with
    ⟨word, hword, rfl⟩

  change word ∈ List.ofFn body at hword
  rw [List.mem_ofFn] at hword

  rcases hword with
    ⟨i, rfl⟩

  exact hcomponent i

/-- A componentwise tuple-word length bound gives the corresponding total tuple
length bound. -/
theorem tuple_componentLengthSum_le
    {d : Nat}
    (x : Tuple α d)
    (bound : Nat)
    (hcomponent :
      ∀ i : Fin d,
        (x i).length <= bound) :
    ((List.ofFn x).map List.length).sum <=
      d * bound := by

  exact
    templateTuple_componentLengthSum_le
      (dB := 0)
      (dC := 0)
      x
      bound
      hcomponent

end TemplateTupleComponentSumBounds


section ControlTupleSampleLengthBounds

variable {α : Type u}
variable {M : Type v} [Monoid M]
variable {K : Finset (Word α)}
variable {obs : α → M}
variable {f : Nat}

namespace CorrectedConcreteFiniteHypothesis

variable
  (H : CorrectedConcreteFiniteHypothesis K obs f)

/-- Every component of every finite control tuple has length at most the total
sample length. -/
theorem controlCode_component_length_le_sampleLengthBudget
    {X : FiniteObjectTupleCode α}
    (hX : H.IsControlCode X) :
    ∀ i : Fin X.arity,
      (X.tuple i).length <=
        sampleLengthBudget K := by

  classical

  unfold IsControlCode at hX
  unfold controlCodes at hX

  rcases Finset.mem_union.mp hX with
    hword | hrest

  · rcases Finset.mem_image.mp hword with
      ⟨word, hword, rfl⟩

    intro i

    simpa [
      FiniteObjectTupleCode.ofWord
    ] using
      sample_word_length_le_budget
        K hword

  · rcases Finset.mem_union.mp hrest with
      hunitSource | hrest

    · rcases Finset.mem_image.mp hunitSource with
        ⟨U, hU, rfl⟩

      intro i

      change
        (U.source i).length <=
          sampleLengthBudget K

      exact
        (namedFill_component_length_le
            U.rule.evidence.context
            U.source
            i).trans
          (sample_word_length_le_budget
            K
            U.rule.evidence.left_mem)

    · rcases Finset.mem_union.mp hrest with
        hunitTarget | hrest

      · rcases Finset.mem_image.mp hunitTarget with
          ⟨U, hU, rfl⟩

        intro i

        change
          (U.target i).length <=
            sampleLengthBudget K

        exact
          (namedFill_component_length_le
              U.rule.evidence.context
              U.target
              i).trans
            (sample_word_length_le_budget
              K
              U.rule.evidence.right_mem)

      · rcases Finset.mem_union.mp hrest with
          hbinarySource | hrest

        · rcases Finset.mem_image.mp hbinarySource with
            ⟨B, hB, rfl⟩

          intro i

          change
            (B.source i).length <=
              sampleLengthBudget K

          exact
            (namedFill_component_length_le
                B.rule.witness.parent.1.context
                B.rule.witness.parent.1.tuple
                i).trans
              (sample_word_length_le_budget
                K
                B.rule.witness.parent.word_mem)

        · rcases Finset.mem_union.mp hrest with
            hbinaryLeft | hbinaryRight

          · rcases Finset.mem_image.mp hbinaryLeft with
              ⟨B, hB, rfl⟩

            intro i

            change
              (B.leftSource i).length <=
                sampleLengthBudget K

            exact
              (namedFill_component_length_le
                  B.rule.witness.left.1.context
                  B.rule.witness.left.1.tuple
                  i).trans
                (sample_word_length_le_budget
                  K
                  B.rule.witness.left.word_mem)

          · rcases Finset.mem_image.mp hbinaryRight with
              ⟨B, hB, rfl⟩

            intro i

            change
              (B.rightSource i).length <=
                sampleLengthBudget K

            exact
              (namedFill_component_length_le
                  B.rule.witness.right.1.context
                  B.rule.witness.right.1.tuple
                  i).trans
                (sample_word_length_le_budget
                  K
                  B.rule.witness.right.word_mem)

/-- The total component length of every finite control tuple is at most its
arity times the total sample length. -/
theorem controlCode_componentLengthSum_le_sampleLengthBudget
    {X : FiniteObjectTupleCode α}
    (hX : H.IsControlCode X) :
    ((List.ofFn X.tuple).map List.length).sum <=
      X.arity * sampleLengthBudget K := by

  exact
    tuple_componentLengthSum_le
      X.tuple
      (sampleLengthBudget K)
      (H.controlCode_component_length_le_sampleLengthBudget
        hX)

end CorrectedConcreteFiniteHypothesis

end ControlTupleSampleLengthBounds


section SampleFanoutBodyTokenBoundDefinition

/-- Common body-token count bound for all three compiled binary-rule families. -/
def compiledWorkingGrammarBinaryRuleBodyTokenCountSampleFanoutBound
    (K : Finset (Word α))
    (f : Nat) :
    Nat :=
  let fanout := max 1 f

  2 * fanout +
    fanout *
      (sampleLengthBudget K +
        2 * fanout)

/-- The common fan-out parameter used by the body-token bound is positive. -/
theorem one_le_max_one_fanout
    (f : Nat) :
    1 <= max 1 f :=
  Nat.le_max_left 1 f

end SampleFanoutBodyTokenBoundDefinition


section ConstantRuleBodyTokenBound

variable {α : Type u}
variable {M : Type v} [Monoid M]
variable {K : Finset (Word α)}
variable {obs : α → M}
variable {f : Nat}

namespace CorrectedConcreteFiniteHypothesis

variable
  (H : CorrectedConcreteFiniteHypothesis K obs f)

/-- Every constant control rule satisfies the common sample/fan-out body-token
bound. -/
theorem cutConstantRule_bodyTokenCount_le_sampleFanoutBound
    (dummy : α)
    (X : H.controlCodes.attach) :
    (correctedConcreteCutConstantRule H X).
        framedStructuralBodyTokens.length <=
      compiledWorkingGrammarBinaryRuleBodyTokenCountSampleFanoutBound
        K f := by

  let fanout := max 1 f
  let sampleLength := sampleLengthBudget K

  have harity :
      X.1.arity <= fanout :=
    H.controlCode_arity_le_max X.2

  have hcomponent :
      ∀ i : Fin X.1.arity,
        ((constantTupleTemplate X.1.tuple) i).length <=
          sampleLength := by

    intro i

    simpa [
      constantTupleTemplate,
      terminalTemplateWord,
      sampleLength
    ] using
      H.controlCode_component_length_le_sampleLengthBudget
        X.2 i

  have hsum :
      ((List.ofFn
          (constantTupleTemplate X.1.tuple)).map
            List.length).sum <=
        X.1.arity * sampleLength :=
    templateTuple_componentLengthSum_le
      (constantTupleTemplate X.1.tuple)
      sampleLength
      hcomponent

  have hmul :
      X.1.arity * sampleLength <=
        fanout * sampleLength :=
    Nat.mul_le_mul_right
      sampleLength
      harity

  have hbasic :
      X.1.arity +
          ((List.ofFn
              (constantTupleTemplate X.1.tuple)).map
                List.length).sum <=
        fanout + fanout * sampleLength :=
    Nat.add_le_add
      harity
      (hsum.trans hmul)

  have hsample :
      fanout * sampleLength <=
        fanout *
          (sampleLength + 2 * fanout) :=
    Nat.mul_le_mul_left
      fanout
      (Nat.le_add_right
        sampleLength
        (2 * fanout))

  have hfinal :
      fanout + fanout * sampleLength <=
        2 * fanout +
          fanout *
            (sampleLength + 2 * fanout) := by

    exact
      Nat.add_le_add
        (by omega)
        hsample

  rw [
    BinaryRule.framedStructuralBodyTokens_length
  ]

  change
    X.1.arity +
        ((List.ofFn
            (constantTupleTemplate X.1.tuple)).map
              List.length).sum <=
      compiledWorkingGrammarBinaryRuleBodyTokenCountSampleFanoutBound
        K f

  simpa [
    compiledWorkingGrammarBinaryRuleBodyTokenCountSampleFanoutBound,
    fanout,
    sampleLength
  ] using
    hbasic.trans hfinal

end CorrectedConcreteFiniteHypothesis

end ConstantRuleBodyTokenBound


section LiftedRuleBodyTokenBound

variable {α : Type u}
variable {M : Type v} [Monoid M]
variable {K : Finset (Word α)}
variable {obs : α → M}
variable {f : Nat}

namespace CorrectedConcreteFiniteHypothesis

variable
  (H : CorrectedConcreteFiniteHypothesis K obs f)

/-- Every output component of a corrected finite binary-rule template has
length at most the sample length plus twice the compiled fan-out bound. -/
theorem correctedBinaryRule_body_component_length_le_sampleFanout
    (B : CorrectedConcreteBinaryRuleCode K f) :
    ∀ o : Fin B.parentArity,
      (B.body o).length <=
        sampleLengthBudget K +
          2 * max 1 f := by

  intro o

  have heval :
      (evalTemplateTuple
          B.body
          B.leftSource
          B.rightSource
          o).length <=
        sampleLengthBudget K := by

    exact
      (namedFill_component_length_le
          B.rule.parentContext
          (evalTemplateTuple
            B.body
            B.leftSource
            B.rightSource)
          o).trans
        (sample_word_length_le_budget
          K
          B.rule.evidence.parent_mem)

  have htemplate :
      (B.body o).length <=
        (evalTemplateTuple
            B.body
            B.leftSource
            B.rightSource
            o).length +
          B.leftArity +
          B.rightArity :=
    exactOnce_templateWord_length_le
      B.rule.witness.body_exactOnce
      B.leftSource
      B.rightSource
      o

  have hleft :
      B.leftArity <= max 1 f :=
    B.leftArity_le.trans
      (Nat.le_max_right 1 f)

  have hright :
      B.rightArity <= max 1 f :=
    B.rightArity_le.trans
      (Nat.le_max_right 1 f)

  omega

/-- Every lifted corrected sample binary rule satisfies the common
sample/fan-out body-token bound. -/
theorem cutLiftedBinaryRule_bodyTokenCount_le_sampleFanoutBound
    (dummy : α)
    (B : H.binaryRuleCodes.attach) :
    (correctedConcreteCutLiftedBinaryRule H B).
        framedStructuralBodyTokens.length <=
      compiledWorkingGrammarBinaryRuleBodyTokenCountSampleFanoutBound
        K f := by

  let fanout := max 1 f
  let sampleLength := sampleLengthBudget K
  let componentBound :=
    sampleLength + 2 * fanout

  have harity :
      B.1.parentArity <= fanout :=
    B.1.parentArity_le.trans
      (Nat.le_max_right 1 f)

  have hcomponent :
      ∀ o : Fin B.1.parentArity,
        (B.1.body o).length <=
          componentBound := by

    intro o

    simpa [
      componentBound,
      sampleLength,
      fanout
    ] using
      correctedBinaryRule_body_component_length_le_sampleFanout
        B.1 o

  have hsum :
      ((List.ofFn B.1.body).map List.length).sum <=
        B.1.parentArity * componentBound :=
    templateTuple_componentLengthSum_le
      B.1.body
      componentBound
      hcomponent

  have hmul :
      B.1.parentArity * componentBound <=
        fanout * componentBound :=
    Nat.mul_le_mul_right
      componentBound
      harity

  have hbasic :
      B.1.parentArity +
          ((List.ofFn B.1.body).map List.length).sum <=
        fanout +
          fanout * componentBound :=
    Nat.add_le_add
      harity
      (hsum.trans hmul)

  have hfinal :
      fanout + fanout * componentBound <=
        2 * fanout +
          fanout * componentBound := by
    omega

  rw [
    BinaryRule.framedStructuralBodyTokens_length
  ]

  change
    B.1.parentArity +
        ((List.ofFn B.1.body).map List.length).sum <=
      compiledWorkingGrammarBinaryRuleBodyTokenCountSampleFanoutBound
        K f

  simpa [
    compiledWorkingGrammarBinaryRuleBodyTokenCountSampleFanoutBound,
    componentBound,
    sampleLength,
    fanout
  ] using
    hbasic.trans hfinal

end CorrectedConcreteFiniteHypothesis

end LiftedRuleBodyTokenBound


section SaturationRuleBodyTokenBound

variable {α : Type u}
variable {M : Type v} [Monoid M]
variable {K : Finset (Word α)}
variable {obs : α → M}
variable {f : Nat}

namespace CorrectedConcreteFiniteHypothesis

variable
  (H : CorrectedConcreteFiniteHypothesis K obs f)

/-- Every output component of a saturation left-identity template has length
one. -/
theorem cutSaturationRule_body_component_length_eq_one
    (p : H.cutPairs.attach) :
    ∀
      o : Fin
        (correctedConcreteCutGrammarArity H
          (correctedConcreteCutSaturationRule H p).lhs),
      ((correctedConcreteCutSaturationRule H p).body o).length =
        1 := by

  intro o

  simp [
    correctedConcreteCutSaturationRule,
    leftIdentityTupleTemplate
  ]

/-- Every saturated cut rule has at most twice the compiled fan-out many framed
body tokens. -/
theorem cutSaturationRule_bodyTokenCount_le_two_mul_fanout
    (dummy : α)
    (p : H.cutPairs.attach) :
    (correctedConcreteCutSaturationRule H p).
        framedStructuralBodyTokens.length <=
      2 * max 1 f := by

  let rho :=
    correctedConcreteCutSaturationRule H p

  let fanout := max 1 f

  have harity :
      correctedConcreteCutGrammarArity H rho.lhs <=
        fanout :=
    H.toCutWorkingMCFG_fanoutAtMost_max
      dummy
      rho.lhs

  have hcomponent :
      ∀
        o : Fin
          (correctedConcreteCutGrammarArity H rho.lhs),
        (rho.body o).length <= 1 := by

    intro o

    have hone :
        (rho.body o).length = 1 := by
      simpa [rho] using
        H.cutSaturationRule_body_component_length_eq_one
          p o

    omega

  have hsum :
      ((List.ofFn rho.body).map List.length).sum <=
        correctedConcreteCutGrammarArity H rho.lhs * 1 :=
    templateTuple_componentLengthSum_le
      rho.body
      1
      hcomponent

  have hsumArity :
      ((List.ofFn rho.body).map List.length).sum <=
        fanout := by

    have hmul :
        correctedConcreteCutGrammarArity H rho.lhs * 1 <=
          fanout * 1 :=
      Nat.mul_le_mul_right
        1
        harity

    simpa using
      hsum.trans hmul

  rw [
    BinaryRule.framedStructuralBodyTokens_length
  ]

  change
    correctedConcreteCutGrammarArity H rho.lhs +
        ((List.ofFn rho.body).map List.length).sum <=
      2 * max 1 f

  simpa [fanout] using
    Nat.add_le_add
      harity
      hsumArity

/-- Every saturated cut rule satisfies the common sample/fan-out body-token
bound. -/
theorem cutSaturationRule_bodyTokenCount_le_sampleFanoutBound
    (dummy : α)
    (p : H.cutPairs.attach) :
    (correctedConcreteCutSaturationRule H p).
        framedStructuralBodyTokens.length <=
      compiledWorkingGrammarBinaryRuleBodyTokenCountSampleFanoutBound
        K f := by

  have htwo :
      (correctedConcreteCutSaturationRule H p).
          framedStructuralBodyTokens.length <=
        2 * max 1 f :=
    H.cutSaturationRule_bodyTokenCount_le_two_mul_fanout
      dummy p

  exact
    htwo.trans
      (Nat.le_add_right
        (2 * max 1 f)
        (max 1 f *
          (sampleLengthBudget K +
            2 * max 1 f)))

end CorrectedConcreteFiniteHypothesis

end SaturationRuleBodyTokenBound


section AllStoredBinaryRuleBodyTokenBound

variable {α : Type u}
variable {M : Type v} [Monoid M]
variable {K : Finset (Word α)}
variable {obs : α → M}
variable {f : Nat}

namespace CorrectedConcreteFiniteHypothesis

variable
  (H : CorrectedConcreteFiniteHypothesis K obs f)

/-- Every binary rule actually stored in the cut-compiled grammar satisfies the
common sample/fan-out body-token bound. -/
theorem cutWorkingGrammar_binaryRule_bodyTokenCount_le_sampleFanoutBound
    (dummy : α)
    (rho : BinaryRule
      (CorrectedConcreteCutGrammarNonterminal H)
      α
      (correctedConcreteCutGrammarArity H))
    (hrho :
      rho ∈ (H.toCutWorkingMCFG dummy).binaryRules) :
    rho.framedStructuralBodyTokens.length <=
      compiledWorkingGrammarBinaryRuleBodyTokenCountSampleFanoutBound
        K f := by

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
      H.cutConstantRule_bodyTokenCount_le_sampleFanoutBound
        dummy X

  · rcases List.mem_append.mp hrest with
      hlifted | hsaturated

    · rcases List.mem_map.mp hlifted with
        ⟨B, hB, rfl⟩

      exact
        H.cutLiftedBinaryRule_bodyTokenCount_le_sampleFanoutBound
          dummy B

    · rcases List.mem_map.mp hsaturated with
        ⟨p, hp, rfl⟩

      exact
        H.cutSaturationRule_bodyTokenCount_le_sampleFanoutBound
          dummy p

/-- The maximum stored binary-rule body-token count is bounded by the explicit
sample/fan-out expression. -/
theorem
    compiledWorkingGrammarMaximumBinaryRuleBodyTokenCount_le_sampleFanoutBound
    (dummy : α) :
    H.compiledWorkingGrammarMaximumBinaryRuleBodyTokenCount dummy <=
      compiledWorkingGrammarBinaryRuleBodyTokenCountSampleFanoutBound
        K f := by

  unfold
    compiledWorkingGrammarMaximumBinaryRuleBodyTokenCount

  apply
    maximumNaturalFieldValue_le_of_forall_mem

  intro bodyTokenCount hbodyTokenCount

  rcases List.mem_map.mp hbodyTokenCount with
    ⟨rho, hrho, rfl⟩

  rw [
    H.encodeCompiledBinaryRuleNaturalPacket_bodyTokens_length
      dummy rho
  ]

  rw [
    ← BinaryRule.framedStructuralBodyTokens_length
      rho
  ]

  exact
    H.cutWorkingGrammar_binaryRule_bodyTokenCount_le_sampleFanoutBound
      dummy rho hrho

/-- Expanded endpoint directly in terms of sample length and `max 1 f`. -/
theorem
    compiledWorkingGrammarMaximumBinaryRuleBodyTokenCount_le_expanded
    (dummy : α) :
    H.compiledWorkingGrammarMaximumBinaryRuleBodyTokenCount dummy <=
      2 * max 1 f +
        max 1 f *
          (sampleLengthBudget K +
            2 * max 1 f) := by

  exact
    H.compiledWorkingGrammarMaximumBinaryRuleBodyTokenCount_le_sampleFanoutBound
      dummy

/-- Compact three-family body-token bound package. -/
theorem
    compiledWorkingGrammarBinaryRuleFamilyBodyBounds_package
    (dummy : α) :
    (∀ X : H.controlCodes.attach,
      (correctedConcreteCutConstantRule H X).
          framedStructuralBodyTokens.length <=
        compiledWorkingGrammarBinaryRuleBodyTokenCountSampleFanoutBound
          K f) ∧
      (∀ B : H.binaryRuleCodes.attach,
        (correctedConcreteCutLiftedBinaryRule H B).
            framedStructuralBodyTokens.length <=
          compiledWorkingGrammarBinaryRuleBodyTokenCountSampleFanoutBound
            K f) ∧
      (∀ p : H.cutPairs.attach,
        (correctedConcreteCutSaturationRule H p).
            framedStructuralBodyTokens.length <=
          compiledWorkingGrammarBinaryRuleBodyTokenCountSampleFanoutBound
            K f) ∧
      (∀ rho ∈ (H.toCutWorkingMCFG dummy).binaryRules,
        rho.framedStructuralBodyTokens.length <=
          compiledWorkingGrammarBinaryRuleBodyTokenCountSampleFanoutBound
            K f) ∧
      (H.compiledWorkingGrammarMaximumBinaryRuleBodyTokenCount dummy <=
        compiledWorkingGrammarBinaryRuleBodyTokenCountSampleFanoutBound
          K f) := by

  exact
    ⟨H.cutConstantRule_bodyTokenCount_le_sampleFanoutBound
        dummy,
      H.cutLiftedBinaryRule_bodyTokenCount_le_sampleFanoutBound
        dummy,
      H.cutSaturationRule_bodyTokenCount_le_sampleFanoutBound
        dummy,
      H.cutWorkingGrammar_binaryRule_bodyTokenCount_le_sampleFanoutBound
        dummy,
      H.compiledWorkingGrammarMaximumBinaryRuleBodyTokenCount_le_sampleFanoutBound
        dummy⟩

end CorrectedConcreteFiniteHypothesis

end AllStoredBinaryRuleBodyTokenBound

end MCFG
