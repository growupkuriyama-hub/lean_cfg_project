/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG.ConcreteCanonicalLearnerWorkingGrammarSampleParametricBitBound

/-!
# ConcreteCanonicalLearnerWorkingGrammarPaperBitEnvelope.lean

The preceding file gives a completely closed sample-parametric bound for the
checked logarithmic bit serialization of the actual cut-compiled grammar.  Its
nested maxima are convenient for verification but too detailed for a paper
statement.

This file compresses those maxima into one dominant paper-facing scale.

Let

```text
R(s,f) =
  correctedLearnerPaperBase(s,f) ^
    correctedLearnerPaperExponent(s,f)
```

be the previously verified linear-base, quadratic-exponent rule-count bound, and

```text
P(s,f) = (s + 3 * R(s,f) + 4)^2
```

the complete presentation-item bound.

The new description scale is

```text
D(s,f) =
  P(s,f)
  + [2 * max 1 f
      + max 1 f * (s + 2 * max 1 f)]
  + s + f + 10.
```

It dominates

* the presentation-item bound;
* the common binary-rule body-token bound;
* the augmented terminal-alphabet bound;
* all tags and framing constants; and
* the fixed compiled fan-out.

We prove

```text
sampleParametricBinaryNaturalValueBound ≤ 3 * D,
sampleParametricEntryNaturalValueBound  ≤ 3 * D.
```

Consequently both the complete natural-field count and every natural field
value are bounded by the single quadratic envelope

```text
E(s,f) = 1 + D(s,f) * (1 + 3 * D(s,f)).
```

The final paper-facing checked bit bound is

```text
(E(s,f) + 1) *
  (2 * binaryNatCodeLength(E(s,f)) + 1).
```

Thus the actual complete prefix-free logarithmic bit serialization is now
controlled by one scale explicitly built from the existing paper base and
quadratic paper exponent.

This file does not yet absorb the final polynomial envelope into one larger
power.  That is the next optional compression layer.

No target grammar is supplied to the learner.
No `sorry`, `admit`, or `axiom` is used.
-/

namespace MCFG

universe u v

section PaperDescriptionScale

/-- The sample/fan-out body-token expression used in the paper-facing
description scale. -/
def correctedConcreteCompiledGrammarPaperBodyBound
    (sampleLength f : Nat) :
    Nat :=
  2 * max 1 f +
    max 1 f *
      (sampleLength +
        2 * max 1 f)

/-- One dominant paper-facing scale for the complete compiled-grammar
serialization. -/
def correctedConcreteCompiledGrammarPaperDescriptionScale
    (sampleLength f : Nat) :
    Nat :=
  correctedConcreteCompiledGrammarPresentationItemBound
      sampleLength f +
    correctedConcreteCompiledGrammarPaperBodyBound
      sampleLength f +
    sampleLength +
    f +
    10

/-- Expanded form showing explicitly the previously verified paper base and
quadratic paper exponent. -/
theorem correctedConcreteCompiledGrammarPaperDescriptionScale_eq_expanded
    (sampleLength f : Nat) :
    correctedConcreteCompiledGrammarPaperDescriptionScale
        sampleLength f =
      (sampleLength +
          3 *
            (correctedLearnerPaperBase sampleLength f ^
              correctedLearnerPaperExponent sampleLength f) +
          4) ^ 2 +
        correctedConcreteCompiledGrammarPaperBodyBound
          sampleLength f +
        sampleLength +
        f +
        10 := by

  rfl

/-- The common body-token bound is contained in the description scale. -/
theorem correctedConcreteCompiledGrammarPaperBodyBound_le_descriptionScale
    (sampleLength f : Nat) :
    correctedConcreteCompiledGrammarPaperBodyBound
        sampleLength f <=
      correctedConcreteCompiledGrammarPaperDescriptionScale
        sampleLength f := by

  unfold
    correctedConcreteCompiledGrammarPaperDescriptionScale

  omega

/-- The complete presentation-item bound is contained in the description
scale. -/
theorem
    correctedConcreteCompiledGrammarPresentationItemBound_le_descriptionScale
    (sampleLength f : Nat) :
    correctedConcreteCompiledGrammarPresentationItemBound
        sampleLength f <=
      correctedConcreteCompiledGrammarPaperDescriptionScale
        sampleLength f := by

  unfold
    correctedConcreteCompiledGrammarPaperDescriptionScale

  omega

/-- Total sample length is contained in the description scale. -/
theorem sampleLength_le_correctedGrammarPaperDescriptionScale
    (sampleLength f : Nat) :
    sampleLength <=
      correctedConcreteCompiledGrammarPaperDescriptionScale
        sampleLength f := by

  unfold
    correctedConcreteCompiledGrammarPaperDescriptionScale

  omega

/-- The augmented-alphabet estimate `sampleLength + 1` is contained in the
description scale. -/
theorem sampleLength_add_one_le_correctedGrammarPaperDescriptionScale
    (sampleLength f : Nat) :
    sampleLength + 1 <=
      correctedConcreteCompiledGrammarPaperDescriptionScale
        sampleLength f := by

  unfold
    correctedConcreteCompiledGrammarPaperDescriptionScale

  omega

/-- The fixed fan-out parameter is contained in the description scale. -/
theorem fanout_le_correctedGrammarPaperDescriptionScale
    (sampleLength f : Nat) :
    f <=
      correctedConcreteCompiledGrammarPaperDescriptionScale
        sampleLength f := by

  unfold
    correctedConcreteCompiledGrammarPaperDescriptionScale

  omega

/-- The compiled fan-out `max 1 f` is contained in the description scale. -/
theorem max_one_fanout_le_correctedGrammarPaperDescriptionScale
    (sampleLength f : Nat) :
    max 1 f <=
      correctedConcreteCompiledGrammarPaperDescriptionScale
        sampleLength f := by

  have hmax :
      max 1 f <= f + 1 := by

    apply max_le

    · omega

    · omega

  exact
    hmax.trans
      (by
        unfold
          correctedConcreteCompiledGrammarPaperDescriptionScale
        omega)

/-- The scale has ample positive constant slack. -/
theorem ten_le_correctedGrammarPaperDescriptionScale
    (sampleLength f : Nat) :
    10 <=
      correctedConcreteCompiledGrammarPaperDescriptionScale
        sampleLength f := by

  unfold
    correctedConcreteCompiledGrammarPaperDescriptionScale

  omega

/-- The scale is below three times itself. -/
theorem correctedGrammarPaperDescriptionScale_le_three_mul
    (sampleLength f : Nat) :
    correctedConcreteCompiledGrammarPaperDescriptionScale
        sampleLength f <=
      3 *
        correctedConcreteCompiledGrammarPaperDescriptionScale
          sampleLength f := by

  have hten :=
    ten_le_correctedGrammarPaperDescriptionScale
      sampleLength f

  omega

end PaperDescriptionScale


section BinaryAndEntryEnvelope

/-- Paper-facing envelope for every serialized binary-rule natural value. -/
def correctedConcreteCompiledGrammarPaperBinaryNaturalValueEnvelope
    (sampleLength f : Nat) :
    Nat :=
  3 *
    correctedConcreteCompiledGrammarPaperDescriptionScale
      sampleLength f

/-- Paper-facing envelope for every serialized top-level entry natural value. -/
def correctedConcreteCompiledGrammarPaperEntryNaturalValueEnvelope
    (sampleLength f : Nat) :
    Nat :=
  3 *
    correctedConcreteCompiledGrammarPaperDescriptionScale
      sampleLength f

/-- The closed sample-parametric binary-rule bound is below three times the
paper description scale. -/
theorem
    correctedConcreteCompiledGrammarSampleParametricBinaryNaturalValueBound_le_paperEnvelope
    (sampleLength f : Nat) :
    correctedConcreteCompiledGrammarSampleParametricBinaryNaturalValueBound
        sampleLength f <=
      correctedConcreteCompiledGrammarPaperBinaryNaturalValueEnvelope
        sampleLength f := by

  have hbody :
      correctedConcreteCompiledGrammarPaperBodyBound sampleLength f <=
        correctedConcreteCompiledGrammarPaperDescriptionScale
          sampleLength f :=
    correctedConcreteCompiledGrammarPaperBodyBound_le_descriptionScale
      sampleLength f

  have hpresentation :
      correctedConcreteCompiledGrammarPresentationItemBound sampleLength f <=
        correctedConcreteCompiledGrammarPaperDescriptionScale
          sampleLength f :=
    correctedConcreteCompiledGrammarPresentationItemBound_le_descriptionScale
      sampleLength f

  have hsample :
      sampleLength + 1 <=
        correctedConcreteCompiledGrammarPaperDescriptionScale
          sampleLength f :=
    sampleLength_add_one_le_correctedGrammarPaperDescriptionScale
      sampleLength f

  have hfanout :
      max 1 f <=
        correctedConcreteCompiledGrammarPaperDescriptionScale
          sampleLength f :=
    max_one_fanout_le_correctedGrammarPaperDescriptionScale
      sampleLength f

  have hten :
      10 <=
        correctedConcreteCompiledGrammarPaperDescriptionScale
          sampleLength f :=
    ten_le_correctedGrammarPaperDescriptionScale
      sampleLength f

  unfold
    correctedConcreteCompiledGrammarSampleParametricBinaryNaturalValueBound
    correctedConcreteCompiledGrammarPaperBinaryNaturalValueEnvelope
    correctedConcreteCompiledGrammarPaperBodyBound

  dsimp

  apply max_le

  · omega

  · apply max_le

    · omega

    · apply max_le

      · exact
          hpresentation.trans
            (correctedGrammarPaperDescriptionScale_le_three_mul
              sampleLength f)

      · apply max_le

        · omega

        · apply max_le

          · exact
              hbody.trans
                (correctedGrammarPaperDescriptionScale_le_three_mul
                  sampleLength f)

          · apply max_le

            · exact
                hsample.trans
                  (correctedGrammarPaperDescriptionScale_le_three_mul
                    sampleLength f)

            · exact
                hfanout.trans
                  (correctedGrammarPaperDescriptionScale_le_three_mul
                    sampleLength f)

/-- The closed sample-parametric presentation-entry bound is below three times
the paper description scale. -/
theorem
    correctedConcreteCompiledGrammarSampleParametricEntryNaturalValueBound_le_paperEnvelope
    (sampleLength f : Nat) :
    correctedConcreteCompiledGrammarSampleParametricEntryNaturalValueBound
        sampleLength f <=
      correctedConcreteCompiledGrammarPaperEntryNaturalValueEnvelope
        sampleLength f := by

  have hbody :
      correctedConcreteCompiledGrammarPaperBodyBound sampleLength f <=
        correctedConcreteCompiledGrammarPaperDescriptionScale
          sampleLength f :=
    correctedConcreteCompiledGrammarPaperBodyBound_le_descriptionScale
      sampleLength f

  have hpresentation :
      correctedConcreteCompiledGrammarPresentationItemBound sampleLength f <=
        correctedConcreteCompiledGrammarPaperDescriptionScale
          sampleLength f :=
    correctedConcreteCompiledGrammarPresentationItemBound_le_descriptionScale
      sampleLength f

  have hsample :
      sampleLength + 1 <=
        correctedConcreteCompiledGrammarPaperDescriptionScale
          sampleLength f :=
    sampleLength_add_one_le_correctedGrammarPaperDescriptionScale
      sampleLength f

  have hbinary :
      correctedConcreteCompiledGrammarSampleParametricBinaryNaturalValueBound
          sampleLength f <=
        3 *
          correctedConcreteCompiledGrammarPaperDescriptionScale
            sampleLength f :=
    correctedConcreteCompiledGrammarSampleParametricBinaryNaturalValueBound_le_paperEnvelope
      sampleLength f

  have hten :
      10 <=
        correctedConcreteCompiledGrammarPaperDescriptionScale
          sampleLength f :=
    ten_le_correctedGrammarPaperDescriptionScale
      sampleLength f

  unfold
    correctedConcreteCompiledGrammarSampleParametricEntryNaturalValueBound
    correctedConcreteCompiledGrammarPaperEntryNaturalValueEnvelope
    correctedConcreteCompiledGrammarPaperBodyBound

  dsimp

  apply max_le

  · omega

  · apply max_le

    · omega

    · apply max_le

      · exact
          hpresentation.trans
            (correctedGrammarPaperDescriptionScale_le_three_mul
              sampleLength f)

      · apply max_le

        · exact
            hsample.trans
              (correctedGrammarPaperDescriptionScale_le_three_mul
                sampleLength f)

        · exact hbinary

end BinaryAndEntryEnvelope


section NaturalFieldPaperEnvelope

/-- One quadratic envelope bounding both the complete natural-field count and
every natural field value. -/
def correctedConcreteCompiledGrammarPaperNaturalFieldEnvelope
    (sampleLength f : Nat) :
    Nat :=

  let scale :=
    correctedConcreteCompiledGrammarPaperDescriptionScale
      sampleLength f

  1 +
    scale *
      (1 + 3 * scale)

/-- The paper description scale is below the quadratic natural-field envelope. -/
theorem
    correctedConcreteCompiledGrammarPaperDescriptionScale_le_naturalFieldEnvelope
    (sampleLength f : Nat) :
    correctedConcreteCompiledGrammarPaperDescriptionScale
        sampleLength f <=
      correctedConcreteCompiledGrammarPaperNaturalFieldEnvelope
        sampleLength f := by

  let scale :=
    correctedConcreteCompiledGrammarPaperDescriptionScale
      sampleLength f

  have hone :
      1 <= 1 + 3 * scale := by
    omega

  have hmul :
      scale * 1 <=
        scale * (1 + 3 * scale) :=
    Nat.mul_le_mul_left
      scale hone

  have hscale :
      scale <=
        scale * (1 + 3 * scale) := by
    simpa using hmul

  unfold
    correctedConcreteCompiledGrammarPaperNaturalFieldEnvelope

  dsimp [scale] at hscale ⊢

  exact
    hscale.trans
      (Nat.le_add_left
        (correctedConcreteCompiledGrammarPaperDescriptionScale
            sampleLength f *
          (1 +
            3 *
              correctedConcreteCompiledGrammarPaperDescriptionScale
                sampleLength f))
        1)

/-- Three times the paper description scale is below the quadratic natural-field
envelope. -/
theorem
    three_mul_correctedGrammarPaperDescriptionScale_le_naturalFieldEnvelope
    (sampleLength f : Nat) :
    3 *
        correctedConcreteCompiledGrammarPaperDescriptionScale
          sampleLength f <=
      correctedConcreteCompiledGrammarPaperNaturalFieldEnvelope
        sampleLength f := by

  let scale :=
    correctedConcreteCompiledGrammarPaperDescriptionScale
      sampleLength f

  have hten :
      10 <= scale := by
    simpa [scale] using
      ten_le_correctedGrammarPaperDescriptionScale
        sampleLength f

  have hthree :
      3 <= 1 + 3 * scale := by
    omega

  have hmul :
      scale * 3 <=
        scale * (1 + 3 * scale) :=
    Nat.mul_le_mul_left
      scale hthree

  have hthreeScale :
      3 * scale <=
        scale * (1 + 3 * scale) := by
    simpa [Nat.mul_comm] using hmul

  unfold
    correctedConcreteCompiledGrammarPaperNaturalFieldEnvelope

  dsimp [scale] at hthreeScale ⊢

  exact
    hthreeScale.trans
      (Nat.le_add_left
        (correctedConcreteCompiledGrammarPaperDescriptionScale
            sampleLength f *
          (1 +
            3 *
              correctedConcreteCompiledGrammarPaperDescriptionScale
                sampleLength f))
        1)

/-- The closed sample-parametric natural-field-count bound is below the single
quadratic paper envelope. -/
theorem
    correctedConcreteCompiledGrammarSampleParametricNaturalFieldCountBound_le_paperEnvelope
    (sampleLength f : Nat) :
    correctedConcreteCompiledGrammarSampleParametricNaturalFieldCountBound
        sampleLength f <=
      correctedConcreteCompiledGrammarPaperNaturalFieldEnvelope
        sampleLength f := by

  have hpresentation :
      correctedConcreteCompiledGrammarPresentationItemBound sampleLength f <=
        correctedConcreteCompiledGrammarPaperDescriptionScale
          sampleLength f :=
    correctedConcreteCompiledGrammarPresentationItemBound_le_descriptionScale
      sampleLength f

  have hentry :
      correctedConcreteCompiledGrammarSampleParametricEntryNaturalValueBound
          sampleLength f <=
        3 *
          correctedConcreteCompiledGrammarPaperDescriptionScale
            sampleLength f :=
    correctedConcreteCompiledGrammarSampleParametricEntryNaturalValueBound_le_paperEnvelope
      sampleLength f

  unfold
    correctedConcreteCompiledGrammarSampleParametricNaturalFieldCountBound
    correctedConcreteCompiledGrammarPaperNaturalFieldEnvelope

  dsimp

  exact
    Nat.add_le_add_left
      (Nat.mul_le_mul
        hpresentation
        (Nat.add_le_add_left hentry 1))
      1

/-- The closed sample-parametric natural-field-value bound is below the same
quadratic paper envelope. -/
theorem
    correctedConcreteCompiledGrammarSampleParametricNaturalFieldBound_le_paperEnvelope
    (sampleLength f : Nat) :
    correctedConcreteCompiledGrammarSampleParametricNaturalFieldBound
        sampleLength f <=
      correctedConcreteCompiledGrammarPaperNaturalFieldEnvelope
        sampleLength f := by

  have hcount :
      correctedConcreteCompiledGrammarSampleParametricNaturalFieldCountBound
          sampleLength f <=
        correctedConcreteCompiledGrammarPaperNaturalFieldEnvelope
          sampleLength f :=
    correctedConcreteCompiledGrammarSampleParametricNaturalFieldCountBound_le_paperEnvelope
      sampleLength f

  have hpresentation :
      correctedConcreteCompiledGrammarPresentationItemBound sampleLength f <=
        correctedConcreteCompiledGrammarPaperDescriptionScale
          sampleLength f :=
    correctedConcreteCompiledGrammarPresentationItemBound_le_descriptionScale
      sampleLength f

  have hentry :
      correctedConcreteCompiledGrammarSampleParametricEntryNaturalValueBound
          sampleLength f <=
        3 *
          correctedConcreteCompiledGrammarPaperDescriptionScale
            sampleLength f :=
    correctedConcreteCompiledGrammarSampleParametricEntryNaturalValueBound_le_paperEnvelope
      sampleLength f

  unfold
    correctedConcreteCompiledGrammarSampleParametricNaturalFieldBound

  dsimp

  apply max_le

  · exact hcount

  · apply max_le

    · exact
        hpresentation.trans
          (correctedConcreteCompiledGrammarPaperDescriptionScale_le_naturalFieldEnvelope
            sampleLength f)

    · exact
        hentry.trans
          (three_mul_correctedGrammarPaperDescriptionScale_le_naturalFieldEnvelope
            sampleLength f)

end NaturalFieldPaperEnvelope


section PaperLogarithmicBitEnvelope

/-- Final paper-facing checked logarithmic bit bound. -/
def correctedConcreteCompiledGrammarPaperLogarithmicBitEnvelope
    (sampleLength f : Nat) :
    Nat :=

  let envelope :=
    correctedConcreteCompiledGrammarPaperNaturalFieldEnvelope
      sampleLength f

  (envelope + 1) *
    (2 *
        binaryNatCodeLength envelope +
      1)

variable {α : Type u}
variable {M : Type v} [Monoid M]

/-- The actual canonical grammar natural-field count is below the paper
envelope. -/
theorem
    correctedConcreteFiniteHypothesis_naturalFieldCount_le_paperEnvelope
    (K : Finset (Word α))
    (obs : α → M)
    (f : Nat)
    (dummy : α) :
    (correctedConcreteFiniteHypothesis K obs f).
        compiledWorkingGrammarNaturalFieldCount dummy <=
      correctedConcreteCompiledGrammarPaperNaturalFieldEnvelope
        (sampleLengthBudget K) f := by

  exact
    (correctedConcreteFiniteHypothesis_naturalFieldCount_le_sampleParametric
        K obs f dummy).trans
      (correctedConcreteCompiledGrammarSampleParametricNaturalFieldCountBound_le_paperEnvelope
        (sampleLengthBudget K) f)

/-- The actual canonical grammar natural-field value bound is below the paper
envelope. -/
theorem
    correctedConcreteFiniteHypothesis_naturalFieldValueBound_le_paperEnvelope
    (K : Finset (Word α))
    (obs : α → M)
    (f : Nat)
    (dummy : α) :
    (correctedConcreteFiniteHypothesis K obs f).
        compiledWorkingGrammarNaturalFieldValueBound dummy <=
      correctedConcreteCompiledGrammarPaperNaturalFieldEnvelope
        (sampleLengthBudget K) f := by

  exact
    (correctedConcreteFiniteHypothesis_naturalFieldValueBound_le_sampleParametric
        K obs f dummy).trans
      (correctedConcreteCompiledGrammarSampleParametricNaturalFieldBound_le_paperEnvelope
        (sampleLengthBudget K) f)

/-- The complete natural stream of the canonical hypothesis fits the standard
binary width of the single paper envelope. -/
theorem
    correctedConcreteFiniteHypothesis_naturalFieldsFitInBits_paperEnvelope
    (K : Finset (Word α))
    (obs : α → M)
    (f : Nat)
    (dummy : α) :
    (correctedConcreteFiniteHypothesis K obs f).
      compiledWorkingGrammarNaturalFieldsFitInBits
        dummy
        (binaryNatCodeLength
          (correctedConcreteCompiledGrammarPaperNaturalFieldEnvelope
            (sampleLengthBudget K) f)) := by

  let H :=
    correctedConcreteFiniteHypothesis K obs f

  refine
    ⟨binaryNatCodeLength_pos
        (correctedConcreteCompiledGrammarPaperNaturalFieldEnvelope
          (sampleLengthBudget K) f),
      ?_,
      ?_⟩

  · rw [
      H.encodeCompiledWorkingGrammarNaturalList_length
        dummy
    ]

    exact
      (correctedConcreteFiniteHypothesis_naturalFieldCount_le_paperEnvelope
          K obs f dummy).trans_lt
        (natCode_lt_two_pow_binaryNatCodeLength
          (correctedConcreteCompiledGrammarPaperNaturalFieldEnvelope
            (sampleLengthBudget K) f))

  · intro n hn

    exact
      ((H.compiledWorkingGrammarNaturalField_le_valueBound_of_mem
          dummy hn).trans
        (correctedConcreteFiniteHypothesis_naturalFieldValueBound_le_paperEnvelope
          K obs f dummy)).trans_lt
        (natCode_lt_two_pow_binaryNatCodeLength
          (correctedConcreteCompiledGrammarPaperNaturalFieldEnvelope
            (sampleLengthBudget K) f))

/-- Final paper-facing checked logarithmic description-size theorem. -/
theorem
    correctedConcreteFiniteHypothesis_logarithmicBitCount_le_paperEnvelope
    (K : Finset (Word α))
    (obs : α → M)
    (f : Nat)
    (dummy : α) :
    (correctedConcreteFiniteHypothesis K obs f).
        compiledWorkingGrammarLogarithmicBitCount dummy <=
      correctedConcreteCompiledGrammarPaperLogarithmicBitEnvelope
        (sampleLengthBudget K) f := by

  let H :=
    correctedConcreteFiniteHypothesis K obs f

  have hfit :
      H.compiledWorkingGrammarNaturalFieldsFitInBits
        dummy
        (binaryNatCodeLength
          (correctedConcreteCompiledGrammarPaperNaturalFieldEnvelope
            (sampleLengthBudget K) f)) := by

    dsimp [H]

    exact
      correctedConcreteFiniteHypothesis_naturalFieldsFitInBits_paperEnvelope
        K obs f dummy

  have hbase :
      H.compiledWorkingGrammarLogarithmicBitCount dummy <=
        (H.compiledWorkingGrammarNaturalFieldCount dummy + 1) *
          (2 *
              binaryNatCodeLength
                (correctedConcreteCompiledGrammarPaperNaturalFieldEnvelope
                  (sampleLengthBudget K) f) +
            1) :=
    H.compiledWorkingGrammarLogarithmicBitCount_le_of_naturalFieldsFitInBits
      dummy hfit

  have hcount :
      H.compiledWorkingGrammarNaturalFieldCount dummy + 1 <=
        correctedConcreteCompiledGrammarPaperNaturalFieldEnvelope
            (sampleLengthBudget K) f +
          1 :=
    Nat.add_le_add_right
      (correctedConcreteFiniteHypothesis_naturalFieldCount_le_paperEnvelope
        K obs f dummy)
      1

  unfold
    correctedConcreteCompiledGrammarPaperLogarithmicBitEnvelope

  dsimp

  exact
    hbase.trans
      (Nat.mul_le_mul_right
        (2 *
            binaryNatCodeLength
              (correctedConcreteCompiledGrammarPaperNaturalFieldEnvelope
                (sampleLengthBudget K) f) +
          1)
        hcount)

/-- Compact paper-facing description-size package. -/
theorem
    correctedConcreteFiniteHypothesis_paperBitEnvelope_package
    (K : Finset (Word α))
    (obs : α → M)
    (f : Nat)
    (dummy : α) :
    ((correctedConcreteFiniteHypothesis K obs f).
        compiledWorkingGrammarNaturalFieldCount dummy <=
      correctedConcreteCompiledGrammarPaperNaturalFieldEnvelope
        (sampleLengthBudget K) f) ∧
      ((correctedConcreteFiniteHypothesis K obs f).
          compiledWorkingGrammarNaturalFieldValueBound dummy <=
        correctedConcreteCompiledGrammarPaperNaturalFieldEnvelope
          (sampleLengthBudget K) f) ∧
      (correctedConcreteFiniteHypothesis K obs f).
        compiledWorkingGrammarNaturalFieldsFitInBits
          dummy
          (binaryNatCodeLength
            (correctedConcreteCompiledGrammarPaperNaturalFieldEnvelope
              (sampleLengthBudget K) f)) ∧
      ((correctedConcreteFiniteHypothesis K obs f).
          compiledWorkingGrammarLogarithmicBitCount dummy <=
        correctedConcreteCompiledGrammarPaperLogarithmicBitEnvelope
          (sampleLengthBudget K) f) := by

  exact
    ⟨correctedConcreteFiniteHypothesis_naturalFieldCount_le_paperEnvelope
        K obs f dummy,
      correctedConcreteFiniteHypothesis_naturalFieldValueBound_le_paperEnvelope
        K obs f dummy,
      correctedConcreteFiniteHypothesis_naturalFieldsFitInBits_paperEnvelope
        K obs f dummy,
      correctedConcreteFiniteHypothesis_logarithmicBitCount_le_paperEnvelope
        K obs f dummy⟩

end PaperLogarithmicBitEnvelope

end MCFG
