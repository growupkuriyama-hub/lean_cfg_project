/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG.ConcreteCanonicalLearnerWorkingGrammarBinaryRuleFamilyBodyBounds

/-!
# ConcreteCanonicalLearnerWorkingGrammarSampleParametricBitBound.lean

The preceding file proves that the maximum framed-body-token count of the
cut-compiled grammar is bounded entirely by the positive sample length and the
fixed fan-out parameter:

```lean
H.compiledWorkingGrammarMaximumBinaryRuleBodyTokenCount dummy
  ≤
compiledWorkingGrammarBinaryRuleBodyTokenCountSampleFanoutBound K f.
```

This file substitutes that estimate through the complete natural serialization
and logarithmic bit codec.

There are two layers.

## Structural sample/fan-out layer

For an arbitrary `CorrectedConcreteFiniteHypothesis K obs f`, we retain only

* its complete presentation-item count; and
* the cardinality of its augmented terminal alphabet.

Every other quantity is replaced by an expression in

```text
sampleLengthBudget K
and
max 1 f.
```

We obtain explicit bounds for

* every stored binary-rule natural payload;
* every stored top-level presentation entry;
* the complete natural-field count;
* every natural field value; and
* the complete logarithmic bit count.

## Canonical paper-facing layer

For the canonical hypothesis

```lean
correctedConcreteFiniteHypothesis K obs f
```

we additionally substitute the already verified estimates

```text
presentationItemCount
  ≤ correctedConcreteCompiledGrammarPresentationItemBound
      (sampleLengthBudget K) f,

compiledTerminalAlphabet.card
  ≤ sampleLengthBudget K + 1.
```

This produces a bound containing only `sampleLengthBudget K` and `f`.

The final endpoint is

```lean
correctedConcreteFiniteHypothesis_logarithmicBitCount_le_sampleParametric.
```

It bounds the complete checked, prefix-free, logarithmic bit serialization of
the actual cut-compiled `WorkingMCFG` by a closed sample-parametric expression.

No per-entry maximum, per-rule maximum, body-token maximum, terminal-alphabet
cardinality, presentation-item count, or natural-field count remains on the
right-hand side of the canonical theorem.

No target grammar is supplied to the learner.
No `sorry`, `admit`, or `axiom` is used.
-/

namespace MCFG

universe u v

section ElementaryMaximumMonotonicity

/-- Monotonicity of binary maximum, stated locally to keep the nested structural
bound proofs readable. -/
theorem nat_max_mono_of_le
    {a b c d : Nat}
    (hac : a <= c)
    (hbd : b <= d) :
    max a b <= max c d := by

  apply max_le

  · exact
      hac.trans
        (Nat.le_max_left c d)

  · exact
      hbd.trans
        (Nat.le_max_right c d)

end ElementaryMaximumMonotonicity


section StructuralSampleFanoutBounds

variable {α : Type u}
variable {M : Type v} [Monoid M]
variable {K : Finset (Word α)}
variable {obs : α → M}
variable {f : Nat}

namespace CorrectedConcreteFiniteHypothesis

variable
  (H : CorrectedConcreteFiniteHypothesis K obs f)

/-- Uniform binary-rule natural-value bound after substituting the common
sample/fan-out body-token bound. -/
noncomputable def
    compiledWorkingGrammarSampleFanoutBinaryRuleNaturalValueBound
    (dummy : α) :
    Nat :=

  let bodyBound :=
    compiledWorkingGrammarBinaryRuleBodyTokenCountSampleFanoutBound
      K f

  max
    (4 + 2 * bodyBound)
    (max 4
      (max
        H.compiledGrammarPresentationItemCount
        (max 3
          (max bodyBound
            (max
              (compiledTerminalAlphabet K dummy).card
              (max 1 f))))))

/-- Uniform presentation-entry natural-value bound after substituting the common
sample/fan-out body-token bound. -/
noncomputable def
    compiledWorkingGrammarSampleFanoutPresentationEntryNaturalValueBound
    (dummy : α) :
    Nat :=

  let bodyBound :=
    compiledWorkingGrammarBinaryRuleBodyTokenCountSampleFanoutBound
      K f

  max
    (6 + 2 * bodyBound)
    (max 3
      (max
        H.compiledGrammarPresentationItemCount
        (max
          (compiledTerminalAlphabet K dummy).card
          (H.compiledWorkingGrammarSampleFanoutBinaryRuleNaturalValueBound
            dummy))))

/-- Complete natural-field-count bound obtained from the presentation-item
count and the uniform sample/fan-out entry bound. -/
noncomputable def
    compiledWorkingGrammarSampleFanoutNaturalFieldCountBound
    (dummy : α) :
    Nat :=
  1 +
    H.compiledGrammarPresentationItemCount *
      (1 +
        H.compiledWorkingGrammarSampleFanoutPresentationEntryNaturalValueBound
          dummy)

/-- Complete natural-field-value bound at the structural sample/fan-out layer. -/
noncomputable def
    compiledWorkingGrammarSampleFanoutNaturalFieldBound
    (dummy : α) :
    Nat :=
  max
    (H.compiledWorkingGrammarSampleFanoutNaturalFieldCountBound
      dummy)
    (max
      H.compiledGrammarPresentationItemCount
      (H.compiledWorkingGrammarSampleFanoutPresentationEntryNaturalValueBound
        dummy))

/-- The previous maximum-body-token uniform binary-rule bound is below its
sample/fan-out substitution. -/
theorem
    compiledWorkingGrammarUniformBinaryRuleNaturalValueBound_le_sampleFanout
    (dummy : α) :
    H.compiledWorkingGrammarUniformBinaryRuleNaturalValueBound dummy <=
      H.compiledWorkingGrammarSampleFanoutBinaryRuleNaturalValueBound
        dummy := by

  have hbody :
      H.compiledWorkingGrammarMaximumBinaryRuleBodyTokenCount dummy <=
        compiledWorkingGrammarBinaryRuleBodyTokenCountSampleFanoutBound
          K f :=
    H.compiledWorkingGrammarMaximumBinaryRuleBodyTokenCount_le_sampleFanoutBound
      dummy

  unfold
    compiledWorkingGrammarUniformBinaryRuleNaturalValueBound
    compiledWorkingGrammarSampleFanoutBinaryRuleNaturalValueBound

  exact
    nat_max_mono_of_le
      (Nat.add_le_add_left
        (Nat.mul_le_mul_left 2 hbody)
        4)
      (nat_max_mono_of_le
        (le_refl 4)
        (nat_max_mono_of_le
          (le_refl H.compiledGrammarPresentationItemCount)
          (nat_max_mono_of_le
            (le_refl 3)
            (nat_max_mono_of_le
              hbody
              (le_refl
                (max
                  (compiledTerminalAlphabet K dummy).card
                  (max 1 f)))))))

/-- The previous uniform presentation-entry bound is below the bound obtained
after substituting the sample/fan-out body-token estimate. -/
theorem
    compiledWorkingGrammarUniformPresentationEntryNaturalValueBound_le_sampleFanout
    (dummy : α) :
    H.compiledWorkingGrammarUniformPresentationEntryNaturalValueBound
        dummy <=
      H.compiledWorkingGrammarSampleFanoutPresentationEntryNaturalValueBound
        dummy := by

  have hbody :
      H.compiledWorkingGrammarMaximumBinaryRuleBodyTokenCount dummy <=
        compiledWorkingGrammarBinaryRuleBodyTokenCountSampleFanoutBound
          K f :=
    H.compiledWorkingGrammarMaximumBinaryRuleBodyTokenCount_le_sampleFanoutBound
      dummy

  have hbinary :
      H.compiledWorkingGrammarUniformBinaryRuleNaturalValueBound dummy <=
        H.compiledWorkingGrammarSampleFanoutBinaryRuleNaturalValueBound
          dummy :=
    H.compiledWorkingGrammarUniformBinaryRuleNaturalValueBound_le_sampleFanout
      dummy

  unfold
    compiledWorkingGrammarUniformPresentationEntryNaturalValueBound
    compiledWorkingGrammarSampleFanoutPresentationEntryNaturalValueBound

  exact
    nat_max_mono_of_le
      (Nat.add_le_add_left
        (Nat.mul_le_mul_left 2 hbody)
        6)
      (nat_max_mono_of_le
        (le_refl 3)
        (nat_max_mono_of_le
          (le_refl H.compiledGrammarPresentationItemCount)
          (nat_max_mono_of_le
            (le_refl
              (compiledTerminalAlphabet K dummy).card)
            hbinary)))

/-- Every stored presentation entry contributes at most one frame field plus the
uniform sample/fan-out entry bound. -/
theorem
    compiledGrammarPresentationEntryFramedNaturalFieldCount_le_sampleFanout
    (dummy : α)
    (entry :
      CorrectedConcreteCompiledGrammarPresentationEntry H)
    (hentry :
      entry ∈ H.compiledGrammarPresentationEntries dummy) :
    1 +
        H.compiledGrammarPresentationEntryNaturalFieldCount
          dummy entry <=
      1 +
        H.compiledWorkingGrammarSampleFanoutPresentationEntryNaturalValueBound
          dummy := by

  have hlocal :
      H.compiledGrammarPresentationEntryNaturalFieldCount dummy entry <=
        H.compiledGrammarPresentationEntryFullyExplicitNaturalValueBound
          dummy entry :=
    H.compiledGrammarPresentationEntryNaturalFieldCount_le_fullyExplicitBound
      dummy entry

  have huniform :
      H.compiledGrammarPresentationEntryFullyExplicitNaturalValueBound
          dummy entry <=
        H.compiledWorkingGrammarUniformPresentationEntryNaturalValueBound
          dummy :=
    H.compiledGrammarPresentationEntryFullyExplicitNaturalValueBound_le_uniform_of_mem
      dummy entry hentry

  have hsample :
      H.compiledWorkingGrammarUniformPresentationEntryNaturalValueBound
          dummy <=
        H.compiledWorkingGrammarSampleFanoutPresentationEntryNaturalValueBound
          dummy :=
    H.compiledWorkingGrammarUniformPresentationEntryNaturalValueBound_le_sampleFanout
      dummy

  exact
    Nat.add_le_add_left
      (hlocal.trans (huniform.trans hsample))
      1

/-- The exact complete natural-field count is below the structural
sample/fan-out field-count bound. -/
theorem
    compiledWorkingGrammarNaturalFieldCount_le_sampleFanoutBound
    (dummy : α) :
    H.compiledWorkingGrammarNaturalFieldCount dummy <=
      H.compiledWorkingGrammarSampleFanoutNaturalFieldCountBound
        dummy := by

  unfold
    compiledWorkingGrammarNaturalFieldCount
    compiledWorkingGrammarSampleFanoutNaturalFieldCountBound

  have hsum :
      ((H.compiledGrammarPresentationEntries dummy).map
        (fun entry =>
          1 +
            H.compiledGrammarPresentationEntryNaturalFieldCount
              dummy entry)).sum <=
        (H.compiledGrammarPresentationEntries dummy).length *
          (1 +
            H.compiledWorkingGrammarSampleFanoutPresentationEntryNaturalValueBound
              dummy) := by

    apply
      list_sum_le_length_mul_of_forall_mem_le

    intro framedCount hframedCount

    rcases List.mem_map.mp hframedCount with
      ⟨entry, hentry, rfl⟩

    exact
      H.compiledGrammarPresentationEntryFramedNaturalFieldCount_le_sampleFanout
        dummy entry hentry

  rw [
    H.compiledGrammarPresentationEntries_length dummy
  ] at hsum

  exact
    Nat.add_le_add_left
      hsum
      1

/-- The previous complete uniform natural-field bound is below the structural
sample/fan-out bound. -/
theorem
    compiledWorkingGrammarUniformNaturalFieldBound_le_sampleFanout
    (dummy : α) :
    H.compiledWorkingGrammarUniformNaturalFieldBound dummy <=
      H.compiledWorkingGrammarSampleFanoutNaturalFieldBound
        dummy := by

  unfold
    compiledWorkingGrammarUniformNaturalFieldBound
    compiledWorkingGrammarSampleFanoutNaturalFieldBound

  exact
    nat_max_mono_of_le
      (H.compiledWorkingGrammarNaturalFieldCount_le_sampleFanoutBound
        dummy)
      (nat_max_mono_of_le
        (le_refl H.compiledGrammarPresentationItemCount)
        (H.compiledWorkingGrammarUniformPresentationEntryNaturalValueBound_le_sampleFanout
          dummy))

/-- The original natural-field value bound is below the structural
sample/fan-out bound. -/
theorem
    compiledWorkingGrammarNaturalFieldValueBound_le_sampleFanout
    (dummy : α) :
    H.compiledWorkingGrammarNaturalFieldValueBound dummy <=
      H.compiledWorkingGrammarSampleFanoutNaturalFieldBound
        dummy := by

  exact
    (H.compiledWorkingGrammarNaturalFieldValueBound_le_uniform
        dummy).trans
      (H.compiledWorkingGrammarUniformNaturalFieldBound_le_sampleFanout
        dummy)

/-- Every complete-grammar natural field is below the structural sample/fan-out
bound. -/
theorem
    compiledWorkingGrammarNaturalField_le_sampleFanout_of_mem
    (dummy : α)
    {n : Nat}
    (hn :
      n ∈ H.encodeCompiledWorkingGrammarNaturalList dummy) :
    n <=
      H.compiledWorkingGrammarSampleFanoutNaturalFieldBound
        dummy := by

  exact
    (H.compiledWorkingGrammarNaturalField_le_valueBound_of_mem
        dummy hn).trans
      (H.compiledWorkingGrammarNaturalFieldValueBound_le_sampleFanout
        dummy)

/-- Standard binary width obtained from the structural sample/fan-out natural
field bound. -/
noncomputable def
    compiledWorkingGrammarSampleFanoutNaturalFieldBitWidth
    (dummy : α) :
    Nat :=
  binaryNatCodeLength
    (H.compiledWorkingGrammarSampleFanoutNaturalFieldBound
      dummy)

/-- The complete natural stream fits the structural sample/fan-out width. -/
theorem
    compiledWorkingGrammarNaturalFieldsFitInBits_sampleFanout
    (dummy : α) :
    H.compiledWorkingGrammarNaturalFieldsFitInBits
        dummy
        (H.compiledWorkingGrammarSampleFanoutNaturalFieldBitWidth
          dummy) := by

  refine
    ⟨binaryNatCodeLength_pos
        (H.compiledWorkingGrammarSampleFanoutNaturalFieldBound
          dummy),
      ?_,
      ?_⟩

  · rw [
      H.encodeCompiledWorkingGrammarNaturalList_length
        dummy
    ]

    exact
      (H.compiledWorkingGrammarNaturalFieldCount_le_sampleFanoutBound
          dummy).trans_lt
        ((Nat.le_max_left
            (H.compiledWorkingGrammarSampleFanoutNaturalFieldCountBound
              dummy)
            (max
              H.compiledGrammarPresentationItemCount
              (H.compiledWorkingGrammarSampleFanoutPresentationEntryNaturalValueBound
                dummy))).trans_lt
          (natCode_lt_two_pow_binaryNatCodeLength
            (H.compiledWorkingGrammarSampleFanoutNaturalFieldBound
              dummy)))

  · intro n hn

    exact
      (H.compiledWorkingGrammarNaturalField_le_sampleFanout_of_mem
          dummy hn).trans_lt
        (natCode_lt_two_pow_binaryNatCodeLength
          (H.compiledWorkingGrammarSampleFanoutNaturalFieldBound
            dummy))

/-- Complete logarithmic bit-count bound at the structural sample/fan-out
layer. -/
theorem
    compiledWorkingGrammarLogarithmicBitCount_le_sampleFanout
    (dummy : α) :
    H.compiledWorkingGrammarLogarithmicBitCount dummy <=
      (H.compiledWorkingGrammarSampleFanoutNaturalFieldCountBound
          dummy + 1) *
        (2 *
            binaryNatCodeLength
              (H.compiledWorkingGrammarSampleFanoutNaturalFieldBound
                dummy) +
          1) := by

  have hbase :
      H.compiledWorkingGrammarLogarithmicBitCount dummy <=
        (H.compiledWorkingGrammarNaturalFieldCount dummy + 1) *
          (2 *
              binaryNatCodeLength
                (H.compiledWorkingGrammarSampleFanoutNaturalFieldBound
                  dummy) +
            1) :=
    H.compiledWorkingGrammarLogarithmicBitCount_le_of_naturalFieldsFitInBits
      dummy
      (H.compiledWorkingGrammarNaturalFieldsFitInBits_sampleFanout
        dummy)

  have hcount :
      H.compiledWorkingGrammarNaturalFieldCount dummy + 1 <=
        H.compiledWorkingGrammarSampleFanoutNaturalFieldCountBound
            dummy +
          1 :=
    Nat.add_le_add_right
      (H.compiledWorkingGrammarNaturalFieldCount_le_sampleFanoutBound
        dummy)
      1

  exact
    hbase.trans
      (Nat.mul_le_mul_right
        (2 *
            binaryNatCodeLength
              (H.compiledWorkingGrammarSampleFanoutNaturalFieldBound
                dummy) +
          1)
        hcount)

/-- Compact endpoint of the structural sample/fan-out substitution layer. -/
theorem
    compiledWorkingGrammarSampleFanoutBitBound_package
    (dummy : α) :
    (H.compiledWorkingGrammarNaturalFieldCount dummy <=
      H.compiledWorkingGrammarSampleFanoutNaturalFieldCountBound
        dummy) ∧
      (H.compiledWorkingGrammarNaturalFieldValueBound dummy <=
        H.compiledWorkingGrammarSampleFanoutNaturalFieldBound
          dummy) ∧
      H.compiledWorkingGrammarNaturalFieldsFitInBits
        dummy
        (H.compiledWorkingGrammarSampleFanoutNaturalFieldBitWidth
          dummy) ∧
      (H.compiledWorkingGrammarLogarithmicBitCount dummy <=
        (H.compiledWorkingGrammarSampleFanoutNaturalFieldCountBound
            dummy + 1) *
          (2 *
              binaryNatCodeLength
                (H.compiledWorkingGrammarSampleFanoutNaturalFieldBound
                  dummy) +
            1)) := by

  exact
    ⟨H.compiledWorkingGrammarNaturalFieldCount_le_sampleFanoutBound
        dummy,
      H.compiledWorkingGrammarNaturalFieldValueBound_le_sampleFanout
        dummy,
      H.compiledWorkingGrammarNaturalFieldsFitInBits_sampleFanout
        dummy,
      H.compiledWorkingGrammarLogarithmicBitCount_le_sampleFanout
        dummy⟩

end CorrectedConcreteFiniteHypothesis

end StructuralSampleFanoutBounds


section CanonicalSampleParametricBounds

variable {α : Type u}
variable {M : Type v} [Monoid M]

/-- The augmented compiled terminal alphabet has at most the total sample length
plus one element. -/
theorem compiledTerminalAlphabet_card_le_sampleLengthBudget_add_one
    (K : Finset (Word α))
    (dummy : α) :
    (compiledTerminalAlphabet K dummy).card <=
      sampleLengthBudget K + 1 := by

  classical

  by_cases hdummy :
      dummy ∈ sampleAlphabet K

  · have hsample :
        (sampleAlphabet K).card <=
          sampleLengthBudget K :=
      card_sampleAlphabet_le_sampleLengthBudget K

    have hinsert :
        (compiledTerminalAlphabet K dummy).card =
          (sampleAlphabet K).card := by
      simp [
        compiledTerminalAlphabet,
        hdummy
      ]

    rw [hinsert]

    exact
      hsample.trans
        (Nat.le_add_right
          (sampleLengthBudget K)
          1)

  · have hsample :
        (sampleAlphabet K).card + 1 <=
          sampleLengthBudget K + 1 :=
      Nat.add_le_add_right
        (card_sampleAlphabet_le_sampleLengthBudget K)
        1

    simpa [
      compiledTerminalAlphabet,
      hdummy
    ] using hsample

/-- Closed sample-parametric binary-rule natural-value bound for the canonical
finite hypothesis. -/
def correctedConcreteCompiledGrammarSampleParametricBinaryNaturalValueBound
    (sampleLength f : Nat) :
    Nat :=

  let canonicalBodyBound :=
    2 * max 1 f +
      max 1 f *
        (sampleLength +
          2 * max 1 f)

  let presentationBound :=
    correctedConcreteCompiledGrammarPresentationItemBound
      sampleLength f

  max
    (4 + 2 * canonicalBodyBound)
    (max 4
      (max presentationBound
        (max 3
          (max canonicalBodyBound
            (max
              (sampleLength + 1)
              (max 1 f))))))

/-- Closed sample-parametric top-level presentation-entry natural-value bound. -/
def correctedConcreteCompiledGrammarSampleParametricEntryNaturalValueBound
    (sampleLength f : Nat) :
    Nat :=

  let bodyBound :=
    2 * max 1 f +
      max 1 f *
        (sampleLength +
          2 * max 1 f)

  let presentationBound :=
    correctedConcreteCompiledGrammarPresentationItemBound
      sampleLength f

  let binaryBound :=
    correctedConcreteCompiledGrammarSampleParametricBinaryNaturalValueBound
      sampleLength f

  max
    (6 + 2 * bodyBound)
    (max 3
      (max presentationBound
        (max
          (sampleLength + 1)
          binaryBound)))

/-- Closed sample-parametric complete natural-field-count bound. -/
def correctedConcreteCompiledGrammarSampleParametricNaturalFieldCountBound
    (sampleLength f : Nat) :
    Nat :=

  let presentationBound :=
    correctedConcreteCompiledGrammarPresentationItemBound
      sampleLength f

  let entryBound :=
    correctedConcreteCompiledGrammarSampleParametricEntryNaturalValueBound
      sampleLength f

  1 +
    presentationBound *
      (1 + entryBound)

/-- Closed sample-parametric complete natural-field-value bound. -/
def correctedConcreteCompiledGrammarSampleParametricNaturalFieldBound
    (sampleLength f : Nat) :
    Nat :=

  let presentationBound :=
    correctedConcreteCompiledGrammarPresentationItemBound
      sampleLength f

  let entryBound :=
    correctedConcreteCompiledGrammarSampleParametricEntryNaturalValueBound
      sampleLength f

  let fieldCountBound :=
    correctedConcreteCompiledGrammarSampleParametricNaturalFieldCountBound
      sampleLength f

  max fieldCountBound
    (max presentationBound entryBound)

/-- Closed sample-parametric logarithmic bit-count bound. -/
def correctedConcreteCompiledGrammarSampleParametricLogarithmicBitBound
    (sampleLength f : Nat) :
    Nat :=

  let fieldCountBound :=
    correctedConcreteCompiledGrammarSampleParametricNaturalFieldCountBound
      sampleLength f

  let fieldBound :=
    correctedConcreteCompiledGrammarSampleParametricNaturalFieldBound
      sampleLength f

  (fieldCountBound + 1) *
    (2 *
        binaryNatCodeLength fieldBound +
      1)

/-- The structural sample/fan-out binary-rule bound of the canonical hypothesis
is below the closed sample-parametric binary bound. -/
theorem
    correctedConcreteFiniteHypothesis_sampleFanoutBinaryBound_le_sampleParametric
    (K : Finset (Word α))
    (obs : α → M)
    (f : Nat)
    (dummy : α) :
    (correctedConcreteFiniteHypothesis K obs f).
        compiledWorkingGrammarSampleFanoutBinaryRuleNaturalValueBound
          dummy <=
      correctedConcreteCompiledGrammarSampleParametricBinaryNaturalValueBound
          (sampleLengthBudget K) f := by

  let H :=
    correctedConcreteFiniteHypothesis K obs f

  have hpresentation :
      H.compiledGrammarPresentationItemCount <=
        correctedConcreteCompiledGrammarPresentationItemBound
          (sampleLengthBudget K) f := by

    dsimp [H]

    exact
      correctedConcreteFiniteHypothesis_presentationItemCount_le_paperBound
        K obs f

  have halphabet :
      (compiledTerminalAlphabet K dummy).card <=
        sampleLengthBudget K + 1 :=
    compiledTerminalAlphabet_card_le_sampleLengthBudget_add_one
      K dummy

  unfold
    CorrectedConcreteFiniteHypothesis.compiledWorkingGrammarSampleFanoutBinaryRuleNaturalValueBound
    correctedConcreteCompiledGrammarSampleParametricBinaryNaturalValueBound

  dsimp

  exact
    nat_max_mono_of_le
      (le_refl
        (4 +
          2 *
            (2 * max 1 f +
              max 1 f *
                (sampleLengthBudget K +
                  2 * max 1 f))))
      (nat_max_mono_of_le
        (le_refl 4)
        (nat_max_mono_of_le
          hpresentation
          (nat_max_mono_of_le
            (le_refl 3)
            (nat_max_mono_of_le
              (le_refl
                (2 * max 1 f +
                  max 1 f *
                    (sampleLengthBudget K +
                      2 * max 1 f)))
              (nat_max_mono_of_le
                halphabet
                (le_refl (max 1 f)))))))

/-- The structural sample/fan-out entry bound of the canonical hypothesis is
below the closed sample-parametric entry bound. -/
theorem
    correctedConcreteFiniteHypothesis_sampleFanoutEntryBound_le_sampleParametric
    (K : Finset (Word α))
    (obs : α → M)
    (f : Nat)
    (dummy : α) :
    (correctedConcreteFiniteHypothesis K obs f).
        compiledWorkingGrammarSampleFanoutPresentationEntryNaturalValueBound
          dummy <=
      correctedConcreteCompiledGrammarSampleParametricEntryNaturalValueBound
          (sampleLengthBudget K) f := by

  let H :=
    correctedConcreteFiniteHypothesis K obs f

  have hpresentation :
      H.compiledGrammarPresentationItemCount <=
        correctedConcreteCompiledGrammarPresentationItemBound
          (sampleLengthBudget K) f := by

    dsimp [H]

    exact
      correctedConcreteFiniteHypothesis_presentationItemCount_le_paperBound
        K obs f

  have halphabet :
      (compiledTerminalAlphabet K dummy).card <=
        sampleLengthBudget K + 1 :=
    compiledTerminalAlphabet_card_le_sampleLengthBudget_add_one
      K dummy

  have hbinary :
      H.compiledWorkingGrammarSampleFanoutBinaryRuleNaturalValueBound
          dummy <=
        correctedConcreteCompiledGrammarSampleParametricBinaryNaturalValueBound
              (sampleLengthBudget K) f := by

    dsimp [H]

    exact
      correctedConcreteFiniteHypothesis_sampleFanoutBinaryBound_le_sampleParametric
        K obs f dummy

  unfold
    CorrectedConcreteFiniteHypothesis.compiledWorkingGrammarSampleFanoutPresentationEntryNaturalValueBound
    correctedConcreteCompiledGrammarSampleParametricEntryNaturalValueBound

  dsimp

  exact
    nat_max_mono_of_le
      (le_refl
        (6 +
          2 *
            (2 * max 1 f +
              max 1 f *
                (sampleLengthBudget K +
                  2 * max 1 f))))
      (nat_max_mono_of_le
        (le_refl 3)
        (nat_max_mono_of_le
          hpresentation
          (nat_max_mono_of_le
            halphabet
            hbinary)))

/-- The structural sample/fan-out field-count bound of the canonical hypothesis
is below the closed sample-parametric field-count bound. -/
theorem
    correctedConcreteFiniteHypothesis_sampleFanoutNaturalFieldCountBound_le_sampleParametric
    (K : Finset (Word α))
    (obs : α → M)
    (f : Nat)
    (dummy : α) :
    (correctedConcreteFiniteHypothesis K obs f).
        compiledWorkingGrammarSampleFanoutNaturalFieldCountBound
          dummy <=
      correctedConcreteCompiledGrammarSampleParametricNaturalFieldCountBound
          (sampleLengthBudget K) f := by

  let H :=
    correctedConcreteFiniteHypothesis K obs f

  have hpresentation :
      H.compiledGrammarPresentationItemCount <=
        correctedConcreteCompiledGrammarPresentationItemBound
          (sampleLengthBudget K) f := by

    dsimp [H]

    exact
      correctedConcreteFiniteHypothesis_presentationItemCount_le_paperBound
        K obs f

  have hentry :
      H.compiledWorkingGrammarSampleFanoutPresentationEntryNaturalValueBound
          dummy <=
        correctedConcreteCompiledGrammarSampleParametricEntryNaturalValueBound
              (sampleLengthBudget K) f := by

    dsimp [H]

    exact
      correctedConcreteFiniteHypothesis_sampleFanoutEntryBound_le_sampleParametric
        K obs f dummy

  unfold
    CorrectedConcreteFiniteHypothesis.compiledWorkingGrammarSampleFanoutNaturalFieldCountBound
    correctedConcreteCompiledGrammarSampleParametricNaturalFieldCountBound

  dsimp

  exact
    Nat.add_le_add_left
      (Nat.mul_le_mul
        hpresentation
        (Nat.add_le_add_left hentry 1))
      1

/-- The structural sample/fan-out natural-field bound of the canonical
hypothesis is below the closed sample-parametric natural-field bound. -/
theorem
    correctedConcreteFiniteHypothesis_sampleFanoutNaturalFieldBound_le_sampleParametric
    (K : Finset (Word α))
    (obs : α → M)
    (f : Nat)
    (dummy : α) :
    (correctedConcreteFiniteHypothesis K obs f).
        compiledWorkingGrammarSampleFanoutNaturalFieldBound
          dummy <=
      correctedConcreteCompiledGrammarSampleParametricNaturalFieldBound
          (sampleLengthBudget K) f := by

  let H :=
    correctedConcreteFiniteHypothesis K obs f

  have hcount :
      H.compiledWorkingGrammarSampleFanoutNaturalFieldCountBound dummy <=
        correctedConcreteCompiledGrammarSampleParametricNaturalFieldCountBound
              (sampleLengthBudget K) f := by

    dsimp [H]

    exact
      correctedConcreteFiniteHypothesis_sampleFanoutNaturalFieldCountBound_le_sampleParametric
        K obs f dummy

  have hpresentation :
      H.compiledGrammarPresentationItemCount <=
        correctedConcreteCompiledGrammarPresentationItemBound
          (sampleLengthBudget K) f := by

    dsimp [H]

    exact
      correctedConcreteFiniteHypothesis_presentationItemCount_le_paperBound
        K obs f

  have hentry :
      H.compiledWorkingGrammarSampleFanoutPresentationEntryNaturalValueBound
          dummy <=
        correctedConcreteCompiledGrammarSampleParametricEntryNaturalValueBound
              (sampleLengthBudget K) f := by

    dsimp [H]

    exact
      correctedConcreteFiniteHypothesis_sampleFanoutEntryBound_le_sampleParametric
        K obs f dummy

  unfold
    CorrectedConcreteFiniteHypothesis.compiledWorkingGrammarSampleFanoutNaturalFieldBound
    correctedConcreteCompiledGrammarSampleParametricNaturalFieldBound

  dsimp

  exact
    nat_max_mono_of_le
      hcount
      (nat_max_mono_of_le
        hpresentation
        hentry)

/-- The actual complete natural-field count of the canonical hypothesis is below
the closed sample-parametric count. -/
theorem
    correctedConcreteFiniteHypothesis_naturalFieldCount_le_sampleParametric
    (K : Finset (Word α))
    (obs : α → M)
    (f : Nat)
    (dummy : α) :
    (correctedConcreteFiniteHypothesis K obs f).
        compiledWorkingGrammarNaturalFieldCount dummy <=
      correctedConcreteCompiledGrammarSampleParametricNaturalFieldCountBound
          (sampleLengthBudget K) f := by

  let H :=
    correctedConcreteFiniteHypothesis K obs f

  exact
    (H.compiledWorkingGrammarNaturalFieldCount_le_sampleFanoutBound
        dummy).trans
      (correctedConcreteFiniteHypothesis_sampleFanoutNaturalFieldCountBound_le_sampleParametric
        K obs f dummy)

/-- The actual complete natural-field value bound of the canonical hypothesis is
below the closed sample-parametric field bound. -/
theorem
    correctedConcreteFiniteHypothesis_naturalFieldValueBound_le_sampleParametric
    (K : Finset (Word α))
    (obs : α → M)
    (f : Nat)
    (dummy : α) :
    (correctedConcreteFiniteHypothesis K obs f).
        compiledWorkingGrammarNaturalFieldValueBound dummy <=
      correctedConcreteCompiledGrammarSampleParametricNaturalFieldBound
          (sampleLengthBudget K) f := by

  let H :=
    correctedConcreteFiniteHypothesis K obs f

  exact
    (H.compiledWorkingGrammarNaturalFieldValueBound_le_sampleFanout
        dummy).trans
      (correctedConcreteFiniteHypothesis_sampleFanoutNaturalFieldBound_le_sampleParametric
        K obs f dummy)

/-- The complete natural stream of the canonical hypothesis fits the standard
binary width of the closed sample-parametric field bound. -/
theorem
    correctedConcreteFiniteHypothesis_naturalFieldsFitInBits_sampleParametric
    (K : Finset (Word α))
    (obs : α → M)
    (f : Nat)
    (dummy : α) :
    (correctedConcreteFiniteHypothesis K obs f).
      compiledWorkingGrammarNaturalFieldsFitInBits
        dummy
        (binaryNatCodeLength
          (correctedConcreteCompiledGrammarSampleParametricNaturalFieldBound
                  (sampleLengthBudget K) f)) := by

  let H :=
    correctedConcreteFiniteHypothesis K obs f

  refine
    ⟨binaryNatCodeLength_pos
        (correctedConcreteCompiledGrammarSampleParametricNaturalFieldBound
              (sampleLengthBudget K) f),
      ?_,
      ?_⟩

  · rw [
      H.encodeCompiledWorkingGrammarNaturalList_length
        dummy
    ]

    exact
      (correctedConcreteFiniteHypothesis_naturalFieldCount_le_sampleParametric
          K obs f dummy).trans_lt
        ((Nat.le_max_left
            (correctedConcreteCompiledGrammarSampleParametricNaturalFieldCountBound
                      (sampleLengthBudget K) f)
            (max
              (correctedConcreteCompiledGrammarPresentationItemBound
                (sampleLengthBudget K) f)
              (correctedConcreteCompiledGrammarSampleParametricEntryNaturalValueBound
                          (sampleLengthBudget K) f))).trans_lt
          (natCode_lt_two_pow_binaryNatCodeLength
            (correctedConcreteCompiledGrammarSampleParametricNaturalFieldBound
                      (sampleLengthBudget K) f)))

  · intro n hn

    exact
      ((H.compiledWorkingGrammarNaturalField_le_valueBound_of_mem
          dummy hn).trans
        (correctedConcreteFiniteHypothesis_naturalFieldValueBound_le_sampleParametric
          K obs f dummy)).trans_lt
        (natCode_lt_two_pow_binaryNatCodeLength
          (correctedConcreteCompiledGrammarSampleParametricNaturalFieldBound
                  (sampleLengthBudget K) f))

/-- Final closed sample-parametric logarithmic bit-count theorem for the actual
cut-compiled grammar of the canonical finite learner. -/
theorem
    correctedConcreteFiniteHypothesis_logarithmicBitCount_le_sampleParametric
    (K : Finset (Word α))
    (obs : α → M)
    (f : Nat)
    (dummy : α) :
    (correctedConcreteFiniteHypothesis K obs f).
        compiledWorkingGrammarLogarithmicBitCount dummy <=
      correctedConcreteCompiledGrammarSampleParametricLogarithmicBitBound
          (sampleLengthBudget K) f := by

  let H :=
    correctedConcreteFiniteHypothesis K obs f

  have hbase :
      H.compiledWorkingGrammarLogarithmicBitCount dummy <=
        (H.compiledWorkingGrammarNaturalFieldCount dummy + 1) *
          (2 *
              binaryNatCodeLength
                (correctedConcreteCompiledGrammarSampleParametricNaturalFieldBound
                              (sampleLengthBudget K) f) +
            1) :=
    H.compiledWorkingGrammarLogarithmicBitCount_le_of_naturalFieldsFitInBits
      dummy
      (correctedConcreteFiniteHypothesis_naturalFieldsFitInBits_sampleParametric
        K obs f dummy)

  have hcount :
      H.compiledWorkingGrammarNaturalFieldCount dummy + 1 <=
        correctedConcreteCompiledGrammarSampleParametricNaturalFieldCountBound
                  (sampleLengthBudget K) f +
          1 :=
    Nat.add_le_add_right
      (correctedConcreteFiniteHypothesis_naturalFieldCount_le_sampleParametric
        K obs f dummy)
      1

  unfold
    correctedConcreteCompiledGrammarSampleParametricLogarithmicBitBound

  dsimp

  exact
    hbase.trans
      (Nat.mul_le_mul_right
        (2 *
            binaryNatCodeLength
              (correctedConcreteCompiledGrammarSampleParametricNaturalFieldBound
                          (sampleLengthBudget K) f) +
          1)
        hcount)

/-- Compact canonical sample-parametric description-size endpoint. -/
theorem
    correctedConcreteFiniteHypothesis_sampleParametricBitBound_package
    (K : Finset (Word α))
    (obs : α → M)
    (f : Nat)
    (dummy : α) :
    ((correctedConcreteFiniteHypothesis K obs f).
        compiledWorkingGrammarNaturalFieldCount dummy <=
      correctedConcreteCompiledGrammarSampleParametricNaturalFieldCountBound
          (sampleLengthBudget K) f) ∧
      ((correctedConcreteFiniteHypothesis K obs f).
          compiledWorkingGrammarNaturalFieldValueBound dummy <=
        correctedConcreteCompiledGrammarSampleParametricNaturalFieldBound
              (sampleLengthBudget K) f) ∧
      (correctedConcreteFiniteHypothesis K obs f).
        compiledWorkingGrammarNaturalFieldsFitInBits
          dummy
          (binaryNatCodeLength
            (correctedConcreteCompiledGrammarSampleParametricNaturalFieldBound
                      (sampleLengthBudget K) f)) ∧
      ((correctedConcreteFiniteHypothesis K obs f).
          compiledWorkingGrammarLogarithmicBitCount dummy <=
        correctedConcreteCompiledGrammarSampleParametricLogarithmicBitBound
              (sampleLengthBudget K) f) := by

  exact
    ⟨correctedConcreteFiniteHypothesis_naturalFieldCount_le_sampleParametric
        K obs f dummy,
      correctedConcreteFiniteHypothesis_naturalFieldValueBound_le_sampleParametric
        K obs f dummy,
      correctedConcreteFiniteHypothesis_naturalFieldsFitInBits_sampleParametric
        K obs f dummy,
      correctedConcreteFiniteHypothesis_logarithmicBitCount_le_sampleParametric
        K obs f dummy⟩

end CanonicalSampleParametricBounds

end MCFG
