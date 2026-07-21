/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG2.ConcreteCanonicalLearnerLengthOnlyBounds

/-!
# ConcreteCanonicalLearnerSinglePowerBounds.lean

The previous files gave exact finite-sum upper bounds for the exhaustive
corrected concrete learner.

This file compresses those sums into one coarse power.

For total sample length `s` and fan-out bound `f`, define

```lean
uniformEnumerationBase s f
uniformRuleExponent s f
singlePowerCorrectedRuleCountBound s f.
```

The final theorem is

```lean
correctedConcreteRuleCountUpToFanout_le_singlePower
```

with conclusion

```lean
correctedConcreteRuleCountUpToFanout K obs f ≤
  singlePowerCorrectedRuleCountBound
    (sampleLengthBudget K) f.
```

The proof has three genuinely new layers.

1. A finite geometric enumeration is bounded by one power:

```lean
finiteWordEnumerationBound a n ≤
  (a + n + 2) ^ (n + 1).
```

2. For all positive arities at most `f`, named contexts, tuple occurrences,
unit rules, and corrected exact-once binary witnesses are bounded by powers of
one common base.

3. The `f` unit-rule families and `f^3` binary-rule families are absorbed into
one additional exponent.

This is intentionally a very coarse elementary bound for the current exhaustive
enumerator.  It is not a polynomial-time claim.

No target grammar occurs in the bound.
No `sorry`, `admit`, or `axiom` is used.
-/

namespace MCFG

universe u v

section ElementaryPowerLemmas

/-- Monotonicity when both the base and exponent increase. -/
theorem nat_pow_le_pow_mixed
    {a b m n : Nat}
    (hab : a ≤ b)
    (hb : 1 < b)
    (hmn : m ≤ n) :
    a ^ m ≤ b ^ n := by
  exact
    (Nat.pow_le_pow_left hab m).trans
      (Nat.pow_le_pow_of_le hb hmn)

/-- A bounded sum of bounded natural numbers is bounded by the number of
summands times the common bound. -/
theorem sum_range_le_mul
    (f bound : Nat)
    (g : Nat → Nat)
    (h :
      ∀ i ∈ Finset.range f,
        g i ≤ bound) :
    (∑ i in Finset.range f, g i) ≤
      f * bound := by
  calc
    (∑ i in Finset.range f, g i) ≤
        ∑ _i in Finset.range f, bound := by
      apply Finset.sum_le_sum
      intro i hi
      exact h i hi
    _ = f * bound := by
      simp

/-- A range sum of terms bounded by `base^exponent` is absorbed into one
additional power whenever the range length is at most the base. -/
theorem sum_range_le_next_power
    {base exponent f : Nat}
    (hbase : 1 < base)
    (hf : f ≤ base)
    (g : Nat → Nat)
    (hg :
      ∀ i ∈ Finset.range f,
        g i ≤ base ^ exponent) :
    (∑ i in Finset.range f, g i) ≤
      base ^ (exponent + 1) := by
  calc
    (∑ i in Finset.range f, g i) ≤
        f * (base ^ exponent) :=
      sum_range_le_mul f (base ^ exponent) g hg
    _ ≤
        base * (base ^ exponent) :=
      Nat.mul_le_mul_right
        (base ^ exponent) hf
    _ =
        base ^ (exponent + 1) := by
      simpa [Nat.pow_add_one', Nat.mul_comm]

/-- If `x ≤ base^wordExponent` and an outer exponent is at most `f`, the
result is bounded by `base^(wordExponent*f)`. -/
theorem bounded_power_le_uniform_power
    {x base wordExponent d f : Nat}
    (hx :
      x ≤ base ^ wordExponent)
    (hbase :
      1 < base)
    (hwordExponent :
      0 < wordExponent)
    (hdf :
      d ≤ f) :
    x ^ d ≤
      base ^ (wordExponent * f) := by

  have hpowBase :
      1 < base ^ wordExponent :=
    Nat.one_lt_pow
      (Nat.ne_of_gt hwordExponent)
      hbase

  calc
    x ^ d ≤
        (base ^ wordExponent) ^ d :=
      Nat.pow_le_pow_left hx d
    _ ≤
        (base ^ wordExponent) ^ f :=
      Nat.pow_le_pow_of_le
        hpowBase hdf
    _ =
        base ^ (wordExponent * f) := by
      symm
      exact Nat.pow_mul
        base wordExponent f

/-- A bounded self-power `d^d` is absorbed by `base^f`. -/
theorem bounded_self_power_le_uniform_power
    {d f base : Nat}
    (hdf : d ≤ f)
    (hfbase : f ≤ base)
    (hbase : 1 < base) :
    d ^ d ≤ base ^ f := by
  exact nat_pow_le_pow_mixed
    (hdf.trans hfbase)
    hbase
    hdf

end ElementaryPowerLemmas


section GeometricEnumerationPower

/-- One-power closed bound for the finite word-enumeration sum. -/
def singlePowerWordEnumerationBound
    (alphabetSize bound : Nat) :
    Nat :=
  (alphabetSize + bound + 2) ^ (bound + 1)

/-- The finite geometric word-enumeration bound is below one elementary
power. -/
theorem finiteWordEnumerationBound_le_singlePower
    (alphabetSize bound : Nat) :
    finiteWordEnumerationBound
        alphabetSize bound ≤
      singlePowerWordEnumerationBound
        alphabetSize bound := by

  let base :=
    alphabetSize + bound + 2

  have hbase :
      1 < base := by
    dsimp [base]
    omega

  have hterm :
      ∀ n ∈ Finset.range (bound + 1),
        alphabetSize ^ n ≤
          base ^ bound := by
    intro n hn

    have hn :
        n ≤ bound := by
      simp only [Finset.mem_range] at hn
      omega

    exact nat_pow_le_pow_mixed
      (by
        dsimp [base]
        omega)
      hbase
      hn

  calc
    finiteWordEnumerationBound
        alphabetSize bound =
        ∑ n in Finset.range (bound + 1),
          alphabetSize ^ n := by
      rfl
    _ ≤
        (bound + 1) * (base ^ bound) :=
      sum_range_le_mul
        (bound + 1)
        (base ^ bound)
        (fun n => alphabetSize ^ n)
        hterm
    _ ≤
        base * (base ^ bound) := by
      apply Nat.mul_le_mul_right
      dsimp [base]
      omega
    _ =
        base ^ (bound + 1) := by
      simpa [Nat.pow_add_one', Nat.mul_comm]
    _ =
        singlePowerWordEnumerationBound
          alphabetSize bound := by
      rfl

/-- A finite word-enumeration bound can be transported to any larger common
base and exponent. -/
theorem finiteWordEnumerationBound_le_commonPower
    {alphabetSize bound base exponent : Nat}
    (hbase :
      1 < base)
    (hbaseSize :
      alphabetSize + bound + 2 ≤ base)
    (hexponent :
      bound + 1 ≤ exponent) :
    finiteWordEnumerationBound
        alphabetSize bound ≤
      base ^ exponent := by
  calc
    finiteWordEnumerationBound
        alphabetSize bound ≤
        (alphabetSize + bound + 2) ^
          (bound + 1) :=
      finiteWordEnumerationBound_le_singlePower
        alphabetSize bound
    _ ≤
        base ^ exponent :=
      nat_pow_le_pow_mixed
        hbaseSize
        hbase
        hexponent

end GeometricEnumerationPower


section UniformSinglePowerParameters

/-- Common base for all word, context, tuple, unit, and binary enumerators at
total sample length `sampleLength` and fan-out `f`. -/
def uniformEnumerationBase
    (sampleLength f : Nat) :
    Nat :=
  2 * sampleLength + 4 * f + 3

/-- Common exponent used for every bounded word alphabet appearing in either
tuple-occurrence or exact-template enumeration. -/
def uniformWordExponent
    (sampleLength f : Nat) :
    Nat :=
  sampleLength + 2 * f + 1

/-- Common exponent for one tuple-occurrence bound. -/
def uniformOccurrenceExponent
    (sampleLength f : Nat) :
    Nat :=
  let q :=
    uniformWordExponent sampleLength f
  q * (f + 1) + f + q * f

/-- Common exponent for one unit-rule family. -/
def uniformUnitRuleExponent
    (sampleLength f : Nat) :
    Nat :=
  uniformOccurrenceExponent sampleLength f +
    uniformOccurrenceExponent sampleLength f

/-- Common exponent for one corrected binary-rule family. -/
def uniformBinaryRuleExponent
    (sampleLength f : Nat) :
    Nat :=
  let q :=
    uniformWordExponent sampleLength f
  uniformOccurrenceExponent sampleLength f +
    uniformOccurrenceExponent sampleLength f +
    uniformOccurrenceExponent sampleLength f +
    q * f

/-- Exponent absorbing the unit-rule range, the three binary-rule ranges, and
the final addition of the two totals. -/
def uniformRuleExponent
    (sampleLength f : Nat) :
    Nat :=
  max
      (uniformUnitRuleExponent sampleLength f + 1)
      (uniformBinaryRuleExponent sampleLength f + 3) +
    1

/-- Final single-power rule-count bound. -/
def singlePowerCorrectedRuleCountBound
    (sampleLength f : Nat) :
    Nat :=
  uniformEnumerationBase sampleLength f ^
    uniformRuleExponent sampleLength f

namespace UniformParameters

theorem base_gt_one
    (sampleLength f : Nat) :
    1 <
      uniformEnumerationBase
        sampleLength f := by
  unfold uniformEnumerationBase
  omega

theorem two_le_base
    (sampleLength f : Nat) :
    2 ≤
      uniformEnumerationBase
        sampleLength f := by
  exact Nat.le_of_lt
    (base_gt_one sampleLength f)

theorem fanout_le_base
    (sampleLength f : Nat) :
    f ≤
      uniformEnumerationBase
        sampleLength f := by
  unfold uniformEnumerationBase
  omega

theorem wordExponent_pos
    (sampleLength f : Nat) :
    0 <
      uniformWordExponent
        sampleLength f := by
  unfold uniformWordExponent
  omega

theorem sample_bound_le_wordExponent
    (sampleLength f : Nat) :
    sampleLength + 1 ≤
      uniformWordExponent
        sampleLength f := by
  unfold uniformWordExponent
  omega

theorem corrected_bound_le_wordExponent
    {sampleLength f dB dC : Nat}
    (hdB : dB ≤ f)
    (hdC : dC ≤ f) :
    sampleLength + dB + dC + 1 ≤
      uniformWordExponent
        sampleLength f := by
  unfold uniformWordExponent
  omega

theorem terminal_word_base_le
    {sampleLength f bound : Nat}
    (hbound :
      bound ≤ sampleLength + 2 * f) :
    sampleLength + bound + 2 ≤
      uniformEnumerationBase
        sampleLength f := by
  unfold uniformEnumerationBase
  omega

theorem template_word_base_le
    {sampleLength f dB dC : Nat}
    (hdB : dB ≤ f)
    (hdC : dC ≤ f) :
    (sampleLength + dB + dC) +
        (sampleLength + dB + dC) + 2 ≤
      uniformEnumerationBase
        sampleLength f := by
  unfold uniformEnumerationBase
  omega

end UniformParameters

end UniformSinglePowerParameters


section UniformWordBounds

/-- Every terminal-word enumeration used at a bound no larger than
`sampleLength + 2*f` is below the common word power. -/
theorem finiteWordEnumerationBound_terminal_le_uniform
    {sampleLength f bound : Nat}
    (hbound :
      bound ≤ sampleLength + 2 * f) :
    finiteWordEnumerationBound
        sampleLength bound ≤
      uniformEnumerationBase sampleLength f ^
        uniformWordExponent sampleLength f := by

  apply finiteWordEnumerationBound_le_commonPower

  · exact UniformParameters.base_gt_one
      sampleLength f

  · exact UniformParameters.terminal_word_base_le
      hbound

  · unfold uniformWordExponent
    omega

/-- Every exact-template-word enumeration used by child arities at most `f` is
below the same common word power. -/
theorem finiteWordEnumerationBound_template_le_uniform
    {sampleLength f dB dC : Nat}
    (hdB : dB ≤ f)
    (hdC : dC ≤ f) :
    finiteWordEnumerationBound
        (sampleLength + dB + dC)
        (sampleLength + dB + dC) ≤
      uniformEnumerationBase sampleLength f ^
        uniformWordExponent sampleLength f := by

  apply finiteWordEnumerationBound_le_commonPower

  · exact UniformParameters.base_gt_one
      sampleLength f

  · exact UniformParameters.template_word_base_le
      hdB hdC

  · exact
      UniformParameters.corrected_bound_le_wordExponent
        hdB hdC

end UniformWordBounds


section UniformContextAndOccurrenceBounds

/-- Named-context enumeration is uniformly bounded for every arity at most
`f` and every terminal-word bound at most `sampleLength + 2*f`. -/
theorem namedContextEnumerationBound_le_uniform
    {sampleLength f d bound : Nat}
    (hd : d ≤ f)
    (hbound :
      bound ≤ sampleLength + 2 * f) :
    namedContextEnumerationBound
        sampleLength bound d ≤
      uniformEnumerationBase sampleLength f ^
        (uniformWordExponent sampleLength f *
            (f + 1) +
          f) := by

  let base :=
    uniformEnumerationBase sampleLength f

  let q :=
    uniformWordExponent sampleLength f

  have hbase :
      1 < base :=
    UniformParameters.base_gt_one
      sampleLength f

  have hq :
      0 < q :=
    UniformParameters.wordExponent_pos
      sampleLength f

  have hword :
      finiteWordEnumerationBound
          sampleLength bound ≤
        base ^ q := by
    exact
      finiteWordEnumerationBound_terminal_le_uniform
        hbound

  have hwordPower :
      finiteWordEnumerationBound
            sampleLength bound ^ (d + 1) ≤
        base ^ (q * (f + 1)) := by
    exact bounded_power_le_uniform_power
      hword hbase hq
      (Nat.add_le_add_right hd 1)

  have hself :
      d ^ d ≤
        base ^ f := by
    exact bounded_self_power_le_uniform_power
      hd
      (UniformParameters.fanout_le_base
        sampleLength f)
      hbase

  unfold namedContextEnumerationBound

  calc
    finiteWordEnumerationBound
          sampleLength bound ^ (d + 1) *
        d ^ d ≤
        base ^ (q * (f + 1)) *
          base ^ f :=
      Nat.mul_le_mul hwordPower hself
    _ =
        base ^ (q * (f + 1) + f) := by
      symm
      exact Nat.pow_add
        base (q * (f + 1)) f

/-- Tuple-occurrence enumeration is uniformly bounded for every arity at most
`f` and every terminal-word bound at most `sampleLength + 2*f`. -/
theorem tupleOccurrenceEnumerationBound_le_uniform
    {sampleLength f d bound : Nat}
    (hd : d ≤ f)
    (hbound :
      bound ≤ sampleLength + 2 * f) :
    tupleOccurrenceEnumerationBound
        sampleLength bound d ≤
      uniformEnumerationBase sampleLength f ^
        uniformOccurrenceExponent
          sampleLength f := by

  let base :=
    uniformEnumerationBase sampleLength f

  let q :=
    uniformWordExponent sampleLength f

  let contextExponent :=
    q * (f + 1) + f

  have hbase :
      1 < base :=
    UniformParameters.base_gt_one
      sampleLength f

  have hq :
      0 < q :=
    UniformParameters.wordExponent_pos
      sampleLength f

  have hcontext :
      namedContextEnumerationBound
          sampleLength bound d ≤
        base ^ contextExponent := by
    exact
      namedContextEnumerationBound_le_uniform
        hd hbound

  have hword :
      finiteWordEnumerationBound
          sampleLength bound ≤
        base ^ q :=
    finiteWordEnumerationBound_terminal_le_uniform
      hbound

  have htuple :
      finiteWordEnumerationBound
            sampleLength bound ^ d ≤
        base ^ (q * f) :=
    bounded_power_le_uniform_power
      hword hbase hq hd

  unfold tupleOccurrenceEnumerationBound
  unfold uniformOccurrenceExponent

  calc
    namedContextEnumerationBound
          sampleLength bound d *
        finiteWordEnumerationBound
          sampleLength bound ^ d ≤
        base ^ contextExponent *
          base ^ (q * f) :=
      Nat.mul_le_mul hcontext htuple
    _ =
        base ^
          (contextExponent + q * f) := by
      symm
      exact Nat.pow_add
        base contextExponent (q * f)

end UniformContextAndOccurrenceBounds


section UniformRuleFamilyBounds

/-- Every unit-rule family of positive arity at most `f` is below one common
power. -/
theorem sampleLengthOnlyUnitRuleBound_le_uniform
    {sampleLength f d : Nat}
    (hd : d ≤ f) :
    sampleLengthOnlyUnitRuleBound
        sampleLength d ≤
      uniformEnumerationBase sampleLength f ^
        uniformUnitRuleExponent
          sampleLength f := by

  have hocc :
      tupleOccurrenceEnumerationBound
          sampleLength sampleLength d ≤
        uniformEnumerationBase sampleLength f ^
          uniformOccurrenceExponent
            sampleLength f := by
    apply tupleOccurrenceEnumerationBound_le_uniform
    · exact hd
    · omega

  unfold sampleLengthOnlyUnitRuleBound
  unfold unitRuleEnumerationBound
  unfold uniformUnitRuleExponent

  calc
    tupleOccurrenceEnumerationBound
          sampleLength sampleLength d *
        tupleOccurrenceEnumerationBound
          sampleLength sampleLength d ≤
        uniformEnumerationBase sampleLength f ^
            uniformOccurrenceExponent
              sampleLength f *
          uniformEnumerationBase sampleLength f ^
            uniformOccurrenceExponent
              sampleLength f :=
      Nat.mul_le_mul hocc hocc
    _ =
        uniformEnumerationBase sampleLength f ^
          (uniformOccurrenceExponent
              sampleLength f +
            uniformOccurrenceExponent
              sampleLength f) := by
      symm
      exact Nat.pow_add
        (uniformEnumerationBase sampleLength f)
        (uniformOccurrenceExponent
          sampleLength f)
        (uniformOccurrenceExponent
          sampleLength f)

/-- Every exact-template-tuple family with all three arities at most `f` is
below the common template power. -/
theorem exactTemplateTupleEnumerationBound_le_uniform
    {sampleLength f e dB dC : Nat}
    (he : e ≤ f)
    (hdB : dB ≤ f)
    (hdC : dC ≤ f) :
    exactTemplateTupleEnumerationBound
        sampleLength
        (sampleLength + dB + dC)
        e dB dC ≤
      uniformEnumerationBase sampleLength f ^
        (uniformWordExponent sampleLength f * f) := by

  let base :=
    uniformEnumerationBase sampleLength f

  let q :=
    uniformWordExponent sampleLength f

  have hword :
      finiteWordEnumerationBound
          (templateAtomEnumerationBound
            sampleLength dB dC)
          (sampleLength + dB + dC) ≤
        base ^ q := by
    change
      finiteWordEnumerationBound
          (sampleLength + dB + dC)
          (sampleLength + dB + dC) ≤
        base ^ q
    exact
      finiteWordEnumerationBound_template_le_uniform
        hdB hdC

  unfold exactTemplateTupleEnumerationBound

  exact bounded_power_le_uniform_power
    hword
    (UniformParameters.base_gt_one
      sampleLength f)
    (UniformParameters.wordExponent_pos
      sampleLength f)
    he

/-- Every corrected binary-witness family with all three positive arities at
most `f` is below one common power. -/
theorem sampleLengthOnlyCorrectedBinaryWitnessBound_le_uniform
    {sampleLength f e dB dC : Nat}
    (he : e ≤ f)
    (hdB : dB ≤ f)
    (hdC : dC ≤ f) :
    sampleLengthOnlyCorrectedBinaryWitnessBound
        sampleLength e dB dC ≤
      uniformEnumerationBase sampleLength f ^
        uniformBinaryRuleExponent
          sampleLength f := by

  let base :=
    uniformEnumerationBase sampleLength f

  let occurrenceExponent :=
    uniformOccurrenceExponent sampleLength f

  let templateExponent :=
    uniformWordExponent sampleLength f * f

  have hbound :
      sampleLength + dB + dC ≤
        sampleLength + 2 * f := by
    omega

  have hparent :
      tupleOccurrenceEnumerationBound
          sampleLength
          (sampleLength + dB + dC)
          e ≤
        base ^ occurrenceExponent :=
    tupleOccurrenceEnumerationBound_le_uniform
      he hbound

  have hleft :
      tupleOccurrenceEnumerationBound
          sampleLength
          (sampleLength + dB + dC)
          dB ≤
        base ^ occurrenceExponent :=
    tupleOccurrenceEnumerationBound_le_uniform
      hdB hbound

  have hright :
      tupleOccurrenceEnumerationBound
          sampleLength
          (sampleLength + dB + dC)
          dC ≤
        base ^ occurrenceExponent :=
    tupleOccurrenceEnumerationBound_le_uniform
      hdC hbound

  have htemplate :
      exactTemplateTupleEnumerationBound
          sampleLength
          (sampleLength + dB + dC)
          e dB dC ≤
        base ^ templateExponent :=
    exactTemplateTupleEnumerationBound_le_uniform
      he hdB hdC

  unfold sampleLengthOnlyCorrectedBinaryWitnessBound
  unfold correctedBinaryWitnessEnumerationBound
  unfold uniformBinaryRuleExponent

  calc
    tupleOccurrenceEnumerationBound
          sampleLength
          (sampleLength + dB + dC)
          e *
        tupleOccurrenceEnumerationBound
          sampleLength
          (sampleLength + dB + dC)
          dB *
        tupleOccurrenceEnumerationBound
          sampleLength
          (sampleLength + dB + dC)
          dC *
        exactTemplateTupleEnumerationBound
          sampleLength
          (sampleLength + dB + dC)
          e dB dC ≤
        base ^ occurrenceExponent *
          base ^ occurrenceExponent *
          base ^ occurrenceExponent *
          base ^ templateExponent :=
      Nat.mul_le_mul
        (Nat.mul_le_mul
          (Nat.mul_le_mul
            hparent hleft)
          hright)
        htemplate
    _ =
        base ^
          (occurrenceExponent +
            occurrenceExponent +
            occurrenceExponent +
            templateExponent) := by
      rw [
        ← Nat.pow_add,
        ← Nat.pow_add,
        ← Nat.pow_add
      ]

end UniformRuleFamilyBounds


section UniformSummedRuleBounds

/-- The sum of all positive-arity unit-rule families up to fan-out `f` is
absorbed by one extra power. -/
theorem sampleLengthOnlyUnitRuleCountBound_le_uniform
    (sampleLength f : Nat) :
    sampleLengthOnlyUnitRuleCountBound
        sampleLength f ≤
      uniformEnumerationBase sampleLength f ^
        (uniformUnitRuleExponent
            sampleLength f + 1) := by

  unfold sampleLengthOnlyUnitRuleCountBound

  apply sum_range_le_next_power

  · exact UniformParameters.base_gt_one
      sampleLength f

  · exact UniformParameters.fanout_le_base
      sampleLength f

  · intro d0 hd0

    have hd :
        d0 + 1 ≤ f := by
      simp only [Finset.mem_range] at hd0
      omega

    exact
      sampleLengthOnlyUnitRuleBound_le_uniform
        hd

/-- The triple sum of corrected binary-rule families is absorbed by three
additional powers. -/
theorem sampleLengthOnlyCorrectedBinaryRuleCountBound_le_uniform
    (sampleLength f : Nat) :
    sampleLengthOnlyCorrectedBinaryRuleCountBound
        sampleLength f ≤
      uniformEnumerationBase sampleLength f ^
        (uniformBinaryRuleExponent
            sampleLength f + 3) := by

  let base :=
    uniformEnumerationBase sampleLength f

  let exponent :=
    uniformBinaryRuleExponent
      sampleLength f

  have hbase :
      1 < base :=
    UniformParameters.base_gt_one
      sampleLength f

  have hf :
      f ≤ base :=
    UniformParameters.fanout_le_base
      sampleLength f

  unfold sampleLengthOnlyCorrectedBinaryRuleCountBound

  apply sum_range_le_next_power
    hbase hf

  intro e0 he0

  apply sum_range_le_next_power
    hbase hf

  intro dB0 hdB0

  apply sum_range_le_next_power
    hbase hf

  intro dC0 hdC0

  have he :
      e0 + 1 ≤ f := by
    simp only [Finset.mem_range] at he0
    omega

  have hdB :
      dB0 + 1 ≤ f := by
    simp only [Finset.mem_range] at hdB0
    omega

  have hdC :
      dC0 + 1 ≤ f := by
    simp only [Finset.mem_range] at hdC0
    omega

  exact
    sampleLengthOnlyCorrectedBinaryWitnessBound_le_uniform
      he hdB hdC

/-- The sum of unit and binary totals is absorbed by the final common
exponent. -/
theorem sampleLengthOnlyCorrectedRuleCountBound_le_singlePower
    (sampleLength f : Nat) :
    sampleLengthOnlyCorrectedRuleCountBound
        sampleLength f ≤
      singlePowerCorrectedRuleCountBound
        sampleLength f := by

  let base :=
    uniformEnumerationBase sampleLength f

  let unitExponent :=
    uniformUnitRuleExponent sampleLength f + 1

  let binaryExponent :=
    uniformBinaryRuleExponent sampleLength f + 3

  let commonExponent :=
    max unitExponent binaryExponent

  have hbase :
      1 < base :=
    UniformParameters.base_gt_one
      sampleLength f

  have hunit :
      sampleLengthOnlyUnitRuleCountBound
          sampleLength f ≤
        base ^ unitExponent :=
    sampleLengthOnlyUnitRuleCountBound_le_uniform
      sampleLength f

  have hbinary :
      sampleLengthOnlyCorrectedBinaryRuleCountBound
          sampleLength f ≤
        base ^ binaryExponent :=
    sampleLengthOnlyCorrectedBinaryRuleCountBound_le_uniform
      sampleLength f

  have hunitCommon :
      base ^ unitExponent ≤
        base ^ commonExponent :=
    Nat.pow_le_pow_of_le hbase
      (Nat.le_max_left _ _)

  have hbinaryCommon :
      base ^ binaryExponent ≤
        base ^ commonExponent :=
    Nat.pow_le_pow_of_le hbase
      (Nat.le_max_right _ _)

  unfold sampleLengthOnlyCorrectedRuleCountBound
  unfold singlePowerCorrectedRuleCountBound
  unfold uniformRuleExponent

  calc
    sampleLengthOnlyUnitRuleCountBound
          sampleLength f +
        sampleLengthOnlyCorrectedBinaryRuleCountBound
          sampleLength f ≤
        base ^ commonExponent +
          base ^ commonExponent :=
      Nat.add_le_add
        (hunit.trans hunitCommon)
        (hbinary.trans hbinaryCommon)
    _ ≤
        base * base ^ commonExponent := by
      apply Nat.mul_le_mul_right
      exact UniformParameters.two_le_base
        sampleLength f
    _ =
        base ^ (commonExponent + 1) := by
      simpa [Nat.pow_add_one', Nat.mul_comm]

end UniformSummedRuleBounds


section ActualLearnerSinglePowerBound

variable {α : Type u}
variable {M : Type v} [Monoid M]

/-- Final single-power estimate for the actual corrected finite learner rule
count. -/
theorem correctedConcreteRuleCountUpToFanout_le_singlePower
    (K : Finset (Word α))
    (obs : α → M)
    (f : Nat) :
    correctedConcreteRuleCountUpToFanout
        K obs f ≤
      singlePowerCorrectedRuleCountBound
        (sampleLengthBudget K) f := by
  exact
    (correctedConcreteRuleCountUpToFanout_le_lengthOnly
      K obs f).trans
      (sampleLengthOnlyCorrectedRuleCountBound_le_singlePower
        (sampleLengthBudget K) f)

/-- Full hierarchy of verified bounds, from the actual enumerator through the
literal finite-sum expressions to the final single power. -/
theorem correctedConcreteRuleCount_singlePower_conclusion_package
    (K : Finset (Word α))
    (obs : α → M)
    (f : Nat) :
    correctedConcreteRuleCountUpToFanout
          K obs f ≤
        correctedConcreteRuleCountBound
          K f ∧
      correctedConcreteRuleCountBound
          K f ≤
        sampleLengthOnlyCorrectedRuleCountBound
          (sampleLengthBudget K) f ∧
      sampleLengthOnlyCorrectedRuleCountBound
          (sampleLengthBudget K) f ≤
        singlePowerCorrectedRuleCountBound
          (sampleLengthBudget K) f ∧
      correctedConcreteRuleCountUpToFanout
          K obs f ≤
        singlePowerCorrectedRuleCountBound
          (sampleLengthBudget K) f := by
  exact
    ⟨correctedConcreteRuleCountUpToFanout_le
        K obs f,
      correctedConcreteRuleCountBound_le_lengthOnly
        K f,
      sampleLengthOnlyCorrectedRuleCountBound_le_singlePower
        (sampleLengthBudget K) f,
      correctedConcreteRuleCountUpToFanout_le_singlePower
        K obs f⟩

end ActualLearnerSinglePowerBound

end MCFG
