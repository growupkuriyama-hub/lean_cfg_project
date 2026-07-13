/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG.ConcreteCanonicalLearnerFiniteEnumerationBounds

/-!
# ConcreteCanonicalLearnerLengthOnlyBounds.lean

The preceding file bounds the finite learner enumerators using both

```lean
(sampleAlphabet K).card
sampleLengthBudget K.
```

This file removes the alphabet-cardinality parameter.

First it proves the structural estimate

```lean
(sampleAlphabet K).card ≤ sampleLengthBudget K.
```

Then it proves monotonicity of every numerical enumeration bound in its
alphabet-size argument.  Combining those results yields bounds depending only
on:

* the total sample length `sampleLengthBudget K`;
* the relevant tuple arities;
* the fan-out bound `f`.

The final theorem is

```lean
correctedConcreteRuleCountUpToFanout_le_lengthOnly
```

and has the form

```lean
correctedConcreteRuleCountUpToFanout K obs f ≤
  sampleLengthOnlyCorrectedRuleCountBound
    (sampleLengthBudget K) f.
```

These remain coarse exponential bounds for the exhaustive concrete learner.
No polynomial-time claim is made.

No target grammar occurs in any bound.
No `sorry`, `admit`, or `axiom` is used.
-/

namespace MCFG

universe u v

section SampleAlphabetSize

variable {α : Type u}

/-- The number of distinct letters in a word is at most its length. -/
theorem card_list_toFinset_le_length
    (word : Word α) :
    word.toFinset.card ≤ word.length := by
  classical
  induction word with

  | nil =>
      simp

  | cons a rest ih =>
      by_cases ha : a ∈ rest
      · simp [ha]
        omega
      · simp [ha]
        omega

/-- The finite alphabet of a sample has cardinality at most the sum of the
lengths of all sample words. -/
theorem card_sampleAlphabet_le_sampleLengthBudget
    (K : Finset (Word α)) :
    (sampleAlphabet K).card ≤
      sampleLengthBudget K := by
  classical
  unfold sampleAlphabet
  unfold sampleLengthBudget
  calc
    (K.biUnion
      (fun word => word.toFinset)).card ≤
        ∑ word in K, word.toFinset.card :=
      finset_card_biUnion_le_sum_card
        K (fun word => word.toFinset)
    _ ≤
        ∑ word in K, word.length := by
      apply Finset.sum_le_sum
      intro word hword
      exact card_list_toFinset_le_length word

end SampleAlphabetSize


section NumericalBoundMonotonicity

/-- Bounded-word cardinality is monotone in the alphabet size. -/
theorem finiteWordEnumerationBound_mono_alphabet
    {a b bound : Nat}
    (hab : a ≤ b) :
    finiteWordEnumerationBound a bound ≤
      finiteWordEnumerationBound b bound := by
  unfold finiteWordEnumerationBound
  apply Finset.sum_le_sum
  intro n hn
  exact Nat.pow_le_pow_left hab n

/-- Named-context cardinality bound is monotone in the alphabet size. -/
theorem namedContextEnumerationBound_mono_alphabet
    {a b bound d : Nat}
    (hab : a ≤ b) :
    namedContextEnumerationBound
        a bound d ≤
      namedContextEnumerationBound
        b bound d := by
  unfold namedContextEnumerationBound
  apply Nat.mul_le_mul_right
  exact Nat.pow_le_pow_left
    (finiteWordEnumerationBound_mono_alphabet
      hab)
    (d + 1)

/-- Tuple-occurrence cardinality bound is monotone in the alphabet size. -/
theorem tupleOccurrenceEnumerationBound_mono_alphabet
    {a b bound d : Nat}
    (hab : a ≤ b) :
    tupleOccurrenceEnumerationBound
        a bound d ≤
      tupleOccurrenceEnumerationBound
        b bound d := by
  unfold tupleOccurrenceEnumerationBound
  exact Nat.mul_le_mul
    (namedContextEnumerationBound_mono_alphabet
      hab)
    (Nat.pow_le_pow_left
      (finiteWordEnumerationBound_mono_alphabet
        hab)
      d)

/-- Unit-rule cardinality bound is monotone in the alphabet size. -/
theorem unitRuleEnumerationBound_mono_alphabet
    {a b bound d : Nat}
    (hab : a ≤ b) :
    unitRuleEnumerationBound
        a bound d ≤
      unitRuleEnumerationBound
        b bound d := by
  unfold unitRuleEnumerationBound
  let h :=
    tupleOccurrenceEnumerationBound_mono_alphabet
      (bound := bound) (d := d) hab
  exact Nat.mul_le_mul h h

/-- Template-atom alphabet bound is monotone in the terminal alphabet size. -/
theorem templateAtomEnumerationBound_mono_alphabet
    {a b dB dC : Nat}
    (hab : a ≤ b) :
    templateAtomEnumerationBound
        a dB dC ≤
      templateAtomEnumerationBound
        b dB dC := by
  unfold templateAtomEnumerationBound
  omega

/-- Exact-template-tuple bound is monotone in the terminal alphabet size. -/
theorem exactTemplateTupleEnumerationBound_mono_alphabet
    {a b bound e dB dC : Nat}
    (hab : a ≤ b) :
    exactTemplateTupleEnumerationBound
        a bound e dB dC ≤
      exactTemplateTupleEnumerationBound
        b bound e dB dC := by
  unfold exactTemplateTupleEnumerationBound
  exact Nat.pow_le_pow_left
    (finiteWordEnumerationBound_mono_alphabet
      (templateAtomEnumerationBound_mono_alphabet
        (dB := dB) (dC := dC) hab))
    e

/-- Corrected binary-witness bound is monotone in the terminal alphabet size. -/
theorem correctedBinaryWitnessEnumerationBound_mono_alphabet
    {a b bound e dB dC : Nat}
    (hab : a ≤ b) :
    correctedBinaryWitnessEnumerationBound
        a bound e dB dC ≤
      correctedBinaryWitnessEnumerationBound
        b bound e dB dC := by
  unfold correctedBinaryWitnessEnumerationBound

  have he :
      tupleOccurrenceEnumerationBound
          a bound e ≤
        tupleOccurrenceEnumerationBound
          b bound e :=
    tupleOccurrenceEnumerationBound_mono_alphabet
      hab

  have hB :
      tupleOccurrenceEnumerationBound
          a bound dB ≤
        tupleOccurrenceEnumerationBound
          b bound dB :=
    tupleOccurrenceEnumerationBound_mono_alphabet
      hab

  have hC :
      tupleOccurrenceEnumerationBound
          a bound dC ≤
        tupleOccurrenceEnumerationBound
          b bound dC :=
    tupleOccurrenceEnumerationBound_mono_alphabet
      hab

  have ht :
      exactTemplateTupleEnumerationBound
          a bound e dB dC ≤
        exactTemplateTupleEnumerationBound
          b bound e dB dC :=
    exactTemplateTupleEnumerationBound_mono_alphabet
      hab

  exact Nat.mul_le_mul
    (Nat.mul_le_mul
      (Nat.mul_le_mul he hB)
      hC)
    ht

end NumericalBoundMonotonicity


section LengthOnlyNumericalBounds

/-- Word-enumeration bound using only one total-length parameter. -/
def sampleLengthOnlyWordEnumerationBound
    (sampleLength : Nat) :
    Nat :=
  finiteWordEnumerationBound
    sampleLength sampleLength

/-- Named-context bound using only total sample length and arity. -/
def sampleLengthOnlyNamedContextBound
    (sampleLength d : Nat) :
    Nat :=
  namedContextEnumerationBound
    sampleLength sampleLength d

/-- Tuple-occurrence bound using only total sample length and arity. -/
def sampleLengthOnlyTupleOccurrenceBound
    (sampleLength d : Nat) :
    Nat :=
  tupleOccurrenceEnumerationBound
    sampleLength sampleLength d

/-- Unit-rule bound using only total sample length and arity. -/
def sampleLengthOnlyUnitRuleBound
    (sampleLength d : Nat) :
    Nat :=
  unitRuleEnumerationBound
    sampleLength sampleLength d

/-- Corrected binary-witness bound using only total sample length and the three
arities. -/
def sampleLengthOnlyCorrectedBinaryWitnessBound
    (sampleLength e dB dC : Nat) :
    Nat :=
  correctedBinaryWitnessEnumerationBound
    sampleLength
    (sampleLength + dB + dC)
    e dB dC

/-- Sum of all positive-arity unit-rule bounds up to fan-out `f`. -/
def sampleLengthOnlyUnitRuleCountBound
    (sampleLength f : Nat) :
    Nat :=
  ∑ d0 in Finset.range f,
    sampleLengthOnlyUnitRuleBound
      sampleLength (d0 + 1)

/-- Sum of all corrected binary-witness bounds over positive arities at most
`f`. -/
def sampleLengthOnlyCorrectedBinaryRuleCountBound
    (sampleLength f : Nat) :
    Nat :=
  ∑ e0 in Finset.range f,
    ∑ dB0 in Finset.range f,
      ∑ dC0 in Finset.range f,
        sampleLengthOnlyCorrectedBinaryWitnessBound
          sampleLength
          (e0 + 1)
          (dB0 + 1)
          (dC0 + 1)

/-- Total corrected concrete rule-count bound depending only on total sample
length and fan-out. -/
def sampleLengthOnlyCorrectedRuleCountBound
    (sampleLength f : Nat) :
    Nat :=
  sampleLengthOnlyUnitRuleCountBound
      sampleLength f +
    sampleLengthOnlyCorrectedBinaryRuleCountBound
      sampleLength f

end LengthOnlyNumericalBounds


section LengthOnlyWordAndContextBounds

variable {α : Type u}

/-- Default bounded-word enumeration is controlled only by total sample
length. -/
theorem card_sampleBoundedWords_le_lengthOnly
    (K : Finset (Word α)) :
    (sampleBoundedWords K).card ≤
      sampleLengthOnlyWordEnumerationBound
        (sampleLengthBudget K) := by
  calc
    (sampleBoundedWords K).card ≤
        finiteWordEnumerationBound
          (sampleAlphabet K).card
          (sampleLengthBudget K) :=
      card_sampleBoundedWords_le K
    _ ≤
        finiteWordEnumerationBound
          (sampleLengthBudget K)
          (sampleLengthBudget K) :=
      finiteWordEnumerationBound_mono_alphabet
        (card_sampleAlphabet_le_sampleLengthBudget K)
    _ =
        sampleLengthOnlyWordEnumerationBound
          (sampleLengthBudget K) := by
      rfl

/-- Named-context candidates at the default sample-length bound are controlled
only by total sample length and arity. -/
theorem card_namedContextCandidates_sampleBound_le_lengthOnly
    (K : Finset (Word α))
    (d : Nat) :
    (namedContextCandidates
        (sampleAlphabet K)
        (sampleLengthBudget K)
        d).card ≤
      sampleLengthOnlyNamedContextBound
        (sampleLengthBudget K) d := by
  calc
    (namedContextCandidates
        (sampleAlphabet K)
        (sampleLengthBudget K)
        d).card ≤
        namedContextEnumerationBound
          (sampleAlphabet K).card
          (sampleLengthBudget K)
          d :=
      card_namedContextCandidates_le
        (sampleAlphabet K)
        (sampleLengthBudget K)
        d
    _ ≤
        namedContextEnumerationBound
          (sampleLengthBudget K)
          (sampleLengthBudget K)
          d :=
      namedContextEnumerationBound_mono_alphabet
        (card_sampleAlphabet_le_sampleLengthBudget K)
    _ =
        sampleLengthOnlyNamedContextBound
          (sampleLengthBudget K) d := by
      rfl

end LengthOnlyWordAndContextBounds


section LengthOnlyTupleAndUnitBounds

variable {α : Type u}
variable {M : Type v} [Monoid M]

/-- Default tuple-occurrence enumeration is controlled only by total sample
length and arity. -/
theorem card_tupleOccurrences_le_lengthOnly
    (K : Finset (Word α))
    (d : Nat) :
    (tupleOccurrences K d).card ≤
      sampleLengthOnlyTupleOccurrenceBound
        (sampleLengthBudget K) d := by
  calc
    (tupleOccurrences K d).card ≤
        tupleOccurrenceEnumerationBound
          (sampleAlphabet K).card
          (sampleLengthBudget K)
          d :=
      card_tupleOccurrences_le K d
    _ ≤
        tupleOccurrenceEnumerationBound
          (sampleLengthBudget K)
          (sampleLengthBudget K)
          d :=
      tupleOccurrenceEnumerationBound_mono_alphabet
        (card_sampleAlphabet_le_sampleLengthBudget K)
    _ =
        sampleLengthOnlyTupleOccurrenceBound
          (sampleLengthBudget K) d := by
      rfl

/-- Default unit-rule enumeration is controlled only by total sample length and
arity. -/
theorem card_concreteUnitRules_le_lengthOnly
    (K : Finset (Word α))
    (obs : α → M)
    (d : Nat) :
    (concreteUnitRules K obs d).card ≤
      sampleLengthOnlyUnitRuleBound
        (sampleLengthBudget K) d := by
  calc
    (concreteUnitRules K obs d).card ≤
        unitRuleEnumerationBound
          (sampleAlphabet K).card
          (sampleLengthBudget K)
          d :=
      card_concreteUnitRules_le
        K obs d
    _ ≤
        unitRuleEnumerationBound
          (sampleLengthBudget K)
          (sampleLengthBudget K)
          d :=
      unitRuleEnumerationBound_mono_alphabet
        (card_sampleAlphabet_le_sampleLengthBudget K)
    _ =
        sampleLengthOnlyUnitRuleBound
          (sampleLengthBudget K) d := by
      rfl

end LengthOnlyTupleAndUnitBounds


section LengthOnlyBinaryBounds

variable {α : Type u}

/-- Corrected binary-witness enumeration is controlled only by total sample
length and the three arities. -/
theorem card_correctedConcreteBinaryWitnesses_le_lengthOnly
    (K : Finset (Word α))
    (e dB dC : Nat) :
    (correctedConcreteBinaryWitnesses
        K e dB dC).card ≤
      sampleLengthOnlyCorrectedBinaryWitnessBound
        (sampleLengthBudget K)
        e dB dC := by
  calc
    (correctedConcreteBinaryWitnesses
        K e dB dC).card ≤
        correctedBinaryWitnessEnumerationBound
          (sampleAlphabet K).card
          (exactBinaryWitnessBudget K dB dC)
          e dB dC :=
      card_correctedConcreteBinaryWitnesses_le
        K e dB dC
    _ ≤
        correctedBinaryWitnessEnumerationBound
          (sampleLengthBudget K)
          (exactBinaryWitnessBudget K dB dC)
          e dB dC :=
      correctedBinaryWitnessEnumerationBound_mono_alphabet
        (card_sampleAlphabet_le_sampleLengthBudget K)
    _ =
        sampleLengthOnlyCorrectedBinaryWitnessBound
          (sampleLengthBudget K)
          e dB dC := by
      rfl

end LengthOnlyBinaryBounds


section LengthOnlyFanoutBounds

variable {α : Type u}
variable {M : Type v} [Monoid M]

/-- Total positive-arity unit-rule count up to fan-out `f`, bounded solely by
total sample length and `f`. -/
theorem concreteUnitRuleCountUpToFanout_le_lengthOnly
    (K : Finset (Word α))
    (obs : α → M)
    (f : Nat) :
    concreteUnitRuleCountUpToFanout
        K obs f ≤
      sampleLengthOnlyUnitRuleCountBound
        (sampleLengthBudget K) f := by
  unfold concreteUnitRuleCountUpToFanout
  unfold sampleLengthOnlyUnitRuleCountBound
  apply Finset.sum_le_sum
  intro d0 hd0
  exact
    card_concreteUnitRules_le_lengthOnly
      K obs (d0 + 1)

/-- Total corrected binary-rule count up to fan-out `f`, bounded solely by
total sample length and `f`. -/
theorem correctedBinaryRuleCountUpToFanout_le_lengthOnly
    (K : Finset (Word α))
    (f : Nat) :
    correctedBinaryRuleCountUpToFanout
        K f ≤
      sampleLengthOnlyCorrectedBinaryRuleCountBound
        (sampleLengthBudget K) f := by
  unfold correctedBinaryRuleCountUpToFanout
  unfold sampleLengthOnlyCorrectedBinaryRuleCountBound
  apply Finset.sum_le_sum
  intro e0 he0
  apply Finset.sum_le_sum
  intro dB0 hdB0
  apply Finset.sum_le_sum
  intro dC0 hdC0
  exact
    card_correctedConcreteBinaryWitnesses_le_lengthOnly
      K
      (e0 + 1)
      (dB0 + 1)
      (dC0 + 1)

/-- Final length-only rule-count estimate for the corrected concrete canonical
learner. -/
theorem correctedConcreteRuleCountUpToFanout_le_lengthOnly
    (K : Finset (Word α))
    (obs : α → M)
    (f : Nat) :
    correctedConcreteRuleCountUpToFanout
        K obs f ≤
      sampleLengthOnlyCorrectedRuleCountBound
        (sampleLengthBudget K) f := by
  unfold correctedConcreteRuleCountUpToFanout
  unfold sampleLengthOnlyCorrectedRuleCountBound
  exact Nat.add_le_add
    (concreteUnitRuleCountUpToFanout_le_lengthOnly
      K obs f)
    (correctedBinaryRuleCountUpToFanout_le_lengthOnly
      K f)

/-- The earlier alphabet-sensitive total bound is itself bounded by the new
length-only total bound. -/
theorem correctedConcreteRuleCountBound_le_lengthOnly
    (K : Finset (Word α))
    (f : Nat) :
    correctedConcreteRuleCountBound
        K f ≤
      sampleLengthOnlyCorrectedRuleCountBound
        (sampleLengthBudget K) f := by
  unfold correctedConcreteRuleCountBound
  unfold concreteUnitRuleCountBound
  unfold correctedBinaryRuleCountBound
  unfold sampleLengthOnlyCorrectedRuleCountBound
  unfold sampleLengthOnlyUnitRuleCountBound
  unfold sampleLengthOnlyCorrectedBinaryRuleCountBound

  apply Nat.add_le_add

  · apply Finset.sum_le_sum
    intro d0 hd0
    exact
      unitRuleEnumerationBound_mono_alphabet
        (card_sampleAlphabet_le_sampleLengthBudget K)

  · apply Finset.sum_le_sum
    intro e0 he0
    apply Finset.sum_le_sum
    intro dB0 hdB0
    apply Finset.sum_le_sum
    intro dC0 hdC0
    exact
      correctedBinaryWitnessEnumerationBound_mono_alphabet
        (card_sampleAlphabet_le_sampleLengthBudget K)

end LengthOnlyFanoutBounds


section PaperFacingBoundPackage

variable {α : Type u}
variable {M : Type v} [Monoid M]

/-- Paper-facing package: the actual finite rule count is bounded first by the
literal alphabet-sensitive enumeration expression and then by the simpler
length-only expression. -/
theorem correctedConcreteRuleCount_lengthOnly_conclusion_package
    (K : Finset (Word α))
    (obs : α → M)
    (f : Nat) :
    correctedConcreteRuleCountUpToFanout
          K obs f ≤
        correctedConcreteRuleCountBound K f ∧
      correctedConcreteRuleCountBound K f ≤
        sampleLengthOnlyCorrectedRuleCountBound
          (sampleLengthBudget K) f ∧
      correctedConcreteRuleCountUpToFanout
          K obs f ≤
        sampleLengthOnlyCorrectedRuleCountBound
          (sampleLengthBudget K) f := by
  exact
    ⟨correctedConcreteRuleCountUpToFanout_le
        K obs f,
      correctedConcreteRuleCountBound_le_lengthOnly
        K f,
      correctedConcreteRuleCountUpToFanout_le_lengthOnly
        K obs f⟩

end PaperFacingBoundPackage

end MCFG
