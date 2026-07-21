/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG.ConcreteCanonicalLearnerFiniteHypothesis

/-!
# ConcreteCanonicalLearnerFiniteHypothesisSize.lean

`ConcreteCanonicalLearnerFiniteHypothesis.lean` constructs an actual finite
dependent rule object:

```lean
correctedConcreteFiniteHypothesis K obs f.
```

This file proves cardinality bounds for that object itself.

The main steps are:

1. prove that `positiveArities f` has exactly `f` elements;
2. bound a dependent finite sigma by the number of indices times a uniform
   fiber bound;
3. apply this once to unit-rule codes and three times to binary-rule codes;
4. show that the actual `ruleCount` of the canonical finite hypothesis is
   bounded by the same single-power and paper-facing expressions established
   for the earlier numerical rule-count model.

The final explicit theorem is:

```lean
correctedConcreteFiniteHypothesis_ruleCount_le_explicit_paperPower
```

with conclusion

```lean
(correctedConcreteFiniteHypothesis K obs f).ruleCount ≤
  (4 * (sampleLengthBudget K + f + 1)) ^
    (64 *
      (sampleLengthBudget K + f + 1) *
      (sampleLengthBudget K + f + 1)).
```

Thus the verified size estimate now applies to the actual finite hypothesis
object whose language was proved equivalent to the corrected concrete learner.

No target grammar occurs in the bound.
No `sorry`, `admit`, or `axiom` is used.
-/

namespace MCFG

universe u v

section PositiveArityCardinality

/-- Positive arities at most `f` are exactly the successors of numbers below
`f`. -/
theorem positiveArities_eq_image_succ
    (f : Nat) :
    positiveArities f =
      (Finset.range f).image
        (fun k => k + 1) := by
  ext d
  simp only [
    positiveArities,
    Finset.mem_filter,
    Finset.mem_range,
    Finset.mem_image
  ]
  constructor

  · intro h
    rcases h with ⟨hdf, hpos⟩
    refine ⟨d - 1, ?_, ?_⟩
    · omega
    · omega

  · intro h
    rcases h with ⟨k, hk, rfl⟩
    constructor
    · omega
    · omega

/-- There are exactly `f` positive natural arities bounded by `f`. -/
@[simp] theorem card_positiveArities
    (f : Nat) :
    (positiveArities f).card = f := by
  rw [positiveArities_eq_image_succ]
  rw [Finset.card_image_of_injective]
  · simp
  · intro a b hab
    omega

/-- The attached positive-arity index set also has cardinality `f`. -/
@[simp] theorem card_positiveArities_attach
    (f : Nat) :
    (positiveArities f).attach.card = f := by
  simp

end PositiveArityCardinality


section DependentSigmaCardinality

/-- A dependent finite sigma is bounded by the number of indices times a
uniform fiber bound. -/
theorem card_finset_sigma_le_card_mul
    {ι : Type u}
    {β : ι → Type v}
    (s : Finset ι)
    (t : ∀ i, Finset (β i))
    (bound : Nat)
    (hbound :
      ∀ i ∈ s,
        (t i).card ≤ bound) :
    (s.sigma t).card ≤
      s.card * bound := by
  classical
  rw [Finset.card_sigma]
  calc
    (∑ i in s, (t i).card) ≤
        ∑ _i in s, bound := by
      apply Finset.sum_le_sum
      intro i hi
      exact hbound i hi
    _ = s.card * bound := by
      simp

/-- Two nested dependent sigma levels contribute at most the square of the
index-set cardinality. -/
theorem card_finset_sigma₂_le
    {ι : Type u}
    {β : ι → Type v}
    {γ : ∀ i, β i → Type u}
    (s : Finset ι)
    (t : ∀ i, Finset (β i))
    (r : ∀ i j, Finset (γ i j))
    (bound : Nat)
    (hbound :
      ∀ i ∈ s,
        ∀ j ∈ t i,
          (r i j).card ≤ bound) :
    (s.sigma
      (fun i =>
        (t i).sigma
          (fun j => r i j))).card ≤
      s.card *
        (s.card * bound) := by
  classical

  apply card_finset_sigma_le_card_mul
    s
    (fun i =>
      (t i).sigma
        (fun j => r i j))
    (s.card * bound)

  intro i hi

  calc
    ((t i).sigma
      (fun j => r i j)).card ≤
        (t i).card * bound :=
      card_finset_sigma_le_card_mul
        (t i)
        (fun j => r i j)
        bound
        (hbound i hi)
    _ ≤
        s.card * bound := by
      apply Nat.mul_le_mul_right
      exact Finset.card_le_card
        (by
          intro j hj
          exact hj)

/-- Three nested sigma levels over the same finite index set contribute at most
the cube of its cardinality. -/
theorem card_finset_sigma₃_sameIndex_le
    {ι : Type u}
    {δ : ι → ι → ι → Type v}
    (s : Finset ι)
    (r : ∀ i j k, Finset (δ i j k))
    (bound : Nat)
    (hbound :
      ∀ i ∈ s,
        ∀ j ∈ s,
          ∀ k ∈ s,
            (r i j k).card ≤ bound) :
    (s.sigma
      (fun i =>
        s.sigma
          (fun j =>
            s.sigma
              (fun k =>
                r i j k)))).card ≤
      s.card *
        (s.card *
          (s.card * bound)) := by
  classical

  apply card_finset_sigma_le_card_mul
    s
    (fun i =>
      s.sigma
        (fun j =>
          s.sigma
            (fun k =>
              r i j k)))
    (s.card *
      (s.card * bound))

  intro i hi

  apply card_finset_sigma_le_card_mul
    s
    (fun j =>
      s.sigma
        (fun k =>
          r i j k))
    (s.card * bound)

  intro j hj

  apply card_finset_sigma_le_card_mul
    s
    (fun k =>
      r i j k)
    bound

  intro k hk

  exact hbound i hi j hj k hk

end DependentSigmaCardinality


section UnitCodeSize

variable {α : Type u}
variable {M : Type v} [Monoid M]

/-- The finite dependent unit-rule code list has at most one fan-out factor
times the uniform unit-family bound. -/
theorem card_finiteCorrectedConcreteUnitRuleCodes_le_mul
    (K : Finset (Word α))
    (obs : α → M)
    (f : Nat) :
    (finiteCorrectedConcreteUnitRuleCodes
        K obs f).card ≤
      f *
        (uniformEnumerationBase
            (sampleLengthBudget K) f ^
          uniformUnitRuleExponent
            (sampleLengthBudget K) f) := by
  classical

  unfold finiteCorrectedConcreteUnitRuleCodes

  have hsigma :
      ((positiveArities f).attach.sigma
        (fun d =>
          (concreteUnitRules
            K obs d.arity).attach)).card ≤
        (positiveArities f).attach.card *
          (uniformEnumerationBase
              (sampleLengthBudget K) f ^
            uniformUnitRuleExponent
              (sampleLengthBudget K) f) := by

    apply card_finset_sigma_le_card_mul

    intro d hd

    simpa using
      (card_concreteUnitRules_le_lengthOnly
        K obs d.arity).trans
        (sampleLengthOnlyUnitRuleBound_le_uniform
          d.le_fanout)

  simpa using hsigma

/-- The finite dependent unit-rule code list is absorbed by one additional
power of the common base. -/
theorem card_finiteCorrectedConcreteUnitRuleCodes_le_uniform
    (K : Finset (Word α))
    (obs : α → M)
    (f : Nat) :
    (finiteCorrectedConcreteUnitRuleCodes
        K obs f).card ≤
      uniformEnumerationBase
          (sampleLengthBudget K) f ^
        (uniformUnitRuleExponent
            (sampleLengthBudget K) f + 1) := by

  let base :=
    uniformEnumerationBase
      (sampleLengthBudget K) f

  let exponent :=
    uniformUnitRuleExponent
      (sampleLengthBudget K) f

  calc
    (finiteCorrectedConcreteUnitRuleCodes
        K obs f).card ≤
        f * (base ^ exponent) :=
      card_finiteCorrectedConcreteUnitRuleCodes_le_mul
        K obs f
    _ ≤
        base * (base ^ exponent) :=
      Nat.mul_le_mul_right
        (base ^ exponent)
        (UniformParameters.fanout_le_base
          (sampleLengthBudget K) f)
    _ =
        base ^ (exponent + 1) := by
      simpa [Nat.pow_add_one', Nat.mul_comm]

end UnitCodeSize


section BinaryCodeSize

variable {α : Type u}

/-- The finite dependent binary-rule code list has at most three fan-out
factors times the uniform binary-family bound. -/
theorem card_finiteCorrectedConcreteBinaryRuleCodes_le_mul
    (K : Finset (Word α))
    (f : Nat) :
    (finiteCorrectedConcreteBinaryRuleCodes
        K f).card ≤
      f *
        (f *
          (f *
            (uniformEnumerationBase
                (sampleLengthBudget K) f ^
              uniformBinaryRuleExponent
                (sampleLengthBudget K) f))) := by
  classical

  unfold finiteCorrectedConcreteBinaryRuleCodes

  have hsigma :
      ((positiveArities f).attach.sigma
        (fun e =>
          (positiveArities f).attach.sigma
            (fun dB =>
              (positiveArities f).attach.sigma
                (fun dC =>
                  (correctedConcreteBinaryWitnesses
                    K e.arity
                      dB.arity dC.arity).attach)))).card ≤
        (positiveArities f).attach.card *
          ((positiveArities f).attach.card *
            ((positiveArities f).attach.card *
              (uniformEnumerationBase
                  (sampleLengthBudget K) f ^
                uniformBinaryRuleExponent
                  (sampleLengthBudget K) f))) := by

    apply card_finset_sigma₃_sameIndex_le

    intro e he dB hdB dC hdC

    simpa using
      (card_correctedConcreteBinaryWitnesses_le_lengthOnly
        K e.arity dB.arity dC.arity).trans
        (sampleLengthOnlyCorrectedBinaryWitnessBound_le_uniform
          e.le_fanout
          dB.le_fanout
          dC.le_fanout)

  simpa using hsigma

/-- The finite dependent binary-rule code list is absorbed by three additional
powers of the common base. -/
theorem card_finiteCorrectedConcreteBinaryRuleCodes_le_uniform
    (K : Finset (Word α))
    (f : Nat) :
    (finiteCorrectedConcreteBinaryRuleCodes
        K f).card ≤
      uniformEnumerationBase
          (sampleLengthBudget K) f ^
        (uniformBinaryRuleExponent
            (sampleLengthBudget K) f + 3) := by

  let base :=
    uniformEnumerationBase
      (sampleLengthBudget K) f

  let exponent :=
    uniformBinaryRuleExponent
      (sampleLengthBudget K) f

  have hf :
      f ≤ base :=
    UniformParameters.fanout_le_base
      (sampleLengthBudget K) f

  have hmul :
      f *
          (f *
            (f * (base ^ exponent))) ≤
        base *
          (base *
            (base * (base ^ exponent))) :=
    Nat.mul_le_mul hf
      (Nat.mul_le_mul hf
        (Nat.mul_le_mul hf
          (Nat.le_refl _)))

  calc
    (finiteCorrectedConcreteBinaryRuleCodes
        K f).card ≤
        f *
          (f *
            (f * (base ^ exponent))) :=
      card_finiteCorrectedConcreteBinaryRuleCodes_le_mul
        K f
    _ ≤
        base *
          (base *
            (base * (base ^ exponent))) :=
      hmul
    _ =
        base ^ (exponent + 3) := by
      simp [
        Nat.pow_add,
        pow_succ,
        Nat.mul_assoc,
        Nat.mul_comm,
        Nat.mul_left_comm
      ]

end BinaryCodeSize


section CanonicalFiniteHypothesisSize

variable {α : Type u}
variable {M : Type v} [Monoid M]

/-- The actual canonical finite-hypothesis rule count is the sum of the two
finite dependent code-list cardinalities. -/
@[simp] theorem correctedConcreteFiniteHypothesis_ruleCount_eq
    (K : Finset (Word α))
    (obs : α → M)
    (f : Nat) :
    (correctedConcreteFiniteHypothesis
        K obs f).ruleCount =
      (finiteCorrectedConcreteUnitRuleCodes
          K obs f).card +
        (finiteCorrectedConcreteBinaryRuleCodes
          K f).card :=
  rfl

/-- The actual finite-hypothesis rule count satisfies the proof-oriented
single-power estimate. -/
theorem correctedConcreteFiniteHypothesis_ruleCount_le_singlePower
    (K : Finset (Word α))
    (obs : α → M)
    (f : Nat) :
    (correctedConcreteFiniteHypothesis
        K obs f).ruleCount ≤
      singlePowerCorrectedRuleCountBound
        (sampleLengthBudget K) f := by

  let base :=
    uniformEnumerationBase
      (sampleLengthBudget K) f

  let unitExponent :=
    uniformUnitRuleExponent
      (sampleLengthBudget K) f + 1

  let binaryExponent :=
    uniformBinaryRuleExponent
      (sampleLengthBudget K) f + 3

  let commonExponent :=
    max unitExponent binaryExponent

  have hbase :
      1 < base :=
    UniformParameters.base_gt_one
      (sampleLengthBudget K) f

  have hunit :
      (finiteCorrectedConcreteUnitRuleCodes
          K obs f).card ≤
        base ^ unitExponent :=
    card_finiteCorrectedConcreteUnitRuleCodes_le_uniform
      K obs f

  have hbinary :
      (finiteCorrectedConcreteBinaryRuleCodes
          K f).card ≤
        base ^ binaryExponent :=
    card_finiteCorrectedConcreteBinaryRuleCodes_le_uniform
      K f

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

  rw [correctedConcreteFiniteHypothesis_ruleCount_eq]

  unfold singlePowerCorrectedRuleCountBound
  unfold uniformRuleExponent

  calc
    (finiteCorrectedConcreteUnitRuleCodes
          K obs f).card +
        (finiteCorrectedConcreteBinaryRuleCodes
          K f).card ≤
        base ^ commonExponent +
          base ^ commonExponent :=
      Nat.add_le_add
        (hunit.trans hunitCommon)
        (hbinary.trans hbinaryCommon)
    _ ≤
        base * (base ^ commonExponent) := by
      apply Nat.mul_le_mul_right
      exact UniformParameters.two_le_base
        (sampleLengthBudget K) f
    _ =
        base ^ (commonExponent + 1) := by
      simpa [Nat.pow_add_one', Nat.mul_comm]

/-- The actual finite-hypothesis rule count satisfies the exact expanded
polynomial-exponent estimate. -/
theorem correctedConcreteFiniteHypothesis_ruleCount_le_expandedPower
    (K : Finset (Word α))
    (obs : α → M)
    (f : Nat) :
    (correctedConcreteFiniteHypothesis
        K obs f).ruleCount ≤
      expandedSinglePowerCorrectedRuleCountBound
        (sampleLengthBudget K) f := by

  calc
    (correctedConcreteFiniteHypothesis
        K obs f).ruleCount ≤
        singlePowerCorrectedRuleCountBound
          (sampleLengthBudget K) f :=
      correctedConcreteFiniteHypothesis_ruleCount_le_singlePower
        K obs f
    _ =
        expandedSinglePowerCorrectedRuleCountBound
          (sampleLengthBudget K) f :=
      singlePowerCorrectedRuleCountBound_eq_expanded
        (sampleLengthBudget K) f

/-- The actual finite-hypothesis rule count satisfies the simpler paper-facing
linear-base, quadratic-exponent estimate. -/
theorem correctedConcreteFiniteHypothesis_ruleCount_le_paperBound
    (K : Finset (Word α))
    (obs : α → M)
    (f : Nat) :
    (correctedConcreteFiniteHypothesis
        K obs f).ruleCount ≤
      correctedLearnerPaperRuleCountBound
        (sampleLengthBudget K) f := by

  exact
    (correctedConcreteFiniteHypothesis_ruleCount_le_singlePower
      K obs f).trans
      (singlePowerCorrectedRuleCountBound_le_paper
        (sampleLengthBudget K) f)

/-- Fully expanded paper-facing estimate for the actual finite hypothesis
object. -/
theorem correctedConcreteFiniteHypothesis_ruleCount_le_explicit_paperPower
    (K : Finset (Word α))
    (obs : α → M)
    (f : Nat) :
    (correctedConcreteFiniteHypothesis
        K obs f).ruleCount ≤
      (4 * (sampleLengthBudget K + f + 1)) ^
        (64 *
          (sampleLengthBudget K + f + 1) *
          (sampleLengthBudget K + f + 1)) :=
  correctedConcreteFiniteHypothesis_ruleCount_le_paperBound
    K obs f

/-- Exact expanded exponent for the actual finite hypothesis object. -/
theorem correctedConcreteFiniteHypothesis_ruleCount_exactExponent_explicit
    (K : Finset (Word α))
    (obs : α → M)
    (f : Nat) :
    (correctedConcreteFiniteHypothesis
        K obs f).ruleCount ≤
      (2 * sampleLengthBudget K + 4 * f + 3) ^
        (14 * f * f +
          7 * sampleLengthBudget K * f +
          16 * f +
          3 * sampleLengthBudget K +
          7) :=
  correctedConcreteFiniteHypothesis_ruleCount_le_expandedPower
    K obs f

end CanonicalFiniteHypothesisSize


section SemanticSizePackage

variable {α : Type u}
variable {M : Type v} [Monoid M]

/-- Paper-facing package joining the actual finite hypothesis object, its
language semantics, and its explicit finite size estimate. -/
theorem correctedConcreteFiniteHypothesis_size_semantic_package
    (K : Finset (Word α))
    (obs : α → M)
    (f : Nat) :
    FiniteCorrectedConcreteLearnerLanguage
          K obs f =
        CorrectedConcreteCanonicalLearnerLanguage
          K obs f ∧
      FiniteCorrectedConcreteLearnerLanguage
          K obs f =
        ExactReachableSampleStringLanguage
          K obs f ∧
      (correctedConcreteFiniteHypothesis
          K obs f).ruleCount ≤
        (4 * (sampleLengthBudget K + f + 1)) ^
          (64 *
            (sampleLengthBudget K + f + 1) *
            (sampleLengthBudget K + f + 1)) := by

  exact
    ⟨finiteCorrectedConcreteLearnerLanguage_eq
        K obs f,
      finiteCorrectedConcreteLearnerLanguage_eq_exactReachable
        K obs f,
      correctedConcreteFiniteHypothesis_ruleCount_le_explicit_paperPower
        K obs f⟩

end SemanticSizePackage

end MCFG
