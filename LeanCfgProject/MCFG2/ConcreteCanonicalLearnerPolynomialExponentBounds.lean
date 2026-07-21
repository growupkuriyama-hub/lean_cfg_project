/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG2.ConcreteCanonicalLearnerSinglePowerBounds

/-!
# ConcreteCanonicalLearnerPolynomialExponentBounds.lean

The preceding file compresses the exhaustive corrected concrete learner into
the single-power bound

```lean
uniformEnumerationBase s f ^ uniformRuleExponent s f.
```

The definitions are convenient for the proof but not ideal for a paper
statement.  This file proves that the exponent has the exact closed form

```lean
14 * f * f + 7 * s * f + 16 * f + 3 * s + 7.
```

It then derives the simpler coarse estimate

```lean
(4 * (s + f + 1)) ^
  (64 * (s + f + 1) * (s + f + 1)).
```

Thus the actual rule count of the corrected finite learner is bounded by one
explicit power whose base is linear in total sample length and fan-out and whose
exponent is quadratic in those parameters.

These are size bounds for the current exhaustive enumerator.  They do not claim
polynomial running time.

No target grammar occurs in the bound.
No `sorry`, `admit`, or `axiom` is used.
-/

namespace MCFG

universe u v

section ExactExponentExpansion

/-- Closed polynomial form of the exponent hidden in
`uniformRuleExponent`. -/
def expandedUniformRuleExponent
    (sampleLength f : Nat) :
    Nat :=
  14 * f * f +
    7 * sampleLength * f +
    16 * f +
    3 * sampleLength +
    7

/-- The binary-family exponent always dominates the unit-family exponent after
the range-absorption constants have been added. -/
theorem uniformUnitRuleExponent_add_one_le_binary_add_three
    (sampleLength f : Nat) :
    uniformUnitRuleExponent sampleLength f + 1 ≤
      uniformBinaryRuleExponent sampleLength f + 3 := by
  simp only [
    uniformUnitRuleExponent,
    uniformBinaryRuleExponent
  ]
  omega

/-- Exact expansion of the final rule exponent. -/
theorem uniformRuleExponent_eq_expanded
    (sampleLength f : Nat) :
    uniformRuleExponent sampleLength f =
      expandedUniformRuleExponent
        sampleLength f := by

  have hmax :
      uniformUnitRuleExponent sampleLength f + 1 ≤
        uniformBinaryRuleExponent sampleLength f + 3 :=
    uniformUnitRuleExponent_add_one_le_binary_add_three
      sampleLength f

  unfold uniformRuleExponent
  rw [max_eq_right hmax]

  simp only [
    uniformBinaryRuleExponent,
    uniformOccurrenceExponent,
    uniformWordExponent,
    expandedUniformRuleExponent
  ]

  ring

/-- Single-power bound with the common base and the exponent written as an
explicit polynomial. -/
def expandedSinglePowerCorrectedRuleCountBound
    (sampleLength f : Nat) :
    Nat :=
  (2 * sampleLength + 4 * f + 3) ^
    expandedUniformRuleExponent
      sampleLength f

/-- The proof-oriented single-power bound is definitionally equal, after the
exponent calculation, to the explicit polynomial-exponent bound. -/
theorem singlePowerCorrectedRuleCountBound_eq_expanded
    (sampleLength f : Nat) :
    singlePowerCorrectedRuleCountBound
        sampleLength f =
      expandedSinglePowerCorrectedRuleCountBound
        sampleLength f := by
  unfold singlePowerCorrectedRuleCountBound
  unfold expandedSinglePowerCorrectedRuleCountBound
  unfold uniformEnumerationBase
  rw [uniformRuleExponent_eq_expanded]

end ExactExponentExpansion


section PaperScaleBound

/-- One paper-facing scale combining total sample length and fan-out. -/
def correctedLearnerPaperScale
    (sampleLength f : Nat) :
    Nat :=
  sampleLength + f + 1

/-- Linear paper-facing base. -/
def correctedLearnerPaperBase
    (sampleLength f : Nat) :
    Nat :=
  4 * correctedLearnerPaperScale
    sampleLength f

/-- Quadratic paper-facing exponent. -/
def correctedLearnerPaperExponent
    (sampleLength f : Nat) :
    Nat :=
  64 *
    correctedLearnerPaperScale sampleLength f *
    correctedLearnerPaperScale sampleLength f

/-- Coarse single-power rule-count bound suitable for a theorem statement. -/
def correctedLearnerPaperRuleCountBound
    (sampleLength f : Nat) :
    Nat :=
  correctedLearnerPaperBase sampleLength f ^
    correctedLearnerPaperExponent
      sampleLength f

/-- Explicit nonnegative slack between the quadratic paper exponent and the
exact expanded exponent. -/
def correctedLearnerPaperExponentSlack
    (sampleLength f : Nat) :
    Nat :=
  64 * sampleLength * sampleLength +
    121 * sampleLength * f +
    50 * f * f +
    125 * sampleLength +
    112 * f +
    57

/-- The paper exponent is exactly the expanded exponent plus an explicit
nonnegative slack. -/
theorem correctedLearnerPaperExponent_eq_expanded_add_slack
    (sampleLength f : Nat) :
    correctedLearnerPaperExponent
        sampleLength f =
      expandedUniformRuleExponent
          sampleLength f +
        correctedLearnerPaperExponentSlack
          sampleLength f := by
  unfold correctedLearnerPaperExponent
  unfold correctedLearnerPaperScale
  unfold expandedUniformRuleExponent
  unfold correctedLearnerPaperExponentSlack
  ring

/-- The exact exponent is bounded by the simpler quadratic paper exponent. -/
theorem expandedUniformRuleExponent_le_paperExponent
    (sampleLength f : Nat) :
    expandedUniformRuleExponent
        sampleLength f ≤
      correctedLearnerPaperExponent
        sampleLength f := by

  rw [
    correctedLearnerPaperExponent_eq_expanded_add_slack
  ]

  omega

/-- The original uniform exponent is bounded by the quadratic paper exponent. -/
theorem uniformRuleExponent_le_paperExponent
    (sampleLength f : Nat) :
    uniformRuleExponent
        sampleLength f ≤
      correctedLearnerPaperExponent
        sampleLength f := by
  rw [uniformRuleExponent_eq_expanded]
  exact
    expandedUniformRuleExponent_le_paperExponent
      sampleLength f

/-- The proof-oriented linear base is bounded by the simpler paper base. -/
theorem uniformEnumerationBase_le_paperBase
    (sampleLength f : Nat) :
    uniformEnumerationBase
        sampleLength f ≤
      correctedLearnerPaperBase
        sampleLength f := by
  unfold uniformEnumerationBase
  unfold correctedLearnerPaperBase
  unfold correctedLearnerPaperScale
  omega

/-- The paper base is always greater than one. -/
theorem correctedLearnerPaperBase_gt_one
    (sampleLength f : Nat) :
    1 <
      correctedLearnerPaperBase
        sampleLength f := by
  unfold correctedLearnerPaperBase
  unfold correctedLearnerPaperScale
  omega

/-- The exact polynomial-exponent single power is bounded by the simpler
paper-facing single power. -/
theorem expandedSinglePowerCorrectedRuleCountBound_le_paper
    (sampleLength f : Nat) :
    expandedSinglePowerCorrectedRuleCountBound
        sampleLength f ≤
      correctedLearnerPaperRuleCountBound
        sampleLength f := by

  unfold expandedSinglePowerCorrectedRuleCountBound
  unfold correctedLearnerPaperRuleCountBound

  exact nat_pow_le_pow_mixed
    (by
      simpa [uniformEnumerationBase] using
        uniformEnumerationBase_le_paperBase
          sampleLength f)
    (correctedLearnerPaperBase_gt_one
      sampleLength f)
    (expandedUniformRuleExponent_le_paperExponent
      sampleLength f)

/-- The proof-oriented single-power bound is bounded by the simpler
paper-facing bound. -/
theorem singlePowerCorrectedRuleCountBound_le_paper
    (sampleLength f : Nat) :
    singlePowerCorrectedRuleCountBound
        sampleLength f ≤
      correctedLearnerPaperRuleCountBound
        sampleLength f := by
  rw [
    singlePowerCorrectedRuleCountBound_eq_expanded
  ]
  exact
    expandedSinglePowerCorrectedRuleCountBound_le_paper
      sampleLength f

end PaperScaleBound


section ActualRuleCountPolynomialBounds

variable {α : Type u}
variable {M : Type v} [Monoid M]

/-- Actual corrected concrete rule count bounded by the common linear base with
the exact expanded quadratic exponent. -/
theorem correctedConcreteRuleCountUpToFanout_le_expandedPower
    (K : Finset (Word α))
    (obs : α → M)
    (f : Nat) :
    correctedConcreteRuleCountUpToFanout
        K obs f ≤
      expandedSinglePowerCorrectedRuleCountBound
        (sampleLengthBudget K) f := by

  calc
    correctedConcreteRuleCountUpToFanout
          K obs f ≤
        singlePowerCorrectedRuleCountBound
          (sampleLengthBudget K) f :=
      correctedConcreteRuleCountUpToFanout_le_singlePower
        K obs f
    _ =
        expandedSinglePowerCorrectedRuleCountBound
          (sampleLengthBudget K) f :=
      singlePowerCorrectedRuleCountBound_eq_expanded
        (sampleLengthBudget K) f

/-- Final paper-facing rule-count estimate:

```lean
ruleCount(K, obs, f) ≤
  (4 * (sampleLengthBudget K + f + 1)) ^
    (64 * (sampleLengthBudget K + f + 1)^2).
```
-/
theorem correctedConcreteRuleCountUpToFanout_le_paperBound
    (K : Finset (Word α))
    (obs : α → M)
    (f : Nat) :
    correctedConcreteRuleCountUpToFanout
        K obs f ≤
      correctedLearnerPaperRuleCountBound
        (sampleLengthBudget K) f := by

  exact
    (correctedConcreteRuleCountUpToFanout_le_singlePower
      K obs f).trans
      (singlePowerCorrectedRuleCountBound_le_paper
        (sampleLengthBudget K) f)

/-- Expanded statement of the final paper-facing inequality. -/
theorem correctedConcreteRuleCountUpToFanout_le_explicit_paperPower
    (K : Finset (Word α))
    (obs : α → M)
    (f : Nat) :
    correctedConcreteRuleCountUpToFanout
        K obs f ≤
      (4 * (sampleLengthBudget K + f + 1)) ^
        (64 *
          (sampleLengthBudget K + f + 1) *
          (sampleLengthBudget K + f + 1)) := by

  exact
    correctedConcreteRuleCountUpToFanout_le_paperBound
      K obs f

/-- Complete hierarchy from the actual enumerated rule count to the exact
polynomial exponent and then to the simpler paper-facing power. -/
theorem correctedConcreteRuleCount_polynomialExponent_conclusion_package
    (K : Finset (Word α))
    (obs : α → M)
    (f : Nat) :
    correctedConcreteRuleCountUpToFanout
          K obs f ≤
        expandedSinglePowerCorrectedRuleCountBound
          (sampleLengthBudget K) f ∧
      expandedSinglePowerCorrectedRuleCountBound
          (sampleLengthBudget K) f ≤
        correctedLearnerPaperRuleCountBound
          (sampleLengthBudget K) f ∧
      correctedConcreteRuleCountUpToFanout
          K obs f ≤
        correctedLearnerPaperRuleCountBound
          (sampleLengthBudget K) f := by

  exact
    ⟨correctedConcreteRuleCountUpToFanout_le_expandedPower
        K obs f,
      expandedSinglePowerCorrectedRuleCountBound_le_paper
        (sampleLengthBudget K) f,
      correctedConcreteRuleCountUpToFanout_le_paperBound
        K obs f⟩

end ActualRuleCountPolynomialBounds


section PaperReadableCorollaries

variable {α : Type u}
variable {M : Type v} [Monoid M]

/-- For fixed fan-out, the verified exhaustive rule-count estimate is an
explicit exponential in a quadratic polynomial of total sample length.

This theorem records the exact elementary expression rather than introducing
asymptotic notation. -/
theorem correctedConcreteRuleCount_fixedFanout_explicit
    (K : Finset (Word α))
    (obs : α → M)
    (f : Nat) :
    correctedConcreteRuleCountUpToFanout
        K obs f ≤
      (4 * (sampleLengthBudget K + f + 1)) ^
        (64 *
          (sampleLengthBudget K + f + 1) *
          (sampleLengthBudget K + f + 1)) :=
  correctedConcreteRuleCountUpToFanout_le_explicit_paperPower
    K obs f

/-- The exact exponent used before coarse simplification. -/
theorem correctedConcreteRuleCount_exactExponent_explicit
    (K : Finset (Word α))
    (obs : α → M)
    (f : Nat) :
    correctedConcreteRuleCountUpToFanout
        K obs f ≤
      (2 * sampleLengthBudget K + 4 * f + 3) ^
        (14 * f * f +
          7 * sampleLengthBudget K * f +
          16 * f +
          3 * sampleLengthBudget K +
          7) := by

  exact
    correctedConcreteRuleCountUpToFanout_le_expandedPower
      K obs f

end PaperReadableCorollaries

end MCFG
