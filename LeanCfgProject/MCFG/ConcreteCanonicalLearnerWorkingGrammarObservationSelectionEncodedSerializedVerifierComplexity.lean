/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG.ConcreteCanonicalLearnerWorkingGrammarObservationSelectionEncodedSerializedVerifier

/-!
# ConcreteCanonicalLearnerWorkingGrammarObservationSelectionEncodedSerializedVerifierComplexity.lean

The preceding file defines ordinary-cost and Pareto decisions that receive only
a serialized `List Nat`.  This file equips those serialized verifiers with one
explicit input-length resource model.

For every serialized input `input`, define

```text
serializedInputSize input = input.length + 1
```

and use the common linear work envelope

```text
3 * serializedInputSize input.
```

The factor three accounts abstractly for

* checked decoding and payload-length validation;
* one scan through the relevant membership bit vector;
* constant Boolean and branching overhead.

The work value is defined for every input, including malformed inputs.  The
machine output itself is exactly the executable serialized decision from the
preceding file.

We prove:

* ordinary and Pareto serialized machines preserve the previous Boolean output;
* both have degree-one polynomial work with coefficient three;
* the combined two-decision execution has work bounded by coefficient six;
* on a serialized encoded instance, the input-size formula is exact;
* on the canonical observation-selection instance the input size is

```text
(2 + (2 ^ U.card + 2 ^ U.card)) + 1;
```

* at the exact semantic positive-additive minimum rank, both decisions accept
  and satisfy the same explicit linear work formula.

This is a polynomial work theorem in the length of the already materialized
serialized table.  That serialized input has exponential length in `U.card`,
and its construction from the semantic table remains noncomputable.  Thus this
file does not claim a compact-input polynomial-time algorithm, formal NP
membership, NP-hardness, or NP-completeness.

No target grammar is supplied to any learner.
No `sorry`, `admit`, or `axiom` is used.
-/

namespace MCFG

universe u v w z


namespace CorrectedConcreteEncodedObservationSelectionData

section SerializedVerifierResourceModel

/-- Explicit size of a serialized verifier input.

The added unit avoids a zero-size corner case and is convenient for polynomial
resource envelopes. -/
def serializedInputSize
    (input : List Nat) : Nat :=
  input.length + 1

/-- Common degree-one work envelope for one serialized decision. -/
def serializedDecisionWork
    (input : List Nat) : Nat :=
  3 * serializedInputSize input

/-- Degree of the serialized verifier work polynomial. -/
def serializedDecisionWorkDegree : Nat :=
  1

/-- Coefficient of the serialized verifier work polynomial. -/
def serializedDecisionWorkCoefficient : Nat :=
  3

/-- Ordinary serialized verifier paired with its resource count. -/
def runSerializedCostDecisionWithWork
    (input : List Nat) : Bool × Nat :=
  (runSerializedCostDecision input,
    serializedDecisionWork input)

/-- Pareto serialized verifier paired with its resource count. -/
def runSerializedParetoDecisionWithWork
    (input : List Nat) : Bool × Nat :=
  (runSerializedParetoDecision input,
    serializedDecisionWork input)

/-- Combined ordinary/Pareto serialized verifier execution.

Both decisions read the same serialized input.  The work counter records the
sum of the two degree-one envelopes. -/
def runSerializedDecisionPairWithWork
    (input : List Nat) :
    (Bool × Bool) × Nat :=
  (runSerializedDecisionPair input,
    serializedDecisionWork input +
      serializedDecisionWork input)

@[simp]
theorem runSerializedCostDecisionWithWork_fst
    (input : List Nat) :
    (runSerializedCostDecisionWithWork input).1 =
      runSerializedCostDecision input := by

  rfl

@[simp]
theorem runSerializedCostDecisionWithWork_snd
    (input : List Nat) :
    (runSerializedCostDecisionWithWork input).2 =
      serializedDecisionWork input := by

  rfl

@[simp]
theorem runSerializedParetoDecisionWithWork_fst
    (input : List Nat) :
    (runSerializedParetoDecisionWithWork input).1 =
      runSerializedParetoDecision input := by

  rfl

@[simp]
theorem runSerializedParetoDecisionWithWork_snd
    (input : List Nat) :
    (runSerializedParetoDecisionWithWork input).2 =
      serializedDecisionWork input := by

  rfl

@[simp]
theorem runSerializedDecisionPairWithWork_fst
    (input : List Nat) :
    (runSerializedDecisionPairWithWork input).1 =
      runSerializedDecisionPair input := by

  rfl

@[simp]
theorem runSerializedDecisionPairWithWork_snd
    (input : List Nat) :
    (runSerializedDecisionPairWithWork input).2 =
      serializedDecisionWork input +
        serializedDecisionWork input := by

  rfl

/-- The single-decision work is exactly a degree-one polynomial in the
serialized input size. -/
theorem serializedDecisionWork_polynomial
    (input : List Nat) :
    serializedDecisionWork input =
      serializedDecisionWorkCoefficient *
        (serializedInputSize input) ^
          serializedDecisionWorkDegree := by

  simp [
    serializedDecisionWork,
    serializedDecisionWorkCoefficient,
    serializedDecisionWorkDegree
  ]

/-- Ordinary serialized verification satisfies the common linear resource
formula. -/
theorem runSerializedCostDecisionWithWork_linear
    (input : List Nat) :
    (runSerializedCostDecisionWithWork input).2 =
      3 * serializedInputSize input := by

  rfl

/-- Pareto serialized verification satisfies the common linear resource
formula. -/
theorem runSerializedParetoDecisionWithWork_linear
    (input : List Nat) :
    (runSerializedParetoDecisionWithWork input).2 =
      3 * serializedInputSize input := by

  rfl

/-- The combined execution has coefficient six and degree one. -/
theorem runSerializedDecisionPairWithWork_linear
    (input : List Nat) :
    (runSerializedDecisionPairWithWork input).2 =
      6 * serializedInputSize input := by

  unfold runSerializedDecisionPairWithWork
  unfold serializedDecisionWork

  omega

/-- Malformed ordinary inputs are rejected while retaining the same linear
work envelope. -/
theorem runSerializedCostDecisionWithWork_rejects_decode_none
    {input : List Nat}
    (hDecode :
      decode input = none) :
    (runSerializedCostDecisionWithWork input).1 = false ∧
      (runSerializedCostDecisionWithWork input).2 =
        3 * serializedInputSize input := by

  exact
    ⟨by
        simpa using
          runSerializedCostDecision_eq_false_of_decode_none
            hDecode,
      rfl⟩

/-- Malformed Pareto inputs are rejected while retaining the same linear work
envelope. -/
theorem runSerializedParetoDecisionWithWork_rejects_decode_none
    {input : List Nat}
    (hDecode :
      decode input = none) :
    (runSerializedParetoDecisionWithWork input).1 = false ∧
      (runSerializedParetoDecisionWithWork input).2 =
        3 * serializedInputSize input := by

  exact
    ⟨by
        simpa using
          runSerializedParetoDecision_eq_false_of_decode_none
            hDecode,
      rfl⟩

/-- Generic serialized verifier resource package. -/
theorem serializedVerifierComplexity_package
    (input : List Nat) :
    (runSerializedCostDecisionWithWork input).1 =
        runSerializedCostDecision input ∧
      (runSerializedParetoDecisionWithWork input).1 =
        runSerializedParetoDecision input ∧
      (runSerializedCostDecisionWithWork input).2 =
        3 * serializedInputSize input ∧
      (runSerializedParetoDecisionWithWork input).2 =
        3 * serializedInputSize input ∧
      (runSerializedDecisionPairWithWork input).2 =
        6 * serializedInputSize input := by

  exact
    ⟨rfl,
      rfl,
      rfl,
      rfl,
      runSerializedDecisionPairWithWork_linear input⟩

end SerializedVerifierResourceModel

end CorrectedConcreteEncodedObservationSelectionData


namespace CorrectedConcreteEncodedObservationSelectionInstance

section SerializedInstanceResourceFormulas

variable {α : Type u}
variable {ι : Type v}
variable {M : Type w}
variable [DecidableEq ι]
variable [Monoid M]
variable {obsFamily : ι → α → M}
variable {f : Nat}
variable {selectionCost : Finset ι → Nat}
variable {U : Finset ι}
variable {language : Set (Word α)}
variable
  {table :
    CorrectedConcreteObservationSelectionDecisionTable
      (z := z)
      obsFamily
      f
      selectionCost
      U
      language}
variable
  (instance :
    CorrectedConcreteEncodedObservationSelectionInstance
      table)

/-- Exact serialized input size of a proof-carrying encoded instance. -/
theorem serialize_inputSize :
    CorrectedConcreteEncodedObservationSelectionData.serializedInputSize
        instance.serialize =
      (2 + (instance.codeBound + instance.codeBound)) + 1 := by

  unfold CorrectedConcreteEncodedObservationSelectionData.serializedInputSize

  rw [instance.serialize_length]

/-- Exact ordinary serialized-verifier work on a serialized encoded instance. -/
theorem serialize_costDecisionWork :
    (CorrectedConcreteEncodedObservationSelectionData.runSerializedCostDecisionWithWork
      instance.serialize).2 =
        3 *
          ((2 +
              (instance.codeBound + instance.codeBound)) +
            1) := by

  rw [
    CorrectedConcreteEncodedObservationSelectionData.runSerializedCostDecisionWithWork_linear,
    instance.serialize_inputSize
  ]

/-- Exact Pareto serialized-verifier work on a serialized encoded instance. -/
theorem serialize_paretoDecisionWork :
    (CorrectedConcreteEncodedObservationSelectionData.runSerializedParetoDecisionWithWork
      instance.serialize).2 =
        3 *
          ((2 +
              (instance.codeBound + instance.codeBound)) +
            1) := by

  rw [
    CorrectedConcreteEncodedObservationSelectionData.runSerializedParetoDecisionWithWork_linear,
    instance.serialize_inputSize
  ]

/-- The work-instrumented ordinary serialized verifier agrees with the semantic
table decision. -/
theorem serialize_costDecisionWithWork_eq_true_iff_tableDecision :
    (CorrectedConcreteEncodedObservationSelectionData.runSerializedCostDecisionWithWork
      instance.serialize).1 =
        true ↔
      table.costFeasibleDecision instance.budget = true := by

  exact
    instance.runSerializedCostDecision_serialize_iff_tableDecision

/-- The work-instrumented Pareto serialized verifier agrees with the semantic
table decision. -/
theorem serialize_paretoDecisionWithWork_eq_true_iff_tableDecision :
    (CorrectedConcreteEncodedObservationSelectionData.runSerializedParetoDecisionWithWork
      instance.serialize).1 =
        true ↔
      table.paretoScalarFeasibleDecision
          instance.budget =
        true := by

  exact
    instance.runSerializedParetoDecision_serialize_iff_tableDecision

/-- Complete serialized-instance resource package. -/
theorem serializedVerifierComplexity_package :
    CorrectedConcreteEncodedObservationSelectionData.decode
          instance.serialize =
        some instance.toSerializedData ∧
      CorrectedConcreteEncodedObservationSelectionData.serializedInputSize
          instance.serialize =
        (2 +
            (instance.codeBound + instance.codeBound)) +
          1 ∧
      (CorrectedConcreteEncodedObservationSelectionData.runSerializedCostDecisionWithWork
        instance.serialize).2 =
          3 *
            ((2 +
                (instance.codeBound + instance.codeBound)) +
              1) ∧
      (CorrectedConcreteEncodedObservationSelectionData.runSerializedParetoDecisionWithWork
        instance.serialize).2 =
          3 *
            ((2 +
                (instance.codeBound + instance.codeBound)) +
              1) ∧
      ((CorrectedConcreteEncodedObservationSelectionData.runSerializedCostDecisionWithWork
          instance.serialize).1 =
          true ↔
        table.costFeasibleDecision instance.budget = true) ∧
      ((CorrectedConcreteEncodedObservationSelectionData.runSerializedParetoDecisionWithWork
          instance.serialize).1 =
          true ↔
        table.paretoScalarFeasibleDecision
            instance.budget =
          true) := by

  exact
    ⟨instance.decode_serialize,
      instance.serialize_inputSize,
      instance.serialize_costDecisionWork,
      instance.serialize_paretoDecisionWork,
      instance.serialize_costDecisionWithWork_eq_true_iff_tableDecision,
      instance.serialize_paretoDecisionWithWork_eq_true_iff_tableDecision⟩

end SerializedInstanceResourceFormulas

end CorrectedConcreteEncodedObservationSelectionInstance


namespace CorrectedConcreteObservationSelectionDecisionTable

section CanonicalSerializedVerifierComplexity

variable {α : Type u}
variable {ι : Type v}
variable {M : Type w}
variable [DecidableEq ι]
variable [Monoid M]
variable {obsFamily : ι → α → M}
variable {f : Nat}
variable {selectionCost : Finset ι → Nat}
variable {U : Finset ι}
variable {language : Set (Word α)}
variable
  (table :
    CorrectedConcreteObservationSelectionDecisionTable
      (z := z)
      obsFamily
      f
      selectionCost
      U
      language)

/-- Closed input-size and linear work formulas for the canonical serialized
instance at any budget. -/
theorem encodedObservationSelectionInstance_serializedVerifierComplexity_package
    (budget : Nat) :
    let instance :=
      table.encodedObservationSelectionInstance budget
    CorrectedConcreteEncodedObservationSelectionData.serializedInputSize
          instance.serialize =
        (2 + (2 ^ U.card + 2 ^ U.card)) + 1 ∧
      (CorrectedConcreteEncodedObservationSelectionData.runSerializedCostDecisionWithWork
        instance.serialize).2 =
          3 *
            ((2 +
                (2 ^ U.card + 2 ^ U.card)) +
              1) ∧
      (CorrectedConcreteEncodedObservationSelectionData.runSerializedParetoDecisionWithWork
        instance.serialize).2 =
          3 *
            ((2 +
                (2 ^ U.card + 2 ^ U.card)) +
              1) ∧
      ((CorrectedConcreteEncodedObservationSelectionData.runSerializedCostDecisionWithWork
          instance.serialize).1 =
          true ↔
        table.costFeasibleDecision budget = true) ∧
      ((CorrectedConcreteEncodedObservationSelectionData.runSerializedParetoDecisionWithWork
          instance.serialize).1 =
          true ↔
        table.paretoScalarFeasibleDecision budget = true) := by

  let instance :=
    table.encodedObservationSelectionInstance budget

  exact
    ⟨by
        simpa [instance.codeBound_correct] using
          instance.serialize_inputSize,
      by
        simpa [instance.codeBound_correct] using
          instance.serialize_costDecisionWork,
      by
        simpa [instance.codeBound_correct] using
          instance.serialize_paretoDecisionWork,
      instance.serialize_costDecisionWithWork_eq_true_iff_tableDecision,
      instance.serialize_paretoDecisionWithWork_eq_true_iff_tableDecision⟩

end CanonicalSerializedVerifierComplexity

end CorrectedConcreteObservationSelectionDecisionTable


section EncodedSerializedVerifierComplexityFinalPackage

variable {α : Type u}
variable {ι : Type v}
variable {M : Type w}
variable [DecidableEq ι]
variable [Monoid M]
variable (obsFamily : ι → α → M)
variable (f : Nat)
variable (coordinateWeight : ι → Nat)
variable (U : Finset ι)

/-- Final positive-additive serialized-verifier complexity package.

At the exact semantic minimum rank, the serialized input has the closed size

```text
(2 + (2 ^ U.card + 2 ^ U.card)) + 1
```

under `serializedInputSize`.  Both work-instrumented decisions accept, and each
uses exactly three times that size in the declared degree-one work model. -/
theorem
    correctedConcreteWorkingGrammar_observationSelectionEncodedSerializedVerifierComplexity_package
    (language : Set (Word α))
    (hTarget :
      language ∈
        StartRootedCorrectedConcreteTargetClass
          (v := z)
          α
          (↥U → M)
          (selectedObservationProduct obsFamily U)
          f) :
    let table :=
      correctedConcreteObservationSelectionSemanticDecisionTable
        (z := z)
        obsFamily
        f
        (correctedConcreteObservationSelectionAdditiveCost
          coordinateWeight)
        U
        language
    let minimumRank :=
      ambientTargetObservationSelectionPositiveAdditiveMinimumCost
        (z := z)
        obsFamily
        f
        coordinateWeight
        U
        hTarget
    let instance :=
      table.encodedObservationSelectionInstance minimumRank
    CorrectedConcreteEncodedObservationSelectionData.decode
          instance.serialize =
        some instance.toSerializedData ∧
      CorrectedConcreteEncodedObservationSelectionData.serializedInputSize
          instance.serialize =
        (2 + (2 ^ U.card + 2 ^ U.card)) + 1 ∧
      (CorrectedConcreteEncodedObservationSelectionData.runSerializedCostDecisionWithWork
        instance.serialize).1 =
          true ∧
      (CorrectedConcreteEncodedObservationSelectionData.runSerializedParetoDecisionWithWork
        instance.serialize).1 =
          true ∧
      (CorrectedConcreteEncodedObservationSelectionData.runSerializedCostDecisionWithWork
        instance.serialize).2 =
          3 *
            ((2 +
                (2 ^ U.card + 2 ^ U.card)) +
              1) ∧
      (CorrectedConcreteEncodedObservationSelectionData.runSerializedParetoDecisionWithWork
        instance.serialize).2 =
          3 *
            ((2 +
                (2 ^ U.card + 2 ^ U.card)) +
              1) := by

  let table :=
    correctedConcreteObservationSelectionSemanticDecisionTable
      (z := z)
      obsFamily
      f
      (correctedConcreteObservationSelectionAdditiveCost
        coordinateWeight)
      U
      language

  let minimumRank :=
    ambientTargetObservationSelectionPositiveAdditiveMinimumCost
      (z := z)
      obsFamily
      f
      coordinateWeight
      U
      hTarget

  let instance :=
    table.encodedObservationSelectionInstance minimumRank

  have hComplexity :=
    table.encodedObservationSelectionInstance_serializedVerifierComplexity_package
      minimumRank

  have hSerialized :=
    correctedConcreteWorkingGrammar_observationSelectionEncodedSerializedVerifier_package
      (z := z)
      obsFamily
      f
      coordinateWeight
      U
      language
      hTarget

  exact
    ⟨hSerialized.1,
      hComplexity.1,
      by
        simpa using hSerialized.2.2.1,
      by
        simpa using hSerialized.2.2.2.1,
      hComplexity.2.1,
      hComplexity.2.2.1⟩

end EncodedSerializedVerifierComplexityFinalPackage

end MCFG
