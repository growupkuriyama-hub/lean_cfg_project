/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG.ConcreteCanonicalLearnerWorkingGrammarObservationSelectionEncodedInstanceSerialization

/-!
# ConcreteCanonicalLearnerWorkingGrammarObservationSelectionEncodedSerializedVerifier.lean

The preceding file serializes a finite encoded observation-selection instance
as one pure `List Nat`:

```text
[budget, codeBound] ++ costBits ++ paretoBits.
```

This file defines executable decisions that receive only such a serialized
natural-number list.

After checked decoding, the ordinary decision accepts exactly when the decoded
ordinary membership vector contains `1`; the Pareto decision is analogous.
Malformed inputs are rejected.

For every proof-carrying encoded instance, we prove that

```text
1 belongs to costMembershipBits
  iff the stored ordinary accepted-code table is nonempty;

1 belongs to paretoMembershipBits
  iff the stored Pareto accepted-code table is nonempty.
```

Consequently, running the serialized decisions on `instance.serialize` agrees
exactly with

* the finite encoded-instance decisions;
* the exhaustive executable decisions;
* the original semantic-table decisions.

At the exact semantic positive-additive minimum rank, the serialized payload
decodes successfully and both serialized decisions return `true`.

This verifier reads only the pure serialized list.  The canonical serialized
input may still have length exponential in `U.card`, and its construction from
the semantic table remains noncomputable.  Therefore this file does not claim
end-to-end polynomial time, formal NP membership, or hardness.

No target grammar is supplied to any learner.
No `sorry`, `admit`, or `axiom` is used.
-/

namespace MCFG

universe u v w z


namespace CorrectedConcreteEncodedObservationSelectionData

section PureDecodedDecisions

/-- Ordinary decision on pure decoded data.

The decision scans only the decoded ordinary membership vector. -/
def runCostBitDecision
    (data : CorrectedConcreteEncodedObservationSelectionData) :
    Bool :=
  decide (1 ∈ data.costBits)

/-- Pareto decision on pure decoded data.

The decision scans only the decoded Pareto membership vector. -/
def runParetoBitDecision
    (data : CorrectedConcreteEncodedObservationSelectionData) :
    Bool :=
  decide (1 ∈ data.paretoBits)

/-- Exact ordinary decoded-data decision specification. -/
theorem runCostBitDecision_eq_true_iff
    (data : CorrectedConcreteEncodedObservationSelectionData) :
    data.runCostBitDecision = true ↔
      1 ∈ data.costBits := by

  simp [runCostBitDecision]

/-- Exact Pareto decoded-data decision specification. -/
theorem runParetoBitDecision_eq_true_iff
    (data : CorrectedConcreteEncodedObservationSelectionData) :
    data.runParetoBitDecision = true ↔
      1 ∈ data.paretoBits := by

  simp [runParetoBitDecision]

/-- Both pure decoded decisions in one executable output pair. -/
def runDecisionPair
    (data : CorrectedConcreteEncodedObservationSelectionData) :
    Bool × Bool :=
  (data.runCostBitDecision,
    data.runParetoBitDecision)

@[simp]
theorem runDecisionPair_fst
    (data : CorrectedConcreteEncodedObservationSelectionData) :
    data.runDecisionPair.1 =
      data.runCostBitDecision := by

  rfl

@[simp]
theorem runDecisionPair_snd
    (data : CorrectedConcreteEncodedObservationSelectionData) :
    data.runDecisionPair.2 =
      data.runParetoBitDecision := by

  rfl

end PureDecodedDecisions


section SerializedListDecisions

/-- Ordinary decision directly on a serialized natural-number list.

Malformed encodings are rejected. -/
def runSerializedCostDecision
    (input : List Nat) : Bool :=
  match decode input with
  | some data => data.runCostBitDecision
  | none => false

/-- Pareto decision directly on a serialized natural-number list.

Malformed encodings are rejected. -/
def runSerializedParetoDecision
    (input : List Nat) : Bool :=
  match decode input with
  | some data => data.runParetoBitDecision
  | none => false

/-- Both serialized decisions in one executable output pair. -/
def runSerializedDecisionPair
    (input : List Nat) : Bool × Bool :=
  (runSerializedCostDecision input,
    runSerializedParetoDecision input)

/-- Exact ordinary behavior after a successful decode. -/
theorem runSerializedCostDecision_of_decode
    {input : List Nat}
    {data : CorrectedConcreteEncodedObservationSelectionData}
    (hDecode :
      decode input = some data) :
    runSerializedCostDecision input =
      data.runCostBitDecision := by

  simp [runSerializedCostDecision, hDecode]

/-- Exact Pareto behavior after a successful decode. -/
theorem runSerializedParetoDecision_of_decode
    {input : List Nat}
    {data : CorrectedConcreteEncodedObservationSelectionData}
    (hDecode :
      decode input = some data) :
    runSerializedParetoDecision input =
      data.runParetoBitDecision := by

  simp [runSerializedParetoDecision, hDecode]

/-- Malformed serialized input is rejected by the ordinary decision. -/
theorem runSerializedCostDecision_eq_false_of_decode_none
    {input : List Nat}
    (hDecode :
      decode input = none) :
    runSerializedCostDecision input = false := by

  simp [runSerializedCostDecision, hDecode]

/-- Malformed serialized input is rejected by the Pareto decision. -/
theorem runSerializedParetoDecision_eq_false_of_decode_none
    {input : List Nat}
    (hDecode :
      decode input = none) :
    runSerializedParetoDecision input = false := by

  simp [runSerializedParetoDecision, hDecode]

/-- Exact serialized ordinary acceptance specification. -/
theorem runSerializedCostDecision_eq_true_iff
    (input : List Nat) :
    runSerializedCostDecision input = true ↔
      ∃ data : CorrectedConcreteEncodedObservationSelectionData,
        decode input = some data ∧
          1 ∈ data.costBits := by

  cases hDecode : decode input with

  | none =>
      simp [
        runSerializedCostDecision,
        hDecode
      ]

  | some data =>
      simp [
        runSerializedCostDecision,
        hDecode,
        runCostBitDecision
      ]

/-- Exact serialized Pareto acceptance specification. -/
theorem runSerializedParetoDecision_eq_true_iff
    (input : List Nat) :
    runSerializedParetoDecision input = true ↔
      ∃ data : CorrectedConcreteEncodedObservationSelectionData,
        decode input = some data ∧
          1 ∈ data.paretoBits := by

  cases hDecode : decode input with

  | none =>
      simp [
        runSerializedParetoDecision,
        hDecode
      ]

  | some data =>
      simp [
        runSerializedParetoDecision,
        hDecode,
        runParetoBitDecision
      ]

end SerializedListDecisions

end CorrectedConcreteEncodedObservationSelectionData


namespace CorrectedConcreteEncodedObservationSelectionInstance

section MembershipBitCorrectness

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

/-- The ordinary membership bit vector contains `1` exactly when the stored
ordinary accepted-code table is nonempty. -/
theorem one_mem_costMembershipBits_iff :
    1 ∈ instance.costMembershipBits ↔
      instance.costCertificateCodes.Nonempty := by

  constructor

  · intro hOne

    rcases List.mem_map.mp hOne with
      ⟨code, hCodeRange, hBit⟩

    by_cases hStored :
        code ∈ instance.costCertificateCodes

    · exact ⟨code, hStored⟩

    · simp [
        costMembershipBits,
        hStored
      ] at hBit

  · rintro ⟨code, hStored⟩

    have hBound :
        code < instance.codeBound :=
      ((instance.costCodes_correct code).mp hStored).1

    have hRange :
        code ∈ List.range instance.codeBound := by

      simpa using hBound

    apply List.mem_map.mpr

    exact
      ⟨code,
        hRange,
        by
          simp [hStored]⟩

/-- The Pareto membership bit vector contains `1` exactly when the stored
Pareto accepted-code table is nonempty. -/
theorem one_mem_paretoMembershipBits_iff :
    1 ∈ instance.paretoMembershipBits ↔
      instance.paretoCertificateCodes.Nonempty := by

  constructor

  · intro hOne

    rcases List.mem_map.mp hOne with
      ⟨code, hCodeRange, hBit⟩

    by_cases hStored :
        code ∈ instance.paretoCertificateCodes

    · exact ⟨code, hStored⟩

    · simp [
        paretoMembershipBits,
        hStored
      ] at hBit

  · rintro ⟨code, hStored⟩

    have hBound :
        code < instance.codeBound :=
      ((instance.paretoCodes_correct code).mp hStored).1

    have hRange :
        code ∈ List.range instance.codeBound := by

      simpa using hBound

    apply List.mem_map.mpr

    exact
      ⟨code,
        hRange,
        by
          simp [hStored]⟩

/-- The pure decoded ordinary decision on the extracted serializable data
agrees with the proof-carrying encoded-instance decision. -/
theorem toSerializedData_runCostBitDecision_eq_true_iff :
    instance.toSerializedData.runCostBitDecision = true ↔
      instance.costDecision = true := by

  rw [
    CorrectedConcreteEncodedObservationSelectionData.runCostBitDecision_eq_true_iff,
    instance.costDecision_eq_true_iff_exists_code
  ]

  exact
    instance.one_mem_costMembershipBits_iff

/-- The pure decoded Pareto decision on the extracted serializable data agrees
with the proof-carrying encoded-instance decision. -/
theorem toSerializedData_runParetoBitDecision_eq_true_iff :
    instance.toSerializedData.runParetoBitDecision = true ↔
      instance.paretoDecision = true := by

  rw [
    CorrectedConcreteEncodedObservationSelectionData.runParetoBitDecision_eq_true_iff,
    instance.paretoDecision_eq_true_iff_exists_code
  ]

  exact
    instance.one_mem_paretoMembershipBits_iff

end MembershipBitCorrectness


section SerializedInstanceVerifierCorrectness

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

/-- Running the pure serialized ordinary decision on the encoded instance
agrees with its proof-carrying ordinary decision. -/
theorem runSerializedCostDecision_serialize_eq_true_iff :
    CorrectedConcreteEncodedObservationSelectionData.runSerializedCostDecision
          instance.serialize =
        true ↔
      instance.costDecision = true := by

  have hRun :
      CorrectedConcreteEncodedObservationSelectionData.runSerializedCostDecision
          instance.serialize =
        instance.toSerializedData.runCostBitDecision :=
    CorrectedConcreteEncodedObservationSelectionData.runSerializedCostDecision_of_decode
      instance.decode_serialize

  rw [hRun]

  exact
    instance.toSerializedData_runCostBitDecision_eq_true_iff

/-- Running the pure serialized Pareto decision on the encoded instance agrees
with its proof-carrying Pareto decision. -/
theorem runSerializedParetoDecision_serialize_eq_true_iff :
    CorrectedConcreteEncodedObservationSelectionData.runSerializedParetoDecision
          instance.serialize =
        true ↔
      instance.paretoDecision = true := by

  have hRun :
      CorrectedConcreteEncodedObservationSelectionData.runSerializedParetoDecision
          instance.serialize =
        instance.toSerializedData.runParetoBitDecision :=
    CorrectedConcreteEncodedObservationSelectionData.runSerializedParetoDecision_of_decode
      instance.decode_serialize

  rw [hRun]

  exact
    instance.toSerializedData_runParetoBitDecision_eq_true_iff

/-- Serialized ordinary decision agrees with the earlier exhaustive executable
ordinary decision. -/
theorem runSerializedCostDecision_serialize_iff_executableDecision :
    CorrectedConcreteEncodedObservationSelectionData.runSerializedCostDecision
          instance.serialize =
        true ↔
      instance.runCostDecision = true := by

  exact
    instance.runSerializedCostDecision_serialize_eq_true_iff.trans
      instance.runCostDecision_eq_true_iff_instanceDecision.symm

/-- Serialized Pareto decision agrees with the earlier exhaustive executable
Pareto decision. -/
theorem runSerializedParetoDecision_serialize_iff_executableDecision :
    CorrectedConcreteEncodedObservationSelectionData.runSerializedParetoDecision
          instance.serialize =
        true ↔
      instance.runParetoDecision = true := by

  exact
    instance.runSerializedParetoDecision_serialize_eq_true_iff.trans
      instance.runParetoDecision_eq_true_iff_instanceDecision.symm

/-- Serialized ordinary decision agrees with the original semantic-table
ordinary decision. -/
theorem runSerializedCostDecision_serialize_iff_tableDecision :
    CorrectedConcreteEncodedObservationSelectionData.runSerializedCostDecision
          instance.serialize =
        true ↔
      table.costFeasibleDecision instance.budget = true := by

  exact
    instance.runSerializedCostDecision_serialize_eq_true_iff.trans
      instance.costDecision_eq_true_iff_tableDecision

/-- Serialized Pareto decision agrees with the original semantic-table Pareto
decision. -/
theorem runSerializedParetoDecision_serialize_iff_tableDecision :
    CorrectedConcreteEncodedObservationSelectionData.runSerializedParetoDecision
          instance.serialize =
        true ↔
      table.paretoScalarFeasibleDecision instance.budget = true := by

  exact
    instance.runSerializedParetoDecision_serialize_eq_true_iff.trans
      instance.paretoDecision_eq_true_iff_tableDecision

/-- Complete pure serialized-verifier package for one finite encoded
instance. -/
theorem serializedVerifier_package :
    CorrectedConcreteEncodedObservationSelectionData.decode
          instance.serialize =
        some instance.toSerializedData ∧
      instance.serialize.length =
        2 + (instance.codeBound + instance.codeBound) ∧
      (CorrectedConcreteEncodedObservationSelectionData.runSerializedCostDecision
            instance.serialize =
          true ↔
        table.costFeasibleDecision instance.budget = true) ∧
      (CorrectedConcreteEncodedObservationSelectionData.runSerializedParetoDecision
            instance.serialize =
          true ↔
        table.paretoScalarFeasibleDecision
            instance.budget =
          true) := by

  exact
    ⟨instance.decode_serialize,
      instance.serialize_length,
      instance.runSerializedCostDecision_serialize_iff_tableDecision,
      instance.runSerializedParetoDecision_serialize_iff_tableDecision⟩

end SerializedInstanceVerifierCorrectness

end CorrectedConcreteEncodedObservationSelectionInstance


namespace CorrectedConcreteObservationSelectionDecisionTable

section CanonicalSerializedVerifier

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

/-- The pure serialized ordinary verifier for the canonical instance agrees
with the semantic-table ordinary decision at every budget. -/
theorem encodedObservationSelectionInstance_runSerializedCostDecision
    (budget : Nat) :
    CorrectedConcreteEncodedObservationSelectionData.runSerializedCostDecision
          (table.encodedObservationSelectionInstance
            budget).serialize =
        true ↔
      table.costFeasibleDecision budget = true := by

  exact
    (table.encodedObservationSelectionInstance
      budget).runSerializedCostDecision_serialize_iff_tableDecision

/-- The pure serialized Pareto verifier for the canonical instance agrees with
the semantic-table Pareto decision at every budget. -/
theorem encodedObservationSelectionInstance_runSerializedParetoDecision
    (budget : Nat) :
    CorrectedConcreteEncodedObservationSelectionData.runSerializedParetoDecision
          (table.encodedObservationSelectionInstance
            budget).serialize =
        true ↔
      table.paretoScalarFeasibleDecision budget = true := by

  exact
    (table.encodedObservationSelectionInstance
      budget).runSerializedParetoDecision_serialize_iff_tableDecision

end CanonicalSerializedVerifier

end CorrectedConcreteObservationSelectionDecisionTable


section EncodedSerializedVerifierFinalPackage

variable {α : Type u}
variable {ι : Type v}
variable {M : Type w}
variable [DecidableEq ι]
variable [Monoid M]
variable (obsFamily : ι → α → M)
variable (f : Nat)
variable (coordinateWeight : ι → Nat)
variable (U : Finset ι)

/-- Final positive-additive pure serialized-verifier package.

At the exact semantic minimum rank, the complete finite verifier input is a
pure natural-number list.  Checked decoding succeeds, and both serialized
decisions return `true`.  Their input length is exactly

```text
2 + (2 ^ U.card + 2 ^ U.card).
``` -/
theorem
    correctedConcreteWorkingGrammar_observationSelectionEncodedSerializedVerifier_package
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
      instance.serialize.length =
        2 + (2 ^ U.card + 2 ^ U.card) ∧
      CorrectedConcreteEncodedObservationSelectionData.runSerializedCostDecision
          instance.serialize =
        true ∧
      CorrectedConcreteEncodedObservationSelectionData.runSerializedParetoDecision
          instance.serialize =
        true ∧
      instance.runCostDecision = true ∧
      instance.runParetoDecision = true := by

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

  have hSerialization :=
    correctedConcreteWorkingGrammar_observationSelectionEncodedInstanceSerialization_package
      (z := z)
      obsFamily
      f
      coordinateWeight
      U
      language
      hTarget

  have hSerializedCost :
      CorrectedConcreteEncodedObservationSelectionData.runSerializedCostDecision
            instance.serialize =
          true :=
    (instance.runSerializedCostDecision_serialize_eq_true_iff).2
      hSerialization.2.2.2.2.2.2.1

  have hSerializedPareto :
      CorrectedConcreteEncodedObservationSelectionData.runSerializedParetoDecision
            instance.serialize =
          true :=
    (instance.runSerializedParetoDecision_serialize_eq_true_iff).2
      hSerialization.2.2.2.2.2.2.2

  exact
    ⟨hSerialization.2.2.2.2.2.1,
      hSerialization.2.2.2.2.1,
      hSerializedCost,
      hSerializedPareto,
      hSerialization.2.2.2.2.2.2.1,
      hSerialization.2.2.2.2.2.2.2⟩

end EncodedSerializedVerifierFinalPackage

end MCFG
