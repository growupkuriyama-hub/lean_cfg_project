/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG.ConcreteCanonicalLearnerWorkingGrammarObservationSelectionEncodedExecutableVerifierComplexity

/-!
# ConcreteCanonicalLearnerWorkingGrammarObservationSelectionEncodedInstanceSerialization.lean

The preceding files define a finite encoded observation-selection instance and
an executable verifier over that instance.  The verifier still receives a
proof-carrying Lean record.  This file gives the record a pure finite
`List Nat` representation.

For an encoded instance with exclusive code bound `B`, we form two membership
bit vectors of length `B`:

```text
costBits[c]   = 1  iff c belongs to the stored ordinary-cost code table;
paretoBits[c] = 1  iff c belongs to the stored Pareto code table.
```

The serialized payload is

```text
[budget, B] ++ costBits ++ paretoBits.
```

The decoder reads the first two natural numbers, checks that the remaining
payload has length exactly `B + B`, and splits it into the two bit vectors.

We prove:

* both membership vectors have length exactly `B`;
* every stored bit is either zero or one;
* checked decode/encode round trip;
* injectivity of the encoding on well-formed serialized data;
* exact serialized length `2 + (B + B)`;
* for the canonical observation-selection instance, `B = 2 ^ U.card`;
* at the semantic positive-additive minimum rank, the serialized input has
  exact length `2 + (2 ^ U.card + 2 ^ U.card)` and decodes back to its complete
  finite data.

This is a pure finite-data serialization layer.  It does not yet reconstruct
the semantic decision table from a compact grammar/observation input.  The bit
vectors may themselves have exponential length in `U.card`, so no end-to-end
polynomial-time or formal NP-membership claim is made here.

No target grammar is supplied to any learner.
No `sorry`, `admit`, or `axiom` is used.
-/

namespace MCFG

universe u v w z


/-- Pure finite data carried by a serialized observation-selection instance. -/
structure CorrectedConcreteEncodedObservationSelectionData where

  budget : Nat

  codeBound : Nat

  costBits : List Nat

  paretoBits : List Nat

namespace CorrectedConcreteEncodedObservationSelectionData

/-- Length correctness for the two fixed-width membership vectors. -/
def WellFormed
    (data : CorrectedConcreteEncodedObservationSelectionData) : Prop :=
  data.costBits.length = data.codeBound ∧
    data.paretoBits.length = data.codeBound

/-- Pure natural-list encoding.

The two membership-vector lengths are implicit because both equal
`codeBound`. -/
def encode
    (data : CorrectedConcreteEncodedObservationSelectionData) :
    List Nat :=
  data.budget ::
    data.codeBound ::
      (data.costBits ++ data.paretoBits)

/-- Checked decoder for the pure natural-list representation. -/
def decode :
    List Nat →
      Option CorrectedConcreteEncodedObservationSelectionData
  | budget :: codeBound :: payload =>
      if payload.length = codeBound + codeBound then
        some
          {
            budget := budget
            codeBound := codeBound
            costBits := payload.take codeBound
            paretoBits := payload.drop codeBound
          }
      else
        none
  | _ => none

/-- Exact serialized length of every well-formed data record. -/
theorem encode_length
    (data : CorrectedConcreteEncodedObservationSelectionData)
    (hWellFormed : data.WellFormed) :
    data.encode.length =
      2 + (data.codeBound + data.codeBound) := by

  rcases hWellFormed with
    ⟨hCostLength, hParetoLength⟩

  simp [
    encode,
    hCostLength,
    hParetoLength,
    Nat.add_assoc
  ]

/-- Checked decoding recovers every well-formed data record exactly. -/
theorem decode_encode
    (data : CorrectedConcreteEncodedObservationSelectionData)
    (hWellFormed : data.WellFormed) :
    decode data.encode = some data := by

  rcases hWellFormed with
    ⟨hCostLength, hParetoLength⟩

  simp [
    encode,
    decode,
    hCostLength,
    hParetoLength
  ]

/-- Encoding is injective on well-formed data. -/
theorem encode_injective_on_wellFormed
    {first second :
      CorrectedConcreteEncodedObservationSelectionData}
    (hFirst : first.WellFormed)
    (hSecond : second.WellFormed)
    (hEncode :
      first.encode = second.encode) :
    first = second := by

  have hFirstDecode :
      decode first.encode = some first :=
    decode_encode first hFirst

  have hSecondDecode :
      decode second.encode = some second :=
    decode_encode second hSecond

  have hSome :
      some first = some second := by

    calc
      some first =
          decode first.encode :=
        hFirstDecode.symm

      _ =
          decode second.encode := by
        rw [hEncode]

      _ =
          some second :=
        hSecondDecode

  exact Option.some.inj hSome

end CorrectedConcreteEncodedObservationSelectionData


namespace CorrectedConcreteEncodedObservationSelectionInstance

section MembershipBitVectors

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

/-- Ordinary accepted-code membership vector. -/
def costMembershipBits : List Nat :=
  (List.range instance.codeBound).map
    (fun code =>
      if code ∈ instance.costCertificateCodes then
        1
      else
        0)

/-- Pareto accepted-code membership vector. -/
def paretoMembershipBits : List Nat :=
  (List.range instance.codeBound).map
    (fun code =>
      if code ∈ instance.paretoCertificateCodes then
        1
      else
        0)

/-- Ordinary membership-vector length. -/
@[simp]
theorem costMembershipBits_length :
    instance.costMembershipBits.length =
      instance.codeBound := by

  simp [costMembershipBits]

/-- Pareto membership-vector length. -/
@[simp]
theorem paretoMembershipBits_length :
    instance.paretoMembershipBits.length =
      instance.codeBound := by

  simp [paretoMembershipBits]

/-- Every ordinary membership entry is a Boolean natural. -/
theorem costMembershipBits_entry
    {bit : Nat}
    (hBit :
      bit ∈ instance.costMembershipBits) :
    bit = 0 ∨ bit = 1 := by

  rcases List.mem_map.mp hBit with
    ⟨code, hCode, rfl⟩

  by_cases hStored :
      code ∈ instance.costCertificateCodes

  · simp [hStored]

  · simp [hStored]

/-- Every Pareto membership entry is a Boolean natural. -/
theorem paretoMembershipBits_entry
    {bit : Nat}
    (hBit :
      bit ∈ instance.paretoMembershipBits) :
    bit = 0 ∨ bit = 1 := by

  rcases List.mem_map.mp hBit with
    ⟨code, hCode, rfl⟩

  by_cases hStored :
      code ∈ instance.paretoCertificateCodes

  · simp [hStored]

  · simp [hStored]

/-- Pure serializable data extracted from a finite encoded instance. -/
def toSerializedData :
    CorrectedConcreteEncodedObservationSelectionData :=
  {
    budget := instance.budget
    codeBound := instance.codeBound
    costBits := instance.costMembershipBits
    paretoBits := instance.paretoMembershipBits
  }

/-- Extracted serialized data is well formed. -/
theorem toSerializedData_wellFormed :
    instance.toSerializedData.WellFormed := by

  exact
    ⟨instance.costMembershipBits_length,
      instance.paretoMembershipBits_length⟩

/-- Complete pure natural-list serialization of a finite encoded instance. -/
def serialize : List Nat :=
  instance.toSerializedData.encode

/-- Exact serialized length. -/
theorem serialize_length :
    instance.serialize.length =
      2 + (instance.codeBound + instance.codeBound) := by

  exact
    CorrectedConcreteEncodedObservationSelectionData.encode_length
      instance.toSerializedData
      instance.toSerializedData_wellFormed

/-- Checked decoder round trip for the complete finite encoded instance. -/
theorem decode_serialize :
    CorrectedConcreteEncodedObservationSelectionData.decode
        instance.serialize =
      some instance.toSerializedData := by

  exact
    CorrectedConcreteEncodedObservationSelectionData.decode_encode
      instance.toSerializedData
      instance.toSerializedData_wellFormed

/-- Serialization summary retaining exact lengths and Boolean-entry
properties. -/
theorem serialization_package :
    instance.toSerializedData.budget =
        instance.budget ∧
      instance.toSerializedData.codeBound =
        instance.codeBound ∧
      instance.toSerializedData.costBits.length =
        instance.codeBound ∧
      instance.toSerializedData.paretoBits.length =
        instance.codeBound ∧
      (∀ bit : Nat,
        bit ∈ instance.toSerializedData.costBits →
          bit = 0 ∨ bit = 1) ∧
      (∀ bit : Nat,
        bit ∈ instance.toSerializedData.paretoBits →
          bit = 0 ∨ bit = 1) ∧
      instance.serialize.length =
        2 + (instance.codeBound + instance.codeBound) ∧
      CorrectedConcreteEncodedObservationSelectionData.decode
          instance.serialize =
        some instance.toSerializedData := by

  exact
    ⟨rfl,
      rfl,
      instance.costMembershipBits_length,
      instance.paretoMembershipBits_length,
      fun bit hBit =>
        instance.costMembershipBits_entry hBit,
      fun bit hBit =>
        instance.paretoMembershipBits_entry hBit,
      instance.serialize_length,
      instance.decode_serialize⟩

end MembershipBitVectors

end CorrectedConcreteEncodedObservationSelectionInstance


namespace CorrectedConcreteObservationSelectionDecisionTable

section CanonicalEncodedInstanceSerialization

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

/-- Exact serialization package for the canonical encoded instance at any
budget. -/
theorem encodedObservationSelectionInstance_serialization_package
    (budget : Nat) :
    let instance :=
      table.encodedObservationSelectionInstance budget
    instance.toSerializedData.budget =
        budget ∧
      instance.toSerializedData.codeBound =
        2 ^ U.card ∧
      instance.toSerializedData.costBits.length =
        2 ^ U.card ∧
      instance.toSerializedData.paretoBits.length =
        2 ^ U.card ∧
      instance.serialize.length =
        2 + (2 ^ U.card + 2 ^ U.card) ∧
      CorrectedConcreteEncodedObservationSelectionData.decode
          instance.serialize =
        some instance.toSerializedData := by

  let instance :=
    table.encodedObservationSelectionInstance budget

  exact
    ⟨rfl,
      rfl,
      by
        simpa [instance.codeBound_correct] using
          instance.costMembershipBits_length,
      by
        simpa [instance.codeBound_correct] using
          instance.paretoMembershipBits_length,
      by
        simpa [instance.codeBound_correct] using
          instance.serialize_length,
      instance.decode_serialize⟩

end CanonicalEncodedInstanceSerialization

end CorrectedConcreteObservationSelectionDecisionTable


section EncodedInstanceSerializationFinalPackage

variable {α : Type u}
variable {ι : Type v}
variable {M : Type w}
variable [DecidableEq ι]
variable [Monoid M]
variable (obsFamily : ι → α → M)
variable (f : Nat)
variable (coordinateWeight : ι → Nat)
variable (U : Finset ι)

/-- Final positive-additive pure-input serialization package.

At the exact semantic minimum rank, the complete finite encoded verifier input
is one natural-number list of exact length

```text
2 + (2 ^ U.card + 2 ^ U.card).
```

Checked decoding recovers the budget, code bound, and both complete membership
bit vectors exactly. -/
theorem
    correctedConcreteWorkingGrammar_observationSelectionEncodedInstanceSerialization_package
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
    instance.toSerializedData.budget =
        minimumRank ∧
      instance.toSerializedData.codeBound =
        2 ^ U.card ∧
      instance.toSerializedData.costBits.length =
        2 ^ U.card ∧
      instance.toSerializedData.paretoBits.length =
        2 ^ U.card ∧
      instance.serialize.length =
        2 + (2 ^ U.card + 2 ^ U.card) ∧
      CorrectedConcreteEncodedObservationSelectionData.decode
          instance.serialize =
        some instance.toSerializedData ∧
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
    table.encodedObservationSelectionInstance_serialization_package
      minimumRank

  have hCostTable :
      table.costFeasibleDecision minimumRank = true := by

    change
      table.minimumRankAtMostDecision minimumRank = true

    exact
      (table.minimumRankAtMostDecision_eq_true_iff
        hTarget
        minimumRank).mpr
        (Nat.le_refl minimumRank)

  have hParetoTable :
      table.paretoScalarFeasibleDecision minimumRank = true := by

    exact
      (table.positiveAdditiveParetoScalarDecision_eq_true_iff_minimumRank_le
        hTarget
        minimumRank).mpr
        (Nat.le_refl minimumRank)

  have hCostRun :
      instance.runCostDecision = true :=
    instance.runCostDecision_eq_true_iff_tableDecision.mpr
      hCostTable

  have hParetoRun :
      instance.runParetoDecision = true :=
    instance.runParetoDecision_eq_true_iff_tableDecision.mpr
      hParetoTable

  exact
    ⟨hSerialization.1,
      hSerialization.2.1,
      hSerialization.2.2.1,
      hSerialization.2.2.2.1,
      hSerialization.2.2.2.2.1,
      hSerialization.2.2.2.2.2,
      hCostRun,
      hParetoRun⟩

end EncodedInstanceSerializationFinalPackage

end MCFG
