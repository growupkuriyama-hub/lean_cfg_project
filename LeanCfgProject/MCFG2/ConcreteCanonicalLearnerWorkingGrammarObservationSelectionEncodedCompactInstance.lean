/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG2.ConcreteCanonicalLearnerWorkingGrammarObservationSelectionEncodedSemanticOracleBoundary

/-!
# ConcreteCanonicalLearnerWorkingGrammarObservationSelectionEncodedCompactInstance.lean

The preceding file separates the materialized feasibility-table input from the
future compact observation-design input.  This file defines the first checked
compact-instance format.

A compact record stores

```text
coordinateCount
budget
coordinateWeights
instancePayload.
```

The opaque `instancePayload` is reserved for a later checked encoding of the
grammar, observations, target data, or other legitimate compact instance
information.  This file does not interpret that payload semantically.

The serialized format is

```text
[coordinateCount, budget, weightLength, payloadLength]
  ++ coordinateWeights
  ++ instancePayload.
```

The decoder checks

```text
weightLength = coordinateCount
body.length = weightLength + payloadLength.
```

We prove

* exact checked encode/decode round trips;
* injectivity on well-formed compact records;
* exact serialized length
  `4 + coordinateCount + instancePayload.length`;
* successful wrapped decoding;
* the intrinsic candidate-code bound `2 ^ coordinateCount`;
* a Boolean certificate-range checker;
* unary certificate size bounded by the candidate universe.

Unlike the materialized table input, this format has no dedicated ordinary or
Pareto membership-bit-vector fields.  The opaque payload could of course be
misused to store arbitrary data; the later compact-instance specification must
state what the payload encodes and prove that it is not merely a hidden truth
table.

This file is only the checked compact syntax layer.  It does not construct a
semantic feasibility verifier and does not prove compact-input NP membership,
hardness, or NP-completeness.

No target grammar is supplied to any learner.
No `sorry`, `admit`, or `axiom` is used.
-/

namespace MCFG


/-- Checked data carried by one compact observation-selection input. -/
structure CorrectedConcreteObservationSelectionCompactData where

  coordinateCount : Nat

  budget : Nat

  coordinateWeights : List Nat

  instancePayload : List Nat


namespace CorrectedConcreteObservationSelectionCompactData

section CompactEncoding

/-- Structural well-formedness of compact data. -/
def WellFormed
    (data :
      CorrectedConcreteObservationSelectionCompactData) : Prop :=
  data.coordinateWeights.length =
    data.coordinateCount

/-- Number of natural-number header fields in the compact serialization. -/
def headerLength : Nat :=
  4

/-- Length-framed natural-number serialization of compact data. -/
def encode
    (data :
      CorrectedConcreteObservationSelectionCompactData) :
    List Nat :=
  [data.coordinateCount,
    data.budget,
    data.coordinateWeights.length,
    data.instancePayload.length] ++
      data.coordinateWeights ++
      data.instancePayload

/-- Checked compact-data decoder. -/
def decode :
    List Nat →
      Option CorrectedConcreteObservationSelectionCompactData

  | coordinateCount ::
      budget ::
      weightLength ::
      payloadLength ::
      body =>
      if hWeights :
          weightLength = coordinateCount then
        if hBody :
            body.length =
              weightLength + payloadLength then
          some
            {
              coordinateCount :=
                coordinateCount

              budget :=
                budget

              coordinateWeights :=
                body.take weightLength

              instancePayload :=
                (body.drop weightLength).take
                  payloadLength
            }
        else
          none
      else
        none

  | _ =>
      none

/-- Exact serialization length before substituting well-formedness. -/
theorem encode_length
    (data :
      CorrectedConcreteObservationSelectionCompactData) :
    data.encode.length =
      4 +
        data.coordinateWeights.length +
        data.instancePayload.length := by

  simp [
    encode
  ]

/-- Exact compact serialization length for well-formed data. -/
theorem encode_length_of_wellFormed
    {data :
      CorrectedConcreteObservationSelectionCompactData}
    (hWellFormed :
      data.WellFormed) :
    data.encode.length =
      4 +
        data.coordinateCount +
        data.instancePayload.length := by

  rw [data.encode_length]

  exact
    congrArg
      (fun length =>
        4 + length + data.instancePayload.length)
      hWellFormed

/-- Checked compact encode/decode round trip. -/
theorem decode_encode
    {data :
      CorrectedConcreteObservationSelectionCompactData}
    (hWellFormed :
      data.WellFormed) :
    decode data.encode =
      some data := by

  simp [
    decode,
    encode,
    WellFormed,
    hWellFormed
  ]

/-- Well-formed compact encodings are injective. -/
theorem encode_injective_of_wellFormed
    {first second :
      CorrectedConcreteObservationSelectionCompactData}
    (hFirst :
      first.WellFormed)
    (hSecond :
      second.WellFormed)
    (hEncode :
      first.encode = second.encode) :
    first = second := by

  have hDecoded :
      some first = some second := by

    calc
      some first =
          decode first.encode :=
        (decode_encode hFirst).symm

      _ =
          decode second.encode := by
        rw [hEncode]

      _ =
          some second :=
        decode_encode hSecond

  exact
    Option.some.inj hDecoded

/-- A malformed header whose weight length disagrees with the coordinate count
is rejected. -/
theorem decode_eq_none_of_weightLength_ne
    {coordinateCount budget weightLength payloadLength : Nat}
    {body : List Nat}
    (hWeights :
      weightLength ≠ coordinateCount) :
    decode
        (coordinateCount ::
          budget ::
          weightLength ::
          payloadLength ::
          body) =
      none := by

  simp [
    decode,
    hWeights
  ]

/-- A malformed body length is rejected after a valid compact header. -/
theorem decode_eq_none_of_bodyLength_ne
    {coordinateCount budget weightLength payloadLength : Nat}
    {body : List Nat}
    (hWeights :
      weightLength = coordinateCount)
    (hBody :
      body.length ≠
        weightLength + payloadLength) :
    decode
        (coordinateCount ::
          budget ::
          weightLength ::
          payloadLength ::
          body) =
      none := by

  simp [
    decode,
    hWeights,
    hBody
  ]

end CompactEncoding


section CompactConstructors

/-- Canonical compact-data constructor from explicit weight and payload lists.

The coordinate count is derived from the weight-list length, so the result is
definitionally well formed. -/
def ofLists
    (budget : Nat)
    (coordinateWeights : List Nat)
    (instancePayload : List Nat) :
    CorrectedConcreteObservationSelectionCompactData :=
  {
    coordinateCount :=
      coordinateWeights.length

    budget :=
      budget

    coordinateWeights :=
      coordinateWeights

    instancePayload :=
      instancePayload
  }

@[simp]
theorem ofLists_wellFormed
    (budget : Nat)
    (coordinateWeights instancePayload : List Nat) :
    (ofLists
      budget
      coordinateWeights
      instancePayload).WellFormed := by

  rfl

@[simp]
theorem ofLists_coordinateCount
    (budget : Nat)
    (coordinateWeights instancePayload : List Nat) :
    (ofLists
      budget
      coordinateWeights
      instancePayload).coordinateCount =
        coordinateWeights.length := by

  rfl

@[simp]
theorem ofLists_budget
    (budget : Nat)
    (coordinateWeights instancePayload : List Nat) :
    (ofLists
      budget
      coordinateWeights
      instancePayload).budget =
        budget := by

  rfl

@[simp]
theorem ofLists_encode_length
    (budget : Nat)
    (coordinateWeights instancePayload : List Nat) :
    (ofLists
      budget
      coordinateWeights
      instancePayload).encode.length =
        4 +
          coordinateWeights.length +
          instancePayload.length := by

  exact
    encode_length_of_wellFormed
      (ofLists_wellFormed
        budget
        coordinateWeights
        instancePayload)

@[simp]
theorem decode_encode_ofLists
    (budget : Nat)
    (coordinateWeights instancePayload : List Nat) :
    decode
        (ofLists
          budget
          coordinateWeights
          instancePayload).encode =
      some
        (ofLists
          budget
          coordinateWeights
          instancePayload) := by

  exact
    decode_encode
      (ofLists_wellFormed
        budget
        coordinateWeights
        instancePayload)

end CompactConstructors


section CompactCandidateCodes

/-- Exclusive dense candidate-code bound of a compact instance. -/
def candidateCodeBound
    (data :
      CorrectedConcreteObservationSelectionCompactData) :
    Nat :=
  2 ^ data.coordinateCount

/-- Boolean range checker for one compact certificate code. -/
def certificateCodeInRange
    (data :
      CorrectedConcreteObservationSelectionCompactData)
    (code : Nat) :
    Bool :=
  decide
    (code < data.candidateCodeBound)

@[simp]
theorem certificateCodeInRange_eq_true_iff
    (data :
      CorrectedConcreteObservationSelectionCompactData)
    (code : Nat) :
    data.certificateCodeInRange code = true ↔
      code < data.candidateCodeBound := by

  simp [
    certificateCodeInRange
  ]

@[simp]
theorem certificateCodeInRange_eq_false_iff
    (data :
      CorrectedConcreteObservationSelectionCompactData)
    (code : Nat) :
    data.certificateCodeInRange code = false ↔
      data.candidateCodeBound <= code := by

  simp [
    certificateCodeInRange,
    Nat.not_lt
  ]

/-- Unary size of one natural-number compact certificate. -/
def certificateSize
    (code : Nat) :
    Nat :=
  code + 1

/-- Every in-range certificate has unary size at most the candidate-code
universe size. -/
theorem certificateSize_le_candidateCodeBound
    {data :
      CorrectedConcreteObservationSelectionCompactData}
    {code : Nat}
    (hCode :
      data.certificateCodeInRange code =
        true) :
    certificateSize code <=
      data.candidateCodeBound := by

  have hLt :
      code < data.candidateCodeBound :=
    (data.certificateCodeInRange_eq_true_iff
      code).mp
      hCode

  unfold certificateSize

  omega

/-- Closed candidate-code bound for `ofLists`. -/
@[simp]
theorem ofLists_candidateCodeBound
    (budget : Nat)
    (coordinateWeights instancePayload : List Nat) :
    (ofLists
      budget
      coordinateWeights
      instancePayload).candidateCodeBound =
        2 ^ coordinateWeights.length := by

  rfl

end CompactCandidateCodes

end CorrectedConcreteObservationSelectionCompactData


namespace CorrectedConcreteObservationSelectionCompactInput

section CheckedCompactInputs

/-- Wrap checked compact data as the compact input type introduced by the
semantic-oracle boundary file. -/
def ofData
    (data :
      CorrectedConcreteObservationSelectionCompactData) :
    CorrectedConcreteObservationSelectionCompactInput :=
  ⟨data.encode⟩

/-- A compact input contains a successfully decoded well-formed compact record. -/
def HasDecodedCompactData
    (input :
      CorrectedConcreteObservationSelectionCompactInput) :
    Prop :=
  ∃ data :
      CorrectedConcreteObservationSelectionCompactData,
    data.WellFormed ∧
      CorrectedConcreteObservationSelectionCompactData.decode
          input.payload =
        some data

@[simp]
theorem ofData_payload
    (data :
      CorrectedConcreteObservationSelectionCompactData) :
    (ofData data).payload =
      data.encode := by

  rfl

/-- Every well-formed compact record yields a successfully decoded compact
input. -/
theorem ofData_hasDecodedCompactData
    {data :
      CorrectedConcreteObservationSelectionCompactData}
    (hWellFormed :
      data.WellFormed) :
    (ofData data).HasDecodedCompactData := by

  exact
    ⟨data,
      hWellFormed,
      CorrectedConcreteObservationSelectionCompactData.decode_encode
        hWellFormed⟩

/-- Exact compact-input payload length. -/
theorem ofData_payload_length
    {data :
      CorrectedConcreteObservationSelectionCompactData}
    (hWellFormed :
      data.WellFormed) :
    (ofData data).payload.length =
      4 +
        data.coordinateCount +
        data.instancePayload.length := by

  exact
    CorrectedConcreteObservationSelectionCompactData.encode_length_of_wellFormed
      hWellFormed

/-- Exact size including the nonzero-size convention used by the preceding
polynomial decision-problem layer. -/
theorem ofData_inputSize
    {data :
      CorrectedConcreteObservationSelectionCompactData}
    (hWellFormed :
      data.WellFormed) :
    (ofData data).payload.length + 1 =
      (4 +
          data.coordinateCount +
          data.instancePayload.length) +
        1 := by

  rw [ofData_payload_length hWellFormed]

/-- Checked compact-input package. -/
theorem checkedCompactInput_package
    {data :
      CorrectedConcreteObservationSelectionCompactData}
    (hWellFormed :
      data.WellFormed) :
    (ofData data).HasDecodedCompactData ∧
      CorrectedConcreteObservationSelectionCompactData.decode
            (ofData data).payload =
        some data ∧
      (ofData data).payload.length =
        4 +
          data.coordinateCount +
          data.instancePayload.length ∧
      data.candidateCodeBound =
        2 ^ data.coordinateCount := by

  exact
    ⟨ofData_hasDecodedCompactData hWellFormed,
      CorrectedConcreteObservationSelectionCompactData.decode_encode
        hWellFormed,
      ofData_payload_length hWellFormed,
      rfl⟩

end CheckedCompactInputs

end CorrectedConcreteObservationSelectionCompactInput


section EncodedCompactInstanceFinalPackage

/-- Final compact-syntax package for an explicit coordinate-weight list.

If the supplied weight-list length is `coordinateCount`, the compact record has
the requested coordinate count, checked round-trip serialization, exact linear
payload length, and the intrinsic dense certificate bound
`2 ^ coordinateCount`. -/
theorem
    correctedConcreteWorkingGrammar_observationSelectionEncodedCompactInstance_package
    (coordinateCount budget : Nat)
    (coordinateWeights instancePayload : List Nat)
    (hWeights :
      coordinateWeights.length =
        coordinateCount) :
    let data :
        CorrectedConcreteObservationSelectionCompactData :=
      {
        coordinateCount :=
          coordinateCount

        budget :=
          budget

        coordinateWeights :=
          coordinateWeights

        instancePayload :=
          instancePayload
      }
    let input :
        CorrectedConcreteObservationSelectionCompactInput :=
      CorrectedConcreteObservationSelectionCompactInput.ofData
        data
    data.WellFormed ∧
      input.HasDecodedCompactData ∧
      CorrectedConcreteObservationSelectionCompactData.decode
            input.payload =
        some data ∧
      input.payload.length =
        4 +
          coordinateCount +
          instancePayload.length ∧
      data.candidateCodeBound =
        2 ^ coordinateCount ∧
      (∀ code : Nat,
        data.certificateCodeInRange code = true ↔
          code < 2 ^ coordinateCount) ∧
      (∀ code : Nat,
        data.certificateCodeInRange code = true →
          CorrectedConcreteObservationSelectionCompactData.certificateSize
              code <=
            2 ^ coordinateCount) := by

  let data :
      CorrectedConcreteObservationSelectionCompactData :=
    {
      coordinateCount :=
        coordinateCount

      budget :=
        budget

      coordinateWeights :=
        coordinateWeights

      instancePayload :=
        instancePayload
    }

  let input :
      CorrectedConcreteObservationSelectionCompactInput :=
    CorrectedConcreteObservationSelectionCompactInput.ofData
      data

  have hWellFormed :
      data.WellFormed := by

    exact hWeights

  exact
    ⟨hWellFormed,
      CorrectedConcreteObservationSelectionCompactInput.ofData_hasDecodedCompactData
        hWellFormed,
      CorrectedConcreteObservationSelectionCompactData.decode_encode
        hWellFormed,
      by
        simpa [data] using
          CorrectedConcreteObservationSelectionCompactInput.ofData_payload_length
            hWellFormed,
      rfl,
      by
        intro code

        exact
          data.certificateCodeInRange_eq_true_iff
            code,
      by
        intro code hCode

        simpa [data] using
          CorrectedConcreteObservationSelectionCompactData.certificateSize_le_candidateCodeBound
            hCode⟩

end EncodedCompactInstanceFinalPackage

end MCFG
