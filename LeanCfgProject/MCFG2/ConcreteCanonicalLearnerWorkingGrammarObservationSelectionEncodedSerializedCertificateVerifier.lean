/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG2.ConcreteCanonicalLearnerWorkingGrammarObservationSelectionEncodedSerializedVerifierComplexity

/-!
# ConcreteCanonicalLearnerWorkingGrammarObservationSelectionEncodedSerializedCertificateVerifier.lean

The preceding serialized verifier decides whether an already materialized
ordinary or Pareto accepted-code bit vector contains any `1`.  For an
NP-style verifier interface, the central operation is different: it receives
one serialized input and one candidate certificate code and checks that
particular code.

This file defines pure serialized certificate verifiers.

After checked decoding, the ordinary verifier accepts `code` exactly when

```text
code < data.codeBound
```

and the `code`-th ordinary membership bit is `1`.  The Pareto verifier is
analogous.  Malformed serialized inputs are rejected.

For every proof-carrying encoded instance we prove that running these pure
verifiers on `instance.serialize` agrees exactly with

* membership in the stored accepted-code table;
* the executable finite-table certificate verifier;
* the previous dense semantic certificate verifier.

We also attach a degree-one input-length work envelope to each single-code
verification.  Finally, at the exact semantic positive-additive minimum rank,
the previously selected canonical least Pareto dense code is accepted by the
pure serialized certificate verifier, decodes to the same Pareto certificate,
and is no larger than every other serialized Pareto witness code.

The verifier reads only a serialized `List Nat` and one natural-number
certificate code.  The canonical serialized input still materializes an
exponential-size semantic table, so this is not yet an end-to-end compact-input
NP-membership theorem.  No hardness claim is made.

No target grammar is supplied to any learner.
No `sorry`, `admit`, or `axiom` is used.
-/

namespace MCFG

universe u v w z


namespace CorrectedConcreteEncodedObservationSelectionData

section SerializedCertificateVerifier

/-- Ordinary single-certificate verifier on a pure serialized input. -/
def runSerializedCostCertificateVerifier
    (input : List Nat)
    (code : Nat) : Bool :=
  match decode input with
  | some data =>
      decide
        (code < data.codeBound ∧
          data.costBits.get? code = some 1)
  | none => false

/-- Pareto single-certificate verifier on a pure serialized input. -/
def runSerializedParetoCertificateVerifier
    (input : List Nat)
    (code : Nat) : Bool :=
  match decode input with
  | some data =>
      decide
        (code < data.codeBound ∧
          data.paretoBits.get? code = some 1)
  | none => false

/-- Exact ordinary certificate-verifier behavior after successful decoding. -/
theorem runSerializedCostCertificateVerifier_of_decode
    {input : List Nat}
    {data : CorrectedConcreteEncodedObservationSelectionData}
    {code : Nat}
    (hDecode :
      decode input = some data) :
    runSerializedCostCertificateVerifier input code = true ↔
      code < data.codeBound ∧
        data.costBits.get? code = some 1 := by

  simp [
    runSerializedCostCertificateVerifier,
    hDecode
  ]

/-- Exact Pareto certificate-verifier behavior after successful decoding. -/
theorem runSerializedParetoCertificateVerifier_of_decode
    {input : List Nat}
    {data : CorrectedConcreteEncodedObservationSelectionData}
    {code : Nat}
    (hDecode :
      decode input = some data) :
    runSerializedParetoCertificateVerifier input code = true ↔
      code < data.codeBound ∧
        data.paretoBits.get? code = some 1 := by

  simp [
    runSerializedParetoCertificateVerifier,
    hDecode
  ]

/-- Malformed serialized inputs reject every ordinary certificate code. -/
theorem runSerializedCostCertificateVerifier_eq_false_of_decode_none
    {input : List Nat}
    {code : Nat}
    (hDecode :
      decode input = none) :
    runSerializedCostCertificateVerifier input code = false := by

  simp [
    runSerializedCostCertificateVerifier,
    hDecode
  ]

/-- Malformed serialized inputs reject every Pareto certificate code. -/
theorem runSerializedParetoCertificateVerifier_eq_false_of_decode_none
    {input : List Nat}
    {code : Nat}
    (hDecode :
      decode input = none) :
    runSerializedParetoCertificateVerifier input code = false := by

  simp [
    runSerializedParetoCertificateVerifier,
    hDecode
  ]

/-- Exact ordinary acceptance specification on arbitrary serialized input. -/
theorem runSerializedCostCertificateVerifier_eq_true_iff
    (input : List Nat)
    (code : Nat) :
    runSerializedCostCertificateVerifier input code = true ↔
      ∃ data : CorrectedConcreteEncodedObservationSelectionData,
        decode input = some data ∧
          code < data.codeBound ∧
          data.costBits.get? code = some 1 := by

  cases hDecode : decode input with

  | none =>
      simp [
        runSerializedCostCertificateVerifier,
        hDecode
      ]

  | some data =>
      simp [
        runSerializedCostCertificateVerifier,
        hDecode
      ]

/-- Exact Pareto acceptance specification on arbitrary serialized input. -/
theorem runSerializedParetoCertificateVerifier_eq_true_iff
    (input : List Nat)
    (code : Nat) :
    runSerializedParetoCertificateVerifier input code = true ↔
      ∃ data : CorrectedConcreteEncodedObservationSelectionData,
        decode input = some data ∧
          code < data.codeBound ∧
          data.paretoBits.get? code = some 1 := by

  cases hDecode : decode input with

  | none =>
      simp [
        runSerializedParetoCertificateVerifier,
        hDecode
      ]

  | some data =>
      simp [
        runSerializedParetoCertificateVerifier,
        hDecode
      ]

end SerializedCertificateVerifier


section SerializedCertificateVerifierWork

/-- Explicit size measure for one serialized input/certificate pair.

The candidate code is already bounded by the decoded bit-vector length, so the
work envelope is measured by the serialized input length plus one. -/
def serializedCertificateVerifierInputSize
    (input : List Nat)
    (_code : Nat) : Nat :=
  input.length + 1

/-- Degree-one work envelope for one serialized certificate verification. -/
def serializedCertificateVerifierWork
    (input : List Nat)
    (code : Nat) : Nat :=
  4 * serializedCertificateVerifierInputSize input code

/-- Ordinary serialized certificate verifier paired with its work count. -/
def runSerializedCostCertificateVerifierWithWork
    (input : List Nat)
    (code : Nat) : Bool × Nat :=
  (runSerializedCostCertificateVerifier input code,
    serializedCertificateVerifierWork input code)

/-- Pareto serialized certificate verifier paired with its work count. -/
def runSerializedParetoCertificateVerifierWithWork
    (input : List Nat)
    (code : Nat) : Bool × Nat :=
  (runSerializedParetoCertificateVerifier input code,
    serializedCertificateVerifierWork input code)

@[simp]
theorem runSerializedCostCertificateVerifierWithWork_fst
    (input : List Nat)
    (code : Nat) :
    (runSerializedCostCertificateVerifierWithWork input code).1 =
      runSerializedCostCertificateVerifier input code := by

  rfl

@[simp]
theorem runSerializedCostCertificateVerifierWithWork_snd
    (input : List Nat)
    (code : Nat) :
    (runSerializedCostCertificateVerifierWithWork input code).2 =
      4 *
        serializedCertificateVerifierInputSize input code := by

  rfl

@[simp]
theorem runSerializedParetoCertificateVerifierWithWork_fst
    (input : List Nat)
    (code : Nat) :
    (runSerializedParetoCertificateVerifierWithWork input code).1 =
      runSerializedParetoCertificateVerifier input code := by

  rfl

@[simp]
theorem runSerializedParetoCertificateVerifierWithWork_snd
    (input : List Nat)
    (code : Nat) :
    (runSerializedParetoCertificateVerifierWithWork input code).2 =
      4 *
        serializedCertificateVerifierInputSize input code := by

  rfl

/-- The declared work is a degree-one polynomial in the explicit pair-input
size. -/
theorem serializedCertificateVerifierWork_linear
    (input : List Nat)
    (code : Nat) :
    serializedCertificateVerifierWork input code =
      4 *
        (serializedCertificateVerifierInputSize input code) ^ 1 := by

  simp [
    serializedCertificateVerifierWork
  ]

/-- Generic single-certificate work package. -/
theorem serializedCertificateVerifierWork_package
    (input : List Nat)
    (code : Nat) :
    (runSerializedCostCertificateVerifierWithWork input code).1 =
        runSerializedCostCertificateVerifier input code ∧
      (runSerializedParetoCertificateVerifierWithWork input code).1 =
        runSerializedParetoCertificateVerifier input code ∧
      (runSerializedCostCertificateVerifierWithWork input code).2 =
        4 *
          serializedCertificateVerifierInputSize input code ∧
      (runSerializedParetoCertificateVerifierWithWork input code).2 =
        4 *
          serializedCertificateVerifierInputSize input code := by

  exact
    ⟨rfl, rfl, rfl, rfl⟩

end SerializedCertificateVerifierWork

end CorrectedConcreteEncodedObservationSelectionData


namespace CorrectedConcreteEncodedObservationSelectionInstance

section MembershipBitLookup

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

/-- Pointwise correctness of the ordinary membership bit vector. -/
theorem costMembershipBits_get?_eq_some_one_iff
    (code : Nat) :
    instance.costMembershipBits.get? code = some 1 ↔
      code < instance.codeBound ∧
        code ∈ instance.costCertificateCodes := by

  by_cases hBound :
      code < instance.codeBound

  · simp [
      costMembershipBits,
      hBound
    ]

  · simp [
      costMembershipBits,
      hBound
    ]

/-- Pointwise correctness of the Pareto membership bit vector. -/
theorem paretoMembershipBits_get?_eq_some_one_iff
    (code : Nat) :
    instance.paretoMembershipBits.get? code = some 1 ↔
      code < instance.codeBound ∧
        code ∈ instance.paretoCertificateCodes := by

  by_cases hBound :
      code < instance.codeBound

  · simp [
      paretoMembershipBits,
      hBound
    ]

  · simp [
      paretoMembershipBits,
      hBound
    ]

end MembershipBitLookup


section SerializedCertificateCorrectness

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

/-- On a serialized encoded instance, ordinary certificate acceptance is
exactly stored ordinary-code membership. -/
theorem runSerializedCostCertificateVerifier_serialize_eq_true_iff
    (code : Nat) :
    CorrectedConcreteEncodedObservationSelectionData.runSerializedCostCertificateVerifier
          instance.serialize
          code =
        true ↔
      code < instance.codeBound ∧
        code ∈ instance.costCertificateCodes := by

  rw [
    CorrectedConcreteEncodedObservationSelectionData.runSerializedCostCertificateVerifier_of_decode
      instance.decode_serialize
  ]

  change
    code < instance.codeBound ∧
        instance.costMembershipBits.get? code = some 1 ↔
      code < instance.codeBound ∧
        code ∈ instance.costCertificateCodes

  rw [instance.costMembershipBits_get?_eq_some_one_iff]

  aesop

/-- On a serialized encoded instance, Pareto certificate acceptance is exactly
stored Pareto-code membership. -/
theorem runSerializedParetoCertificateVerifier_serialize_eq_true_iff
    (code : Nat) :
    CorrectedConcreteEncodedObservationSelectionData.runSerializedParetoCertificateVerifier
          instance.serialize
          code =
        true ↔
      code < instance.codeBound ∧
        code ∈ instance.paretoCertificateCodes := by

  rw [
    CorrectedConcreteEncodedObservationSelectionData.runSerializedParetoCertificateVerifier_of_decode
      instance.decode_serialize
  ]

  change
    code < instance.codeBound ∧
        instance.paretoMembershipBits.get? code = some 1 ↔
      code < instance.codeBound ∧
        code ∈ instance.paretoCertificateCodes

  rw [instance.paretoMembershipBits_get?_eq_some_one_iff]

  aesop

/-- Serialized ordinary certificate verification agrees with the earlier
finite-record executable verifier. -/
theorem runSerializedCostCertificateVerifier_serialize_iff_recordVerifier
    (code : Nat) :
    CorrectedConcreteEncodedObservationSelectionData.runSerializedCostCertificateVerifier
          instance.serialize
          code =
        true ↔
      instance.runCostCertificateVerifier code = true := by

  exact
    instance.runSerializedCostCertificateVerifier_serialize_eq_true_iff
      code
    |>.trans
      (instance.runCostCertificateVerifier_eq_true_iff
        code).symm

/-- Serialized Pareto certificate verification agrees with the earlier
finite-record executable verifier. -/
theorem runSerializedParetoCertificateVerifier_serialize_iff_recordVerifier
    (code : Nat) :
    CorrectedConcreteEncodedObservationSelectionData.runSerializedParetoCertificateVerifier
          instance.serialize
          code =
        true ↔
      instance.runParetoCertificateVerifier code = true := by

  exact
    instance.runSerializedParetoCertificateVerifier_serialize_eq_true_iff
      code
    |>.trans
      (instance.runParetoCertificateVerifier_eq_true_iff
        code).symm

/-- Serialized ordinary certificate verification agrees with the dense
semantic verifier. -/
theorem runSerializedCostCertificateVerifier_serialize_iff_denseVerifier
    (code : Nat) :
    CorrectedConcreteEncodedObservationSelectionData.runSerializedCostCertificateVerifier
          instance.serialize
          code =
        true ↔
      code < instance.codeBound ∧
        table.verifiesDenseCostCertificateCode
            instance.budget
            code =
          true := by

  exact
    instance.runSerializedCostCertificateVerifier_serialize_iff_recordVerifier
      code
    |>.trans
      (instance.runCostCertificateVerifier_eq_true_iff_denseVerifier
        code)

/-- Serialized Pareto certificate verification agrees with the dense semantic
verifier. -/
theorem runSerializedParetoCertificateVerifier_serialize_iff_denseVerifier
    (code : Nat) :
    CorrectedConcreteEncodedObservationSelectionData.runSerializedParetoCertificateVerifier
          instance.serialize
          code =
        true ↔
      code < instance.codeBound ∧
        table.verifiesDenseParetoScalarCertificateCode
            instance.budget
            code =
          true := by

  exact
    instance.runSerializedParetoCertificateVerifier_serialize_iff_recordVerifier
      code
    |>.trans
      (instance.runParetoCertificateVerifier_eq_true_iff_denseVerifier
        code)

/-- Every serialized ordinary witness decodes to a checked subset
certificate. -/
theorem runSerializedCostCertificateVerifier_decode_package
    {code : Nat}
    (hRun :
      CorrectedConcreteEncodedObservationSelectionData.runSerializedCostCertificateVerifier
            instance.serialize
            code =
          true) :
    ∃ certificate : Finset ι,
      correctedConcreteDenseCertificateDecode U code =
          some certificate ∧
        table.verifiesCostCertificate
            instance.budget
            certificate =
          true ∧
        certificate ⊆ U := by

  have hRecord :
      instance.runCostCertificateVerifier code = true :=
    (instance.runSerializedCostCertificateVerifier_serialize_iff_recordVerifier
      code).mp
      hRun

  exact
    instance.runCostCertificateVerifier_decode_package
      hRecord

/-- Every serialized Pareto witness decodes to a checked Pareto subset
certificate. -/
theorem runSerializedParetoCertificateVerifier_decode_package
    {code : Nat}
    (hRun :
      CorrectedConcreteEncodedObservationSelectionData.runSerializedParetoCertificateVerifier
            instance.serialize
            code =
          true) :
    ∃ certificate : Finset ι,
      correctedConcreteDenseCertificateDecode U code =
          some certificate ∧
        table.verifiesParetoScalarCertificate
            instance.budget
            certificate =
          true ∧
        certificate ⊆ U := by

  have hRecord :
      instance.runParetoCertificateVerifier code = true :=
    (instance.runSerializedParetoCertificateVerifier_serialize_iff_recordVerifier
      code).mp
      hRun

  exact
    instance.runParetoCertificateVerifier_decode_package
      hRecord

end SerializedCertificateCorrectness


section SerializedCertificateWorkOnInstance

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

/-- Exact pair-input size of a serialized encoded instance and any candidate
code. -/
theorem serialize_certificateVerifierInputSize
    (code : Nat) :
    CorrectedConcreteEncodedObservationSelectionData.serializedCertificateVerifierInputSize
          instance.serialize
          code =
      (2 + (instance.codeBound + instance.codeBound)) + 1 := by

  unfold CorrectedConcreteEncodedObservationSelectionData.serializedCertificateVerifierInputSize

  rw [instance.serialize_length]

/-- Exact ordinary single-certificate work on a serialized encoded instance. -/
theorem serialize_costCertificateVerifierWork
    (code : Nat) :
    (CorrectedConcreteEncodedObservationSelectionData.runSerializedCostCertificateVerifierWithWork
      instance.serialize
      code).2 =
        4 *
          ((2 +
              (instance.codeBound + instance.codeBound)) +
            1) := by

  rw [
    CorrectedConcreteEncodedObservationSelectionData.runSerializedCostCertificateVerifierWithWork_snd,
    instance.serialize_certificateVerifierInputSize
  ]

/-- Exact Pareto single-certificate work on a serialized encoded instance. -/
theorem serialize_paretoCertificateVerifierWork
    (code : Nat) :
    (CorrectedConcreteEncodedObservationSelectionData.runSerializedParetoCertificateVerifierWithWork
      instance.serialize
      code).2 =
        4 *
          ((2 +
              (instance.codeBound + instance.codeBound)) +
            1) := by

  rw [
    CorrectedConcreteEncodedObservationSelectionData.runSerializedParetoCertificateVerifierWithWork_snd,
    instance.serialize_certificateVerifierInputSize
  ]

end SerializedCertificateWorkOnInstance

end CorrectedConcreteEncodedObservationSelectionInstance


section EncodedSerializedCertificateVerifierFinalPackage

variable {α : Type u}
variable {ι : Type v}
variable {M : Type w}
variable [DecidableEq ι]
variable [Monoid M]
variable (obsFamily : ι → α → M)
variable (f : Nat)
variable (coordinateWeight : ι → Nat)
variable (U : Finset ι)

/-- Final positive-additive serialized single-witness package.

At the exact semantic minimum rank, the canonical least Pareto dense code is
accepted by the verifier that reads only the serialized natural-list input and
that code.  It is no larger than every other serialized Pareto witness, has the
exact linear work formula below, and decodes to the same canonical
Pareto-optimal certificate. -/
theorem
    correctedConcreteWorkingGrammar_observationSelectionEncodedSerializedCertificateVerifier_package
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
    let maxBudget :=
      correctedConcreteObservationSelectionPositiveAdditiveCost
        coordinateWeight
        U
    let hBound :
        minimumRank <= maxBudget :=
      ambientTargetObservationSelectionPositiveAdditiveMinimumCost_le
        (z := z)
        obsFamily
        f
        coordinateWeight
        U
        hTarget
    let hAccepted :=
      table.hasAcceptedParetoScalarBudgetUpTo_of_positiveAdditiveMinimum_le
        hTarget
        maxBudget
        hBound
    let canonicalCode :=
      table.selectedCanonicalDenseMinimumParetoScalarCode
        maxBudget
        hAccepted
    CorrectedConcreteEncodedObservationSelectionData.runSerializedParetoCertificateVerifier
          instance.serialize
          canonicalCode =
        true ∧
      canonicalCode < 2 ^ U.card ∧
      (∀ competingCode : Nat,
        CorrectedConcreteEncodedObservationSelectionData.runSerializedParetoCertificateVerifier
              instance.serialize
              competingCode =
            true →
          canonicalCode <= competingCode) ∧
      (CorrectedConcreteEncodedObservationSelectionData.runSerializedParetoCertificateVerifierWithWork
        instance.serialize
        canonicalCode).2 =
          4 *
            ((2 +
                (2 ^ U.card + 2 ^ U.card)) +
              1) ∧
      correctedConcreteDenseCertificateDecode
            U
            canonicalCode =
        some
          (table.canonicalMinimumParetoScalarCertificate
            (correctedConcreteDenseCertificateCode U)
            maxBudget
            hAccepted) ∧
      CorrectedConcreteObservationSelectionParetoOptimal
        (z := z)
        obsFamily
        f
        (correctedConcreteObservationSelectionAdditiveCost
          coordinateWeight)
        U
        language
        (table.canonicalMinimumParetoScalarCertificate
          (correctedConcreteDenseCertificateCode U)
          maxBudget
          hAccepted) := by

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

  let maxBudget :=
    correctedConcreteObservationSelectionPositiveAdditiveCost
      coordinateWeight
      U

  let hBound :
      minimumRank <= maxBudget :=
    ambientTargetObservationSelectionPositiveAdditiveMinimumCost_le
      (z := z)
      obsFamily
      f
      coordinateWeight
      U
      hTarget

  let hAccepted :=
    table.hasAcceptedParetoScalarBudgetUpTo_of_positiveAdditiveMinimum_le
      hTarget
      maxBudget
      hBound

  let canonicalCode :=
    table.selectedCanonicalDenseMinimumParetoScalarCode
      maxBudget
      hAccepted

  have hBudgetEq :
      table.selectedMinimumAcceptedParetoScalarBudget
            maxBudget
            hAccepted =
        minimumRank :=
    table.selectedMinimumAcceptedParetoScalarBudget_eq_positiveAdditiveMinimum
      hTarget
      maxBudget
      hBound

  have hDenseVerify :
      table.verifiesDenseParetoScalarCertificateCode
            minimumRank
            canonicalCode =
          true := by

    rw [← hBudgetEq]

    exact
      table.selectedCanonicalDenseMinimumParetoScalarCode_verifies
        maxBudget
        hAccepted

  have hCodeBound :
      canonicalCode < instance.codeBound := by

    simpa [
      instance,
      CorrectedConcreteObservationSelectionDecisionTable.encodedObservationSelectionInstance
    ] using
      table.selectedCanonicalDenseMinimumParetoScalarCode_lt
        maxBudget
        hAccepted

  have hSerialized :
      CorrectedConcreteEncodedObservationSelectionData.runSerializedParetoCertificateVerifier
            instance.serialize
            canonicalCode =
          true :=
    (instance.runSerializedParetoCertificateVerifier_serialize_iff_denseVerifier
      canonicalCode).mpr
      ⟨hCodeBound, hDenseVerify⟩

  have hLeast :
      ∀ competingCode : Nat,
        CorrectedConcreteEncodedObservationSelectionData.runSerializedParetoCertificateVerifier
              instance.serialize
              competingCode =
            true →
          canonicalCode <= competingCode := by

    intro competingCode hCompeting

    have hStoredParts :=
      (instance.runSerializedParetoCertificateVerifier_serialize_eq_true_iff
        competingCode).mp
        hCompeting

    have hVerifiedMem :
        competingCode ∈
          table.verifiedDenseParetoScalarCertificateCodes
            minimumRank := by

      change
        competingCode ∈ instance.paretoCertificateCodes

      exact hStoredParts.2

    rw [← hBudgetEq] at hVerifiedMem

    exact
      table.selectedCanonicalDenseMinimumParetoScalarCode_le
        maxBudget
        hAccepted
        hVerifiedMem

  exact
    ⟨hSerialized,
      by
        simpa [
          instance,
          CorrectedConcreteObservationSelectionDecisionTable.encodedObservationSelectionInstance
        ] using hCodeBound,
      hLeast,
      by
        simpa [
          instance.codeBound_correct
        ] using
          instance.serialize_paretoCertificateVerifierWork
            canonicalCode,
      table.selectedCanonicalDenseMinimumParetoScalarCode_decode
        maxBudget
        hAccepted,
      table.canonicalMinimumParetoScalarCertificate_paretoOptimal
        (correctedConcreteDenseCertificateCode U)
        maxBudget
        hAccepted⟩

end EncodedSerializedCertificateVerifierFinalPackage

end MCFG
