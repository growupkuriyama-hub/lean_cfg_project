/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG.ConcreteCanonicalLearnerWorkingGrammarObservationSelectionEncodedSerializedDecisionProblem

/-!
# ConcreteCanonicalLearnerWorkingGrammarObservationSelectionEncodedSerializedPolynomialDecisionProblem.lean

The preceding file defines ordinary-cost and Pareto serialized witness decision
problems on arbitrary pure `List Nat` inputs.  This file adds global polynomial
resource bounds.

A serialized polynomial witness decision problem consists of

* a Boolean decision on `List Nat`;
* a natural-number certificate verifier;
* explicit input-size, certificate-size, and verifier-work functions;
* exact decision/witness equivalence on every input;
* polynomial certificate-size and verifier-work bounds for every accepted
  certificate.

For the observation-selection serialization we use

```text
inputSize input        = input.length + 1
certificateSize code   = code + 1
verifierWork input code = 4 * (input.length + 1).
```

A successful decode forces the exact input-length equation

```text
input.length = 2 + (codeBound + codeBound).
```

Hence every accepted certificate satisfies `code < codeBound` and therefore
has unary size at most the serialized input size.  The verifier work has
coefficient four and degree one on every input, including malformed inputs.

Both ordinary-cost and Pareto-scalar global decision problems instantiate the
same resource-bounded interface.  On canonical encoded instances they agree
with the semantic decision table.  At the exact semantic positive-additive
minimum rank, the previous canonical Pareto dense code is a least polynomial
witness for the global Pareto problem and retains checked decoding and Pareto
optimality.

This is a formal polynomial witness theorem in the length of the already
materialized serialized table.  It is intentionally not identified with a
particular library's complexity class.  Canonical inputs still materialize an
exponential-size semantic table, so no compact-input NP-membership or hardness
claim is made.

No target grammar is supplied to any learner.
No `sorry`, `admit`, or `axiom` is used.
-/

namespace MCFG

universe u v w z


namespace CorrectedConcreteEncodedObservationSelectionData

section SuccessfulDecodeLength

/-- Successful decoding determines the exact serialized input length. -/
theorem input_length_eq_of_decode_eq_some
    {input : List Nat}
    {data :
      CorrectedConcreteEncodedObservationSelectionData}
    (hDecode :
      decode input = some data) :
    input.length =
      2 + (data.codeBound + data.codeBound) := by

  cases input with

  | nil =>
      simp [decode] at hDecode

  | cons budget tail =>
      cases tail with

      | nil =>
          simp [decode] at hDecode

      | cons codeBound payload =>
          by_cases hLength :
              payload.length =
                codeBound + codeBound

          · simp [decode, hLength] at hDecode

            subst data

            simp [hLength]

          · simp [decode, hLength] at hDecode

/-- A successfully decoded code bound is at most the serialized input length. -/
theorem codeBound_le_input_length_of_decode_eq_some
    {input : List Nat}
    {data :
      CorrectedConcreteEncodedObservationSelectionData}
    (hDecode :
      decode input = some data) :
    data.codeBound <= input.length := by

  rw [input_length_eq_of_decode_eq_some hDecode]

  omega

/-- Every accepted ordinary serialized certificate has unary code size bounded
by the serialized input size. -/
theorem acceptedCostCertificate_size_le_input
    {input : List Nat}
    {code : Nat}
    (hAccepted :
      runSerializedCostCertificateVerifier
          input
          code =
        true) :
    code + 1 <= input.length + 1 := by

  rcases
      (runSerializedCostCertificateVerifier_eq_true_iff
        input
        code).mp
        hAccepted with
    ⟨data, hDecode, hCodeBound, hGet⟩

  have hBoundLe :
      data.codeBound <= input.length :=
    codeBound_le_input_length_of_decode_eq_some
      hDecode

  omega

/-- Every accepted Pareto serialized certificate has unary code size bounded
by the serialized input size. -/
theorem acceptedParetoCertificate_size_le_input
    {input : List Nat}
    {code : Nat}
    (hAccepted :
      runSerializedParetoCertificateVerifier
          input
          code =
        true) :
    code + 1 <= input.length + 1 := by

  rcases
      (runSerializedParetoCertificateVerifier_eq_true_iff
        input
        code).mp
        hAccepted with
    ⟨data, hDecode, hCodeBound, hGet⟩

  have hBoundLe :
      data.codeBound <= input.length :=
    codeBound_le_input_length_of_decode_eq_some
      hDecode

  omega

end SuccessfulDecodeLength

end CorrectedConcreteEncodedObservationSelectionData


/-- A global serialized witness decision problem with polynomial certificate
and verifier resource bounds. -/
structure CorrectedConcreteSerializedPolynomialWitnessDecisionProblem where

  decision :
    List Nat → Bool

  verifier :
    List Nat → Nat → Bool

  inputSize :
    List Nat → Nat

  certificateSize :
    Nat → Nat

  verifierWork :
    List Nat → Nat → Nat

  certificateCoefficient : Nat

  certificateDegree : Nat

  verifierCoefficient : Nat

  verifierDegree : Nat

  inputSize_eq :
    ∀ input : List Nat,
      inputSize input = input.length + 1

  decision_eq_true_iff_exists :
    ∀ input : List Nat,
      decision input = true ↔
        ∃ code : Nat,
          verifier input code = true

  certificateSize_le :
    ∀ input : List Nat,
      ∀ code : Nat,
        verifier input code = true →
          certificateSize code <=
            certificateCoefficient *
              inputSize input ^
                certificateDegree

  verifierWork_le :
    ∀ input : List Nat,
      ∀ code : Nat,
        verifier input code = true →
          verifierWork input code <=
            verifierCoefficient *
              inputSize input ^
                verifierDegree


namespace CorrectedConcreteSerializedPolynomialWitnessDecisionProblem

section GenericPolynomialDecisionProblem

variable
  (problem :
    CorrectedConcreteSerializedPolynomialWitnessDecisionProblem)

/-- Language accepted by the polynomial serialized decision problem. -/
def AcceptedLanguage :
    Set (List Nat) :=
  {input |
    problem.decision input = true}

/-- Witness relation of the polynomial serialized decision problem. -/
def Witness
    (input : List Nat)
    (code : Nat) : Prop :=
  problem.verifier input code = true

/-- A witness carrying the resource bounds for one accepted input. -/
structure PolynomialWitness
    (input : List Nat) where

  code : Nat

  accepted :
    problem.Witness input code

  certificateSize_le :
    problem.certificateSize code <=
      problem.certificateCoefficient *
        problem.inputSize input ^
          problem.certificateDegree

  verifierWork_le :
    problem.verifierWork input code <=
      problem.verifierCoefficient *
        problem.inputSize input ^
          problem.verifierDegree

/-- Exact accepted-language/witness equivalence. -/
theorem mem_acceptedLanguage_iff_exists_witness
    (input : List Nat) :
    input ∈ problem.AcceptedLanguage ↔
      ∃ code : Nat,
        problem.Witness input code := by

  exact
    problem.decision_eq_true_iff_exists
      input

/-- Package any accepted code as a polynomial witness. -/
def polynomialWitnessOfAccepted
    (input : List Nat)
    (code : Nat)
    (hAccepted :
      problem.Witness input code) :
    problem.PolynomialWitness input :=
  {
    code := code

    accepted := hAccepted

    certificateSize_le :=
      problem.certificateSize_le
        input
        code
        hAccepted

    verifierWork_le :=
      problem.verifierWork_le
        input
        code
        hAccepted
  }

/-- Every accepted input has a polynomial witness. -/
noncomputable def selectedPolynomialWitness
    (input : List Nat)
    (hAccepted :
      input ∈ problem.AcceptedLanguage) :
    problem.PolynomialWitness input := by

  rcases
      (problem.mem_acceptedLanguage_iff_exists_witness
        input).mp
        hAccepted with
    ⟨code, hWitness⟩

  exact
    problem.polynomialWitnessOfAccepted
      input
      code
      hWitness

/-- Rejected inputs have no witnesses. -/
theorem no_witness_of_not_mem
    {input : List Nat}
    (hRejected :
      input ∉ problem.AcceptedLanguage) :
    ¬ ∃ code : Nat,
        problem.Witness input code := by

  intro hWitness

  exact
    hRejected
      ((problem.mem_acceptedLanguage_iff_exists_witness
        input).mpr
        hWitness)

/-- Complete generic global polynomial witness package. -/
theorem package
    (input : List Nat) :
    (input ∈ problem.AcceptedLanguage ↔
      ∃ code : Nat,
        problem.Witness input code) ∧
      (∀ code : Nat,
        problem.Witness input code →
          problem.certificateSize code <=
            problem.certificateCoefficient *
              problem.inputSize input ^
                problem.certificateDegree) ∧
      (∀ code : Nat,
        problem.Witness input code →
          problem.verifierWork input code <=
            problem.verifierCoefficient *
              problem.inputSize input ^
                problem.verifierDegree) := by

  exact
    ⟨problem.mem_acceptedLanguage_iff_exists_witness
      input,
      problem.certificateSize_le input,
      problem.verifierWork_le input⟩

end GenericPolynomialDecisionProblem

end CorrectedConcreteSerializedPolynomialWitnessDecisionProblem


namespace CorrectedConcreteEncodedObservationSelectionData

section GlobalPolynomialDecisionProblems

/-- Global ordinary-cost serialized polynomial witness decision problem. -/
def serializedCostPolynomialWitnessDecisionProblem :
    CorrectedConcreteSerializedPolynomialWitnessDecisionProblem :=
  {
    decision :=
      runSerializedCostDecision

    verifier :=
      runSerializedCostCertificateVerifier

    inputSize :=
      fun input =>
        input.length + 1

    certificateSize :=
      serializedWitnessCertificateSize

    verifierWork :=
      serializedCertificateVerifierWork

    certificateCoefficient := 1

    certificateDegree := 1

    verifierCoefficient := 4

    verifierDegree := 1

    inputSize_eq := by
      intro input

      rfl

    decision_eq_true_iff_exists :=
      runSerializedCostDecision_eq_true_iff_exists_certificate

    certificateSize_le := by
      intro input code hAccepted

      have hSize :
          code + 1 <= input.length + 1 :=
        acceptedCostCertificate_size_le_input
          hAccepted

      simpa [
        serializedWitnessCertificateSize
      ] using hSize

    verifierWork_le := by
      intro input code hAccepted

      simp [
        serializedCertificateVerifierWork,
        serializedCertificateVerifierInputSize
      ]
  }

/-- Global Pareto-scalar serialized polynomial witness decision problem. -/
def serializedParetoPolynomialWitnessDecisionProblem :
    CorrectedConcreteSerializedPolynomialWitnessDecisionProblem :=
  {
    decision :=
      runSerializedParetoDecision

    verifier :=
      runSerializedParetoCertificateVerifier

    inputSize :=
      fun input =>
        input.length + 1

    certificateSize :=
      serializedWitnessCertificateSize

    verifierWork :=
      serializedCertificateVerifierWork

    certificateCoefficient := 1

    certificateDegree := 1

    verifierCoefficient := 4

    verifierDegree := 1

    inputSize_eq := by
      intro input

      rfl

    decision_eq_true_iff_exists :=
      runSerializedParetoDecision_eq_true_iff_exists_certificate

    certificateSize_le := by
      intro input code hAccepted

      have hSize :
          code + 1 <= input.length + 1 :=
        acceptedParetoCertificate_size_le_input
          hAccepted

      simpa [
        serializedWitnessCertificateSize
      ] using hSize

    verifierWork_le := by
      intro input code hAccepted

      simp [
        serializedCertificateVerifierWork,
        serializedCertificateVerifierInputSize
      ]
  }

@[simp]
theorem serializedCostPolynomialWitnessDecisionProblem_coefficients :
    serializedCostPolynomialWitnessDecisionProblem.certificateCoefficient = 1 ∧
      serializedCostPolynomialWitnessDecisionProblem.certificateDegree = 1 ∧
      serializedCostPolynomialWitnessDecisionProblem.verifierCoefficient = 4 ∧
      serializedCostPolynomialWitnessDecisionProblem.verifierDegree = 1 := by

  exact ⟨rfl, rfl, rfl, rfl⟩

@[simp]
theorem serializedParetoPolynomialWitnessDecisionProblem_coefficients :
    serializedParetoPolynomialWitnessDecisionProblem.certificateCoefficient = 1 ∧
      serializedParetoPolynomialWitnessDecisionProblem.certificateDegree = 1 ∧
      serializedParetoPolynomialWitnessDecisionProblem.verifierCoefficient = 4 ∧
      serializedParetoPolynomialWitnessDecisionProblem.verifierDegree = 1 := by

  exact ⟨rfl, rfl, rfl, rfl⟩

/-- Both global serialized problems have exact witness equivalence and
degree-one certificate/verifier bounds on every input. -/
theorem serializedPolynomialWitnessDecisionProblem_package
    (input : List Nat) :
    (input ∈
        serializedCostPolynomialWitnessDecisionProblem.AcceptedLanguage ↔
      ∃ code : Nat,
        serializedCostPolynomialWitnessDecisionProblem.Witness
          input
          code) ∧
      (input ∈
          serializedParetoPolynomialWitnessDecisionProblem.AcceptedLanguage ↔
        ∃ code : Nat,
          serializedParetoPolynomialWitnessDecisionProblem.Witness
            input
            code) ∧
      serializedCostPolynomialWitnessDecisionProblem.certificateCoefficient =
        1 ∧
      serializedCostPolynomialWitnessDecisionProblem.certificateDegree =
        1 ∧
      serializedCostPolynomialWitnessDecisionProblem.verifierCoefficient =
        4 ∧
      serializedCostPolynomialWitnessDecisionProblem.verifierDegree =
        1 ∧
      serializedParetoPolynomialWitnessDecisionProblem.certificateCoefficient =
        1 ∧
      serializedParetoPolynomialWitnessDecisionProblem.certificateDegree =
        1 ∧
      serializedParetoPolynomialWitnessDecisionProblem.verifierCoefficient =
        4 ∧
      serializedParetoPolynomialWitnessDecisionProblem.verifierDegree =
        1 := by

  exact
    ⟨serializedCostPolynomialWitnessDecisionProblem.mem_acceptedLanguage_iff_exists_witness
      input,
      serializedParetoPolynomialWitnessDecisionProblem.mem_acceptedLanguage_iff_exists_witness
        input,
      rfl,
      rfl,
      rfl,
      rfl,
      rfl,
      rfl,
      rfl,
      rfl⟩

end GlobalPolynomialDecisionProblems

end CorrectedConcreteEncodedObservationSelectionData


namespace CorrectedConcreteEncodedObservationSelectionInstance

section PolynomialDecisionProblemOnCanonicalInstance

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

/-- Global ordinary polynomial decision agrees with the semantic table on a
canonical instance. -/
theorem serializedCostPolynomialDecisionProblem_serialize_iff_tableDecision :
    instance.serialize ∈
        CorrectedConcreteEncodedObservationSelectionData.serializedCostPolynomialWitnessDecisionProblem.AcceptedLanguage ↔
      table.costFeasibleDecision instance.budget = true := by

  exact
    instance.runSerializedCostDecision_serialize_iff_tableDecision

/-- Global Pareto polynomial decision agrees with the semantic table on a
canonical instance. -/
theorem serializedParetoPolynomialDecisionProblem_serialize_iff_tableDecision :
    instance.serialize ∈
        CorrectedConcreteEncodedObservationSelectionData.serializedParetoPolynomialWitnessDecisionProblem.AcceptedLanguage ↔
      table.paretoScalarFeasibleDecision
          instance.budget =
        true := by

  exact
    instance.runSerializedParetoDecision_serialize_iff_tableDecision

/-- Global ordinary polynomial witness acceptance agrees with the dense
semantic verifier. -/
theorem serializedCostPolynomialDecisionProblem_serialize_witness_iff_denseVerifier
    (code : Nat) :
    CorrectedConcreteEncodedObservationSelectionData.serializedCostPolynomialWitnessDecisionProblem.Witness
          instance.serialize
          code ↔
      code < instance.codeBound ∧
        table.verifiesDenseCostCertificateCode
            instance.budget
            code =
          true := by

  exact
    instance.runSerializedCostCertificateVerifier_serialize_iff_denseVerifier
      code

/-- Global Pareto polynomial witness acceptance agrees with the dense semantic
verifier. -/
theorem serializedParetoPolynomialDecisionProblem_serialize_witness_iff_denseVerifier
    (code : Nat) :
    CorrectedConcreteEncodedObservationSelectionData.serializedParetoPolynomialWitnessDecisionProblem.Witness
          instance.serialize
          code ↔
      code < instance.codeBound ∧
        table.verifiesDenseParetoScalarCertificateCode
            instance.budget
            code =
          true := by

  exact
    instance.runSerializedParetoCertificateVerifier_serialize_iff_denseVerifier
      code

end PolynomialDecisionProblemOnCanonicalInstance

end CorrectedConcreteEncodedObservationSelectionInstance


section EncodedSerializedPolynomialDecisionProblemFinalPackage

variable {α : Type u}
variable {ι : Type v}
variable {M : Type w}
variable [DecidableEq ι]
variable [Monoid M]
variable (obsFamily : ι → α → M)
variable (f : Nat)
variable (coordinateWeight : ι → Nat)
variable (U : Finset ι)

/-- Final global polynomial decision-problem package.

At the exact semantic positive-additive minimum rank, the canonical serialized
input belongs to the global Pareto polynomial accepted language.  The previous
canonical dense code is a least polynomial witness with degree-one
certificate-size and verifier-work bounds, remains below `2 ^ U.card`, and
decodes to the same Pareto-optimal certificate. -/
theorem
    correctedConcreteWorkingGrammar_observationSelectionEncodedSerializedPolynomialDecisionProblem_package
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
      table.serializedNPStyleMinimumRank hTarget
    let instance :=
      table.encodedObservationSelectionInstance minimumRank
    let problem :=
      CorrectedConcreteEncodedObservationSelectionData.serializedParetoPolynomialWitnessDecisionProblem
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
    instance.serialize ∈ problem.AcceptedLanguage ∧
      problem.Witness instance.serialize canonicalCode ∧
      (∀ competingCode : Nat,
        problem.Witness instance.serialize competingCode →
          canonicalCode <= competingCode) ∧
      problem.certificateSize canonicalCode <=
        problem.certificateCoefficient *
          problem.inputSize instance.serialize ^
            problem.certificateDegree ∧
      problem.verifierWork instance.serialize canonicalCode <=
        problem.verifierCoefficient *
          problem.inputSize instance.serialize ^
            problem.verifierDegree ∧
      problem.certificateCoefficient = 1 ∧
      problem.certificateDegree = 1 ∧
      problem.verifierCoefficient = 4 ∧
      problem.verifierDegree = 1 ∧
      canonicalCode < 2 ^ U.card ∧
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
    table.serializedNPStyleMinimumRank hTarget

  let instance :=
    table.encodedObservationSelectionInstance minimumRank

  let problem :=
    CorrectedConcreteEncodedObservationSelectionData.serializedParetoPolynomialWitnessDecisionProblem

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

  have hCanonical :=
    correctedConcreteWorkingGrammar_observationSelectionEncodedSerializedCertificateVerifier_package
      (z := z)
      obsFamily
      f
      coordinateWeight
      U
      language
      hTarget

  rcases hCanonical with
    ⟨hAcceptedCode,
      hCodeBound,
      hLeast,
      hWork,
      hDecode,
      hPareto⟩

  have hProblemWitness :
      problem.Witness instance.serialize canonicalCode :=
    hAcceptedCode

  have hProblemAccepted :
      instance.serialize ∈ problem.AcceptedLanguage :=
    (problem.mem_acceptedLanguage_iff_exists_witness
      instance.serialize).mpr
      ⟨canonicalCode, hProblemWitness⟩

  exact
    ⟨hProblemAccepted,
      hProblemWitness,
      by
        intro competingCode hCompeting

        exact
          hLeast
            competingCode
            hCompeting,
      problem.certificateSize_le
        instance.serialize
        canonicalCode
        hProblemWitness,
      problem.verifierWork_le
        instance.serialize
        canonicalCode
        hProblemWitness,
      rfl,
      rfl,
      rfl,
      rfl,
      hCodeBound,
      hDecode,
      hPareto⟩

end EncodedSerializedPolynomialDecisionProblemFinalPackage

end MCFG
