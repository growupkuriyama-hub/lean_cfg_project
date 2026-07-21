/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG.ConcreteCanonicalLearnerWorkingGrammarObservationSelectionEncodedCompactVerifier

/-!
# ConcreteCanonicalLearnerWorkingGrammarObservationSelectionEncodedCompactVerifierRuntime.lean

The preceding file isolates a direct compact certificate verifier without
materializing the complete feasibility truth table.  This file adds an explicit
counted-runtime interface.

A counted compact verifier supplies

```text
runWithWork : CompactInput → Nat → Bool × Nat
```

and proves

```text
(runWithWork input code).1
  = runCertificateVerifier input code

(runWithWork input code).2
  ≤ coefficient * compactInputSize input ^ degree.
```

The second component is intended to be the operation count of the concrete
verifier implementation.  The runtime theorem is required for every input and
certificate, including malformed and rejecting inputs.

Certificate length is measured as a fixed-width dense subset code:

```text
compactCertificateLength input code
  = coordinateCount
```

after successful decoding, and zero on malformed input.  Every accepted
certificate therefore has length at most the compact serialized input length.
This avoids the inappropriate unary measure `code + 1`, which can be
exponential in the coordinate count.

From a counted runtime we derive

* exact runtime-result/verifier agreement;
* decision iff existence of a runtime-accepted certificate;
* polynomial certificate-length and verifier-work witnesses;
* malformed-input rejection;
* complete packages on checked compact encodings.

A logical envelope reference runtime is also supplied to show that the API is
inhabited.  Its declared work is the input size itself; it is not a genuine
operation count for evaluating an arbitrary semantic `Feasible` predicate.
A real compact complexity theorem must replace it with an implementation whose
second component counts the actual decoding and feasibility-checking steps.

The exhaustive whole-instance decision may inspect up to
`2 ^ coordinateCount` certificates.  This file claims polynomial time only for
verification of one supplied certificate, as required by an NP-style witness
interface.

No compact-input standard-library NP membership, hardness, or NP-completeness
claim is made.
No target grammar is supplied to any learner.
No `sorry`, `admit`, or `axiom` is used.
-/

namespace MCFG


namespace CorrectedConcreteObservationSelectionCompactData

section SuccessfulDecodeBounds

/-- Successful compact decoding implies that the decoded coordinate count is
bounded by the serialized input length. -/
theorem coordinateCount_le_input_length_of_decode_eq_some
    {input : List Nat}
    {data :
      CorrectedConcreteObservationSelectionCompactData}
    (hDecode :
      decode input = some data) :
    data.coordinateCount <= input.length := by

  cases input with

  | nil =>
      simp [decode] at hDecode

  | cons coordinateCount tail₁ =>
      cases tail₁ with

      | nil =>
          simp [decode] at hDecode

      | cons budget tail₂ =>
          cases tail₂ with

          | nil =>
              simp [decode] at hDecode

          | cons weightLength tail₃ =>
              cases tail₃ with

              | nil =>
                  simp [decode] at hDecode

              | cons payloadLength body =>
                  by_cases hWeights :
                      weightLength = coordinateCount

                  · by_cases hBody :
                        body.length =
                          weightLength + payloadLength

                    · simp [
                        decode,
                        hWeights,
                        hBody
                      ] at hDecode

                      subst data

                      simp only [
                        List.length_cons
                      ]

                      omega

                    · simp [
                        decode,
                        hWeights,
                        hBody
                      ] at hDecode

                  · simp [
                      decode,
                      hWeights
                    ] at hDecode

/-- Successful compact decoding implies the same bound under the nonzero input
size convention. -/
theorem coordinateCount_le_inputSize_of_decode_eq_some
    {input : List Nat}
    {data :
      CorrectedConcreteObservationSelectionCompactData}
    (hDecode :
      decode input = some data) :
    data.coordinateCount <= input.length + 1 := by

  exact
    Nat.le_trans
      (coordinateCount_le_input_length_of_decode_eq_some
        hDecode)
      (Nat.le_add_right
        input.length
        1)

end SuccessfulDecodeBounds

end CorrectedConcreteObservationSelectionCompactData


namespace CorrectedConcreteObservationSelectionCompactVerifierSpecification

section CompactResourceMeasures

/-- Nonzero serialized compact-input size. -/
def compactInputSize
    (input :
      CorrectedConcreteObservationSelectionCompactInput) :
    Nat :=
  input.payload.length + 1

/-- Fixed-width dense certificate length.

After successful decoding, one subset code is represented using exactly the
coordinate count as its declared bit width.  Malformed inputs receive length
zero. -/
def compactCertificateLength
    (input :
      CorrectedConcreteObservationSelectionCompactInput)
    (_code : Nat) :
    Nat :=
  match
    CorrectedConcreteObservationSelectionCompactData.decode
      input.payload with

  | some data =>
      data.coordinateCount

  | none =>
      0

/-- Every certificate accepted by a direct compact verifier has fixed-width
length bounded by the compact input size. -/
theorem compactCertificateLength_le_inputSize
    (specification :
      CorrectedConcreteObservationSelectionCompactVerifierSpecification)
    {input :
      CorrectedConcreteObservationSelectionCompactInput}
    {code : Nat}
    (hAccepted :
      specification.runCertificateVerifier
          input
          code =
        true) :
    compactCertificateLength input code <=
      compactInputSize input := by

  rcases
      (specification.runCertificateVerifier_eq_true_iff
        input
        code).mp
        hAccepted with
    ⟨data,
      hDecode,
      hCodeBound,
      hFeasible⟩

  unfold compactCertificateLength
  unfold compactInputSize

  rw [hDecode]

  exact
    CorrectedConcreteObservationSelectionCompactData.coordinateCount_le_inputSize_of_decode_eq_some
      hDecode

/-- Degree-one form of the compact certificate-length bound. -/
theorem compactCertificateLength_polynomial_le
    (specification :
      CorrectedConcreteObservationSelectionCompactVerifierSpecification)
    {input :
      CorrectedConcreteObservationSelectionCompactInput}
    {code : Nat}
    (hAccepted :
      specification.runCertificateVerifier
          input
          code =
        true) :
    compactCertificateLength input code <=
      1 * compactInputSize input ^ 1 := by

  simpa using
    specification.compactCertificateLength_le_inputSize
      hAccepted

end CompactResourceMeasures

end CorrectedConcreteObservationSelectionCompactVerifierSpecification


/-- Counted implementation of one direct compact certificate verifier. -/
structure CorrectedConcreteObservationSelectionCompactVerifierRuntimeSpecification where

  verifierSpecification :
    CorrectedConcreteObservationSelectionCompactVerifierSpecification

  runWithWork :
    CorrectedConcreteObservationSelectionCompactInput →
      Nat →
        Bool × Nat

  result_eq :
    ∀ input :
        CorrectedConcreteObservationSelectionCompactInput,
      ∀ code : Nat,
        (runWithWork input code).1 =
          verifierSpecification.runCertificateVerifier
            input
            code

  workCoefficient : Nat

  workDegree : Nat

  work_le :
    ∀ input :
        CorrectedConcreteObservationSelectionCompactInput,
      ∀ code : Nat,
        (runWithWork input code).2 <=
          workCoefficient *
            CorrectedConcreteObservationSelectionCompactVerifierSpecification.compactInputSize
                input ^
              workDegree


namespace CorrectedConcreteObservationSelectionCompactVerifierRuntimeSpecification

section GenericCountedRuntime

variable
  (runtime :
    CorrectedConcreteObservationSelectionCompactVerifierRuntimeSpecification)

/-- Boolean result returned by the counted compact verifier. -/
def result
    (input :
      CorrectedConcreteObservationSelectionCompactInput)
    (code : Nat) :
    Bool :=
  (runtime.runWithWork input code).1

/-- Operation count returned by the counted compact verifier. -/
def work
    (input :
      CorrectedConcreteObservationSelectionCompactInput)
    (code : Nat) :
    Nat :=
  (runtime.runWithWork input code).2

/-- The counted implementation returns exactly the verified compact Boolean
result. -/
theorem result_eq_runCertificateVerifier
    (input :
      CorrectedConcreteObservationSelectionCompactInput)
    (code : Nat) :
    runtime.result input code =
      runtime.verifierSpecification.runCertificateVerifier
        input
        code := by

  exact
    runtime.result_eq
      input
      code

/-- Counted acceptance agrees exactly with the compact semantic verifier
relation. -/
theorem result_eq_true_iff
    (input :
      CorrectedConcreteObservationSelectionCompactInput)
    (code : Nat) :
    runtime.result input code = true ↔
      ∃ data :
          CorrectedConcreteObservationSelectionCompactData,
        CorrectedConcreteObservationSelectionCompactData.decode
              input.payload =
            some data ∧
          code < data.candidateCodeBound ∧
          runtime.verifierSpecification.Feasible
            data
            code := by

  rw [
    runtime.result_eq_runCertificateVerifier
      input
      code
  ]

  exact
    runtime.verifierSpecification.runCertificateVerifier_eq_true_iff
      input
      code

/-- The compact whole-instance decision is positive exactly when some
certificate is accepted by the counted implementation. -/
theorem runDecision_eq_true_iff_exists_result
    (input :
      CorrectedConcreteObservationSelectionCompactInput) :
    runtime.verifierSpecification.runDecision input = true ↔
      ∃ code : Nat,
        runtime.result input code = true := by

  rw [
    runtime.verifierSpecification.runDecision_eq_true_iff_exists_certificate
      input
  ]

  constructor

  · rintro ⟨code, hAccepted⟩

    exact
      ⟨code,
        by
          rw [
            runtime.result_eq_runCertificateVerifier
              input
              code
          ]

          exact hAccepted⟩

  · rintro ⟨code, hAccepted⟩

    exact
      ⟨code,
        by
          rw [
            ← runtime.result_eq_runCertificateVerifier
              input
              code
          ]

          exact hAccepted⟩

/-- Declared counted work obeys its polynomial envelope on every input and
certificate. -/
theorem work_polynomial_le
    (input :
      CorrectedConcreteObservationSelectionCompactInput)
    (code : Nat) :
    runtime.work input code <=
      runtime.workCoefficient *
        CorrectedConcreteObservationSelectionCompactVerifierSpecification.compactInputSize
            input ^
          runtime.workDegree := by

  exact
    runtime.work_le
      input
      code

/-- One accepted compact certificate carrying fixed-width certificate and
counted-runtime bounds. -/
structure PolynomialWitness
    (input :
      CorrectedConcreteObservationSelectionCompactInput) where

  code : Nat

  accepted :
    runtime.result input code = true

  certificateLength_le :
    CorrectedConcreteObservationSelectionCompactVerifierSpecification.compactCertificateLength
          input
          code <=
      1 *
        CorrectedConcreteObservationSelectionCompactVerifierSpecification.compactInputSize
            input ^
          1

  work_le :
    runtime.work input code <=
      runtime.workCoefficient *
        CorrectedConcreteObservationSelectionCompactVerifierSpecification.compactInputSize
            input ^
          runtime.workDegree

/-- Package one counted accepted code as a polynomial witness. -/
def polynomialWitnessOfAccepted
    (input :
      CorrectedConcreteObservationSelectionCompactInput)
    (code : Nat)
    (hAccepted :
      runtime.result input code =
        true) :
    runtime.PolynomialWitness input :=
  {
    code :=
      code

    accepted :=
      hAccepted

    certificateLength_le := by
      apply
        runtime.verifierSpecification.compactCertificateLength_polynomial_le

      rw [
        ← runtime.result_eq_runCertificateVerifier
          input
          code
      ]

      exact hAccepted

    work_le :=
      runtime.work_polynomial_le
        input
        code
  }

/-- Every positive compact decision has a counted polynomial witness. -/
noncomputable def selectedPolynomialWitness
    (input :
      CorrectedConcreteObservationSelectionCompactInput)
    (hDecision :
      runtime.verifierSpecification.runDecision
            input =
          true) :
    runtime.PolynomialWitness input := by

  rcases
      (runtime.runDecision_eq_true_iff_exists_result
        input).mp
        hDecision with
    ⟨code, hAccepted⟩

  exact
    runtime.polynomialWitnessOfAccepted
      input
      code
      hAccepted

/-- Malformed compact inputs are rejected by the counted verifier result. -/
theorem result_eq_false_of_decode_eq_none
    {input :
      CorrectedConcreteObservationSelectionCompactInput}
    (hDecode :
      CorrectedConcreteObservationSelectionCompactData.decode
          input.payload =
        none)
    (code : Nat) :
    runtime.result input code =
      false := by

  rw [
    runtime.result_eq_runCertificateVerifier
      input
      code
  ]

  exact
    runtime.verifierSpecification.runCertificateVerifier_eq_false_of_decode_eq_none
      hDecode
      code

/-- Complete counted-runtime package on one compact input. -/
theorem package
    (input :
      CorrectedConcreteObservationSelectionCompactInput) :
    (runtime.verifierSpecification.runDecision input = true ↔
      ∃ code : Nat,
        runtime.result input code = true) ∧
      (∀ code : Nat,
        runtime.result input code = true →
          CorrectedConcreteObservationSelectionCompactVerifierSpecification.compactCertificateLength
                input
                code <=
            1 *
              CorrectedConcreteObservationSelectionCompactVerifierSpecification.compactInputSize
                  input ^
                1) ∧
      (∀ code : Nat,
        runtime.work input code <=
          runtime.workCoefficient *
            CorrectedConcreteObservationSelectionCompactVerifierSpecification.compactInputSize
                input ^
              runtime.workDegree) := by

  exact
    ⟨runtime.runDecision_eq_true_iff_exists_result
      input,
      by
        intro code hAccepted

        apply
          runtime.verifierSpecification.compactCertificateLength_polynomial_le

        rw [
          ← runtime.result_eq_runCertificateVerifier
            input
            code
        ]

        exact hAccepted,
      runtime.work_polynomial_le
        input⟩

end GenericCountedRuntime


section LogicalEnvelopeReferenceRuntime

/-- Logical envelope reference runtime.

The Boolean result is the direct compact verifier, while the declared work is
the compact input size.  This demonstrates the runtime API but does not count
the internal computation of an arbitrary semantic feasibility predicate. -/
def logicalEnvelopeReference
    (specification :
      CorrectedConcreteObservationSelectionCompactVerifierSpecification) :
    CorrectedConcreteObservationSelectionCompactVerifierRuntimeSpecification :=
  {
    verifierSpecification :=
      specification

    runWithWork :=
      fun input code =>
        (specification.runCertificateVerifier input code,
          CorrectedConcreteObservationSelectionCompactVerifierSpecification.compactInputSize
            input)

    result_eq := by
      intro input code

      rfl

    workCoefficient :=
      1

    workDegree :=
      1

    work_le := by
      intro input code

      simp
  }

@[simp]
theorem logicalEnvelopeReference_result
    (specification :
      CorrectedConcreteObservationSelectionCompactVerifierSpecification)
    (input :
      CorrectedConcreteObservationSelectionCompactInput)
    (code : Nat) :
    (logicalEnvelopeReference specification).result
          input
          code =
      specification.runCertificateVerifier
        input
        code := by

  rfl

@[simp]
theorem logicalEnvelopeReference_work
    (specification :
      CorrectedConcreteObservationSelectionCompactVerifierSpecification)
    (input :
      CorrectedConcreteObservationSelectionCompactInput)
    (code : Nat) :
    (logicalEnvelopeReference specification).work
          input
          code =
      CorrectedConcreteObservationSelectionCompactVerifierSpecification.compactInputSize
        input := by

  rfl

end LogicalEnvelopeReferenceRuntime

end CorrectedConcreteObservationSelectionCompactVerifierRuntimeSpecification


section EncodedCompactVerifierRuntimeFinalPackage

variable
  (runtime :
    CorrectedConcreteObservationSelectionCompactVerifierRuntimeSpecification)

/-- Final counted compact-verifier package on one checked compact record.

This theorem is conditional on the supplied counted runtime.  Instantiating it
with a genuine compact grammar-level verifier and an actual operation count is
the remaining runtime construction obligation. -/
theorem
    correctedConcreteWorkingGrammar_observationSelectionEncodedCompactVerifierRuntime_package
    (data :
      CorrectedConcreteObservationSelectionCompactData)
    (hWellFormed :
      data.WellFormed) :
    let input :
        CorrectedConcreteObservationSelectionCompactInput :=
      CorrectedConcreteObservationSelectionCompactInput.ofData
        data
    CorrectedConcreteObservationSelectionCompactData.decode
          input.payload =
        some data ∧
      (runtime.verifierSpecification.runDecision input = true ↔
        ∃ code : Nat,
          runtime.result input code = true) ∧
      (∀ code : Nat,
        runtime.result input code = true ↔
          code < data.candidateCodeBound ∧
            runtime.verifierSpecification.Feasible
              data
              code) ∧
      (∀ code : Nat,
        runtime.result input code = true →
          CorrectedConcreteObservationSelectionCompactVerifierSpecification.compactCertificateLength
                input
                code <=
            CorrectedConcreteObservationSelectionCompactVerifierSpecification.compactInputSize
              input) ∧
      (∀ code : Nat,
        runtime.work input code <=
          runtime.workCoefficient *
            CorrectedConcreteObservationSelectionCompactVerifierSpecification.compactInputSize
                input ^
              runtime.workDegree) ∧
      CorrectedConcreteObservationSelectionCompactVerifierSpecification.compactInputSize
          input =
        (4 +
            data.coordinateCount +
            data.instancePayload.length) +
          1 := by

  let input :
      CorrectedConcreteObservationSelectionCompactInput :=
    CorrectedConcreteObservationSelectionCompactInput.ofData
      data

  have hDecode :
      CorrectedConcreteObservationSelectionCompactData.decode
            input.payload =
          some data :=
    CorrectedConcreteObservationSelectionCompactData.decode_encode
      hWellFormed

  exact
    ⟨hDecode,
      runtime.runDecision_eq_true_iff_exists_result
        input,
      by
        intro code

        rw [
          runtime.result_eq_runCertificateVerifier
            input
            code,
          runtime.verifierSpecification.runCertificateVerifier_of_decode
            hDecode
        ]

        exact
          runtime.verifierSpecification.verifier_eq_true_iff
            data
            code,
      by
        intro code hAccepted

        have hPolynomial :
            CorrectedConcreteObservationSelectionCompactVerifierSpecification.compactCertificateLength
                  input
                  code <=
              1 *
                CorrectedConcreteObservationSelectionCompactVerifierSpecification.compactInputSize
                    input ^
                  1 := by

          apply
            runtime.verifierSpecification.compactCertificateLength_polynomial_le

          rw [
            ← runtime.result_eq_runCertificateVerifier
              input
              code
          ]

          exact hAccepted

        simpa using hPolynomial,
      runtime.work_polynomial_le
        input,
      CorrectedConcreteObservationSelectionCompactInput.ofData_inputSize
        hWellFormed⟩

end EncodedCompactVerifierRuntimeFinalPackage

end MCFG
