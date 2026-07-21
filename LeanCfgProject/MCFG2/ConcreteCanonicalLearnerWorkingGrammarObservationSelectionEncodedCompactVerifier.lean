/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG2.ConcreteCanonicalLearnerWorkingGrammarObservationSelectionEncodedCompactInstance

/-!
# ConcreteCanonicalLearnerWorkingGrammarObservationSelectionEncodedCompactVerifier.lean

The preceding file defines a checked compact syntax that does not contain
dedicated ordinary/Pareto feasibility-bit vectors.  This file defines the
direct compact certificate-verifier interface.

A compact verifier specification supplies

```text
Feasible : CompactData → Nat → Prop
verifier : CompactData → Nat → Bool
```

and proves the exact law

```text
verifier data code = true
  iff
code < 2 ^ data.coordinateCount
  and
Feasible data code.
```

Thus all semantic dependence is isolated in `Feasible`, while the executable
Boolean verifier must be proved sound and complete for that relation.

From this specification we construct

* a finite verified-code set;
* a whole-instance existential decision;
* a decoder-fronted verifier on arbitrary compact `List Nat` inputs;
* a decoder-fronted whole-instance decision;
* malformed-input rejection;
* global decision/witness equivalence;
* an accepted compact-input language and witness relation;
* exact specialization to every checked encoded compact record.

We also provide a generic implementation from any decidable feasibility
relation.  This implementation uses `decide`; it is a logical reference
verifier, not yet the desired grammar-level observation-selection algorithm.
A later file must instantiate `Feasible` with the actual compact semantics and
prove a concrete runtime bound for its Boolean decision procedure.

No materialized `2 ^ coordinateCount` truth table is generated or consumed by
the verifier interface in this file.

No compact-input complexity-class membership, hardness, or NP-completeness
claim is made.
No target grammar is supplied to any learner.
No `sorry`, `admit`, or `axiom` is used.
-/

namespace MCFG


/-- Sound-and-complete Boolean verifier for one compact feasibility relation. -/
structure CorrectedConcreteObservationSelectionCompactVerifierSpecification where

  Feasible :
    CorrectedConcreteObservationSelectionCompactData →
      Nat →
        Prop

  verifier :
    CorrectedConcreteObservationSelectionCompactData →
      Nat →
        Bool

  verifier_eq_true_iff :
    ∀ data :
        CorrectedConcreteObservationSelectionCompactData,
      ∀ code : Nat,
        verifier data code = true ↔
          code < data.candidateCodeBound ∧
            Feasible data code


namespace CorrectedConcreteObservationSelectionCompactVerifierSpecification

section GenericCompactVerifier

variable
  (specification :
    CorrectedConcreteObservationSelectionCompactVerifierSpecification)

/-- Finite family of all compact certificate codes accepted for one decoded
instance. -/
def verifiedCodes
    (data :
      CorrectedConcreteObservationSelectionCompactData) :
    Finset Nat :=
  (Finset.range data.candidateCodeBound).filter
    (fun code =>
      specification.verifier data code = true)

/-- Exact membership characterization of the finite verified-code family. -/
@[simp]
theorem mem_verifiedCodes_iff
    (data :
      CorrectedConcreteObservationSelectionCompactData)
    (code : Nat) :
    code ∈ specification.verifiedCodes data ↔
      code < data.candidateCodeBound ∧
        specification.Feasible data code := by

  simp [
    verifiedCodes,
    specification.verifier_eq_true_iff
  ]

/-- The verified-code family is bounded by the full dense candidate universe. -/
theorem verifiedCodes_card_le
    (data :
      CorrectedConcreteObservationSelectionCompactData) :
    (specification.verifiedCodes data).card <=
      data.candidateCodeBound := by

  calc
    (specification.verifiedCodes data).card <=
        (Finset.range data.candidateCodeBound).card :=
      Finset.card_filter_le_iff.mpr
        (by
          intro code hCode

          exact hCode)

    _ =
        data.candidateCodeBound := by
      simp

/-- Whole decoded-instance decision: some dense certificate code is accepted. -/
def decision
    (data :
      CorrectedConcreteObservationSelectionCompactData) :
    Bool :=
  decide
    (∃ code : Fin data.candidateCodeBound,
      specification.verifier data code.1 = true)

/-- Decoded-instance decision in terms of a finite certificate. -/
theorem decision_eq_true_iff_exists_fin
    (data :
      CorrectedConcreteObservationSelectionCompactData) :
    specification.decision data = true ↔
      ∃ code : Fin data.candidateCodeBound,
        specification.verifier data code.1 = true := by

  simp [
    decision
  ]

/-- Decoded-instance decision in natural-code form. -/
theorem decision_eq_true_iff_exists_verifier
    (data :
      CorrectedConcreteObservationSelectionCompactData) :
    specification.decision data = true ↔
      ∃ code : Nat,
        code < data.candidateCodeBound ∧
          specification.verifier data code = true := by

  constructor

  · intro hDecision

    rcases
        (specification.decision_eq_true_iff_exists_fin
          data).mp
          hDecision with
      ⟨code, hCode⟩

    exact
      ⟨code.1,
        code.2,
        hCode⟩

  · rintro ⟨code, hCodeBound, hCode⟩

    exact
      (specification.decision_eq_true_iff_exists_fin
        data).mpr
        ⟨⟨code, hCodeBound⟩,
          hCode⟩

/-- Exact semantic characterization of the decoded-instance decision. -/
theorem decision_eq_true_iff_exists_feasible
    (data :
      CorrectedConcreteObservationSelectionCompactData) :
    specification.decision data = true ↔
      ∃ code : Nat,
        code < data.candidateCodeBound ∧
          specification.Feasible data code := by

  constructor

  · intro hDecision

    rcases
        (specification.decision_eq_true_iff_exists_verifier
          data).mp
          hDecision with
      ⟨code, hCodeBound, hVerifier⟩

    have hParts :
        code < data.candidateCodeBound ∧
          specification.Feasible data code :=
      (specification.verifier_eq_true_iff
        data
        code).mp
        hVerifier

    exact
      ⟨code,
        hCodeBound,
        hParts.2⟩

  · rintro ⟨code, hCodeBound, hFeasible⟩

    exact
      (specification.decision_eq_true_iff_exists_verifier
        data).mpr
        ⟨code,
          hCodeBound,
          (specification.verifier_eq_true_iff
            data
            code).mpr
            ⟨hCodeBound,
              hFeasible⟩⟩

/-- The decoded decision is true exactly when the verified-code family is
nonempty. -/
theorem decision_eq_true_iff_verifiedCodes_nonempty
    (data :
      CorrectedConcreteObservationSelectionCompactData) :
    specification.decision data = true ↔
      (specification.verifiedCodes data).Nonempty := by

  constructor

  · intro hDecision

    rcases
        (specification.decision_eq_true_iff_exists_feasible
          data).mp
          hDecision with
      ⟨code, hCodeBound, hFeasible⟩

    exact
      ⟨code,
        (specification.mem_verifiedCodes_iff
          data
          code).mpr
          ⟨hCodeBound,
            hFeasible⟩⟩

  · rintro ⟨code, hCode⟩

    have hParts :
        code < data.candidateCodeBound ∧
          specification.Feasible data code :=
      (specification.mem_verifiedCodes_iff
        data
        code).mp
        hCode

    exact
      (specification.decision_eq_true_iff_exists_feasible
        data).mpr
        ⟨code,
          hParts.1,
          hParts.2⟩

end GenericCompactVerifier


section DecoderFrontedCompactVerifier

variable
  (specification :
    CorrectedConcreteObservationSelectionCompactVerifierSpecification)

/-- Pure compact certificate verifier on an arbitrary wrapped `List Nat`
input.  Malformed compact inputs reject. -/
def runCertificateVerifier
    (input :
      CorrectedConcreteObservationSelectionCompactInput)
    (code : Nat) :
    Bool :=
  match
    CorrectedConcreteObservationSelectionCompactData.decode
      input.payload with

  | some data =>
      specification.verifier data code

  | none =>
      false

/-- Pure whole compact-input decision.  Malformed compact inputs reject. -/
def runDecision
    (input :
      CorrectedConcreteObservationSelectionCompactInput) :
    Bool :=
  match
    CorrectedConcreteObservationSelectionCompactData.decode
      input.payload with

  | some data =>
      specification.decision data

  | none =>
      false

/-- Certificate verification after one successful checked decode. -/
theorem runCertificateVerifier_of_decode
    {input :
      CorrectedConcreteObservationSelectionCompactInput}
    {data :
      CorrectedConcreteObservationSelectionCompactData}
    {code : Nat}
    (hDecode :
      CorrectedConcreteObservationSelectionCompactData.decode
          input.payload =
        some data) :
    specification.runCertificateVerifier input code =
      specification.verifier data code := by

  simp [
    runCertificateVerifier,
    hDecode
  ]

/-- Whole-instance decision after one successful checked decode. -/
theorem runDecision_of_decode
    {input :
      CorrectedConcreteObservationSelectionCompactInput}
    {data :
      CorrectedConcreteObservationSelectionCompactData}
    (hDecode :
      CorrectedConcreteObservationSelectionCompactData.decode
          input.payload =
        some data) :
    specification.runDecision input =
      specification.decision data := by

  simp [
    runDecision,
    hDecode
  ]

/-- Malformed compact inputs reject every certificate. -/
theorem runCertificateVerifier_eq_false_of_decode_eq_none
    {input :
      CorrectedConcreteObservationSelectionCompactInput}
    (hDecode :
      CorrectedConcreteObservationSelectionCompactData.decode
          input.payload =
        none)
    (code : Nat) :
    specification.runCertificateVerifier input code =
      false := by

  simp [
    runCertificateVerifier,
    hDecode
  ]

/-- Malformed compact inputs reject at the whole-instance level. -/
theorem runDecision_eq_false_of_decode_eq_none
    {input :
      CorrectedConcreteObservationSelectionCompactInput}
    (hDecode :
      CorrectedConcreteObservationSelectionCompactData.decode
          input.payload =
        none) :
    specification.runDecision input =
      false := by

  simp [
    runDecision,
    hDecode
  ]

/-- Global certificate-verifier characterization on arbitrary compact inputs. -/
theorem runCertificateVerifier_eq_true_iff
    (input :
      CorrectedConcreteObservationSelectionCompactInput)
    (code : Nat) :
    specification.runCertificateVerifier input code = true ↔
      ∃ data :
          CorrectedConcreteObservationSelectionCompactData,
        CorrectedConcreteObservationSelectionCompactData.decode
              input.payload =
            some data ∧
          code < data.candidateCodeBound ∧
          specification.Feasible data code := by

  cases hDecode :
      CorrectedConcreteObservationSelectionCompactData.decode
        input.payload with

  | none =>
      simp [
        runCertificateVerifier,
        hDecode
      ]

  | some data =>
      simp [
        runCertificateVerifier,
        hDecode,
        specification.verifier_eq_true_iff
      ]

/-- Global whole-instance semantic characterization on arbitrary compact
inputs. -/
theorem runDecision_eq_true_iff
    (input :
      CorrectedConcreteObservationSelectionCompactInput) :
    specification.runDecision input = true ↔
      ∃ data :
          CorrectedConcreteObservationSelectionCompactData,
        CorrectedConcreteObservationSelectionCompactData.decode
              input.payload =
            some data ∧
          ∃ code : Nat,
            code < data.candidateCodeBound ∧
              specification.Feasible data code := by

  cases hDecode :
      CorrectedConcreteObservationSelectionCompactData.decode
        input.payload with

  | none =>
      simp [
        runDecision,
        hDecode
      ]

  | some data =>
      simp [
        runDecision,
        hDecode,
        specification.decision_eq_true_iff_exists_feasible
      ]

/-- Global decision/witness equivalence for the direct compact verifier. -/
theorem runDecision_eq_true_iff_exists_certificate
    (input :
      CorrectedConcreteObservationSelectionCompactInput) :
    specification.runDecision input = true ↔
      ∃ code : Nat,
        specification.runCertificateVerifier
            input
            code =
          true := by

  cases hDecode :
      CorrectedConcreteObservationSelectionCompactData.decode
        input.payload with

  | none =>
      simp [
        runDecision,
        runCertificateVerifier,
        hDecode
      ]

  | some data =>
      simp [
        runDecision,
        runCertificateVerifier,
        hDecode,
        specification.decision_eq_true_iff_exists_verifier
      ]

/-- Language accepted by the direct compact whole-instance decision. -/
def AcceptedLanguage :
    Set CorrectedConcreteObservationSelectionCompactInput :=
  {input |
    specification.runDecision input = true}

/-- Direct compact witness relation. -/
def Witness
    (input :
      CorrectedConcreteObservationSelectionCompactInput)
    (code : Nat) :
    Prop :=
  specification.runCertificateVerifier input code =
    true

/-- Exact accepted-language/witness theorem. -/
theorem mem_acceptedLanguage_iff_exists_witness
    (input :
      CorrectedConcreteObservationSelectionCompactInput) :
    input ∈ specification.AcceptedLanguage ↔
      ∃ code : Nat,
        specification.Witness input code := by

  exact
    specification.runDecision_eq_true_iff_exists_certificate
      input

/-- Every accepted compact input has a verifier-accepted certificate. -/
theorem complete
    {input :
      CorrectedConcreteObservationSelectionCompactInput}
    (hInput :
      input ∈ specification.AcceptedLanguage) :
    ∃ code : Nat,
      specification.Witness input code := by

  exact
    (specification.mem_acceptedLanguage_iff_exists_witness
      input).mp
      hInput

/-- Every accepted compact certificate implies whole-instance acceptance. -/
theorem sound
    {input :
      CorrectedConcreteObservationSelectionCompactInput}
    {code : Nat}
    (hWitness :
      specification.Witness input code) :
    input ∈ specification.AcceptedLanguage := by

  exact
    (specification.mem_acceptedLanguage_iff_exists_witness
      input).mpr
      ⟨code, hWitness⟩

end DecoderFrontedCompactVerifier


section DecidableFeasibilityReference

/-- Logical reference verifier for any decidable compact feasibility relation.

A genuine compact observation-selection theorem must instantiate `Feasible`
with the intended semantic relation and justify the runtime of its decision
procedure. -/
def ofDecidableFeasible
    (Feasible :
      CorrectedConcreteObservationSelectionCompactData →
        Nat →
          Prop)
    [∀ data code,
      Decidable
        (Feasible data code)] :
    CorrectedConcreteObservationSelectionCompactVerifierSpecification :=
  {
    Feasible :=
      Feasible

    verifier :=
      fun data code =>
        decide
          (code < data.candidateCodeBound ∧
            Feasible data code)

    verifier_eq_true_iff := by
      intro data code

      simp
  }

@[simp]
theorem ofDecidableFeasible_verifier
    (Feasible :
      CorrectedConcreteObservationSelectionCompactData →
        Nat →
          Prop)
    [∀ data code,
      Decidable
        (Feasible data code)]
    (data :
      CorrectedConcreteObservationSelectionCompactData)
    (code : Nat) :
    (ofDecidableFeasible Feasible).verifier data code =
      decide
        (code < data.candidateCodeBound ∧
          Feasible data code) := by

  rfl

end DecidableFeasibilityReference

end CorrectedConcreteObservationSelectionCompactVerifierSpecification


section EncodedCompactVerifierFinalPackage

variable
  (specification :
    CorrectedConcreteObservationSelectionCompactVerifierSpecification)

/-- Final direct compact-verifier package on one checked compact record. -/
theorem
    correctedConcreteWorkingGrammar_observationSelectionEncodedCompactVerifier_package
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
      (specification.runDecision input = true ↔
        ∃ code : Nat,
          code < data.candidateCodeBound ∧
            specification.Feasible data code) ∧
      (∀ code : Nat,
        specification.runCertificateVerifier input code = true ↔
          code < data.candidateCodeBound ∧
            specification.Feasible data code) ∧
      (specification.runDecision input = true ↔
        ∃ code : Nat,
          specification.runCertificateVerifier input code =
            true) ∧
      (specification.runDecision input = true ↔
        (specification.verifiedCodes data).Nonempty) ∧
      (specification.verifiedCodes data).card <=
        data.candidateCodeBound := by

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
      by
        rw [
          specification.runDecision_of_decode
            hDecode
        ]

        exact
          specification.decision_eq_true_iff_exists_feasible
            data,
      by
        intro code

        rw [
          specification.runCertificateVerifier_of_decode
            hDecode
        ]

        exact
          specification.verifier_eq_true_iff
            data
            code,
      specification.runDecision_eq_true_iff_exists_certificate
        input,
      by
        rw [
          specification.runDecision_of_decode
            hDecode
        ]

        exact
          specification.decision_eq_true_iff_verifiedCodes_nonempty
            data,
      specification.verifiedCodes_card_le
        data⟩

end EncodedCompactVerifierFinalPackage

end MCFG
