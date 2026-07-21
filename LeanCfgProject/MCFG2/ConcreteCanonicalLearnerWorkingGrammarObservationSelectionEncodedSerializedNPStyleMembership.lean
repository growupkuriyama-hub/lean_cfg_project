/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG2.ConcreteCanonicalLearnerWorkingGrammarObservationSelectionEncodedSerializedPolynomialWitness

/-!
# ConcreteCanonicalLearnerWorkingGrammarObservationSelectionEncodedSerializedNPStyleMembership.lean

The preceding file proves a complete witness theorem for the pure serialized
observation-selection input.  This file packages that theorem in one generic
NP-style membership interface.

A serialized NP-style membership package contains

* one pure `List Nat` input;
* one Boolean decision;
* one natural-number certificate verifier;
* explicit input-size, certificate-size, and verifier-work functions;
* an exact decision/witness equivalence;
* polynomial certificate-size and verifier-work bounds.

The ordinary-cost and Pareto-scalar serialized verifiers both instantiate this
interface with

```text
certificate-size coefficient = 1,
certificate-size degree      = 1,
verifier-work coefficient    = 4,
verifier-work degree         = 1.
```

For every encoded observation-selection instance, the packaged decision agrees
with the preceding semantic-table decision.  At the exact semantic
positive-additive minimum rank, the canonical least Pareto dense code is a
witness in this common interface, is no larger than every competing witness,
and retains its checked decoding and Pareto optimality.

This is an NP-style membership interface relative to the already materialized
serialized table.  It intentionally does not assert membership in a particular
library's complexity class.  The serialized table can have exponential length
in `U.card`, and its semantic construction is still noncomputable.  No
compact-input NP-membership or hardness claim is made.

No target grammar is supplied to any learner.
No `sorry`, `admit`, or `axiom` is used.
-/

namespace MCFG

universe u v w z


/-- Generic NP-style membership data for one pure serialized input. -/
structure CorrectedConcreteSerializedNPStyleMembership where

  input : List Nat

  decision : Bool

  verifier : Nat → Bool

  inputSize : Nat

  certificateSize : Nat → Nat

  verifierWork : Nat → Nat

  certificateCoefficient : Nat

  certificateDegree : Nat

  verifierCoefficient : Nat

  verifierDegree : Nat

  inputSize_eq :
    inputSize = input.length + 1

  decision_eq_true_iff_exists :
    decision = true ↔
      ∃ code : Nat,
        verifier code = true

  certificateSize_le :
    ∀ code : Nat,
      verifier code = true →
        certificateSize code <=
          certificateCoefficient *
            inputSize ^ certificateDegree

  verifierWork_le :
    ∀ code : Nat,
      verifier code = true →
        verifierWork code <=
          verifierCoefficient *
            inputSize ^ verifierDegree


namespace CorrectedConcreteSerializedNPStyleMembership

section GenericInterface

variable
  (membership :
    CorrectedConcreteSerializedNPStyleMembership)

/-- Witness relation exposed by the generic serialized membership package. -/
def Witness
    (code : Nat) : Prop :=
  membership.verifier code = true

/-- Exact decision/witness characterization. -/
theorem decision_eq_true_iff_exists_witness :
    membership.decision = true ↔
      ∃ code : Nat,
        membership.Witness code := by

  exact membership.decision_eq_true_iff_exists

/-- A witness carrying the resource bounds of the generic package. -/
structure PolynomialWitness where

  code : Nat

  accepted :
    membership.Witness code

  certificateSize_le :
    membership.certificateSize code <=
      membership.certificateCoefficient *
        membership.inputSize ^
          membership.certificateDegree

  verifierWork_le :
    membership.verifierWork code <=
      membership.verifierCoefficient *
        membership.inputSize ^
          membership.verifierDegree

/-- Package any accepted code as a polynomial witness. -/
def polynomialWitnessOfAccepted
    (code : Nat)
    (hAccepted :
      membership.Witness code) :
    membership.PolynomialWitness :=
  {
    code := code

    accepted := hAccepted

    certificateSize_le :=
      membership.certificateSize_le
        code
        hAccepted

    verifierWork_le :=
      membership.verifierWork_le
        code
        hAccepted
  }

/-- Select one polynomial witness from every positive decision. -/
noncomputable def selectedPolynomialWitness
    (hDecision :
      membership.decision = true) :
    membership.PolynomialWitness := by

  rcases
      membership.decision_eq_true_iff_exists_witness.mp
        hDecision with
    ⟨code, hAccepted⟩

  exact
    membership.polynomialWitnessOfAccepted
      code
      hAccepted

/-- No witness exists for a negative decision. -/
theorem no_witness_of_decision_eq_false
    (hDecision :
      membership.decision = false) :
    ¬ ∃ code : Nat,
        membership.Witness code := by

  intro hWitness

  have hTrue :
      membership.decision = true :=
    membership.decision_eq_true_iff_exists_witness.mpr
      hWitness

  simp [hDecision] at hTrue

/-- Complete generic NP-style membership package. -/
theorem package :
    (membership.decision = true ↔
      ∃ code : Nat,
        membership.Witness code) ∧
      (∀ code : Nat,
        membership.Witness code →
          membership.certificateSize code <=
            membership.certificateCoefficient *
              membership.inputSize ^
                membership.certificateDegree) ∧
      (∀ code : Nat,
        membership.Witness code →
          membership.verifierWork code <=
            membership.verifierCoefficient *
              membership.inputSize ^
                membership.verifierDegree) := by

  exact
    ⟨membership.decision_eq_true_iff_exists_witness,
      membership.certificateSize_le,
      membership.verifierWork_le⟩

end GenericInterface

end CorrectedConcreteSerializedNPStyleMembership


namespace CorrectedConcreteEncodedObservationSelectionInstance

section SerializedNPStyleMembershipConstruction

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

/-- Ordinary-cost serialized NP-style membership package. -/
noncomputable def serializedCostNPStyleMembership :
    CorrectedConcreteSerializedNPStyleMembership :=
  {
    input := instance.serialize

    decision :=
      CorrectedConcreteEncodedObservationSelectionData.runSerializedCostDecision
        instance.serialize

    verifier :=
      fun code =>
        CorrectedConcreteEncodedObservationSelectionData.runSerializedCostCertificateVerifier
          instance.serialize
          code

    inputSize :=
      CorrectedConcreteEncodedObservationSelectionData.serializedCertificateVerifierInputSize
        instance.serialize
        0

    certificateSize :=
      CorrectedConcreteEncodedObservationSelectionData.serializedWitnessCertificateSize

    verifierWork :=
      fun code =>
        CorrectedConcreteEncodedObservationSelectionData.serializedCertificateVerifierWork
          instance.serialize
          code

    certificateCoefficient := 1

    certificateDegree := 1

    verifierCoefficient := 4

    verifierDegree := 1

    inputSize_eq := by
      rfl

    decision_eq_true_iff_exists := by
      exact
        instance.runSerializedCostDecision_eq_true_iff_exists_witness

    certificateSize_le := by
      intro code hAccepted

      have hBound :=
        instance.serializedCostWitness_certificateSize_le
          hAccepted

      simpa [
        CorrectedConcreteEncodedObservationSelectionData.serializedCertificateVerifierInputSize
      ] using hBound

    verifierWork_le := by
      intro code hAccepted

      simp [
        CorrectedConcreteEncodedObservationSelectionData.serializedCertificateVerifierWork,
        CorrectedConcreteEncodedObservationSelectionData.serializedCertificateVerifierInputSize
      ]
  }

/-- Pareto-scalar serialized NP-style membership package. -/
noncomputable def serializedParetoNPStyleMembership :
    CorrectedConcreteSerializedNPStyleMembership :=
  {
    input := instance.serialize

    decision :=
      CorrectedConcreteEncodedObservationSelectionData.runSerializedParetoDecision
        instance.serialize

    verifier :=
      fun code =>
        CorrectedConcreteEncodedObservationSelectionData.runSerializedParetoCertificateVerifier
          instance.serialize
          code

    inputSize :=
      CorrectedConcreteEncodedObservationSelectionData.serializedCertificateVerifierInputSize
        instance.serialize
        0

    certificateSize :=
      CorrectedConcreteEncodedObservationSelectionData.serializedWitnessCertificateSize

    verifierWork :=
      fun code =>
        CorrectedConcreteEncodedObservationSelectionData.serializedCertificateVerifierWork
          instance.serialize
          code

    certificateCoefficient := 1

    certificateDegree := 1

    verifierCoefficient := 4

    verifierDegree := 1

    inputSize_eq := by
      rfl

    decision_eq_true_iff_exists := by
      exact
        instance.runSerializedParetoDecision_eq_true_iff_exists_witness

    certificateSize_le := by
      intro code hAccepted

      have hBound :=
        instance.serializedParetoWitness_certificateSize_le
          hAccepted

      simpa [
        CorrectedConcreteEncodedObservationSelectionData.serializedCertificateVerifierInputSize
      ] using hBound

    verifierWork_le := by
      intro code hAccepted

      simp [
        CorrectedConcreteEncodedObservationSelectionData.serializedCertificateVerifierWork,
        CorrectedConcreteEncodedObservationSelectionData.serializedCertificateVerifierInputSize
      ]
  }

@[simp]
theorem serializedCostNPStyleMembership_input :
    instance.serializedCostNPStyleMembership.input =
      instance.serialize := by

  rfl

@[simp]
theorem serializedParetoNPStyleMembership_input :
    instance.serializedParetoNPStyleMembership.input =
      instance.serialize := by

  rfl

@[simp]
theorem serializedCostNPStyleMembership_coefficients :
    instance.serializedCostNPStyleMembership.certificateCoefficient = 1 ∧
      instance.serializedCostNPStyleMembership.certificateDegree = 1 ∧
      instance.serializedCostNPStyleMembership.verifierCoefficient = 4 ∧
      instance.serializedCostNPStyleMembership.verifierDegree = 1 := by

  exact ⟨rfl, rfl, rfl, rfl⟩

@[simp]
theorem serializedParetoNPStyleMembership_coefficients :
    instance.serializedParetoNPStyleMembership.certificateCoefficient = 1 ∧
      instance.serializedParetoNPStyleMembership.certificateDegree = 1 ∧
      instance.serializedParetoNPStyleMembership.verifierCoefficient = 4 ∧
      instance.serializedParetoNPStyleMembership.verifierDegree = 1 := by

  exact ⟨rfl, rfl, rfl, rfl⟩

/-- Ordinary packaged decision agrees with the semantic-table decision. -/
theorem serializedCostNPStyleMembership_decision_iff_tableDecision :
    instance.serializedCostNPStyleMembership.decision = true ↔
      table.costFeasibleDecision instance.budget = true := by

  exact
    instance.runSerializedCostDecision_serialize_iff_tableDecision

/-- Pareto packaged decision agrees with the semantic-table decision. -/
theorem serializedParetoNPStyleMembership_decision_iff_tableDecision :
    instance.serializedParetoNPStyleMembership.decision = true ↔
      table.paretoScalarFeasibleDecision
          instance.budget =
        true := by

  exact
    instance.runSerializedParetoDecision_serialize_iff_tableDecision

/-- Ordinary packaged witness is exactly pure serialized ordinary certificate
acceptance. -/
theorem serializedCostNPStyleMembership_witness_iff
    (code : Nat) :
    instance.serializedCostNPStyleMembership.Witness code ↔
      CorrectedConcreteEncodedObservationSelectionData.SerializedCostWitness
        instance.serialize
        code := by

  rfl

/-- Pareto packaged witness is exactly pure serialized Pareto certificate
acceptance. -/
theorem serializedParetoNPStyleMembership_witness_iff
    (code : Nat) :
    instance.serializedParetoNPStyleMembership.Witness code ↔
      CorrectedConcreteEncodedObservationSelectionData.SerializedParetoWitness
        instance.serialize
        code := by

  rfl

/-- Complete ordinary and Pareto NP-style interface package for one encoded
instance. -/
theorem serializedNPStyleMembership_package :
    (instance.serializedCostNPStyleMembership.decision = true ↔
      ∃ code : Nat,
        instance.serializedCostNPStyleMembership.Witness code) ∧
      (instance.serializedParetoNPStyleMembership.decision = true ↔
        ∃ code : Nat,
          instance.serializedParetoNPStyleMembership.Witness code) ∧
      instance.serializedCostNPStyleMembership.certificateCoefficient = 1 ∧
      instance.serializedCostNPStyleMembership.certificateDegree = 1 ∧
      instance.serializedCostNPStyleMembership.verifierCoefficient = 4 ∧
      instance.serializedCostNPStyleMembership.verifierDegree = 1 ∧
      instance.serializedParetoNPStyleMembership.certificateCoefficient = 1 ∧
      instance.serializedParetoNPStyleMembership.certificateDegree = 1 ∧
      instance.serializedParetoNPStyleMembership.verifierCoefficient = 4 ∧
      instance.serializedParetoNPStyleMembership.verifierDegree = 1 := by

  exact
    ⟨instance.serializedCostNPStyleMembership.decision_eq_true_iff_exists_witness,
      instance.serializedParetoNPStyleMembership.decision_eq_true_iff_exists_witness,
      rfl,
      rfl,
      rfl,
      rfl,
      rfl,
      rfl,
      rfl,
      rfl⟩

end SerializedNPStyleMembershipConstruction

end CorrectedConcreteEncodedObservationSelectionInstance


namespace CorrectedConcreteObservationSelectionDecisionTable

section CanonicalSerializedNPStyleMembership

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

/-- Canonical ordinary serialized NP-style decision agrees with the ordinary
table decision at every budget. -/
theorem encodedObservationSelectionInstance_serializedCostNPStyleDecision
    (budget : Nat) :
    (table.encodedObservationSelectionInstance
      budget).serializedCostNPStyleMembership.decision =
        true ↔
      table.costFeasibleDecision budget = true := by

  exact
    (table.encodedObservationSelectionInstance
      budget).serializedCostNPStyleMembership_decision_iff_tableDecision

/-- Canonical Pareto serialized NP-style decision agrees with the Pareto table
decision at every budget. -/
theorem encodedObservationSelectionInstance_serializedParetoNPStyleDecision
    (budget : Nat) :
    (table.encodedObservationSelectionInstance
      budget).serializedParetoNPStyleMembership.decision =
        true ↔
      table.paretoScalarFeasibleDecision budget = true := by

  exact
    (table.encodedObservationSelectionInstance
      budget).serializedParetoNPStyleMembership_decision_iff_tableDecision

end CanonicalSerializedNPStyleMembership

end CorrectedConcreteObservationSelectionDecisionTable


section EncodedSerializedNPStyleMembershipFinalPackage

variable {α : Type u}
variable {ι : Type v}
variable {M : Type w}
variable [DecidableEq ι]
variable [Monoid M]
variable (obsFamily : ι → α → M)
variable (f : Nat)
variable (coordinateWeight : ι → Nat)
variable (U : Finset ι)

/-- Final positive-additive NP-style membership package.

At the exact semantic minimum rank, the canonical least Pareto dense code is a
witness in the common serialized membership interface.  It is least among all
packaged Pareto witnesses, has degree-one certificate and verifier bounds, and
decodes to the same Pareto-optimal certificate. -/
theorem
    correctedConcreteWorkingGrammar_observationSelectionEncodedSerializedNPStyleMembership_package
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
    let membership :=
      instance.serializedParetoNPStyleMembership
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
    membership.decision = true ∧
      membership.Witness canonicalCode ∧
      (∀ competingCode : Nat,
        membership.Witness competingCode →
          canonicalCode <= competingCode) ∧
      membership.certificateSize canonicalCode <=
        membership.certificateCoefficient *
          membership.inputSize ^
            membership.certificateDegree ∧
      membership.verifierWork canonicalCode <=
        membership.verifierCoefficient *
          membership.inputSize ^
            membership.verifierDegree ∧
      membership.certificateCoefficient = 1 ∧
      membership.certificateDegree = 1 ∧
      membership.verifierCoefficient = 4 ∧
      membership.verifierDegree = 1 ∧
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
    ambientTargetObservationSelectionPositiveAdditiveMinimumCost
      (z := z)
      obsFamily
      f
      coordinateWeight
      U
      hTarget

  let instance :=
    table.encodedObservationSelectionInstance minimumRank

  let membership :=
    instance.serializedParetoNPStyleMembership

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

  have hPrevious :=
    correctedConcreteWorkingGrammar_observationSelectionEncodedSerializedPolynomialWitness_package
      (z := z)
      obsFamily
      f
      coordinateWeight
      U
      language
      hTarget

  have hMembershipWitness :
      membership.Witness canonicalCode := by

    exact hPrevious.2.1

  have hLeast :
      ∀ competingCode : Nat,
        membership.Witness competingCode →
          canonicalCode <= competingCode := by

    intro competingCode hCompeting

    exact
      hPrevious.2.2.1
        competingCode
        hCompeting

  exact
    ⟨hPrevious.1,
      hMembershipWitness,
      hLeast,
      membership.certificateSize_le
        canonicalCode
        hMembershipWitness,
      membership.verifierWork_le
        canonicalCode
        hMembershipWitness,
      rfl,
      rfl,
      rfl,
      rfl,
      hPrevious.2.2.2.2.2.1,
      hPrevious.2.2.2.2.2.2.1,
      hPrevious.2.2.2.2.2.2.2⟩

end EncodedSerializedNPStyleMembershipFinalPackage

end MCFG
