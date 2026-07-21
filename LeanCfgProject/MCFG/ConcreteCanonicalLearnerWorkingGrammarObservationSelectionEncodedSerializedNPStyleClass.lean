/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG.ConcreteCanonicalLearnerWorkingGrammarObservationSelectionEncodedSerializedPolynomialDecisionProblem

/-!
# ConcreteCanonicalLearnerWorkingGrammarObservationSelectionEncodedSerializedNPStyleClass.lean

The preceding file constructs global serialized polynomial witness decision
problems for ordinary-cost and Pareto-scalar observation selection.  This file
packages those problems as members of an abstract serialized NP-style language
class.

A language `L : Set (List Nat)` belongs to the class when there exists a global
serialized polynomial witness decision problem whose accepted language is
exactly `L`.  Thus membership supplies

* one Boolean decision on every pure serialized input;
* one natural-number certificate verifier;
* exact decision/witness equivalence;
* a polynomial certificate-size bound;
* a polynomial verifier-work bound.

This class deliberately records the mathematical witness characterization
without identifying it with a particular library's formal complexity class or
standard machine model.

We prove:

* every polynomial witness decision problem presents an NP-style language;
* NP-style membership transports across extensional language equality;
* the ordinary-cost and Pareto serialized observation-selection languages both
  belong to the class;
* their concrete coefficients and degrees are respectively `1, 1, 4, 1`;
* canonical encoded inputs agree with the semantic observation-selection
  decision table;
* at the exact positive-additive minimum rank, the canonical serialized input
  belongs to the Pareto NP-style language and the canonical least dense code is
  a least polynomial witness with checked decoding and Pareto optimality.

The canonical serialized input still materializes an exponential-size semantic
table and is constructed noncomputably.  Therefore this is an abstract
serialized NP-style classification, not a compact-input NP-membership,
NP-hardness, or NP-completeness theorem.

No target grammar is supplied to any learner.
No `sorry`, `admit`, or `axiom` is used.
-/

namespace MCFG

universe u v w z


/-- A certificate that a language of serialized natural-number lists is
presented by a global polynomial witness decision problem. -/
structure CorrectedConcreteSerializedNPStyleLanguageCertificate
    (language : Set (List Nat)) where

  problem :
    CorrectedConcreteSerializedPolynomialWitnessDecisionProblem

  acceptedLanguage_eq :
    problem.AcceptedLanguage = language


/-- Abstract serialized NP-style language class.

This is intentionally a project-local witness class and is not definitionally
identified with a library's standard `NP` class. -/
def CorrectedConcreteSerializedNPStyleLanguage
    (language : Set (List Nat)) : Prop :=
  Nonempty
    (CorrectedConcreteSerializedNPStyleLanguageCertificate
      language)


namespace CorrectedConcreteSerializedNPStyleLanguageCertificate

section GenericCertificate

variable {language : Set (List Nat)}
variable
  (certificate :
    CorrectedConcreteSerializedNPStyleLanguageCertificate
      language)

/-- Exact language-membership/witness characterization supplied by an
NP-style language certificate. -/
theorem mem_iff_exists_witness
    (input : List Nat) :
    input ∈ language ↔
      ∃ code : Nat,
        certificate.problem.Witness input code := by

  rw [← certificate.acceptedLanguage_eq]

  exact
    certificate.problem.mem_acceptedLanguage_iff_exists_witness
      input

/-- Every accepted input has a polynomial witness. -/
noncomputable def selectedPolynomialWitness
    (input : List Nat)
    (hInput :
      input ∈ language) :
    certificate.problem.PolynomialWitness input := by

  have hAccepted :
      input ∈ certificate.problem.AcceptedLanguage := by

    rw [certificate.acceptedLanguage_eq]

    exact hInput

  exact
    certificate.problem.selectedPolynomialWitness
      input
      hAccepted

/-- Rejected inputs have no verifier-accepted certificate. -/
theorem no_witness_of_not_mem
    {input : List Nat}
    (hInput :
      input ∉ language) :
    ¬ ∃ code : Nat,
        certificate.problem.Witness input code := by

  intro hWitness

  exact
    hInput
      ((certificate.mem_iff_exists_witness input).mpr
        hWitness)

/-- Certificate-size bound exposed directly at the language-certificate
level. -/
theorem certificateSize_le
    {input : List Nat}
    {code : Nat}
    (hWitness :
      certificate.problem.Witness input code) :
    certificate.problem.certificateSize code <=
      certificate.problem.certificateCoefficient *
        certificate.problem.inputSize input ^
          certificate.problem.certificateDegree := by

  exact
    certificate.problem.certificateSize_le
      input
      code
      hWitness

/-- Verifier-work bound exposed directly at the language-certificate level. -/
theorem verifierWork_le
    {input : List Nat}
    {code : Nat}
    (hWitness :
      certificate.problem.Witness input code) :
    certificate.problem.verifierWork input code <=
      certificate.problem.verifierCoefficient *
        certificate.problem.inputSize input ^
          certificate.problem.verifierDegree := by

  exact
    certificate.problem.verifierWork_le
      input
      code
      hWitness

/-- Complete generic language-certificate package. -/
theorem package
    (input : List Nat) :
    (input ∈ language ↔
      ∃ code : Nat,
        certificate.problem.Witness input code) ∧
      (∀ code : Nat,
        certificate.problem.Witness input code →
          certificate.problem.certificateSize code <=
            certificate.problem.certificateCoefficient *
              certificate.problem.inputSize input ^
                certificate.problem.certificateDegree) ∧
      (∀ code : Nat,
        certificate.problem.Witness input code →
          certificate.problem.verifierWork input code <=
            certificate.problem.verifierCoefficient *
              certificate.problem.inputSize input ^
                certificate.problem.verifierDegree) := by

  exact
    ⟨certificate.mem_iff_exists_witness input,
      fun code hWitness =>
        certificate.certificateSize_le hWitness,
      fun code hWitness =>
        certificate.verifierWork_le hWitness⟩

end GenericCertificate

end CorrectedConcreteSerializedNPStyleLanguageCertificate


namespace CorrectedConcreteSerializedNPStyleLanguage

section GenericClass

/-- Every global polynomial witness decision problem presents an abstract
serialized NP-style language. -/
theorem acceptedLanguage
    (problem :
      CorrectedConcreteSerializedPolynomialWitnessDecisionProblem) :
    CorrectedConcreteSerializedNPStyleLanguage
      problem.AcceptedLanguage := by

  exact
    ⟨{
      problem := problem
      acceptedLanguage_eq := rfl
    }⟩

/-- NP-style language membership is invariant under extensional language
equality. -/
theorem congr
    {first second : Set (List Nat)}
    (hFirst :
      CorrectedConcreteSerializedNPStyleLanguage first)
    (hEq :
      first = second) :
    CorrectedConcreteSerializedNPStyleLanguage second := by

  rcases hFirst with
    ⟨certificate⟩

  exact
    ⟨{
      problem := certificate.problem
      acceptedLanguage_eq := by
        calc
          certificate.problem.AcceptedLanguage =
              first :=
            certificate.acceptedLanguage_eq

          _ = second :=
            hEq
    }⟩

/-- Extensional form of the preceding transport theorem. -/
theorem congr_iff
    {first second : Set (List Nat)}
    (hEq :
      first = second) :
    CorrectedConcreteSerializedNPStyleLanguage first ↔
      CorrectedConcreteSerializedNPStyleLanguage second := by

  constructor

  · intro hFirst

    exact congr hFirst hEq

  · intro hSecond

    exact congr hSecond hEq.symm

end GenericClass

end CorrectedConcreteSerializedNPStyleLanguage


namespace CorrectedConcreteEncodedObservationSelectionData

section ObservationSelectionNPStyleLanguages

/-- Ordinary-cost global serialized observation-selection language. -/
def serializedCostNPStyleLanguage :
    Set (List Nat) :=
  serializedCostPolynomialWitnessDecisionProblem.AcceptedLanguage

/-- Pareto-scalar global serialized observation-selection language. -/
def serializedParetoNPStyleLanguage :
    Set (List Nat) :=
  serializedParetoPolynomialWitnessDecisionProblem.AcceptedLanguage

/-- Canonical NP-style certificate for the ordinary-cost serialized language. -/
def serializedCostNPStyleLanguageCertificate :
    CorrectedConcreteSerializedNPStyleLanguageCertificate
      serializedCostNPStyleLanguage :=
  {
    problem :=
      serializedCostPolynomialWitnessDecisionProblem

    acceptedLanguage_eq := rfl
  }

/-- Canonical NP-style certificate for the Pareto serialized language. -/
def serializedParetoNPStyleLanguageCertificate :
    CorrectedConcreteSerializedNPStyleLanguageCertificate
      serializedParetoNPStyleLanguage :=
  {
    problem :=
      serializedParetoPolynomialWitnessDecisionProblem

    acceptedLanguage_eq := rfl
  }

/-- The ordinary-cost serialized observation-selection language belongs to the
abstract serialized NP-style class. -/
theorem serializedCostNPStyleLanguage_mem :
    CorrectedConcreteSerializedNPStyleLanguage
      serializedCostNPStyleLanguage := by

  exact
    ⟨serializedCostNPStyleLanguageCertificate⟩

/-- The Pareto-scalar serialized observation-selection language belongs to the
abstract serialized NP-style class. -/
theorem serializedParetoNPStyleLanguage_mem :
    CorrectedConcreteSerializedNPStyleLanguage
      serializedParetoNPStyleLanguage := by

  exact
    ⟨serializedParetoNPStyleLanguageCertificate⟩

/-- Exact ordinary language/witness characterization. -/
theorem mem_serializedCostNPStyleLanguage_iff
    (input : List Nat) :
    input ∈ serializedCostNPStyleLanguage ↔
      ∃ code : Nat,
        serializedCostPolynomialWitnessDecisionProblem.Witness
          input
          code := by

  exact
    serializedCostNPStyleLanguageCertificate.mem_iff_exists_witness
      input

/-- Exact Pareto language/witness characterization. -/
theorem mem_serializedParetoNPStyleLanguage_iff
    (input : List Nat) :
    input ∈ serializedParetoNPStyleLanguage ↔
      ∃ code : Nat,
        serializedParetoPolynomialWitnessDecisionProblem.Witness
          input
          code := by

  exact
    serializedParetoNPStyleLanguageCertificate.mem_iff_exists_witness
      input

/-- The ordinary serialized language has degree-one certificate and verifier
bounds with coefficients one and four. -/
theorem serializedCostNPStyleLanguage_resource_package :
    serializedCostNPStyleLanguageCertificate.problem.certificateCoefficient =
        1 ∧
      serializedCostNPStyleLanguageCertificate.problem.certificateDegree =
        1 ∧
      serializedCostNPStyleLanguageCertificate.problem.verifierCoefficient =
        4 ∧
      serializedCostNPStyleLanguageCertificate.problem.verifierDegree =
        1 := by

  exact ⟨rfl, rfl, rfl, rfl⟩

/-- The Pareto serialized language has degree-one certificate and verifier
bounds with coefficients one and four. -/
theorem serializedParetoNPStyleLanguage_resource_package :
    serializedParetoNPStyleLanguageCertificate.problem.certificateCoefficient =
        1 ∧
      serializedParetoNPStyleLanguageCertificate.problem.certificateDegree =
        1 ∧
      serializedParetoNPStyleLanguageCertificate.problem.verifierCoefficient =
        4 ∧
      serializedParetoNPStyleLanguageCertificate.problem.verifierDegree =
        1 := by

  exact ⟨rfl, rfl, rfl, rfl⟩

/-- Complete abstract serialized NP-style classification package. -/
theorem serializedNPStyleLanguage_package :
    CorrectedConcreteSerializedNPStyleLanguage
        serializedCostNPStyleLanguage ∧
      CorrectedConcreteSerializedNPStyleLanguage
        serializedParetoNPStyleLanguage ∧
      serializedCostNPStyleLanguageCertificate.problem.certificateCoefficient =
        1 ∧
      serializedCostNPStyleLanguageCertificate.problem.certificateDegree =
        1 ∧
      serializedCostNPStyleLanguageCertificate.problem.verifierCoefficient =
        4 ∧
      serializedCostNPStyleLanguageCertificate.problem.verifierDegree =
        1 ∧
      serializedParetoNPStyleLanguageCertificate.problem.certificateCoefficient =
        1 ∧
      serializedParetoNPStyleLanguageCertificate.problem.certificateDegree =
        1 ∧
      serializedParetoNPStyleLanguageCertificate.problem.verifierCoefficient =
        4 ∧
      serializedParetoNPStyleLanguageCertificate.problem.verifierDegree =
        1 := by

  exact
    ⟨serializedCostNPStyleLanguage_mem,
      serializedParetoNPStyleLanguage_mem,
      rfl,
      rfl,
      rfl,
      rfl,
      rfl,
      rfl,
      rfl,
      rfl⟩

end ObservationSelectionNPStyleLanguages

end CorrectedConcreteEncodedObservationSelectionData


namespace CorrectedConcreteEncodedObservationSelectionInstance

section CanonicalInstanceLanguageMembership

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

/-- Canonical serialized ordinary input belongs to the ordinary NP-style
language exactly when the semantic ordinary table accepts its budget. -/
theorem serialize_mem_costNPStyleLanguage_iff_tableDecision :
    instance.serialize ∈
        CorrectedConcreteEncodedObservationSelectionData.serializedCostNPStyleLanguage ↔
      table.costFeasibleDecision instance.budget = true := by

  exact
    instance.serializedCostPolynomialDecisionProblem_serialize_iff_tableDecision

/-- Canonical serialized Pareto input belongs to the Pareto NP-style language
exactly when the semantic Pareto table accepts its budget. -/
theorem serialize_mem_paretoNPStyleLanguage_iff_tableDecision :
    instance.serialize ∈
        CorrectedConcreteEncodedObservationSelectionData.serializedParetoNPStyleLanguage ↔
      table.paretoScalarFeasibleDecision
          instance.budget =
        true := by

  exact
    instance.serializedParetoPolynomialDecisionProblem_serialize_iff_tableDecision

end CanonicalInstanceLanguageMembership

end CorrectedConcreteEncodedObservationSelectionInstance


section EncodedSerializedNPStyleClassFinalPackage

variable {α : Type u}
variable {ι : Type v}
variable {M : Type w}
variable [DecidableEq ι]
variable [Monoid M]
variable (obsFamily : ι → α → M)
variable (f : Nat)
variable (coordinateWeight : ι → Nat)
variable (U : Finset ι)

/-- Final abstract serialized NP-style classification package.

At the exact semantic positive-additive minimum rank, the canonical serialized
input belongs to the globally defined Pareto NP-style language.  The canonical
least dense code is a least witness for its global polynomial verifier, carries
the degree-one certificate and work bounds, and decodes to the same
Pareto-optimal observation-selection certificate. -/
theorem
    correctedConcreteWorkingGrammar_observationSelectionEncodedSerializedNPStyleClass_package
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
    let npLanguage :=
      CorrectedConcreteEncodedObservationSelectionData.serializedParetoNPStyleLanguage
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
    CorrectedConcreteSerializedNPStyleLanguage npLanguage ∧
      instance.serialize ∈ npLanguage ∧
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

  let npLanguage :=
    CorrectedConcreteEncodedObservationSelectionData.serializedParetoNPStyleLanguage

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
    correctedConcreteWorkingGrammar_observationSelectionEncodedSerializedPolynomialDecisionProblem_package
      (z := z)
      obsFamily
      f
      coordinateWeight
      U
      language
      hTarget

  rcases hPrevious with
    ⟨hInput,
      hWitness,
      hLeast,
      hCertificateSize,
      hVerifierWork,
      hCertificateCoefficient,
      hCertificateDegree,
      hVerifierCoefficient,
      hVerifierDegree,
      hCodeBound,
      hDecode,
      hPareto⟩

  exact
    ⟨CorrectedConcreteEncodedObservationSelectionData.serializedParetoNPStyleLanguage_mem,
      hInput,
      hWitness,
      hLeast,
      hCertificateSize,
      hVerifierWork,
      hCertificateCoefficient,
      hCertificateDegree,
      hVerifierCoefficient,
      hVerifierDegree,
      hCodeBound,
      hDecode,
      hPareto⟩

end EncodedSerializedNPStyleClassFinalPackage

end MCFG
