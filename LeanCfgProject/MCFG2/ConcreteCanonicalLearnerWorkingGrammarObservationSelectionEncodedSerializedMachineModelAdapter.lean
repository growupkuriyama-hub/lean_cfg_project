/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG2.ConcreteCanonicalLearnerWorkingGrammarObservationSelectionEncodedSerializedNPStyleClass

/-!
# ConcreteCanonicalLearnerWorkingGrammarObservationSelectionEncodedSerializedMachineModelAdapter.lean

The preceding file introduces a project-local serialized NP-style language
class.  Its verifier and resource functions are still fields of one abstract
polynomial witness decision problem.  This file separates those fields through
an explicit machine-model adapter.

A serialized verifier machine model contains

```text
run               : List Nat → Nat → Bool
steps             : List Nat → Nat → Nat
inputLength       : List Nat → Nat
certificateLength : Nat → Nat.
```

An adapter from a polynomial witness decision problem identifies

* machine acceptance with the problem verifier;
* machine input length with the problem input-size function;
* machine certificate length with the problem certificate-size function;
* machine step count with the problem verifier-work function.

We construct the canonical identity adapter for every global polynomial witness
decision problem and derive

* exact decision/machine-witness equivalence;
* polynomial certificate-length bounds;
* polynomial machine-step bounds;
* language-level machine-model NP-style certificates;
* transport from the preceding project-local serialized NP-style class to the
  machine-adapted class.

The ordinary-cost and Pareto serialized observation-selection languages are
both classified by this machine-adapted interface.  At the exact semantic
positive-additive minimum rank, the canonical least Pareto dense code is
accepted by the adapted machine, is least among all accepted machine
certificates, and retains its checked decoding and Pareto optimality.

The identity adapter is not yet a proof that the verifier is implemented by a
standard Turing-machine or RAM library.  It isolates the exact remaining
obligation: construct another adapter whose `steps` field is the genuine step
count of the chosen standard machine model.  No compact-input NP-membership or
hardness claim is made here.

No target grammar is supplied to any learner.
No `sorry`, `admit`, or `axiom` is used.
-/

namespace MCFG

universe u v w z


/-- Abstract machine interface for serialized inputs and natural-number
certificates. -/
structure CorrectedConcreteSerializedVerifierMachineModel where

  run :
    List Nat → Nat → Bool

  steps :
    List Nat → Nat → Nat

  inputLength :
    List Nat → Nat

  certificateLength :
    Nat → Nat


namespace CorrectedConcreteSerializedVerifierMachineModel

section GenericMachine

variable
  (machine :
    CorrectedConcreteSerializedVerifierMachineModel)

/-- Machine acceptance relation. -/
def Accepts
    (input : List Nat)
    (code : Nat) : Prop :=
  machine.run input code = true

end GenericMachine

end CorrectedConcreteSerializedVerifierMachineModel


/-- Adapter from a global polynomial witness decision problem to a serialized
verifier machine model. -/
structure CorrectedConcreteSerializedPolynomialMachineAdapter
    (problem :
      CorrectedConcreteSerializedPolynomialWitnessDecisionProblem) where

  machine :
    CorrectedConcreteSerializedVerifierMachineModel

  run_eq :
    ∀ input : List Nat,
      ∀ code : Nat,
        machine.run input code =
          problem.verifier input code

  steps_eq :
    ∀ input : List Nat,
      ∀ code : Nat,
        machine.steps input code =
          problem.verifierWork input code

  inputLength_eq :
    ∀ input : List Nat,
      machine.inputLength input =
        problem.inputSize input

  certificateLength_eq :
    ∀ code : Nat,
      machine.certificateLength code =
        problem.certificateSize code


namespace CorrectedConcreteSerializedPolynomialMachineAdapter

section GenericAdapter

variable
  {problem :
    CorrectedConcreteSerializedPolynomialWitnessDecisionProblem}
variable
  (adapter :
    CorrectedConcreteSerializedPolynomialMachineAdapter
      problem)

/-- Machine acceptance agrees exactly with the problem witness relation. -/
theorem accepts_iff_witness
    (input : List Nat)
    (code : Nat) :
    adapter.machine.Accepts input code ↔
      problem.Witness input code := by

  unfold CorrectedConcreteSerializedVerifierMachineModel.Accepts
  unfold CorrectedConcreteSerializedPolynomialWitnessDecisionProblem.Witness

  rw [adapter.run_eq input code]

/-- Exact decision/machine-witness equivalence. -/
theorem decision_eq_true_iff_exists_machine_accepts
    (input : List Nat) :
    problem.decision input = true ↔
      ∃ code : Nat,
        adapter.machine.Accepts input code := by

  rw [problem.decision_eq_true_iff_exists input]

  constructor

  · rintro ⟨code, hWitness⟩

    exact
      ⟨code,
        (adapter.accepts_iff_witness
          input
          code).mpr
          hWitness⟩

  · rintro ⟨code, hAccepts⟩

    exact
      ⟨code,
        (adapter.accepts_iff_witness
          input
          code).mp
          hAccepts⟩

/-- Every machine-accepted certificate satisfies the problem's polynomial
certificate-length bound. -/
theorem certificateLength_le
    {input : List Nat}
    {code : Nat}
    (hAccepts :
      adapter.machine.Accepts input code) :
    adapter.machine.certificateLength code <=
      problem.certificateCoefficient *
        adapter.machine.inputLength input ^
          problem.certificateDegree := by

  have hWitness :
      problem.Witness input code :=
    (adapter.accepts_iff_witness
      input
      code).mp
      hAccepts

  rw [
    adapter.certificateLength_eq code,
    adapter.inputLength_eq input
  ]

  exact
    problem.certificateSize_le
      input
      code
      hWitness

/-- Every machine-accepted certificate satisfies the problem's polynomial
machine-step bound. -/
theorem machineSteps_le
    {input : List Nat}
    {code : Nat}
    (hAccepts :
      adapter.machine.Accepts input code) :
    adapter.machine.steps input code <=
      problem.verifierCoefficient *
        adapter.machine.inputLength input ^
          problem.verifierDegree := by

  have hWitness :
      problem.Witness input code :=
    (adapter.accepts_iff_witness
      input
      code).mp
      hAccepts

  rw [
    adapter.steps_eq input code,
    adapter.inputLength_eq input
  ]

  exact
    problem.verifierWork_le
      input
      code
      hWitness

/-- Machine polynomial witness package. -/
structure MachinePolynomialWitness
    (input : List Nat) where

  code : Nat

  accepted :
    adapter.machine.Accepts input code

  certificateLength_le :
    adapter.machine.certificateLength code <=
      problem.certificateCoefficient *
        adapter.machine.inputLength input ^
          problem.certificateDegree

  machineSteps_le :
    adapter.machine.steps input code <=
      problem.verifierCoefficient *
        adapter.machine.inputLength input ^
          problem.verifierDegree

/-- Package any machine-accepted code with its inherited polynomial resource
bounds. -/
def machinePolynomialWitnessOfAccepted
    (input : List Nat)
    (code : Nat)
    (hAccepted :
      adapter.machine.Accepts input code) :
    adapter.MachinePolynomialWitness input :=
  {
    code := code

    accepted := hAccepted

    certificateLength_le :=
      adapter.certificateLength_le
        hAccepted

    machineSteps_le :=
      adapter.machineSteps_le
        hAccepted
  }

/-- Every accepted problem input has a machine polynomial witness. -/
noncomputable def selectedMachinePolynomialWitness
    (input : List Nat)
    (hAccepted :
      input ∈ problem.AcceptedLanguage) :
    adapter.MachinePolynomialWitness input := by

  rcases
      (problem.mem_acceptedLanguage_iff_exists_witness
        input).mp
        hAccepted with
    ⟨code, hWitness⟩

  exact
    adapter.machinePolynomialWitnessOfAccepted
      input
      code
      ((adapter.accepts_iff_witness
        input
        code).mpr
        hWitness)

/-- Complete generic adapter package. -/
theorem package
    (input : List Nat) :
    (problem.decision input = true ↔
      ∃ code : Nat,
        adapter.machine.Accepts input code) ∧
      (∀ code : Nat,
        adapter.machine.Accepts input code →
          adapter.machine.certificateLength code <=
            problem.certificateCoefficient *
              adapter.machine.inputLength input ^
                problem.certificateDegree) ∧
      (∀ code : Nat,
        adapter.machine.Accepts input code →
          adapter.machine.steps input code <=
            problem.verifierCoefficient *
              adapter.machine.inputLength input ^
                problem.verifierDegree) := by

  exact
    ⟨adapter.decision_eq_true_iff_exists_machine_accepts
      input,
      fun code hAccepts =>
        adapter.certificateLength_le hAccepts,
      fun code hAccepts =>
        adapter.machineSteps_le hAccepts⟩

end GenericAdapter


section IdentityAdapter

/-- Canonical identity adapter for every global polynomial witness decision
problem.

This adapter isolates the machine interface without changing the verifier or
its resource accounting. -/
def identity
    (problem :
      CorrectedConcreteSerializedPolynomialWitnessDecisionProblem) :
    CorrectedConcreteSerializedPolynomialMachineAdapter
      problem :=
  {
    machine :=
      {
        run :=
          problem.verifier

        steps :=
          problem.verifierWork

        inputLength :=
          problem.inputSize

        certificateLength :=
          problem.certificateSize
      }

    run_eq := by
      intro input code

      rfl

    steps_eq := by
      intro input code

      rfl

    inputLength_eq := by
      intro input

      rfl

    certificateLength_eq := by
      intro code

      rfl
  }

@[simp]
theorem identity_machine_run
    (problem :
      CorrectedConcreteSerializedPolynomialWitnessDecisionProblem)
    (input : List Nat)
    (code : Nat) :
    (identity problem).machine.run input code =
      problem.verifier input code := by

  rfl

@[simp]
theorem identity_machine_steps
    (problem :
      CorrectedConcreteSerializedPolynomialWitnessDecisionProblem)
    (input : List Nat)
    (code : Nat) :
    (identity problem).machine.steps input code =
      problem.verifierWork input code := by

  rfl

@[simp]
theorem identity_machine_inputLength
    (problem :
      CorrectedConcreteSerializedPolynomialWitnessDecisionProblem)
    (input : List Nat) :
    (identity problem).machine.inputLength input =
      problem.inputSize input := by

  rfl

@[simp]
theorem identity_machine_certificateLength
    (problem :
      CorrectedConcreteSerializedPolynomialWitnessDecisionProblem)
    (code : Nat) :
    (identity problem).machine.certificateLength code =
      problem.certificateSize code := by

  rfl

end IdentityAdapter

end CorrectedConcreteSerializedPolynomialMachineAdapter


/-- A machine-adapted certificate for a serialized language. -/
structure CorrectedConcreteSerializedMachineNPStyleLanguageCertificate
    (language : Set (List Nat)) where

  problem :
    CorrectedConcreteSerializedPolynomialWitnessDecisionProblem

  adapter :
    CorrectedConcreteSerializedPolynomialMachineAdapter
      problem

  acceptedLanguage_eq :
    problem.AcceptedLanguage = language


/-- Serialized NP-style language class with an explicit verifier-machine
adapter. -/
def CorrectedConcreteSerializedMachineNPStyleLanguage
    (language : Set (List Nat)) : Prop :=
  Nonempty
    (CorrectedConcreteSerializedMachineNPStyleLanguageCertificate
      language)


namespace CorrectedConcreteSerializedMachineNPStyleLanguageCertificate

section GenericMachineLanguageCertificate

variable {language : Set (List Nat)}
variable
  (certificate :
    CorrectedConcreteSerializedMachineNPStyleLanguageCertificate
      language)

/-- Exact language-membership/machine-witness equivalence. -/
theorem mem_iff_exists_machine_accepts
    (input : List Nat) :
    input ∈ language ↔
      ∃ code : Nat,
        certificate.adapter.machine.Accepts
          input
          code := by

  rw [← certificate.acceptedLanguage_eq]

  exact
    certificate.adapter.decision_eq_true_iff_exists_machine_accepts
      input

/-- Every accepted language input has a machine polynomial witness. -/
noncomputable def selectedMachinePolynomialWitness
    (input : List Nat)
    (hInput :
      input ∈ language) :
    certificate.adapter.MachinePolynomialWitness
      input := by

  have hAccepted :
      input ∈ certificate.problem.AcceptedLanguage := by

    rw [certificate.acceptedLanguage_eq]

    exact hInput

  exact
    certificate.adapter.selectedMachinePolynomialWitness
      input
      hAccepted

/-- Machine certificate-length bound at the language-certificate level. -/
theorem certificateLength_le
    {input : List Nat}
    {code : Nat}
    (hAccepts :
      certificate.adapter.machine.Accepts
        input
        code) :
    certificate.adapter.machine.certificateLength code <=
      certificate.problem.certificateCoefficient *
        certificate.adapter.machine.inputLength input ^
          certificate.problem.certificateDegree := by

  exact
    certificate.adapter.certificateLength_le
      hAccepts

/-- Machine-step bound at the language-certificate level. -/
theorem machineSteps_le
    {input : List Nat}
    {code : Nat}
    (hAccepts :
      certificate.adapter.machine.Accepts
        input
        code) :
    certificate.adapter.machine.steps input code <=
      certificate.problem.verifierCoefficient *
        certificate.adapter.machine.inputLength input ^
          certificate.problem.verifierDegree := by

  exact
    certificate.adapter.machineSteps_le
      hAccepts

end GenericMachineLanguageCertificate

end CorrectedConcreteSerializedMachineNPStyleLanguageCertificate


namespace CorrectedConcreteSerializedMachineNPStyleLanguage

section GenericMachineLanguageClass

/-- Every polynomial witness decision problem presents a machine-adapted
NP-style language through its identity adapter. -/
theorem acceptedLanguage
    (problem :
      CorrectedConcreteSerializedPolynomialWitnessDecisionProblem) :
    CorrectedConcreteSerializedMachineNPStyleLanguage
      problem.AcceptedLanguage := by

  exact
    ⟨{
      problem := problem

      adapter :=
        CorrectedConcreteSerializedPolynomialMachineAdapter.identity
          problem

      acceptedLanguage_eq := rfl
    }⟩

/-- Every project-local serialized NP-style language has a machine-adapted
certificate through the identity adapter. -/
theorem ofNPStyleLanguage
    {language : Set (List Nat)}
    (hLanguage :
      CorrectedConcreteSerializedNPStyleLanguage
        language) :
    CorrectedConcreteSerializedMachineNPStyleLanguage
      language := by

  rcases hLanguage with
    ⟨certificate⟩

  exact
    ⟨{
      problem :=
        certificate.problem

      adapter :=
        CorrectedConcreteSerializedPolynomialMachineAdapter.identity
          certificate.problem

      acceptedLanguage_eq :=
        certificate.acceptedLanguage_eq
    }⟩

/-- Machine-adapted class membership is invariant under extensional language
equality. -/
theorem congr
    {first second : Set (List Nat)}
    (hFirst :
      CorrectedConcreteSerializedMachineNPStyleLanguage
        first)
    (hEq :
      first = second) :
    CorrectedConcreteSerializedMachineNPStyleLanguage
      second := by

  rcases hFirst with
    ⟨certificate⟩

  exact
    ⟨{
      problem :=
        certificate.problem

      adapter :=
        certificate.adapter

      acceptedLanguage_eq := by
        calc
          certificate.problem.AcceptedLanguage =
              first :=
            certificate.acceptedLanguage_eq

          _ = second :=
            hEq
    }⟩

end GenericMachineLanguageClass

end CorrectedConcreteSerializedMachineNPStyleLanguage


namespace CorrectedConcreteEncodedObservationSelectionData

section ObservationSelectionMachineAdapters

/-- Identity machine adapter for the ordinary serialized polynomial decision
problem. -/
def serializedCostPolynomialMachineAdapter :
    CorrectedConcreteSerializedPolynomialMachineAdapter
      serializedCostPolynomialWitnessDecisionProblem :=
  CorrectedConcreteSerializedPolynomialMachineAdapter.identity
    serializedCostPolynomialWitnessDecisionProblem

/-- Identity machine adapter for the Pareto serialized polynomial decision
problem. -/
def serializedParetoPolynomialMachineAdapter :
    CorrectedConcreteSerializedPolynomialMachineAdapter
      serializedParetoPolynomialWitnessDecisionProblem :=
  CorrectedConcreteSerializedPolynomialMachineAdapter.identity
    serializedParetoPolynomialWitnessDecisionProblem

/-- Canonical machine-adapted certificate for the ordinary serialized
observation-selection language. -/
def serializedCostMachineNPStyleLanguageCertificate :
    CorrectedConcreteSerializedMachineNPStyleLanguageCertificate
      serializedCostNPStyleLanguage :=
  {
    problem :=
      serializedCostPolynomialWitnessDecisionProblem

    adapter :=
      serializedCostPolynomialMachineAdapter

    acceptedLanguage_eq := rfl
  }

/-- Canonical machine-adapted certificate for the Pareto serialized
observation-selection language. -/
def serializedParetoMachineNPStyleLanguageCertificate :
    CorrectedConcreteSerializedMachineNPStyleLanguageCertificate
      serializedParetoNPStyleLanguage :=
  {
    problem :=
      serializedParetoPolynomialWitnessDecisionProblem

    adapter :=
      serializedParetoPolynomialMachineAdapter

    acceptedLanguage_eq := rfl
  }

/-- Ordinary serialized observation selection belongs to the machine-adapted
NP-style language class. -/
theorem serializedCostMachineNPStyleLanguage_mem :
    CorrectedConcreteSerializedMachineNPStyleLanguage
      serializedCostNPStyleLanguage := by

  exact
    ⟨serializedCostMachineNPStyleLanguageCertificate⟩

/-- Pareto serialized observation selection belongs to the machine-adapted
NP-style language class. -/
theorem serializedParetoMachineNPStyleLanguage_mem :
    CorrectedConcreteSerializedMachineNPStyleLanguage
      serializedParetoNPStyleLanguage := by

  exact
    ⟨serializedParetoMachineNPStyleLanguageCertificate⟩

/-- Complete observation-selection machine-adapter package. -/
theorem serializedMachineNPStyleLanguage_package :
    CorrectedConcreteSerializedMachineNPStyleLanguage
        serializedCostNPStyleLanguage ∧
      CorrectedConcreteSerializedMachineNPStyleLanguage
        serializedParetoNPStyleLanguage ∧
      (∀ input : List Nat,
        serializedCostPolynomialMachineAdapter.machine.run
              input
              0 =
            serializedCostPolynomialWitnessDecisionProblem.verifier
              input
              0) ∧
      (∀ input : List Nat,
        serializedParetoPolynomialMachineAdapter.machine.run
              input
              0 =
            serializedParetoPolynomialWitnessDecisionProblem.verifier
              input
              0) := by

  exact
    ⟨serializedCostMachineNPStyleLanguage_mem,
      serializedParetoMachineNPStyleLanguage_mem,
      fun input => rfl,
      fun input => rfl⟩

end ObservationSelectionMachineAdapters

end CorrectedConcreteEncodedObservationSelectionData


section EncodedSerializedMachineModelAdapterFinalPackage

variable {α : Type u}
variable {ι : Type v}
variable {M : Type w}
variable [DecidableEq ι]
variable [Monoid M]
variable (obsFamily : ι → α → M)
variable (f : Nat)
variable (coordinateWeight : ι → Nat)
variable (U : Finset ι)

/-- Final machine-adapter package at the exact semantic positive-additive
minimum rank.

The canonical serialized input belongs to the Pareto machine-adapted NP-style
language.  The canonical least dense Pareto code is accepted by the adapted
machine, is least among every accepted machine certificate, satisfies the
machine certificate-length and step bounds, and retains checked decoding and
Pareto optimality. -/
theorem
    correctedConcreteWorkingGrammar_observationSelectionEncodedSerializedMachineModelAdapter_package
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
    let adapter :=
      CorrectedConcreteEncodedObservationSelectionData.serializedParetoPolynomialMachineAdapter
    let machine :=
      adapter.machine
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
    CorrectedConcreteSerializedMachineNPStyleLanguage
        npLanguage ∧
      instance.serialize ∈ npLanguage ∧
      machine.Accepts instance.serialize canonicalCode ∧
      (∀ competingCode : Nat,
        machine.Accepts instance.serialize competingCode →
          canonicalCode <= competingCode) ∧
      machine.certificateLength canonicalCode <=
        problem.certificateCoefficient *
          machine.inputLength instance.serialize ^
            problem.certificateDegree ∧
      machine.steps instance.serialize canonicalCode <=
        problem.verifierCoefficient *
          machine.inputLength instance.serialize ^
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

  let adapter :=
    CorrectedConcreteEncodedObservationSelectionData.serializedParetoPolynomialMachineAdapter

  let machine :=
    adapter.machine

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
      hProblemWitness,
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

  have hMachineAccepts :
      machine.Accepts instance.serialize canonicalCode :=
    (adapter.accepts_iff_witness
      instance.serialize
      canonicalCode).mpr
      hProblemWitness

  exact
    ⟨CorrectedConcreteEncodedObservationSelectionData.serializedParetoMachineNPStyleLanguage_mem,
      hInput,
      hMachineAccepts,
      by
        intro competingCode hCompeting

        exact
          hLeast
            competingCode
            ((adapter.accepts_iff_witness
              instance.serialize
              competingCode).mp
              hCompeting),
      adapter.certificateLength_le
        hMachineAccepts,
      adapter.machineSteps_le
        hMachineAccepts,
      hCertificateCoefficient,
      hCertificateDegree,
      hVerifierCoefficient,
      hVerifierDegree,
      hCodeBound,
      hDecode,
      hPareto⟩

end EncodedSerializedMachineModelAdapterFinalPackage

end MCFG
