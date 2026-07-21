/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG2.ConcreteCanonicalLearnerWorkingGrammarObservationSelectionEncodedSerializedMachineModelAdapter

/-!
# ConcreteCanonicalLearnerWorkingGrammarObservationSelectionEncodedSerializedStandardMachineRealization.lean

The preceding file introduces an adapter whose machine interface still lives
inside the observation-selection development.  This file isolates the exact
obligation needed to connect the verified serialized decision problem to an
independently implemented standard machine.

A standard serialized machine semantics consists of

```text
Program
run
steps
inputLength
certificateLength.
```

A realization of a polynomial witness decision problem supplies one concrete
program and proves

```text
machine run = verified Boolean verifier,
machine input length = verified input size,
machine certificate length = verified certificate size,
machine steps <= verified verifier work.
```

The last inequality is the step-simulation obligation.  Once these four facts
are supplied, all earlier witness soundness, completeness, certificate-size,
and polynomial-work bounds transfer automatically to the implemented machine.

This file also provides

* a functional reference realization for every verified problem;
* a compatibility construction from the preceding machine adapter;
* a standard-machine NP-style language certificate and language class;
* ordinary-cost and Pareto observation-selection instances of that class;
* a final canonical minimum-rank Pareto package.

The functional realization is only a reference model.  To connect to a genuine
Turing-machine, RAM, register-machine, or another library implementation, one
replaces it with a realization record for that implementation and proves the
four fields above.  No compact-input NP-membership, NP-hardness, or
NP-completeness claim is made here.

No target grammar is supplied to any learner.
No `sorry`, `admit`, or `axiom` is used.
-/

namespace MCFG

universe u v w z


/-- Semantics of an independently implemented machine for serialized inputs
and natural-number certificates. -/
structure CorrectedConcreteSerializedStandardMachineSemantics where

  Program : Type

  run :
    Program → List Nat → Nat → Bool

  steps :
    Program → List Nat → Nat → Nat

  inputLength :
    List Nat → Nat

  certificateLength :
    Nat → Nat


namespace CorrectedConcreteSerializedStandardMachineSemantics

section StandardMachineSemantics

variable
  (semantics :
    CorrectedConcreteSerializedStandardMachineSemantics)

/-- Acceptance relation of one standard-machine program. -/
def Accepts
    (program : semantics.Program)
    (input : List Nat)
    (code : Nat) : Prop :=
  semantics.run program input code = true

end StandardMachineSemantics

end CorrectedConcreteSerializedStandardMachineSemantics


/-- Realization obligation for an independently implemented standard machine.

The machine step count is required to be bounded by the already verified
abstract work counter. -/
structure CorrectedConcreteSerializedStandardMachineRealization
    (problem :
      CorrectedConcreteSerializedPolynomialWitnessDecisionProblem)
    (semantics :
      CorrectedConcreteSerializedStandardMachineSemantics) where

  program :
    semantics.Program

  run_eq :
    ∀ input : List Nat,
      ∀ code : Nat,
        semantics.run program input code =
          problem.verifier input code

  inputLength_eq :
    ∀ input : List Nat,
      semantics.inputLength input =
        problem.inputSize input

  certificateLength_eq :
    ∀ code : Nat,
      semantics.certificateLength code =
        problem.certificateSize code

  steps_le :
    ∀ input : List Nat,
      ∀ code : Nat,
        semantics.steps program input code <=
          problem.verifierWork input code


namespace CorrectedConcreteSerializedStandardMachineRealization

section GenericRealization

variable
  {problem :
    CorrectedConcreteSerializedPolynomialWitnessDecisionProblem}
variable
  {semantics :
    CorrectedConcreteSerializedStandardMachineSemantics}
variable
  (realization :
    CorrectedConcreteSerializedStandardMachineRealization
      problem
      semantics)

/-- Standard-machine acceptance agrees exactly with the verified witness
relation. -/
theorem accepts_iff_witness
    (input : List Nat)
    (code : Nat) :
    semantics.Accepts realization.program input code ↔
      problem.Witness input code := by

  unfold CorrectedConcreteSerializedStandardMachineSemantics.Accepts
  unfold CorrectedConcreteSerializedPolynomialWitnessDecisionProblem.Witness

  rw [realization.run_eq input code]

/-- Exact decision/standard-machine-witness equivalence. -/
theorem decision_eq_true_iff_exists_accepts
    (input : List Nat) :
    problem.decision input = true ↔
      ∃ code : Nat,
        semantics.Accepts
          realization.program
          input
          code := by

  rw [problem.decision_eq_true_iff_exists input]

  constructor

  · rintro ⟨code, hWitness⟩

    exact
      ⟨code,
        (realization.accepts_iff_witness
          input
          code).mpr
          hWitness⟩

  · rintro ⟨code, hAccepts⟩

    exact
      ⟨code,
        (realization.accepts_iff_witness
          input
          code).mp
          hAccepts⟩

/-- Every accepted standard-machine certificate satisfies the verified
polynomial certificate-length bound. -/
theorem certificateLength_le
    {input : List Nat}
    {code : Nat}
    (hAccepts :
      semantics.Accepts
        realization.program
        input
        code) :
    semantics.certificateLength code <=
      problem.certificateCoefficient *
        semantics.inputLength input ^
          problem.certificateDegree := by

  have hWitness :
      problem.Witness input code :=
    (realization.accepts_iff_witness
      input
      code).mp
      hAccepts

  rw [
    realization.certificateLength_eq code,
    realization.inputLength_eq input
  ]

  exact
    problem.certificateSize_le
      input
      code
      hWitness

/-- Every accepted standard-machine computation satisfies the inherited
polynomial step bound. -/
theorem steps_polynomial_le
    {input : List Nat}
    {code : Nat}
    (hAccepts :
      semantics.Accepts
        realization.program
        input
        code) :
    semantics.steps realization.program input code <=
      problem.verifierCoefficient *
        semantics.inputLength input ^
          problem.verifierDegree := by

  have hWitness :
      problem.Witness input code :=
    (realization.accepts_iff_witness
      input
      code).mp
      hAccepts

  calc
    semantics.steps realization.program input code <=
        problem.verifierWork input code :=
      realization.steps_le input code

    _ <=
        problem.verifierCoefficient *
          problem.inputSize input ^
            problem.verifierDegree :=
      problem.verifierWork_le
        input
        code
        hWitness

    _ =
        problem.verifierCoefficient *
          semantics.inputLength input ^
            problem.verifierDegree := by
      rw [realization.inputLength_eq input]

/-- A standard-machine witness carrying the transferred resource bounds. -/
structure StandardMachinePolynomialWitness
    (input : List Nat) where

  code : Nat

  accepted :
    semantics.Accepts
      realization.program
      input
      code

  certificateLength_le :
    semantics.certificateLength code <=
      problem.certificateCoefficient *
        semantics.inputLength input ^
          problem.certificateDegree

  steps_polynomial_le :
    semantics.steps realization.program input code <=
      problem.verifierCoefficient *
        semantics.inputLength input ^
          problem.verifierDegree

/-- Package any accepted standard-machine code with its transferred resource
proofs. -/
def standardMachinePolynomialWitnessOfAccepted
    (input : List Nat)
    (code : Nat)
    (hAccepted :
      semantics.Accepts
        realization.program
        input
        code) :
    realization.StandardMachinePolynomialWitness input :=
  {
    code := code

    accepted := hAccepted

    certificateLength_le :=
      realization.certificateLength_le
        hAccepted

    steps_polynomial_le :=
      realization.steps_polynomial_le
        hAccepted
  }

/-- Every accepted verified input has a standard-machine polynomial witness. -/
noncomputable def selectedStandardMachinePolynomialWitness
    (input : List Nat)
    (hAccepted :
      input ∈ problem.AcceptedLanguage) :
    realization.StandardMachinePolynomialWitness input := by

  rcases
      (problem.mem_acceptedLanguage_iff_exists_witness
        input).mp
        hAccepted with
    ⟨code, hWitness⟩

  exact
    realization.standardMachinePolynomialWitnessOfAccepted
      input
      code
      ((realization.accepts_iff_witness
        input
        code).mpr
        hWitness)

/-- Complete realization package on one serialized input. -/
theorem package
    (input : List Nat) :
    (problem.decision input = true ↔
      ∃ code : Nat,
        semantics.Accepts
          realization.program
          input
          code) ∧
      (∀ code : Nat,
        semantics.Accepts
              realization.program
              input
              code →
          semantics.certificateLength code <=
            problem.certificateCoefficient *
              semantics.inputLength input ^
                problem.certificateDegree) ∧
      (∀ code : Nat,
        semantics.Accepts
              realization.program
              input
              code →
          semantics.steps realization.program input code <=
            problem.verifierCoefficient *
              semantics.inputLength input ^
                problem.verifierDegree) := by

  exact
    ⟨realization.decision_eq_true_iff_exists_accepts
      input,
      fun code hAccepts =>
        realization.certificateLength_le hAccepts,
      fun code hAccepts =>
        realization.steps_polynomial_le hAccepts⟩

end GenericRealization


section FunctionalReferenceRealization

/-- Functional reference semantics for a verified polynomial witness decision
problem.

This is an executable specification, not a claim of realization in an external
standard-machine library. -/
def functionalSemantics
    (problem :
      CorrectedConcreteSerializedPolynomialWitnessDecisionProblem) :
    CorrectedConcreteSerializedStandardMachineSemantics :=
  {
    Program := Unit

    run :=
      fun _ input code =>
        problem.verifier input code

    steps :=
      fun _ input code =>
        problem.verifierWork input code

    inputLength :=
      problem.inputSize

    certificateLength :=
      problem.certificateSize
  }

/-- Canonical realization of a problem by its functional reference semantics. -/
def functional
    (problem :
      CorrectedConcreteSerializedPolynomialWitnessDecisionProblem) :
    CorrectedConcreteSerializedStandardMachineRealization
      problem
      (functionalSemantics problem) :=
  {
    program := ()

    run_eq := by
      intro input code

      rfl

    inputLength_eq := by
      intro input

      rfl

    certificateLength_eq := by
      intro code

      rfl

    steps_le := by
      intro input code

      exact Nat.le_refl _
  }

@[simp]
theorem functional_run
    (problem :
      CorrectedConcreteSerializedPolynomialWitnessDecisionProblem)
    (input : List Nat)
    (code : Nat) :
    (functionalSemantics problem).run
          (functional problem).program
          input
          code =
      problem.verifier input code := by

  rfl

@[simp]
theorem functional_steps
    (problem :
      CorrectedConcreteSerializedPolynomialWitnessDecisionProblem)
    (input : List Nat)
    (code : Nat) :
    (functionalSemantics problem).steps
          (functional problem).program
          input
          code =
      problem.verifierWork input code := by

  rfl

end FunctionalReferenceRealization


section AdapterCompatibility

/-- Standard-machine semantics induced by any preceding machine adapter.

The realization record below is independent of the adapter structure; this
construction only provides backward compatibility with existing adapters. -/
def semanticsOfAdapter
    {problem :
      CorrectedConcreteSerializedPolynomialWitnessDecisionProblem}
    (adapter :
      CorrectedConcreteSerializedPolynomialMachineAdapter
        problem) :
    CorrectedConcreteSerializedStandardMachineSemantics :=
  {
    Program := Unit

    run :=
      fun _ input code =>
        adapter.machine.run input code

    steps :=
      fun _ input code =>
        adapter.machine.steps input code

    inputLength :=
      adapter.machine.inputLength

    certificateLength :=
      adapter.machine.certificateLength
  }

/-- Every preceding machine adapter satisfies the new standard-machine
realization obligation. -/
def ofAdapter
    {problem :
      CorrectedConcreteSerializedPolynomialWitnessDecisionProblem}
    (adapter :
      CorrectedConcreteSerializedPolynomialMachineAdapter
        problem) :
    CorrectedConcreteSerializedStandardMachineRealization
      problem
      (semanticsOfAdapter adapter) :=
  {
    program := ()

    run_eq := by
      intro input code

      exact adapter.run_eq input code

    inputLength_eq := by
      intro input

      exact adapter.inputLength_eq input

    certificateLength_eq := by
      intro code

      exact adapter.certificateLength_eq code

    steps_le := by
      intro input code

      rw [adapter.steps_eq input code]
  }

end AdapterCompatibility

end CorrectedConcreteSerializedStandardMachineRealization


/-- A serialized language certificate realized by an explicit standard-machine
semantics and program. -/
structure CorrectedConcreteSerializedStandardMachineNPStyleLanguageCertificate
    (language : Set (List Nat)) where

  problem :
    CorrectedConcreteSerializedPolynomialWitnessDecisionProblem

  semantics :
    CorrectedConcreteSerializedStandardMachineSemantics

  realization :
    CorrectedConcreteSerializedStandardMachineRealization
      problem
      semantics

  acceptedLanguage_eq :
    problem.AcceptedLanguage = language


/-- Abstract class of serialized languages with an explicit standard-machine
realization record. -/
def CorrectedConcreteSerializedStandardMachineNPStyleLanguage
    (language : Set (List Nat)) : Prop :=
  Nonempty
    (CorrectedConcreteSerializedStandardMachineNPStyleLanguageCertificate
      language)


namespace CorrectedConcreteSerializedStandardMachineNPStyleLanguageCertificate

section GenericStandardMachineLanguageCertificate

variable {language : Set (List Nat)}
variable
  (certificate :
    CorrectedConcreteSerializedStandardMachineNPStyleLanguageCertificate
      language)

/-- Exact language-membership/standard-machine-witness equivalence. -/
theorem mem_iff_exists_machine_accepts
    (input : List Nat) :
    input ∈ language ↔
      ∃ code : Nat,
        certificate.semantics.Accepts
          certificate.realization.program
          input
          code := by

  rw [← certificate.acceptedLanguage_eq]

  exact
    certificate.realization.decision_eq_true_iff_exists_accepts
      input

/-- Every accepted language input has a standard-machine polynomial witness. -/
noncomputable def selectedStandardMachinePolynomialWitness
    (input : List Nat)
    (hInput :
      input ∈ language) :
    certificate.realization.StandardMachinePolynomialWitness
      input := by

  have hAccepted :
      input ∈ certificate.problem.AcceptedLanguage := by

    rw [certificate.acceptedLanguage_eq]

    exact hInput

  exact
    certificate.realization.selectedStandardMachinePolynomialWitness
      input
      hAccepted

/-- Certificate-length bound at the language-certificate level. -/
theorem certificateLength_le
    {input : List Nat}
    {code : Nat}
    (hAccepts :
      certificate.semantics.Accepts
        certificate.realization.program
        input
        code) :
    certificate.semantics.certificateLength code <=
      certificate.problem.certificateCoefficient *
        certificate.semantics.inputLength input ^
          certificate.problem.certificateDegree := by

  exact
    certificate.realization.certificateLength_le
      hAccepts

/-- Standard-machine step bound at the language-certificate level. -/
theorem steps_polynomial_le
    {input : List Nat}
    {code : Nat}
    (hAccepts :
      certificate.semantics.Accepts
        certificate.realization.program
        input
        code) :
    certificate.semantics.steps
          certificate.realization.program
          input
          code <=
      certificate.problem.verifierCoefficient *
        certificate.semantics.inputLength input ^
          certificate.problem.verifierDegree := by

  exact
    certificate.realization.steps_polynomial_le
      hAccepts

end GenericStandardMachineLanguageCertificate

end CorrectedConcreteSerializedStandardMachineNPStyleLanguageCertificate


namespace CorrectedConcreteSerializedStandardMachineNPStyleLanguage

section GenericStandardMachineLanguageClass

/-- Every verified polynomial witness decision problem has a functional
reference standard-machine realization. -/
theorem acceptedLanguage
    (problem :
      CorrectedConcreteSerializedPolynomialWitnessDecisionProblem) :
    CorrectedConcreteSerializedStandardMachineNPStyleLanguage
      problem.AcceptedLanguage := by

  exact
    ⟨{
      problem := problem

      semantics :=
        CorrectedConcreteSerializedStandardMachineRealization.functionalSemantics
          problem

      realization :=
        CorrectedConcreteSerializedStandardMachineRealization.functional
          problem

      acceptedLanguage_eq := rfl
    }⟩

/-- Any externally supplied realization immediately yields standard-machine
NP-style language membership. -/
theorem ofRealization
    {language : Set (List Nat)}
    (problem :
      CorrectedConcreteSerializedPolynomialWitnessDecisionProblem)
    (semantics :
      CorrectedConcreteSerializedStandardMachineSemantics)
    (realization :
      CorrectedConcreteSerializedStandardMachineRealization
        problem
        semantics)
    (hLanguage :
      problem.AcceptedLanguage = language) :
    CorrectedConcreteSerializedStandardMachineNPStyleLanguage
      language := by

  exact
    ⟨{
      problem := problem
      semantics := semantics
      realization := realization
      acceptedLanguage_eq := hLanguage
    }⟩

/-- Standard-machine class membership is invariant under extensional language
equality. -/
theorem congr
    {first second : Set (List Nat)}
    (hFirst :
      CorrectedConcreteSerializedStandardMachineNPStyleLanguage
        first)
    (hEq :
      first = second) :
    CorrectedConcreteSerializedStandardMachineNPStyleLanguage
      second := by

  rcases hFirst with
    ⟨certificate⟩

  exact
    ⟨{
      problem := certificate.problem
      semantics := certificate.semantics
      realization := certificate.realization

      acceptedLanguage_eq := by
        calc
          certificate.problem.AcceptedLanguage =
              first :=
            certificate.acceptedLanguage_eq

          _ = second :=
            hEq
    }⟩

end GenericStandardMachineLanguageClass

end CorrectedConcreteSerializedStandardMachineNPStyleLanguage


namespace CorrectedConcreteEncodedObservationSelectionData

section ObservationSelectionStandardMachineRealizations

/-- Functional reference standard-machine semantics for ordinary serialized
observation selection. -/
def serializedCostStandardMachineSemantics :
    CorrectedConcreteSerializedStandardMachineSemantics :=
  CorrectedConcreteSerializedStandardMachineRealization.functionalSemantics
    serializedCostPolynomialWitnessDecisionProblem

/-- Functional reference realization for ordinary serialized observation
selection. -/
def serializedCostStandardMachineRealization :
    CorrectedConcreteSerializedStandardMachineRealization
      serializedCostPolynomialWitnessDecisionProblem
      serializedCostStandardMachineSemantics :=
  CorrectedConcreteSerializedStandardMachineRealization.functional
    serializedCostPolynomialWitnessDecisionProblem

/-- Functional reference standard-machine semantics for Pareto serialized
observation selection. -/
def serializedParetoStandardMachineSemantics :
    CorrectedConcreteSerializedStandardMachineSemantics :=
  CorrectedConcreteSerializedStandardMachineRealization.functionalSemantics
    serializedParetoPolynomialWitnessDecisionProblem

/-- Functional reference realization for Pareto serialized observation
selection. -/
def serializedParetoStandardMachineRealization :
    CorrectedConcreteSerializedStandardMachineRealization
      serializedParetoPolynomialWitnessDecisionProblem
      serializedParetoStandardMachineSemantics :=
  CorrectedConcreteSerializedStandardMachineRealization.functional
    serializedParetoPolynomialWitnessDecisionProblem

/-- Ordinary serialized observation selection belongs to the
standard-machine-realized NP-style class. -/
theorem serializedCostStandardMachineNPStyleLanguage_mem :
    CorrectedConcreteSerializedStandardMachineNPStyleLanguage
      serializedCostNPStyleLanguage := by

  exact
    CorrectedConcreteSerializedStandardMachineNPStyleLanguage.ofRealization
      serializedCostPolynomialWitnessDecisionProblem
      serializedCostStandardMachineSemantics
      serializedCostStandardMachineRealization
      rfl

/-- Pareto serialized observation selection belongs to the
standard-machine-realized NP-style class. -/
theorem serializedParetoStandardMachineNPStyleLanguage_mem :
    CorrectedConcreteSerializedStandardMachineNPStyleLanguage
      serializedParetoNPStyleLanguage := by

  exact
    CorrectedConcreteSerializedStandardMachineNPStyleLanguage.ofRealization
      serializedParetoPolynomialWitnessDecisionProblem
      serializedParetoStandardMachineSemantics
      serializedParetoStandardMachineRealization
      rfl

/-- Complete observation-selection standard-machine realization package. -/
theorem serializedStandardMachineRealization_package :
    CorrectedConcreteSerializedStandardMachineNPStyleLanguage
        serializedCostNPStyleLanguage ∧
      CorrectedConcreteSerializedStandardMachineNPStyleLanguage
        serializedParetoNPStyleLanguage ∧
      (∀ input : List Nat,
        ∀ code : Nat,
          serializedCostStandardMachineSemantics.run
                serializedCostStandardMachineRealization.program
                input
                code =
            serializedCostPolynomialWitnessDecisionProblem.verifier
              input
              code) ∧
      (∀ input : List Nat,
        ∀ code : Nat,
          serializedParetoStandardMachineSemantics.run
                serializedParetoStandardMachineRealization.program
                input
                code =
            serializedParetoPolynomialWitnessDecisionProblem.verifier
              input
              code) := by

  exact
    ⟨serializedCostStandardMachineNPStyleLanguage_mem,
      serializedParetoStandardMachineNPStyleLanguage_mem,
      fun input code => rfl,
      fun input code => rfl⟩

end ObservationSelectionStandardMachineRealizations

end CorrectedConcreteEncodedObservationSelectionData


section EncodedSerializedStandardMachineRealizationFinalPackage

variable {α : Type u}
variable {ι : Type v}
variable {M : Type w}
variable [DecidableEq ι]
variable [Monoid M]
variable (obsFamily : ι → α → M)
variable (f : Nat)
variable (coordinateWeight : ι → Nat)
variable (U : Finset ι)

/-- Final standard-machine realization package at the exact semantic
positive-additive minimum rank.

The canonical serialized input belongs to the Pareto standard-machine-realized
NP-style language.  The canonical least dense Pareto code is accepted by the
realized program, is least among all accepted program certificates, satisfies
the transferred certificate-length and step bounds, and retains checked
decoding and Pareto optimality. -/
theorem
    correctedConcreteWorkingGrammar_observationSelectionEncodedSerializedStandardMachineRealization_package
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
    let semantics :=
      CorrectedConcreteEncodedObservationSelectionData.serializedParetoStandardMachineSemantics
    let realization :=
      CorrectedConcreteEncodedObservationSelectionData.serializedParetoStandardMachineRealization
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
    CorrectedConcreteSerializedStandardMachineNPStyleLanguage
        npLanguage ∧
      instance.serialize ∈ npLanguage ∧
      semantics.Accepts
          realization.program
          instance.serialize
          canonicalCode ∧
      (∀ competingCode : Nat,
        semantics.Accepts
              realization.program
              instance.serialize
              competingCode →
          canonicalCode <= competingCode) ∧
      semantics.certificateLength canonicalCode <=
        problem.certificateCoefficient *
          semantics.inputLength instance.serialize ^
            problem.certificateDegree ∧
      semantics.steps
            realization.program
            instance.serialize
            canonicalCode <=
        problem.verifierCoefficient *
          semantics.inputLength instance.serialize ^
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

  let semantics :=
    CorrectedConcreteEncodedObservationSelectionData.serializedParetoStandardMachineSemantics

  let realization :=
    CorrectedConcreteEncodedObservationSelectionData.serializedParetoStandardMachineRealization

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
      semantics.Accepts
        realization.program
        instance.serialize
        canonicalCode :=
    (realization.accepts_iff_witness
      instance.serialize
      canonicalCode).mpr
      hProblemWitness

  exact
    ⟨CorrectedConcreteEncodedObservationSelectionData.serializedParetoStandardMachineNPStyleLanguage_mem,
      hInput,
      hMachineAccepts,
      by
        intro competingCode hCompeting

        exact
          hLeast
            competingCode
            ((realization.accepts_iff_witness
              instance.serialize
              competingCode).mp
              hCompeting),
      realization.certificateLength_le
        hMachineAccepts,
      realization.steps_polynomial_le
        hMachineAccepts,
      hCertificateCoefficient,
      hCertificateDegree,
      hVerifierCoefficient,
      hVerifierDegree,
      hCodeBound,
      hDecode,
      hPareto⟩

end EncodedSerializedStandardMachineRealizationFinalPackage

end MCFG
