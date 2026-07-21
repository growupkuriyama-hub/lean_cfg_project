/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG.ConcreteCanonicalLearnerWorkingGrammarObservationSelectionEncodedSerializedNPStyleCanonicalWitness

/-!
# ConcreteCanonicalLearnerWorkingGrammarObservationSelectionEncodedSerializedDecisionProblem.lean

The preceding files package one canonical serialized observation-selection
instance at a time.  This file moves to a language-level decision problem whose
inputs are arbitrary pure natural-number lists.

A serialized witness decision problem consists of

```text
decision : List Nat → Bool
verifier : List Nat → Nat → Bool
```

together with the exact global law

```text
decision input = true
  iff
there exists a certificate code accepted by `verifier input`.
```

We prove this law for the ordinary-cost and Pareto-scalar serialized
observation-selection verifiers on every input list, not only on canonical
encodings.  Malformed inputs are rejected and have no witnesses.

For canonical encoded instances, the global decision problems agree with the
semantic observation-selection table.  At the exact positive-additive minimum
rank, the previously selected canonical Pareto dense code is a least witness
for the global Pareto decision problem and retains checked decoding and Pareto
optimality.

This is a pure decision-problem/witness interface over `List Nat`.  Its
canonical inputs still materialize exponential-size semantic tables, so no
compact-input NP-membership or hardness claim is made.

No target grammar is supplied to any learner.
No `sorry`, `admit`, or `axiom` is used.
-/

namespace MCFG

universe u v w z


namespace CorrectedConcreteEncodedObservationSelectionData

section ListLookupLemmas

/-- Membership yields an index at which `get?` returns the member. -/
theorem exists_get?_eq_some_of_mem
    {β : Type u}
    {value : β}
    {xs : List β}
    (hMem : value ∈ xs) :
    ∃ index : Nat,
      xs.get? index = some value := by

  induction xs with

  | nil =>
      simp at hMem

  | cons head tail ih =>
      simp only [List.mem_cons] at hMem

      rcases hMem with hHead | hTail

      · subst head

        exact
          ⟨0, by simp⟩

      · rcases ih hTail with
          ⟨index, hIndex⟩

        exact
          ⟨index + 1, by
            simpa [Nat.add_comm] using hIndex⟩

/-- A successful `get?` lookup yields list membership. -/
theorem mem_of_get?_eq_some
    {β : Type u}
    {value : β}
    {xs : List β}
    {index : Nat}
    (hGet :
      xs.get? index = some value) :
    value ∈ xs := by

  induction xs generalizing index with

  | nil =>
      simp at hGet

  | cons head tail ih =>
      cases index with

      | zero =>
          simp at hGet

          subst head

          simp

      | succ index =>
          simp at hGet

          exact
            List.mem_cons_of_mem
              head
              (ih hGet)

/-- A successful `get?` lookup is within the list length. -/
theorem lt_length_of_get?_eq_some
    {β : Type u}
    {value : β}
    {xs : List β}
    {index : Nat}
    (hGet :
      xs.get? index = some value) :
    index < xs.length := by

  induction xs generalizing index with

  | nil =>
      simp at hGet

  | cons head tail ih =>
      cases index with

      | zero =>
          simp

      | succ index =>
          simp at hGet

          have hTail :
              index < tail.length :=
            ih hGet

          simpa using hTail

end ListLookupLemmas


section DecoderWellFormedness

/-- Every successfully decoded serialized observation-selection data record has
the two membership vectors at exactly the declared code bound. -/
theorem wellFormed_of_decode_eq_some
    {input : List Nat}
    {data :
      CorrectedConcreteEncodedObservationSelectionData}
    (hDecode :
      decode input = some data) :
    data.WellFormed := by

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

            constructor

            · simp [hLength]

            · simp [hLength]

          · simp [decode, hLength] at hDecode

end DecoderWellFormedness


section GlobalSerializedDecisionWitnessEquivalence

/-- On every serialized input, the ordinary decision is positive exactly when
one ordinary certificate code is accepted. -/
theorem runSerializedCostDecision_eq_true_iff_exists_certificate
    (input : List Nat) :
    runSerializedCostDecision input = true ↔
      ∃ code : Nat,
        runSerializedCostCertificateVerifier
            input
            code =
          true := by

  constructor

  · intro hDecision

    rcases
        (runSerializedCostDecision_eq_true_iff
          input).mp
          hDecision with
      ⟨data, hDecode, hOne⟩

    rcases
        exists_get?_eq_some_of_mem
          hOne with
      ⟨code, hGet⟩

    have hWellFormed :
        data.WellFormed :=
      wellFormed_of_decode_eq_some hDecode

    have hCodeLtLength :
        code < data.costBits.length :=
      lt_length_of_get?_eq_some hGet

    have hCodeBound :
        code < data.codeBound := by

      simpa [hWellFormed.1] using
        hCodeLtLength

    exact
      ⟨code,
        (runSerializedCostCertificateVerifier_of_decode
          hDecode).mpr
          ⟨hCodeBound, hGet⟩⟩

  · rintro ⟨code, hAccepted⟩

    rcases
        (runSerializedCostCertificateVerifier_eq_true_iff
          input
          code).mp
          hAccepted with
      ⟨data, hDecode, hCodeBound, hGet⟩

    have hOne :
        1 ∈ data.costBits :=
      mem_of_get?_eq_some hGet

    exact
      (runSerializedCostDecision_eq_true_iff
        input).mpr
        ⟨data, hDecode, hOne⟩

/-- On every serialized input, the Pareto decision is positive exactly when one
Pareto certificate code is accepted. -/
theorem runSerializedParetoDecision_eq_true_iff_exists_certificate
    (input : List Nat) :
    runSerializedParetoDecision input = true ↔
      ∃ code : Nat,
        runSerializedParetoCertificateVerifier
            input
            code =
          true := by

  constructor

  · intro hDecision

    rcases
        (runSerializedParetoDecision_eq_true_iff
          input).mp
          hDecision with
      ⟨data, hDecode, hOne⟩

    rcases
        exists_get?_eq_some_of_mem
          hOne with
      ⟨code, hGet⟩

    have hWellFormed :
        data.WellFormed :=
      wellFormed_of_decode_eq_some hDecode

    have hCodeLtLength :
        code < data.paretoBits.length :=
      lt_length_of_get?_eq_some hGet

    have hCodeBound :
        code < data.codeBound := by

      simpa [hWellFormed.2] using
        hCodeLtLength

    exact
      ⟨code,
        (runSerializedParetoCertificateVerifier_of_decode
          hDecode).mpr
          ⟨hCodeBound, hGet⟩⟩

  · rintro ⟨code, hAccepted⟩

    rcases
        (runSerializedParetoCertificateVerifier_eq_true_iff
          input
          code).mp
          hAccepted with
      ⟨data, hDecode, hCodeBound, hGet⟩

    have hOne :
        1 ∈ data.paretoBits :=
      mem_of_get?_eq_some hGet

    exact
      (runSerializedParetoDecision_eq_true_iff
        input).mpr
        ⟨data, hDecode, hOne⟩

end GlobalSerializedDecisionWitnessEquivalence

end CorrectedConcreteEncodedObservationSelectionData


/-- A pure serialized decision problem with natural-number certificates. -/
structure CorrectedConcreteSerializedWitnessDecisionProblem where

  decision :
    List Nat → Bool

  verifier :
    List Nat → Nat → Bool

  decision_eq_true_iff_exists :
    ∀ input : List Nat,
      decision input = true ↔
        ∃ code : Nat,
          verifier input code = true


namespace CorrectedConcreteSerializedWitnessDecisionProblem

section GenericDecisionProblem

variable
  (problem :
    CorrectedConcreteSerializedWitnessDecisionProblem)

/-- Language accepted by the serialized decision problem. -/
def AcceptedLanguage :
    Set (List Nat) :=
  {input |
    problem.decision input = true}

/-- Witness relation of the serialized decision problem. -/
def Witness
    (input : List Nat)
    (code : Nat) : Prop :=
  problem.verifier input code = true

/-- Exact accepted-language/witness equivalence. -/
theorem mem_acceptedLanguage_iff_exists_witness
    (input : List Nat) :
    input ∈ problem.AcceptedLanguage ↔
      ∃ code : Nat,
        problem.Witness input code := by

  exact
    problem.decision_eq_true_iff_exists
      input

/-- Verifier soundness for the accepted language. -/
theorem sound
    {input : List Nat}
    {code : Nat}
    (hWitness :
      problem.Witness input code) :
    input ∈ problem.AcceptedLanguage := by

  exact
    (problem.mem_acceptedLanguage_iff_exists_witness
      input).mpr
      ⟨code, hWitness⟩

/-- Verifier completeness for the accepted language. -/
theorem complete
    {input : List Nat}
    (hAccepted :
      input ∈ problem.AcceptedLanguage) :
    ∃ code : Nat,
      problem.Witness input code := by

  exact
    (problem.mem_acceptedLanguage_iff_exists_witness
      input).mp
      hAccepted

/-- Rejected inputs have no accepted certificates. -/
theorem no_witness_of_decision_eq_false
    {input : List Nat}
    (hRejected :
      problem.decision input = false) :
    ¬ ∃ code : Nat,
        problem.Witness input code := by

  intro hWitness

  have hAccepted :
      problem.decision input = true :=
    problem.decision_eq_true_iff_exists
      input
    |>.mpr
      hWitness

  simp [hRejected] at hAccepted

end GenericDecisionProblem

end CorrectedConcreteSerializedWitnessDecisionProblem


namespace CorrectedConcreteEncodedObservationSelectionData

/-- Global ordinary-cost serialized observation-selection decision problem. -/
def serializedCostWitnessDecisionProblem :
    CorrectedConcreteSerializedWitnessDecisionProblem :=
  {
    decision :=
      runSerializedCostDecision

    verifier :=
      runSerializedCostCertificateVerifier

    decision_eq_true_iff_exists :=
      runSerializedCostDecision_eq_true_iff_exists_certificate
  }

/-- Global Pareto-scalar serialized observation-selection decision problem. -/
def serializedParetoWitnessDecisionProblem :
    CorrectedConcreteSerializedWitnessDecisionProblem :=
  {
    decision :=
      runSerializedParetoDecision

    verifier :=
      runSerializedParetoCertificateVerifier

    decision_eq_true_iff_exists :=
      runSerializedParetoDecision_eq_true_iff_exists_certificate
  }

@[simp]
theorem serializedCostWitnessDecisionProblem_decision
    (input : List Nat) :
    serializedCostWitnessDecisionProblem.decision input =
      runSerializedCostDecision input := by

  rfl

@[simp]
theorem serializedCostWitnessDecisionProblem_verifier
    (input : List Nat)
    (code : Nat) :
    serializedCostWitnessDecisionProblem.verifier input code =
      runSerializedCostCertificateVerifier input code := by

  rfl

@[simp]
theorem serializedParetoWitnessDecisionProblem_decision
    (input : List Nat) :
    serializedParetoWitnessDecisionProblem.decision input =
      runSerializedParetoDecision input := by

  rfl

@[simp]
theorem serializedParetoWitnessDecisionProblem_verifier
    (input : List Nat)
    (code : Nat) :
    serializedParetoWitnessDecisionProblem.verifier input code =
      runSerializedParetoCertificateVerifier input code := by

  rfl

/-- Both global serialized decision problems satisfy exact witness
soundness/completeness on every input. -/
theorem serializedWitnessDecisionProblem_package
    (input : List Nat) :
    (serializedCostWitnessDecisionProblem.decision input = true ↔
      ∃ code : Nat,
        serializedCostWitnessDecisionProblem.Witness
          input
          code) ∧
      (serializedParetoWitnessDecisionProblem.decision input = true ↔
        ∃ code : Nat,
          serializedParetoWitnessDecisionProblem.Witness
            input
            code) := by

  exact
    ⟨serializedCostWitnessDecisionProblem.decision_eq_true_iff_exists
      input,
      serializedParetoWitnessDecisionProblem.decision_eq_true_iff_exists
        input⟩

end CorrectedConcreteEncodedObservationSelectionData


namespace CorrectedConcreteEncodedObservationSelectionInstance

section GlobalDecisionProblemOnCanonicalInstance

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

/-- The global ordinary serialized decision problem agrees with the semantic
table on a canonical encoded instance. -/
theorem serializedCostWitnessDecisionProblem_serialize_iff_tableDecision :
    CorrectedConcreteEncodedObservationSelectionData.serializedCostWitnessDecisionProblem.decision
          instance.serialize =
        true ↔
      table.costFeasibleDecision instance.budget = true := by

  exact
    instance.runSerializedCostDecision_serialize_iff_tableDecision

/-- The global Pareto serialized decision problem agrees with the semantic
table on a canonical encoded instance. -/
theorem serializedParetoWitnessDecisionProblem_serialize_iff_tableDecision :
    CorrectedConcreteEncodedObservationSelectionData.serializedParetoWitnessDecisionProblem.decision
          instance.serialize =
        true ↔
      table.paretoScalarFeasibleDecision
          instance.budget =
        true := by

  exact
    instance.runSerializedParetoDecision_serialize_iff_tableDecision

/-- Global ordinary witness acceptance agrees with the dense semantic
certificate verifier on a canonical encoded instance. -/
theorem serializedCostWitnessDecisionProblem_serialize_witness_iff_denseVerifier
    (code : Nat) :
    CorrectedConcreteEncodedObservationSelectionData.serializedCostWitnessDecisionProblem.Witness
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

/-- Global Pareto witness acceptance agrees with the dense semantic certificate
verifier on a canonical encoded instance. -/
theorem serializedParetoWitnessDecisionProblem_serialize_witness_iff_denseVerifier
    (code : Nat) :
    CorrectedConcreteEncodedObservationSelectionData.serializedParetoWitnessDecisionProblem.Witness
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

end GlobalDecisionProblemOnCanonicalInstance

end CorrectedConcreteEncodedObservationSelectionInstance


section EncodedSerializedDecisionProblemFinalPackage

variable {α : Type u}
variable {ι : Type v}
variable {M : Type w}
variable [DecidableEq ι]
variable [Monoid M]
variable (obsFamily : ι → α → M)
variable (f : Nat)
variable (coordinateWeight : ι → Nat)
variable (U : Finset ι)

/-- Final global serialized decision-problem package.

At the exact semantic positive-additive minimum rank, the canonical serialized
input belongs to the global Pareto accepted language.  The previously selected
canonical dense Pareto code is a least witness for that global problem, remains
below `2 ^ U.card`, and decodes to the same Pareto-optimal certificate. -/
theorem
    correctedConcreteWorkingGrammar_observationSelectionEncodedSerializedDecisionProblem_package
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
      CorrectedConcreteEncodedObservationSelectionData.serializedParetoWitnessDecisionProblem
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
    CorrectedConcreteEncodedObservationSelectionData.serializedParetoWitnessDecisionProblem

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
    problem.sound hProblemWitness

  exact
    ⟨hProblemAccepted,
      hProblemWitness,
      by
        intro competingCode hCompeting

        exact
          hLeast
            competingCode
            hCompeting,
      hCodeBound,
      hDecode,
      hPareto⟩

end EncodedSerializedDecisionProblemFinalPackage

end MCFG
