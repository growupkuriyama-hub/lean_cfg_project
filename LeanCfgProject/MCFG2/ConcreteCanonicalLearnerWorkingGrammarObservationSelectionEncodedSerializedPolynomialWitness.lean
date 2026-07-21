/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG2.ConcreteCanonicalLearnerWorkingGrammarObservationSelectionEncodedSerializedCertificateVerifier

/-!
# ConcreteCanonicalLearnerWorkingGrammarObservationSelectionEncodedSerializedPolynomialWitness.lean

The preceding file defines a pure single-certificate verifier that receives

```text
a serialized `List Nat` input
+ one natural-number certificate code.
```

This file turns that verifier into an explicit serialized witness relation.

For ordinary cost and Pareto-scalar feasibility, a witness is simply a
certificate code accepted by the corresponding pure serialized verifier.  For
every serialized proof-carrying encoded instance we prove

```text
serialized decision = true
  iff
there exists a serialized certificate witness.
```

We also construct the finite sets of all bounded serialized witnesses and prove

* exact equality with the stored accepted-code tables;
* nonemptiness exactly for positive serialized decisions;
* cardinality at most the decoded code bound;
* every witness code has unary-size `code + 1` bounded by the serialized input
  size;
* every witness is checked with the degree-one work envelope from the preceding
  file.

At the exact semantic positive-additive minimum rank, the previously selected
canonical least Pareto dense code is a serialized polynomial witness.  It is no
larger than every competing serialized Pareto witness, has bounded certificate
size and linear verifier work, and decodes to the same Pareto-optimal
certificate.

This is a complete NP-style witness theorem relative to the already
materialized serialized table.  The table has exponential length in `U.card`
and is still constructed noncomputably from semantic feasibility data.
Therefore this file does not claim compact-input NP membership, NP-hardness, or
NP-completeness.

No target grammar is supplied to any learner.
No `sorry`, `admit`, or `axiom` is used.
-/

namespace MCFG

universe u v w z


namespace CorrectedConcreteEncodedObservationSelectionData

section PureSerializedWitnessRelations

/-- Ordinary serialized certificate witness relation. -/
def SerializedCostWitness
    (input : List Nat)
    (code : Nat) : Prop :=
  runSerializedCostCertificateVerifier input code = true

/-- Pareto serialized certificate witness relation. -/
def SerializedParetoWitness
    (input : List Nat)
    (code : Nat) : Prop :=
  runSerializedParetoCertificateVerifier input code = true

/-- Unary natural-size accounting for one serialized certificate code. -/
def serializedWitnessCertificateSize
    (code : Nat) : Nat :=
  code + 1

/-- The ordinary witness relation is decidable by the pure serialized
certificate verifier. -/
instance instDecidableSerializedCostWitness
    (input : List Nat)
    (code : Nat) :
    Decidable (SerializedCostWitness input code) :=
  inferInstance

/-- The Pareto witness relation is decidable by the pure serialized
certificate verifier. -/
instance instDecidableSerializedParetoWitness
    (input : List Nat)
    (code : Nat) :
    Decidable (SerializedParetoWitness input code) :=
  inferInstance

end PureSerializedWitnessRelations

end CorrectedConcreteEncodedObservationSelectionData


namespace CorrectedConcreteEncodedObservationSelectionInstance

section SerializedWitnessDecisionEquivalence

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

/-- The serialized ordinary decision is positive exactly when one serialized
ordinary certificate witness exists. -/
theorem runSerializedCostDecision_eq_true_iff_exists_witness :
    CorrectedConcreteEncodedObservationSelectionData.runSerializedCostDecision
          instance.serialize =
        true ↔
      ∃ code : Nat,
        CorrectedConcreteEncodedObservationSelectionData.SerializedCostWitness
          instance.serialize
          code := by

  constructor

  · intro hDecision

    have hInstanceDecision :
        instance.costDecision = true :=
      (instance.runSerializedCostDecision_serialize_eq_true_iff).mp
        hDecision

    rcases
        (instance.costDecision_eq_true_iff_exists_code).mp
          hInstanceDecision with
      ⟨code, hStored⟩

    have hBound :
        code < instance.codeBound :=
      ((instance.costCodes_correct code).mp hStored).1

    refine ⟨code, ?_⟩

    exact
      (instance.runSerializedCostCertificateVerifier_serialize_eq_true_iff
        code).mpr
        ⟨hBound, hStored⟩

  · rintro ⟨code, hWitness⟩

    have hParts :
        code < instance.codeBound ∧
          code ∈ instance.costCertificateCodes :=
      (instance.runSerializedCostCertificateVerifier_serialize_eq_true_iff
        code).mp
        hWitness

    have hInstanceDecision :
        instance.costDecision = true :=
      (instance.costDecision_eq_true_iff_exists_code).mpr
        ⟨code, hParts.2⟩

    exact
      (instance.runSerializedCostDecision_serialize_eq_true_iff).mpr
        hInstanceDecision

/-- The serialized Pareto decision is positive exactly when one serialized
Pareto certificate witness exists. -/
theorem runSerializedParetoDecision_eq_true_iff_exists_witness :
    CorrectedConcreteEncodedObservationSelectionData.runSerializedParetoDecision
          instance.serialize =
        true ↔
      ∃ code : Nat,
        CorrectedConcreteEncodedObservationSelectionData.SerializedParetoWitness
          instance.serialize
          code := by

  constructor

  · intro hDecision

    have hInstanceDecision :
        instance.paretoDecision = true :=
      (instance.runSerializedParetoDecision_serialize_eq_true_iff).mp
        hDecision

    rcases
        (instance.paretoDecision_eq_true_iff_exists_code).mp
          hInstanceDecision with
      ⟨code, hStored⟩

    have hBound :
        code < instance.codeBound :=
      ((instance.paretoCodes_correct code).mp hStored).1

    refine ⟨code, ?_⟩

    exact
      (instance.runSerializedParetoCertificateVerifier_serialize_eq_true_iff
        code).mpr
        ⟨hBound, hStored⟩

  · rintro ⟨code, hWitness⟩

    have hParts :
        code < instance.codeBound ∧
          code ∈ instance.paretoCertificateCodes :=
      (instance.runSerializedParetoCertificateVerifier_serialize_eq_true_iff
        code).mp
        hWitness

    have hInstanceDecision :
        instance.paretoDecision = true :=
      (instance.paretoDecision_eq_true_iff_exists_code).mpr
        ⟨code, hParts.2⟩

    exact
      (instance.runSerializedParetoDecision_serialize_eq_true_iff).mpr
        hInstanceDecision

end SerializedWitnessDecisionEquivalence


section FiniteSerializedWitnessSets

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

/-- Finite set of all bounded ordinary serialized witnesses. -/
def serializedCostWitnessCodes : Finset Nat :=
  (Finset.range instance.codeBound).filter
    (fun code =>
      CorrectedConcreteEncodedObservationSelectionData.runSerializedCostCertificateVerifier
          instance.serialize
          code =
        true)

/-- Finite set of all bounded Pareto serialized witnesses. -/
def serializedParetoWitnessCodes : Finset Nat :=
  (Finset.range instance.codeBound).filter
    (fun code =>
      CorrectedConcreteEncodedObservationSelectionData.runSerializedParetoCertificateVerifier
          instance.serialize
          code =
        true)

/-- Membership in the finite ordinary serialized witness family. -/
theorem mem_serializedCostWitnessCodes_iff
    (code : Nat) :
    code ∈ instance.serializedCostWitnessCodes ↔
      code < instance.codeBound ∧
        CorrectedConcreteEncodedObservationSelectionData.SerializedCostWitness
          instance.serialize
          code := by

  simp [
    serializedCostWitnessCodes,
    CorrectedConcreteEncodedObservationSelectionData.SerializedCostWitness
  ]

/-- Membership in the finite Pareto serialized witness family. -/
theorem mem_serializedParetoWitnessCodes_iff
    (code : Nat) :
    code ∈ instance.serializedParetoWitnessCodes ↔
      code < instance.codeBound ∧
        CorrectedConcreteEncodedObservationSelectionData.SerializedParetoWitness
          instance.serialize
          code := by

  simp [
    serializedParetoWitnessCodes,
    CorrectedConcreteEncodedObservationSelectionData.SerializedParetoWitness
  ]

/-- The finite ordinary serialized witness family is exactly the stored
ordinary accepted-code table. -/
theorem serializedCostWitnessCodes_eq :
    instance.serializedCostWitnessCodes =
      instance.costCertificateCodes := by

  ext code

  simp [
    serializedCostWitnessCodes,
    instance.runSerializedCostCertificateVerifier_serialize_eq_true_iff
  ]

/-- The finite Pareto serialized witness family is exactly the stored Pareto
accepted-code table. -/
theorem serializedParetoWitnessCodes_eq :
    instance.serializedParetoWitnessCodes =
      instance.paretoCertificateCodes := by

  ext code

  simp [
    serializedParetoWitnessCodes,
    instance.runSerializedParetoCertificateVerifier_serialize_eq_true_iff
  ]

/-- Ordinary serialized witness-family nonemptiness exactly characterizes the
serialized ordinary decision. -/
theorem serializedCostWitnessCodes_nonempty_iff :
    instance.serializedCostWitnessCodes.Nonempty ↔
      CorrectedConcreteEncodedObservationSelectionData.runSerializedCostDecision
          instance.serialize =
        true := by

  constructor

  · rintro ⟨code, hCode⟩

    have hWitness :
        CorrectedConcreteEncodedObservationSelectionData.SerializedCostWitness
          instance.serialize
          code :=
      ((instance.mem_serializedCostWitnessCodes_iff code).mp hCode).2

    exact
      (instance.runSerializedCostDecision_eq_true_iff_exists_witness).mpr
        ⟨code, hWitness⟩

  · intro hDecision

    rcases
        (instance.runSerializedCostDecision_eq_true_iff_exists_witness).mp
          hDecision with
      ⟨code, hWitness⟩

    have hParts :
        code < instance.codeBound ∧
          code ∈ instance.costCertificateCodes :=
      (instance.runSerializedCostCertificateVerifier_serialize_eq_true_iff
        code).mp
        hWitness

    exact
      ⟨code,
        (instance.mem_serializedCostWitnessCodes_iff code).mpr
          ⟨hParts.1, hWitness⟩⟩

/-- Pareto serialized witness-family nonemptiness exactly characterizes the
serialized Pareto decision. -/
theorem serializedParetoWitnessCodes_nonempty_iff :
    instance.serializedParetoWitnessCodes.Nonempty ↔
      CorrectedConcreteEncodedObservationSelectionData.runSerializedParetoDecision
          instance.serialize =
        true := by

  constructor

  · rintro ⟨code, hCode⟩

    have hWitness :
        CorrectedConcreteEncodedObservationSelectionData.SerializedParetoWitness
          instance.serialize
          code :=
      ((instance.mem_serializedParetoWitnessCodes_iff code).mp hCode).2

    exact
      (instance.runSerializedParetoDecision_eq_true_iff_exists_witness).mpr
        ⟨code, hWitness⟩

  · intro hDecision

    rcases
        (instance.runSerializedParetoDecision_eq_true_iff_exists_witness).mp
          hDecision with
      ⟨code, hWitness⟩

    have hParts :
        code < instance.codeBound ∧
          code ∈ instance.paretoCertificateCodes :=
      (instance.runSerializedParetoCertificateVerifier_serialize_eq_true_iff
        code).mp
        hWitness

    exact
      ⟨code,
        (instance.mem_serializedParetoWitnessCodes_iff code).mpr
          ⟨hParts.1, hWitness⟩⟩

/-- Ordinary serialized witness count is bounded by the decoded code
universe. -/
theorem serializedCostWitnessCodes_card_le :
    instance.serializedCostWitnessCodes.card <=
      instance.codeBound := by

  rw [instance.serializedCostWitnessCodes_eq]

  exact instance.costCertificateCodes_card_le

/-- Pareto serialized witness count is bounded by the decoded code universe. -/
theorem serializedParetoWitnessCodes_card_le :
    instance.serializedParetoWitnessCodes.card <=
      instance.codeBound := by

  rw [instance.serializedParetoWitnessCodes_eq]

  exact instance.paretoCertificateCodes_card_le

end FiniteSerializedWitnessSets


section SerializedWitnessResourceBounds

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

/-- Every ordinary serialized witness code has unary size bounded by the
serialized input size. -/
theorem serializedCostWitness_certificateSize_le
    {code : Nat}
    (hWitness :
      CorrectedConcreteEncodedObservationSelectionData.SerializedCostWitness
        instance.serialize
        code) :
    CorrectedConcreteEncodedObservationSelectionData.serializedWitnessCertificateSize
          code <=
      CorrectedConcreteEncodedObservationSelectionData.serializedCertificateVerifierInputSize
        instance.serialize
        code := by

  have hBound :
      code < instance.codeBound :=
    ((instance.runSerializedCostCertificateVerifier_serialize_eq_true_iff
      code).mp
      hWitness).1

  rw [instance.serialize_certificateVerifierInputSize]

  unfold CorrectedConcreteEncodedObservationSelectionData.serializedWitnessCertificateSize

  omega

/-- Every Pareto serialized witness code has unary size bounded by the
serialized input size. -/
theorem serializedParetoWitness_certificateSize_le
    {code : Nat}
    (hWitness :
      CorrectedConcreteEncodedObservationSelectionData.SerializedParetoWitness
        instance.serialize
        code) :
    CorrectedConcreteEncodedObservationSelectionData.serializedWitnessCertificateSize
          code <=
      CorrectedConcreteEncodedObservationSelectionData.serializedCertificateVerifierInputSize
        instance.serialize
        code := by

  have hBound :
      code < instance.codeBound :=
    ((instance.runSerializedParetoCertificateVerifier_serialize_eq_true_iff
      code).mp
      hWitness).1

  rw [instance.serialize_certificateVerifierInputSize]

  unfold CorrectedConcreteEncodedObservationSelectionData.serializedWitnessCertificateSize

  omega

/-- Ordinary serialized witness with certificate-size and verifier-work
bounds. -/
structure SerializedCostPolynomialWitness where

  code : Nat

  accepted :
    CorrectedConcreteEncodedObservationSelectionData.SerializedCostWitness
      instance.serialize
      code

  certificateSize_le :
    CorrectedConcreteEncodedObservationSelectionData.serializedWitnessCertificateSize
          code <=
      CorrectedConcreteEncodedObservationSelectionData.serializedCertificateVerifierInputSize
        instance.serialize
        code

  verifierWork :
    (CorrectedConcreteEncodedObservationSelectionData.runSerializedCostCertificateVerifierWithWork
      instance.serialize
      code).2 =
        4 *
          CorrectedConcreteEncodedObservationSelectionData.serializedCertificateVerifierInputSize
            instance.serialize
            code

/-- Pareto serialized witness with certificate-size and verifier-work bounds. -/
structure SerializedParetoPolynomialWitness where

  code : Nat

  accepted :
    CorrectedConcreteEncodedObservationSelectionData.SerializedParetoWitness
      instance.serialize
      code

  certificateSize_le :
    CorrectedConcreteEncodedObservationSelectionData.serializedWitnessCertificateSize
          code <=
      CorrectedConcreteEncodedObservationSelectionData.serializedCertificateVerifierInputSize
        instance.serialize
        code

  verifierWork :
    (CorrectedConcreteEncodedObservationSelectionData.runSerializedParetoCertificateVerifierWithWork
      instance.serialize
      code).2 =
        4 *
          CorrectedConcreteEncodedObservationSelectionData.serializedCertificateVerifierInputSize
            instance.serialize
            code

/-- Package any accepted ordinary serialized code as a polynomial witness. -/
def serializedCostPolynomialWitnessOfAccepted
    (code : Nat)
    (hAccepted :
      CorrectedConcreteEncodedObservationSelectionData.SerializedCostWitness
        instance.serialize
        code) :
    instance.SerializedCostPolynomialWitness :=
  {
    code := code
    accepted := hAccepted
    certificateSize_le :=
      instance.serializedCostWitness_certificateSize_le hAccepted
    verifierWork := rfl
  }

/-- Package any accepted Pareto serialized code as a polynomial witness. -/
def serializedParetoPolynomialWitnessOfAccepted
    (code : Nat)
    (hAccepted :
      CorrectedConcreteEncodedObservationSelectionData.SerializedParetoWitness
        instance.serialize
        code) :
    instance.SerializedParetoPolynomialWitness :=
  {
    code := code
    accepted := hAccepted
    certificateSize_le :=
      instance.serializedParetoWitness_certificateSize_le hAccepted
    verifierWork := rfl
  }

/-- Every positive serialized ordinary decision has a polynomial witness. -/
noncomputable def selectedSerializedCostPolynomialWitness
    (hDecision :
      CorrectedConcreteEncodedObservationSelectionData.runSerializedCostDecision
          instance.serialize =
        true) :
    instance.SerializedCostPolynomialWitness := by

  rcases
      (instance.runSerializedCostDecision_eq_true_iff_exists_witness).mp
        hDecision with
    ⟨code, hAccepted⟩

  exact
    instance.serializedCostPolynomialWitnessOfAccepted
      code
      hAccepted

/-- Every positive serialized Pareto decision has a polynomial witness. -/
noncomputable def selectedSerializedParetoPolynomialWitness
    (hDecision :
      CorrectedConcreteEncodedObservationSelectionData.runSerializedParetoDecision
          instance.serialize =
        true) :
    instance.SerializedParetoPolynomialWitness := by

  rcases
      (instance.runSerializedParetoDecision_eq_true_iff_exists_witness).mp
        hDecision with
    ⟨code, hAccepted⟩

  exact
    instance.serializedParetoPolynomialWitnessOfAccepted
      code
      hAccepted

/-- Complete serialized witness/resource package for one encoded instance. -/
theorem serializedPolynomialWitness_package :
    (CorrectedConcreteEncodedObservationSelectionData.runSerializedCostDecision
          instance.serialize =
        true ↔
      ∃ witness : instance.SerializedCostPolynomialWitness,
        CorrectedConcreteEncodedObservationSelectionData.SerializedCostWitness
          instance.serialize
          witness.code) ∧
      (CorrectedConcreteEncodedObservationSelectionData.runSerializedParetoDecision
          instance.serialize =
        true ↔
        ∃ witness : instance.SerializedParetoPolynomialWitness,
          CorrectedConcreteEncodedObservationSelectionData.SerializedParetoWitness
            instance.serialize
            witness.code) ∧
      instance.serializedCostWitnessCodes.card <=
        instance.codeBound ∧
      instance.serializedParetoWitnessCodes.card <=
        instance.codeBound := by

  constructor

  · constructor

    · intro hDecision

      let witness :=
        instance.selectedSerializedCostPolynomialWitness
          hDecision

      exact ⟨witness, witness.accepted⟩

    · rintro ⟨witness, hAccepted⟩

      exact
        (instance.runSerializedCostDecision_eq_true_iff_exists_witness).mpr
          ⟨witness.code, hAccepted⟩

  · constructor

    · constructor

      · intro hDecision

        let witness :=
          instance.selectedSerializedParetoPolynomialWitness
            hDecision

        exact ⟨witness, witness.accepted⟩

      · rintro ⟨witness, hAccepted⟩

        exact
          (instance.runSerializedParetoDecision_eq_true_iff_exists_witness).mpr
            ⟨witness.code, hAccepted⟩

    · exact
        ⟨instance.serializedCostWitnessCodes_card_le,
          instance.serializedParetoWitnessCodes_card_le⟩

end SerializedWitnessResourceBounds

end CorrectedConcreteEncodedObservationSelectionInstance


section EncodedSerializedPolynomialWitnessFinalPackage

variable {α : Type u}
variable {ι : Type v}
variable {M : Type w}
variable [DecidableEq ι]
variable [Monoid M]
variable (obsFamily : ι → α → M)
variable (f : Nat)
variable (coordinateWeight : ι → Nat)
variable (U : Finset ι)

/-- Final positive-additive canonical serialized polynomial-witness package.

At the exact semantic minimum rank, the previously selected canonical least
Pareto dense code is a polynomial witness for the pure serialized input.  It is
least among all serialized Pareto witnesses, has certificate size bounded by
the serialized input size, uses the exact degree-one verifier work envelope,
and decodes to the same Pareto-optimal observation-selection certificate. -/
theorem
    correctedConcreteWorkingGrammar_observationSelectionEncodedSerializedPolynomialWitness_package
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
    let witness :=
      instance.serializedParetoPolynomialWitnessOfAccepted
        canonicalCode
        (by
          exact
            (correctedConcreteWorkingGrammar_observationSelectionEncodedSerializedCertificateVerifier_package
              (z := z)
              obsFamily
              f
              coordinateWeight
              U
              language
              hTarget).1)
    CorrectedConcreteEncodedObservationSelectionData.runSerializedParetoDecision
          instance.serialize =
        true ∧
      CorrectedConcreteEncodedObservationSelectionData.SerializedParetoWitness
          instance.serialize
          witness.code ∧
      (∀ competingCode : Nat,
        CorrectedConcreteEncodedObservationSelectionData.SerializedParetoWitness
              instance.serialize
              competingCode →
          witness.code <= competingCode) ∧
      CorrectedConcreteEncodedObservationSelectionData.serializedWitnessCertificateSize
            witness.code <=
        CorrectedConcreteEncodedObservationSelectionData.serializedCertificateVerifierInputSize
          instance.serialize
          witness.code ∧
      (CorrectedConcreteEncodedObservationSelectionData.runSerializedParetoCertificateVerifierWithWork
        instance.serialize
        witness.code).2 =
          4 *
            CorrectedConcreteEncodedObservationSelectionData.serializedCertificateVerifierInputSize
              instance.serialize
              witness.code ∧
      witness.code < 2 ^ U.card ∧
      correctedConcreteDenseCertificateDecode
            U
            witness.code =
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

  have hCanonical :=
    correctedConcreteWorkingGrammar_observationSelectionEncodedSerializedCertificateVerifier_package
      (z := z)
      obsFamily
      f
      coordinateWeight
      U
      language
      hTarget

  let witness :=
    instance.serializedParetoPolynomialWitnessOfAccepted
      canonicalCode
      hCanonical.1

  have hDecision :
      CorrectedConcreteEncodedObservationSelectionData.runSerializedParetoDecision
            instance.serialize =
          true :=
    (instance.runSerializedParetoDecision_eq_true_iff_exists_witness).mpr
      ⟨canonicalCode, hCanonical.1⟩

  exact
    ⟨hDecision,
      witness.accepted,
      by
        intro competingCode hCompeting

        exact hCanonical.2.2.1 competingCode hCompeting,
      witness.certificateSize_le,
      witness.verifierWork,
      hCanonical.2.1,
      hCanonical.2.2.2.2.1,
      hCanonical.2.2.2.2.2⟩

end EncodedSerializedPolynomialWitnessFinalPackage

end MCFG
