/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG2.ConcreteCanonicalLearnerWorkingGrammarObservationSelectionEncodedSerializedNPStyleMinimumBudgetSelector

/-!
# ConcreteCanonicalLearnerWorkingGrammarObservationSelectionEncodedSerializedNPStyleCanonicalWitness.lean

The preceding file selects the least accepted budget and then chooses an
arbitrary polynomial witness at that budget.  This file canonically refines the
witness choice itself.

For every positive serialized encoded-instance decision, we take the `Finset.min'`
of the finite serialized witness-code family.  The selected code

* is accepted by the pure serialized certificate verifier;
* is no larger than every competing serialized witness code;
* carries the degree-one certificate-size bound;
* carries the degree-one verifier-work bound.

Ordinary-cost and Pareto-scalar canonical witnesses are both constructed.

At the exact semantic positive-additive minimum rank, the new finite
`min'`-selected Pareto witness is proved equal to the previously constructed
canonical dense Pareto code.  Hence the budget selector, dense-code selector,
serialized verifier, and NP-style membership interface all use one and the
same canonical witness.

This remains relative to the already materialized serialized semantic table.
It does not claim compact-input NP membership, NP-hardness, or NP-completeness.

No target grammar is supplied to any learner.
No `sorry`, `admit`, or `axiom` is used.
-/

namespace MCFG

universe u v w z


namespace CorrectedConcreteSerializedNPStyleMembership

section CanonicalPolynomialWitness

variable
  (membership :
    CorrectedConcreteSerializedNPStyleMembership)

/-- A polynomial witness that is least among all accepted certificate codes. -/
structure CanonicalPolynomialWitness where

  code : Nat

  accepted :
    membership.Witness code

  least :
    ∀ competingCode : Nat,
      membership.Witness competingCode →
        code <= competingCode

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

/-- Any two canonical polynomial witnesses for one membership package have the
same certificate code. -/
theorem canonicalPolynomialWitness_code_unique
    (first second :
      membership.CanonicalPolynomialWitness) :
    first.code = second.code := by

  exact
    Nat.le_antisymm
      (first.least second.code second.accepted)
      (second.least first.code first.accepted)

/-- Complete generic canonical polynomial-witness package. -/
theorem canonicalPolynomialWitness_package
    (canonical :
      membership.CanonicalPolynomialWitness) :
    membership.Witness canonical.code ∧
      (∀ competingCode : Nat,
        membership.Witness competingCode →
          canonical.code <= competingCode) ∧
      membership.certificateSize canonical.code <=
        membership.certificateCoefficient *
          membership.inputSize ^
            membership.certificateDegree ∧
      membership.verifierWork canonical.code <=
        membership.verifierCoefficient *
          membership.inputSize ^
            membership.verifierDegree := by

  exact
    ⟨canonical.accepted,
      canonical.least,
      canonical.certificateSize_le,
      canonical.verifierWork_le⟩

end CanonicalPolynomialWitness

end CorrectedConcreteSerializedNPStyleMembership


namespace CorrectedConcreteEncodedObservationSelectionInstance

section LeastSerializedWitnessCodes

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

/-- Least ordinary serialized witness code for a positive encoded-instance
decision. -/
noncomputable def selectedLeastSerializedCostWitnessCode
    (hDecision :
      CorrectedConcreteEncodedObservationSelectionData.runSerializedCostDecision
          instance.serialize =
        true) : Nat :=
  instance.serializedCostWitnessCodes.min'
    ((instance.serializedCostWitnessCodes_nonempty_iff).mpr
      hDecision)

/-- Least Pareto serialized witness code for a positive encoded-instance
decision. -/
noncomputable def selectedLeastSerializedParetoWitnessCode
    (hDecision :
      CorrectedConcreteEncodedObservationSelectionData.runSerializedParetoDecision
          instance.serialize =
        true) : Nat :=
  instance.serializedParetoWitnessCodes.min'
    ((instance.serializedParetoWitnessCodes_nonempty_iff).mpr
      hDecision)

/-- The selected ordinary code belongs to the finite ordinary witness family. -/
theorem selectedLeastSerializedCostWitnessCode_mem
    (hDecision :
      CorrectedConcreteEncodedObservationSelectionData.runSerializedCostDecision
          instance.serialize =
        true) :
    instance.selectedLeastSerializedCostWitnessCode hDecision ∈
      instance.serializedCostWitnessCodes := by

  exact
    Finset.min'_mem
      instance.serializedCostWitnessCodes
      ((instance.serializedCostWitnessCodes_nonempty_iff).mpr
        hDecision)

/-- The selected Pareto code belongs to the finite Pareto witness family. -/
theorem selectedLeastSerializedParetoWitnessCode_mem
    (hDecision :
      CorrectedConcreteEncodedObservationSelectionData.runSerializedParetoDecision
          instance.serialize =
        true) :
    instance.selectedLeastSerializedParetoWitnessCode hDecision ∈
      instance.serializedParetoWitnessCodes := by

  exact
    Finset.min'_mem
      instance.serializedParetoWitnessCodes
      ((instance.serializedParetoWitnessCodes_nonempty_iff).mpr
        hDecision)

/-- The selected ordinary code is accepted by the pure serialized verifier. -/
theorem selectedLeastSerializedCostWitnessCode_accepted
    (hDecision :
      CorrectedConcreteEncodedObservationSelectionData.runSerializedCostDecision
          instance.serialize =
        true) :
    CorrectedConcreteEncodedObservationSelectionData.SerializedCostWitness
      instance.serialize
      (instance.selectedLeastSerializedCostWitnessCode hDecision) := by

  exact
    ((instance.mem_serializedCostWitnessCodes_iff
      (instance.selectedLeastSerializedCostWitnessCode
        hDecision)).mp
      (instance.selectedLeastSerializedCostWitnessCode_mem
        hDecision)).2

/-- The selected Pareto code is accepted by the pure serialized verifier. -/
theorem selectedLeastSerializedParetoWitnessCode_accepted
    (hDecision :
      CorrectedConcreteEncodedObservationSelectionData.runSerializedParetoDecision
          instance.serialize =
        true) :
    CorrectedConcreteEncodedObservationSelectionData.SerializedParetoWitness
      instance.serialize
      (instance.selectedLeastSerializedParetoWitnessCode hDecision) := by

  exact
    ((instance.mem_serializedParetoWitnessCodes_iff
      (instance.selectedLeastSerializedParetoWitnessCode
        hDecision)).mp
      (instance.selectedLeastSerializedParetoWitnessCode_mem
        hDecision)).2

/-- The selected ordinary code lies below the decoded exclusive code bound. -/
theorem selectedLeastSerializedCostWitnessCode_lt
    (hDecision :
      CorrectedConcreteEncodedObservationSelectionData.runSerializedCostDecision
          instance.serialize =
        true) :
    instance.selectedLeastSerializedCostWitnessCode hDecision <
      instance.codeBound := by

  exact
    ((instance.mem_serializedCostWitnessCodes_iff
      (instance.selectedLeastSerializedCostWitnessCode
        hDecision)).mp
      (instance.selectedLeastSerializedCostWitnessCode_mem
        hDecision)).1

/-- The selected Pareto code lies below the decoded exclusive code bound. -/
theorem selectedLeastSerializedParetoWitnessCode_lt
    (hDecision :
      CorrectedConcreteEncodedObservationSelectionData.runSerializedParetoDecision
          instance.serialize =
        true) :
    instance.selectedLeastSerializedParetoWitnessCode hDecision <
      instance.codeBound := by

  exact
    ((instance.mem_serializedParetoWitnessCodes_iff
      (instance.selectedLeastSerializedParetoWitnessCode
        hDecision)).mp
      (instance.selectedLeastSerializedParetoWitnessCode_mem
        hDecision)).1

/-- Least-code property for the selected ordinary serialized witness. -/
theorem selectedLeastSerializedCostWitnessCode_le
    (hDecision :
      CorrectedConcreteEncodedObservationSelectionData.runSerializedCostDecision
          instance.serialize =
        true)
    {competingCode : Nat}
    (hCompeting :
      CorrectedConcreteEncodedObservationSelectionData.SerializedCostWitness
        instance.serialize
        competingCode) :
    instance.selectedLeastSerializedCostWitnessCode hDecision <=
      competingCode := by

  have hParts :
      competingCode < instance.codeBound ∧
        competingCode ∈ instance.costCertificateCodes :=
    (instance.runSerializedCostCertificateVerifier_serialize_eq_true_iff
      competingCode).mp
      hCompeting

  have hMem :
      competingCode ∈ instance.serializedCostWitnessCodes :=
    (instance.mem_serializedCostWitnessCodes_iff
      competingCode).mpr
      ⟨hParts.1, hCompeting⟩

  exact
    Finset.min'_le
      instance.serializedCostWitnessCodes
      competingCode
      hMem

/-- Least-code property for the selected Pareto serialized witness. -/
theorem selectedLeastSerializedParetoWitnessCode_le
    (hDecision :
      CorrectedConcreteEncodedObservationSelectionData.runSerializedParetoDecision
          instance.serialize =
        true)
    {competingCode : Nat}
    (hCompeting :
      CorrectedConcreteEncodedObservationSelectionData.SerializedParetoWitness
        instance.serialize
        competingCode) :
    instance.selectedLeastSerializedParetoWitnessCode hDecision <=
      competingCode := by

  have hParts :
      competingCode < instance.codeBound ∧
        competingCode ∈ instance.paretoCertificateCodes :=
    (instance.runSerializedParetoCertificateVerifier_serialize_eq_true_iff
      competingCode).mp
      hCompeting

  have hMem :
      competingCode ∈ instance.serializedParetoWitnessCodes :=
    (instance.mem_serializedParetoWitnessCodes_iff
      competingCode).mpr
      ⟨hParts.1, hCompeting⟩

  exact
    Finset.min'_le
      instance.serializedParetoWitnessCodes
      competingCode
      hMem

end LeastSerializedWitnessCodes


section CanonicalSerializedNPStyleWitnesses

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

/-- Canonical least ordinary witness in the common serialized NP-style
membership interface. -/
noncomputable def selectedLeastSerializedCostCanonicalPolynomialWitness
    (hDecision :
      instance.serializedCostNPStyleMembership.decision =
        true) :
    instance.serializedCostNPStyleMembership.CanonicalPolynomialWitness := by

  have hSerializedDecision :
      CorrectedConcreteEncodedObservationSelectionData.runSerializedCostDecision
            instance.serialize =
          true :=
    hDecision

  let code :=
    instance.selectedLeastSerializedCostWitnessCode
      hSerializedDecision

  have hSerializedAccepted :
      CorrectedConcreteEncodedObservationSelectionData.SerializedCostWitness
        instance.serialize
        code :=
    instance.selectedLeastSerializedCostWitnessCode_accepted
      hSerializedDecision

  have hMembershipAccepted :
      instance.serializedCostNPStyleMembership.Witness code :=
    (instance.serializedCostNPStyleMembership_witness_iff
      code).mpr
      hSerializedAccepted

  exact
    {
      code := code

      accepted := hMembershipAccepted

      least := by
        intro competingCode hCompeting

        exact
          instance.selectedLeastSerializedCostWitnessCode_le
            hSerializedDecision
            ((instance.serializedCostNPStyleMembership_witness_iff
              competingCode).mp
              hCompeting)

      certificateSize_le :=
        instance.serializedCostNPStyleMembership.certificateSize_le
          code
          hMembershipAccepted

      verifierWork_le :=
        instance.serializedCostNPStyleMembership.verifierWork_le
          code
          hMembershipAccepted
    }

/-- Canonical least Pareto witness in the common serialized NP-style
membership interface. -/
noncomputable def selectedLeastSerializedParetoCanonicalPolynomialWitness
    (hDecision :
      instance.serializedParetoNPStyleMembership.decision =
        true) :
    instance.serializedParetoNPStyleMembership.CanonicalPolynomialWitness := by

  have hSerializedDecision :
      CorrectedConcreteEncodedObservationSelectionData.runSerializedParetoDecision
            instance.serialize =
          true :=
    hDecision

  let code :=
    instance.selectedLeastSerializedParetoWitnessCode
      hSerializedDecision

  have hSerializedAccepted :
      CorrectedConcreteEncodedObservationSelectionData.SerializedParetoWitness
        instance.serialize
        code :=
    instance.selectedLeastSerializedParetoWitnessCode_accepted
      hSerializedDecision

  have hMembershipAccepted :
      instance.serializedParetoNPStyleMembership.Witness code :=
    (instance.serializedParetoNPStyleMembership_witness_iff
      code).mpr
      hSerializedAccepted

  exact
    {
      code := code

      accepted := hMembershipAccepted

      least := by
        intro competingCode hCompeting

        exact
          instance.selectedLeastSerializedParetoWitnessCode_le
            hSerializedDecision
            ((instance.serializedParetoNPStyleMembership_witness_iff
              competingCode).mp
              hCompeting)

      certificateSize_le :=
        instance.serializedParetoNPStyleMembership.certificateSize_le
          code
          hMembershipAccepted

      verifierWork_le :=
        instance.serializedParetoNPStyleMembership.verifierWork_le
          code
          hMembershipAccepted
    }

/-- The canonical ordinary witness code is the finite `min'` selector. -/
theorem selectedLeastSerializedCostCanonicalPolynomialWitness_code
    (hDecision :
      instance.serializedCostNPStyleMembership.decision =
        true) :
    (instance.selectedLeastSerializedCostCanonicalPolynomialWitness
      hDecision).code =
        instance.selectedLeastSerializedCostWitnessCode
          hDecision := by

  rfl

/-- The canonical Pareto witness code is the finite `min'` selector. -/
theorem selectedLeastSerializedParetoCanonicalPolynomialWitness_code
    (hDecision :
      instance.serializedParetoNPStyleMembership.decision =
        true) :
    (instance.selectedLeastSerializedParetoCanonicalPolynomialWitness
      hDecision).code =
        instance.selectedLeastSerializedParetoWitnessCode
          hDecision := by

  rfl

/-- Complete canonical ordinary/Pareto witness package for one positive
encoded instance. -/
theorem selectedLeastSerializedCanonicalPolynomialWitness_package
    (hCostDecision :
      instance.serializedCostNPStyleMembership.decision =
        true)
    (hParetoDecision :
      instance.serializedParetoNPStyleMembership.decision =
        true) :
    let costCanonical :=
      instance.selectedLeastSerializedCostCanonicalPolynomialWitness
        hCostDecision
    let paretoCanonical :=
      instance.selectedLeastSerializedParetoCanonicalPolynomialWitness
        hParetoDecision
    costCanonical.accepted ∧
      costCanonical.least =
        costCanonical.least ∧
      costCanonical.certificateSize_le ∧
      costCanonical.verifierWork_le ∧
      paretoCanonical.accepted ∧
      paretoCanonical.least =
        paretoCanonical.least ∧
      paretoCanonical.certificateSize_le ∧
      paretoCanonical.verifierWork_le ∧
      costCanonical.code < instance.codeBound ∧
      paretoCanonical.code < instance.codeBound := by

  let costCanonical :=
    instance.selectedLeastSerializedCostCanonicalPolynomialWitness
      hCostDecision

  let paretoCanonical :=
    instance.selectedLeastSerializedParetoCanonicalPolynomialWitness
      hParetoDecision

  exact
    ⟨costCanonical.accepted,
      rfl,
      costCanonical.certificateSize_le,
      costCanonical.verifierWork_le,
      paretoCanonical.accepted,
      rfl,
      paretoCanonical.certificateSize_le,
      paretoCanonical.verifierWork_le,
      by
        change
          instance.selectedLeastSerializedCostWitnessCode
              hCostDecision <
            instance.codeBound

        exact
          instance.selectedLeastSerializedCostWitnessCode_lt
            hCostDecision,
      by
        change
          instance.selectedLeastSerializedParetoWitnessCode
              hParetoDecision <
            instance.codeBound

        exact
          instance.selectedLeastSerializedParetoWitnessCode_lt
            hParetoDecision⟩

end CanonicalSerializedNPStyleWitnesses

end CorrectedConcreteEncodedObservationSelectionInstance


section EncodedSerializedNPStyleCanonicalWitnessFinalPackage

variable {α : Type u}
variable {ι : Type v}
variable {M : Type w}
variable [DecidableEq ι]
variable [Monoid M]
variable (obsFamily : ι → α → M)
variable (f : Nat)
variable (coordinateWeight : ι → Nat)
variable (U : Finset ι)

/-- Final positive-additive canonical serialized NP-style witness package.

The finite `min'` selector on the serialized Pareto witness family agrees
exactly with the previously selected canonical dense Pareto code.  The least
accepted budget is the semantic minimum rank, so all selector layers now share
one canonical minimum-budget, minimum-code polynomial witness. -/
theorem
    correctedConcreteWorkingGrammar_observationSelectionEncodedSerializedNPStyleCanonicalWitness_package
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
    let selectedBudget :=
      table.selectedMinimumSerializedParetoNPStyleBudget
        hTarget
        maxBudget
        hBound
    let hAccepted :=
      table.hasAcceptedParetoScalarBudgetUpTo_of_positiveAdditiveMinimum_le
        hTarget
        maxBudget
        hBound
    let denseCanonicalCode :=
      table.selectedCanonicalDenseMinimumParetoScalarCode
        maxBudget
        hAccepted
    let hDecision :
        membership.decision = true :=
      (membership.decision_eq_true_iff_exists_witness).mpr
        ⟨denseCanonicalCode,
          (instance.serializedParetoNPStyleMembership_witness_iff
            denseCanonicalCode).mpr
            (correctedConcreteWorkingGrammar_observationSelectionEncodedSerializedCertificateVerifier_package
              (z := z)
              obsFamily
              f
              coordinateWeight
              U
              language
              hTarget).1⟩
    let canonical :=
      instance.selectedLeastSerializedParetoCanonicalPolynomialWitness
        hDecision
    selectedBudget = minimumRank ∧
      canonical.accepted ∧
      (∀ competingCode : Nat,
        membership.Witness competingCode →
          canonical.code <= competingCode) ∧
      canonical.code = denseCanonicalCode ∧
      canonical.certificateSize_le ∧
      canonical.verifierWork_le ∧
      canonical.code < 2 ^ U.card ∧
      correctedConcreteDenseCertificateDecode
            U
            canonical.code =
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

  let selectedBudget :=
    table.selectedMinimumSerializedParetoNPStyleBudget
      hTarget
      maxBudget
      hBound

  let hAccepted :=
    table.hasAcceptedParetoScalarBudgetUpTo_of_positiveAdditiveMinimum_le
      hTarget
      maxBudget
      hBound

  let denseCanonicalCode :=
    table.selectedCanonicalDenseMinimumParetoScalarCode
      maxBudget
      hAccepted

  have hDensePackage :=
    correctedConcreteWorkingGrammar_observationSelectionEncodedSerializedCertificateVerifier_package
      (z := z)
      obsFamily
      f
      coordinateWeight
      U
      language
      hTarget

  rcases hDensePackage with
    ⟨hDenseAccepted,
      hDenseCodeBound,
      hDenseLeast,
      hDenseWork,
      hDenseDecode,
      hDensePareto⟩

  have hDenseMembership :
      membership.Witness denseCanonicalCode :=
    (instance.serializedParetoNPStyleMembership_witness_iff
      denseCanonicalCode).mpr
      hDenseAccepted

  let hDecision :
      membership.decision = true :=
    membership.decision_eq_true_iff_exists_witness.mpr
      ⟨denseCanonicalCode, hDenseMembership⟩

  let canonical :=
    instance.selectedLeastSerializedParetoCanonicalPolynomialWitness
      hDecision

  have hCanonicalSerialized :
      CorrectedConcreteEncodedObservationSelectionData.SerializedParetoWitness
        instance.serialize
        canonical.code :=
    (instance.serializedParetoNPStyleMembership_witness_iff
      canonical.code).mp
      canonical.accepted

  have hCanonicalLeDense :
      canonical.code <= denseCanonicalCode :=
    canonical.least
      denseCanonicalCode
      hDenseMembership

  have hDenseLeCanonical :
      denseCanonicalCode <= canonical.code :=
    hDenseLeast
      canonical.code
      hCanonicalSerialized

  have hCodeEq :
      canonical.code = denseCanonicalCode :=
    Nat.le_antisymm
      hCanonicalLeDense
      hDenseLeCanonical

  have hSelectedBudget :
      selectedBudget = minimumRank :=
    table.selectedMinimumSerializedParetoNPStyleBudget_eq_minimumRank
      hTarget
      maxBudget
      hBound

  exact
    ⟨hSelectedBudget,
      canonical.accepted,
      canonical.least,
      hCodeEq,
      canonical.certificateSize_le,
      canonical.verifierWork_le,
      by
        rw [hCodeEq]

        exact hDenseCodeBound,
      by
        rw [hCodeEq]

        exact hDenseDecode,
      hDensePareto⟩

end EncodedSerializedNPStyleCanonicalWitnessFinalPackage

end MCFG
