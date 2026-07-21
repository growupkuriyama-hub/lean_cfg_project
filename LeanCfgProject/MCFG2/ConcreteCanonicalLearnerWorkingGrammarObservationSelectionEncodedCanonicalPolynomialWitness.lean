/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG2.ConcreteCanonicalLearnerWorkingGrammarObservationSelectionEncodedPolynomialWitness

/-!
# ConcreteCanonicalLearnerWorkingGrammarObservationSelectionEncodedCanonicalPolynomialWitness.lean

The preceding file defines the bounded machine-witness relation associated with
an abstract polynomial verifier.  Earlier encoded-selector files already chose
the least accepted dense certificate code at the minimum accepted budget.

This file proves that the same selected dense code is also the canonical
polynomial machine witness.  Thus no second witness-selection convention is
introduced.

A canonical polynomial witness contains

* a bounded machine-accepted code;
* proof that it is no larger than every other machine witness at that budget;
* the certificate-size polynomial bound;
* the work bound for the same verifier machine.

We construct ordinary-cost and Pareto-scalar canonical polynomial witnesses.
The final positive-additive package identifies the witness budget with the
semantic minimum positive-additive observation-selection rank, and retains the
checked decoding and Pareto-optimality of the selected certificate.

This is still an abstract polynomial-machine result.  It does not yet identify
the work counter with the step count of a fixed standard machine model, and
therefore does not claim formal NP membership.  No hardness claim is made.

No target grammar is supplied to any learner.
No `sorry`, `admit`, or `axiom` is used.
-/

namespace MCFG

universe u v w z


namespace CorrectedConcreteEncodedPolynomialVerifier

section GenericCanonicalPolynomialWitness

variable {Question : Nat → Prop}
variable
  (verifier :
    CorrectedConcreteEncodedPolynomialVerifier
      Question)

/-- A least bounded machine witness carrying the resource bounds of the same
polynomial verifier. -/
structure CanonicalPolynomialWitness
    (budget : Nat) where

  code : Nat

  witness :
    verifier.Witness budget code

  least :
    ∀ competingCode : Nat,
      verifier.Witness budget competingCode →
        code <= competingCode

  certificateSize_le :
    verifier.resources.certificateSize code <=
      verifier.resources.certificateCoeff *
        (verifier.resources.inputSize budget + 1) ^
          verifier.resources.certificateDegree

  machineWork_le :
    verifier.machine.work budget code <=
      verifier.resources.verifierCoeff *
        (verifier.resources.inputSize budget +
            verifier.resources.certificateSize code + 1) ^
          verifier.resources.verifierDegree

/-- Construct a canonical polynomial witness from a least machine witness.
The resource bounds are inherited automatically from the verifier package. -/
def canonicalPolynomialWitnessOfLeast
    (budget code : Nat)
    (hWitness :
      verifier.Witness budget code)
    (hLeast :
      ∀ competingCode : Nat,
        verifier.Witness budget competingCode →
          code <= competingCode) :
    verifier.CanonicalPolynomialWitness budget :=
  {
    code := code

    witness := hWitness

    least := hLeast

    certificateSize_le :=
      verifier.resources.certificateSize_le
        budget
        code
        hWitness.1

    machineWork_le := by
      calc
        verifier.machine.work budget code =
            verifier.resources.verifierWork budget code :=
          verifier.machineWork_eq budget code

        _ <=
            verifier.resources.verifierCoeff *
              (verifier.resources.inputSize budget +
                  verifier.resources.certificateSize code + 1) ^
                verifier.resources.verifierDegree :=
          verifier.resources.verifierWork_le
            budget
            code
            hWitness.1
  }

/-- The code of a canonical polynomial witness belongs to the finite witness
set. -/
theorem canonicalPolynomialWitness_mem_witnessCodes
    {budget : Nat}
    (canonical :
      verifier.CanonicalPolynomialWitness budget) :
    canonical.code ∈ verifier.witnessCodes budget := by

  exact
    (verifier.mem_witnessCodes_iff
      budget
      canonical.code).mpr
      canonical.witness

/-- The code of a canonical polynomial witness is below every member of the
finite witness set. -/
theorem canonicalPolynomialWitness_le_of_mem
    {budget competingCode : Nat}
    (canonical :
      verifier.CanonicalPolynomialWitness budget)
    (hCompeting :
      competingCode ∈ verifier.witnessCodes budget) :
    canonical.code <= competingCode := by

  exact
    canonical.least
      competingCode
      ((verifier.mem_witnessCodes_iff
        budget
        competingCode).mp
        hCompeting)

/-- Any two canonical polynomial witnesses for the same verifier and budget
have the same code. -/
theorem canonicalPolynomialWitness_code_unique
    {budget : Nat}
    (first second :
      verifier.CanonicalPolynomialWitness budget) :
    first.code = second.code := by

  exact
    Nat.le_antisymm
      (first.least second.code second.witness)
      (second.least first.code first.witness)

/-- Complete generic canonical-witness package. -/
theorem canonicalPolynomialWitness_package
    {budget : Nat}
    (canonical :
      verifier.CanonicalPolynomialWitness budget) :
    verifier.Witness budget canonical.code ∧
      canonical.code ∈ verifier.witnessCodes budget ∧
      (∀ competingCode : Nat,
        competingCode ∈ verifier.witnessCodes budget →
          canonical.code <= competingCode) ∧
      verifier.resources.certificateSize canonical.code <=
        verifier.resources.certificateCoeff *
          (verifier.resources.inputSize budget + 1) ^
            verifier.resources.certificateDegree ∧
      verifier.machine.work budget canonical.code <=
        verifier.resources.verifierCoeff *
          (verifier.resources.inputSize budget +
              verifier.resources.certificateSize canonical.code + 1) ^
            verifier.resources.verifierDegree := by

  exact
    ⟨canonical.witness,
      verifier.canonicalPolynomialWitness_mem_witnessCodes canonical,
      fun competingCode hCompeting =>
        verifier.canonicalPolynomialWitness_le_of_mem
          canonical
          hCompeting,
      canonical.certificateSize_le,
      canonical.machineWork_le⟩

end GenericCanonicalPolynomialWitness

end CorrectedConcreteEncodedPolynomialVerifier


namespace CorrectedConcreteObservationSelectionDecisionTable

section DenseCostCanonicalPolynomialWitness

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

/-- The previously selected canonical dense ordinary-cost code, regarded as
the canonical polynomial machine witness at the minimum accepted budget. -/
noncomputable def denseCostCanonicalPolynomialWitness
    (verifierWork : Nat → Nat → Nat)
    (verifierCoeff verifierDegree : Nat)
    (hVerifierWork :
      ∀ budget code : Nat,
        code < 2 ^ U.card →
          verifierWork budget code <=
            verifierCoeff *
              (U.card + budget + U.card + 1) ^
                verifierDegree)
    (maxBudget : Nat)
    (hAccepted :
      table.HasAcceptedCostBudgetUpTo maxBudget) :
    let verifier :=
      table.denseCostEncodedPolynomialVerifier
        verifierWork
        verifierCoeff
        verifierDegree
        hVerifierWork
    verifier.CanonicalPolynomialWitness
      (table.selectedMinimumAcceptedCostBudget
        maxBudget
        hAccepted) := by

  let verifier :=
    table.denseCostEncodedPolynomialVerifier
      verifierWork
      verifierCoeff
      verifierDegree
      hVerifierWork

  let budget :=
    table.selectedMinimumAcceptedCostBudget
      maxBudget
      hAccepted

  let selectedCode :=
    table.selectedCanonicalDenseMinimumCostCode
      maxBudget
      hAccepted

  have hCodeLt :
      selectedCode <
        verifier.resources.specification.codeBound budget := by

    simpa [
      verifier,
      budget,
      selectedCode,
      denseCostEncodedPolynomialVerifier,
      CorrectedConcreteEncodedPolynomialVerifier.ofResourceSpecification,
      denseCostVerifierResourceSpecification,
      costDecisionEncodedCertificateSpecification
    ] using
      table.selectedCanonicalDenseMinimumCostCode_lt
        maxBudget
        hAccepted

  have hRun :
      verifier.machine.run budget selectedCode = true := by

    simpa [
      verifier,
      budget,
      selectedCode,
      denseCostEncodedPolynomialVerifier,
      CorrectedConcreteEncodedPolynomialVerifier.ofResourceSpecification,
      denseCostVerifierResourceSpecification,
      costDecisionEncodedCertificateSpecification
    ] using
      table.selectedCanonicalDenseMinimumCostCode_verifies
        maxBudget
        hAccepted

  have hWitness :
      verifier.Witness budget selectedCode :=
    ⟨hCodeLt, hRun⟩

  have hLeast :
      ∀ competingCode : Nat,
        verifier.Witness budget competingCode →
          selectedCode <= competingCode := by

    intro competingCode hCompeting

    have hCompetingVerify :
        table.verifiesDenseCostCertificateCode
              budget
              competingCode =
            true := by

      simpa [
        verifier,
        budget,
        denseCostEncodedPolynomialVerifier,
        CorrectedConcreteEncodedPolynomialVerifier.ofResourceSpecification,
        denseCostVerifierResourceSpecification,
        costDecisionEncodedCertificateSpecification
      ] using hCompeting.2

    have hCompetingMem :
        competingCode ∈
          table.verifiedDenseCostCertificateCodes budget :=
      (table.mem_verifiedDenseCostCertificateCodes_iff
        budget
        competingCode).mpr
        ⟨by
          simpa [
            verifier,
            budget,
            denseCostEncodedPolynomialVerifier,
            CorrectedConcreteEncodedPolynomialVerifier.ofResourceSpecification,
            denseCostVerifierResourceSpecification,
            costDecisionEncodedCertificateSpecification
          ] using hCompeting.1,
          hCompetingVerify⟩

    exact
      table.selectedCanonicalDenseMinimumCostCode_le
        maxBudget
        hAccepted
        hCompetingMem

  exact
    verifier.canonicalPolynomialWitnessOfLeast
      budget
      selectedCode
      hWitness
      hLeast

/-- The ordinary-cost canonical polynomial witness uses exactly the previously
selected canonical dense code. -/
theorem denseCostCanonicalPolynomialWitness_code
    (verifierWork : Nat → Nat → Nat)
    (verifierCoeff verifierDegree : Nat)
    (hVerifierWork :
      ∀ budget code : Nat,
        code < 2 ^ U.card →
          verifierWork budget code <=
            verifierCoeff *
              (U.card + budget + U.card + 1) ^
                verifierDegree)
    (maxBudget : Nat)
    (hAccepted :
      table.HasAcceptedCostBudgetUpTo maxBudget) :
    (table.denseCostCanonicalPolynomialWitness
      verifierWork
      verifierCoeff
      verifierDegree
      hVerifierWork
      maxBudget
      hAccepted).code =
        table.selectedCanonicalDenseMinimumCostCode
          maxBudget
          hAccepted := by

  rfl

/-- Complete ordinary-cost canonical polynomial-witness package. -/
theorem denseCostCanonicalPolynomialWitness_package
    (verifierWork : Nat → Nat → Nat)
    (verifierCoeff verifierDegree : Nat)
    (hVerifierWork :
      ∀ budget code : Nat,
        code < 2 ^ U.card →
          verifierWork budget code <=
            verifierCoeff *
              (U.card + budget + U.card + 1) ^
                verifierDegree)
    (maxBudget : Nat)
    (hAccepted :
      table.HasAcceptedCostBudgetUpTo maxBudget) :
    let verifier :=
      table.denseCostEncodedPolynomialVerifier
        verifierWork
        verifierCoeff
        verifierDegree
        hVerifierWork
    let canonical :=
      table.denseCostCanonicalPolynomialWitness
        verifierWork
        verifierCoeff
        verifierDegree
        hVerifierWork
        maxBudget
        hAccepted
    canonical.code =
        table.selectedCanonicalDenseMinimumCostCode
          maxBudget
          hAccepted ∧
      verifier.Witness
        (table.selectedMinimumAcceptedCostBudget
          maxBudget
          hAccepted)
        canonical.code ∧
      (∀ competingCode : Nat,
        verifier.Witness
            (table.selectedMinimumAcceptedCostBudget
              maxBudget
              hAccepted)
            competingCode →
          canonical.code <= competingCode) ∧
      canonical.code < 2 ^ U.card ∧
      correctedConcreteDenseCertificateDecode
            U
            canonical.code =
        some
          (table.canonicalMinimumCostCertificate
            (correctedConcreteDenseCertificateCode U)
            maxBudget
            hAccepted) ∧
      canonical.machineWork_le =
        canonical.machineWork_le := by

  let canonical :=
    table.denseCostCanonicalPolynomialWitness
      verifierWork
      verifierCoeff
      verifierDegree
      hVerifierWork
      maxBudget
      hAccepted

  exact
    ⟨rfl,
      canonical.witness,
      canonical.least,
      table.selectedCanonicalDenseMinimumCostCode_lt
        maxBudget
        hAccepted,
      table.selectedCanonicalDenseMinimumCostCode_decode
        maxBudget
        hAccepted,
      rfl⟩

end DenseCostCanonicalPolynomialWitness


section DenseParetoCanonicalPolynomialWitness

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

/-- The previously selected canonical dense Pareto-scalar code, regarded as
the canonical polynomial machine witness at the minimum accepted scalar
budget. -/
noncomputable def denseParetoCanonicalPolynomialWitness
    (verifierWork : Nat → Nat → Nat)
    (verifierCoeff verifierDegree : Nat)
    (hVerifierWork :
      ∀ budget code : Nat,
        code < 2 ^ U.card →
          verifierWork budget code <=
            verifierCoeff *
              (U.card + budget + U.card + 1) ^
                verifierDegree)
    (maxBudget : Nat)
    (hAccepted :
      table.HasAcceptedParetoScalarBudgetUpTo maxBudget) :
    let verifier :=
      table.denseParetoEncodedPolynomialVerifier
        verifierWork
        verifierCoeff
        verifierDegree
        hVerifierWork
    verifier.CanonicalPolynomialWitness
      (table.selectedMinimumAcceptedParetoScalarBudget
        maxBudget
        hAccepted) := by

  let verifier :=
    table.denseParetoEncodedPolynomialVerifier
      verifierWork
      verifierCoeff
      verifierDegree
      hVerifierWork

  let budget :=
    table.selectedMinimumAcceptedParetoScalarBudget
      maxBudget
      hAccepted

  let selectedCode :=
    table.selectedCanonicalDenseMinimumParetoScalarCode
      maxBudget
      hAccepted

  have hCodeLt :
      selectedCode <
        verifier.resources.specification.codeBound budget := by

    simpa [
      verifier,
      budget,
      selectedCode,
      denseParetoEncodedPolynomialVerifier,
      CorrectedConcreteEncodedPolynomialVerifier.ofResourceSpecification,
      denseParetoVerifierResourceSpecification,
      paretoDecisionEncodedCertificateSpecification
    ] using
      table.selectedCanonicalDenseMinimumParetoScalarCode_lt
        maxBudget
        hAccepted

  have hRun :
      verifier.machine.run budget selectedCode = true := by

    simpa [
      verifier,
      budget,
      selectedCode,
      denseParetoEncodedPolynomialVerifier,
      CorrectedConcreteEncodedPolynomialVerifier.ofResourceSpecification,
      denseParetoVerifierResourceSpecification,
      paretoDecisionEncodedCertificateSpecification
    ] using
      table.selectedCanonicalDenseMinimumParetoScalarCode_verifies
        maxBudget
        hAccepted

  have hWitness :
      verifier.Witness budget selectedCode :=
    ⟨hCodeLt, hRun⟩

  have hLeast :
      ∀ competingCode : Nat,
        verifier.Witness budget competingCode →
          selectedCode <= competingCode := by

    intro competingCode hCompeting

    have hCompetingVerify :
        table.verifiesDenseParetoScalarCertificateCode
              budget
              competingCode =
            true := by

      simpa [
        verifier,
        budget,
        denseParetoEncodedPolynomialVerifier,
        CorrectedConcreteEncodedPolynomialVerifier.ofResourceSpecification,
        denseParetoVerifierResourceSpecification,
        paretoDecisionEncodedCertificateSpecification
      ] using hCompeting.2

    have hCompetingMem :
        competingCode ∈
          table.verifiedDenseParetoScalarCertificateCodes budget :=
      (table.mem_verifiedDenseParetoScalarCertificateCodes_iff
        budget
        competingCode).mpr
        ⟨by
          simpa [
            verifier,
            budget,
            denseParetoEncodedPolynomialVerifier,
            CorrectedConcreteEncodedPolynomialVerifier.ofResourceSpecification,
            denseParetoVerifierResourceSpecification,
            paretoDecisionEncodedCertificateSpecification
          ] using hCompeting.1,
          hCompetingVerify⟩

    exact
      table.selectedCanonicalDenseMinimumParetoScalarCode_le
        maxBudget
        hAccepted
        hCompetingMem

  exact
    verifier.canonicalPolynomialWitnessOfLeast
      budget
      selectedCode
      hWitness
      hLeast

/-- The Pareto canonical polynomial witness uses exactly the previously
selected canonical dense Pareto code. -/
theorem denseParetoCanonicalPolynomialWitness_code
    (verifierWork : Nat → Nat → Nat)
    (verifierCoeff verifierDegree : Nat)
    (hVerifierWork :
      ∀ budget code : Nat,
        code < 2 ^ U.card →
          verifierWork budget code <=
            verifierCoeff *
              (U.card + budget + U.card + 1) ^
                verifierDegree)
    (maxBudget : Nat)
    (hAccepted :
      table.HasAcceptedParetoScalarBudgetUpTo maxBudget) :
    (table.denseParetoCanonicalPolynomialWitness
      verifierWork
      verifierCoeff
      verifierDegree
      hVerifierWork
      maxBudget
      hAccepted).code =
        table.selectedCanonicalDenseMinimumParetoScalarCode
          maxBudget
          hAccepted := by

  rfl

/-- Complete Pareto canonical polynomial-witness package. -/
theorem denseParetoCanonicalPolynomialWitness_package
    (verifierWork : Nat → Nat → Nat)
    (verifierCoeff verifierDegree : Nat)
    (hVerifierWork :
      ∀ budget code : Nat,
        code < 2 ^ U.card →
          verifierWork budget code <=
            verifierCoeff *
              (U.card + budget + U.card + 1) ^
                verifierDegree)
    (maxBudget : Nat)
    (hAccepted :
      table.HasAcceptedParetoScalarBudgetUpTo maxBudget) :
    let verifier :=
      table.denseParetoEncodedPolynomialVerifier
        verifierWork
        verifierCoeff
        verifierDegree
        hVerifierWork
    let canonical :=
      table.denseParetoCanonicalPolynomialWitness
        verifierWork
        verifierCoeff
        verifierDegree
        hVerifierWork
        maxBudget
        hAccepted
    canonical.code =
        table.selectedCanonicalDenseMinimumParetoScalarCode
          maxBudget
          hAccepted ∧
      verifier.Witness
        (table.selectedMinimumAcceptedParetoScalarBudget
          maxBudget
          hAccepted)
        canonical.code ∧
      (∀ competingCode : Nat,
        verifier.Witness
            (table.selectedMinimumAcceptedParetoScalarBudget
              maxBudget
              hAccepted)
            competingCode →
          canonical.code <= competingCode) ∧
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
        selectionCost
        U
        language
        (table.canonicalMinimumParetoScalarCertificate
          (correctedConcreteDenseCertificateCode U)
          maxBudget
          hAccepted) ∧
      canonical.machineWork_le =
        canonical.machineWork_le := by

  let canonical :=
    table.denseParetoCanonicalPolynomialWitness
      verifierWork
      verifierCoeff
      verifierDegree
      hVerifierWork
      maxBudget
      hAccepted

  have hPareto :
      CorrectedConcreteObservationSelectionParetoOptimal
        (z := z)
        obsFamily
        f
        selectionCost
        U
        language
        (table.canonicalMinimumParetoScalarCertificate
          (correctedConcreteDenseCertificateCode U)
          maxBudget
          hAccepted) :=
    table.canonicalMinimumParetoScalarCertificate_paretoOptimal
      (correctedConcreteDenseCertificateCode U)
      maxBudget
      hAccepted

  exact
    ⟨rfl,
      canonical.witness,
      canonical.least,
      table.selectedCanonicalDenseMinimumParetoScalarCode_lt
        maxBudget
        hAccepted,
      table.selectedCanonicalDenseMinimumParetoScalarCode_decode
        maxBudget
        hAccepted,
      hPareto,
      rfl⟩

end DenseParetoCanonicalPolynomialWitness

end CorrectedConcreteObservationSelectionDecisionTable


section EncodedCanonicalPolynomialWitnessFinalPackage

variable {α : Type u}
variable {ι : Type v}
variable {M : Type w}
variable [DecidableEq ι]
variable [Monoid M]
variable (obsFamily : ι → α → M)
variable (f : Nat)
variable (coordinateWeight : ι → Nat)
variable (U : Finset ι)

/-- Final positive-additive canonical polynomial-witness package.

At the ambient full-interface ceiling, the canonical Pareto machine witness is
the previously selected least dense code at the semantic minimum rank.  It
decodes to a Pareto-optimal observation-selection certificate and carries the
polynomial resource bounds of the same verifier machine. -/
theorem
    correctedConcreteWorkingGrammar_observationSelectionEncodedCanonicalPolynomialWitness_package
    (language : Set (Word α))
    (hTarget :
      language ∈
        StartRootedCorrectedConcreteTargetClass
          (v := z)
          α
          (↥U → M)
          (selectedObservationProduct obsFamily U)
          f)
    (verifierWork : Nat → Nat → Nat)
    (verifierCoeff verifierDegree : Nat)
    (hVerifierWork :
      ∀ budget code : Nat,
        code < 2 ^ U.card →
          verifierWork budget code <=
            verifierCoeff *
              (U.card + budget + U.card + 1) ^
                verifierDegree) :
    let table :=
      correctedConcreteObservationSelectionSemanticDecisionTable
        (z := z)
        obsFamily
        f
        (correctedConcreteObservationSelectionAdditiveCost
          coordinateWeight)
        U
        language
    let maxBudget :=
      correctedConcreteObservationSelectionPositiveAdditiveCost
        coordinateWeight
        U
    let minimumRank :=
      ambientTargetObservationSelectionPositiveAdditiveMinimumCost
        (z := z)
        obsFamily
        f
        coordinateWeight
        U
        hTarget
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
    let verifier :=
      table.denseParetoEncodedPolynomialVerifier
        verifierWork
        verifierCoeff
        verifierDegree
        hVerifierWork
    let canonical :=
      table.denseParetoCanonicalPolynomialWitness
        verifierWork
        verifierCoeff
        verifierDegree
        hVerifierWork
        maxBudget
        hAccepted
    table.selectedMinimumAcceptedParetoScalarBudget
          maxBudget
          hAccepted =
        minimumRank ∧
      verifier.Witness minimumRank canonical.code ∧
      (∀ competingCode : Nat,
        verifier.Witness minimumRank competingCode →
          canonical.code <= competingCode) ∧
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
          hAccepted) ∧
      canonical.machineWork_le =
        canonical.machineWork_le := by

  let table :=
    correctedConcreteObservationSelectionSemanticDecisionTable
      (z := z)
      obsFamily
      f
      (correctedConcreteObservationSelectionAdditiveCost
        coordinateWeight)
      U
      language

  let maxBudget :=
    correctedConcreteObservationSelectionPositiveAdditiveCost
      coordinateWeight
      U

  let minimumRank :=
    ambientTargetObservationSelectionPositiveAdditiveMinimumCost
      (z := z)
      obsFamily
      f
      coordinateWeight
      U
      hTarget

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

  let verifier :=
    table.denseParetoEncodedPolynomialVerifier
      verifierWork
      verifierCoeff
      verifierDegree
      hVerifierWork

  let canonical :=
    table.denseParetoCanonicalPolynomialWitness
      verifierWork
      verifierCoeff
      verifierDegree
      hVerifierWork
      maxBudget
      hAccepted

  have hBudgetEq :
      table.selectedMinimumAcceptedParetoScalarBudget
            maxBudget
            hAccepted =
        minimumRank :=
    table.selectedMinimumAcceptedParetoScalarBudget_eq_positiveAdditiveMinimum
      hTarget
      maxBudget
      hBound

  have hWitnessAtMinimum :
      verifier.Witness minimumRank canonical.code := by

    rw [← hBudgetEq]

    exact canonical.witness

  have hLeastAtMinimum :
      ∀ competingCode : Nat,
        verifier.Witness minimumRank competingCode →
          canonical.code <= competingCode := by

    intro competingCode hCompeting

    rw [← hBudgetEq] at hCompeting

    exact
      canonical.least
        competingCode
        hCompeting

  exact
    ⟨hBudgetEq,
      hWitnessAtMinimum,
      hLeastAtMinimum,
      table.selectedCanonicalDenseMinimumParetoScalarCode_lt
        maxBudget
        hAccepted,
      table.selectedCanonicalDenseMinimumParetoScalarCode_decode
        maxBudget
        hAccepted,
      table.canonicalMinimumParetoScalarCertificate_paretoOptimal
        (correctedConcreteDenseCertificateCode U)
        maxBudget
        hAccepted,
      rfl⟩

end EncodedCanonicalPolynomialWitnessFinalPackage

end MCFG
