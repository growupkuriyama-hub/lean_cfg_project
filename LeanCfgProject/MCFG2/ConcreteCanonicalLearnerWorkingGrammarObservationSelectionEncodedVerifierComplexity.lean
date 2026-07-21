/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG.ConcreteCanonicalLearnerWorkingGrammarObservationSelectionEncodedCertificateSpecification

/-!
# ConcreteCanonicalLearnerWorkingGrammarObservationSelectionEncodedVerifierComplexity.lean

The preceding file isolates the logical encoded-certificate specification.
This file adds an explicit verifier-resource interface without pretending that
a machine-model complexity theorem has already been proved.

A resource specification records

* an input-size measure;
* a certificate-size measure;
* a verifier-work measure;
* polynomial envelopes for certificate size and verifier work;
* proofs that every bounded certificate satisfies those envelopes.

The generic theorem combines logical soundness/completeness with these resource
bounds.  We then specialize it to the dense observation-selection code, whose
certificate is a bit mask of exact length `U.card`.  Thus the certificate-size
bound is discharged internally; only the concrete verifier-work bound remains
as an explicit obligation.

This is the correct pre-NP interface:

```text
logical certificate correctness
+ polynomial certificate-size envelope
+ polynomial verifier-work envelope.
```

It is not yet a formal NP-membership theorem.  Such a theorem still requires a
chosen machine model, a concrete encoded input, and a proof that the actual
Boolean verifier realizes the supplied work measure.  No NP-hardness or
NP-completeness claim is made.

No target grammar is supplied to any learner.
No `sorry`, `admit`, or `axiom` is used.
-/

namespace MCFG

universe u v w z


section GenericEncodedVerifierResourceSpecification

/-- Resource-bounded encoded certificate specification.

The polynomial envelopes are represented explicitly as

```text
certificateCoeff * (inputSize + 1) ^ certificateDegree
verifierCoeff *
  (inputSize + certificateSize + 1) ^ verifierDegree.
```

This record states the bounds; it does not choose a machine model. -/
structure CorrectedConcreteEncodedVerifierResourceSpecification
    (Question : Nat → Prop) where

  specification :
    CorrectedConcreteEncodedCertificateSpecification Question

  inputSize : Nat → Nat

  certificateSize : Nat → Nat

  verifierWork : Nat → Nat → Nat

  certificateCoeff : Nat

  certificateDegree : Nat

  verifierCoeff : Nat

  verifierDegree : Nat

  certificateSize_le :
    ∀ budget code : Nat,
      code < specification.codeBound budget →
        certificateSize code <=
          certificateCoeff *
            (inputSize budget + 1) ^ certificateDegree

  verifierWork_le :
    ∀ budget code : Nat,
      code < specification.codeBound budget →
        verifierWork budget code <=
          verifierCoeff *
            (inputSize budget + certificateSize code + 1) ^
              verifierDegree

namespace CorrectedConcreteEncodedVerifierResourceSpecification

variable {Question : Nat → Prop}
variable
  (resources :
    CorrectedConcreteEncodedVerifierResourceSpecification
      Question)

/-- Every positive instance has one accepted certificate satisfying both
declared polynomial resource envelopes. -/
theorem exists_verified_code_with_resource_bounds
    {budget : Nat}
    (hQuestion : Question budget) :
    ∃ code : Nat,
      code < resources.specification.codeBound budget ∧
        resources.specification.verify budget code = true ∧
        resources.certificateSize code <=
          resources.certificateCoeff *
            (resources.inputSize budget + 1) ^
              resources.certificateDegree ∧
        resources.verifierWork budget code <=
          resources.verifierCoeff *
            (resources.inputSize budget +
                resources.certificateSize code + 1) ^
              resources.verifierDegree := by

  rcases
      resources.specification.exists_bounded_verified_code
        hQuestion with
    ⟨code, hCode, hVerify⟩

  exact
    ⟨code,
      hCode,
      hVerify,
      resources.certificateSize_le budget code hCode,
      resources.verifierWork_le budget code hCode⟩

/-- Every bounded accepted code remains logically sound, independently of its
resource accounting. -/
theorem question_of_verified_code
    {budget code : Nat}
    (hCode :
      code < resources.specification.codeBound budget)
    (hVerify :
      resources.specification.verify budget code = true) :
    Question budget := by

  exact
    resources.specification.question_of_bounded_verified_code
      hCode
      hVerify

/-- Every code in the declared universe satisfies the certificate-size
envelope. -/
theorem certificate_resource_bound
    {budget code : Nat}
    (hCode :
      code < resources.specification.codeBound budget) :
    resources.certificateSize code <=
      resources.certificateCoeff *
        (resources.inputSize budget + 1) ^
          resources.certificateDegree := by

  exact
    resources.certificateSize_le budget code hCode

/-- Every code in the declared universe satisfies the verifier-work envelope. -/
theorem verifier_resource_bound
    {budget code : Nat}
    (hCode :
      code < resources.specification.codeBound budget) :
    resources.verifierWork budget code <=
      resources.verifierCoeff *
        (resources.inputSize budget +
            resources.certificateSize code + 1) ^
          resources.verifierDegree := by

  exact
    resources.verifierWork_le budget code hCode

end CorrectedConcreteEncodedVerifierResourceSpecification

end GenericEncodedVerifierResourceSpecification


namespace CorrectedConcreteObservationSelectionDecisionTable

section DenseCostVerifierResources

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

/-- Dense ordinary-cost verifier resource specification.

The encoded input-size measure is `U.card + budget`, and every certificate is
accounted for as a bit mask of length `U.card`.  Hence the certificate-size
polynomial is fixed internally to degree one and coefficient one.

The only external obligation is a concrete work bound for the supplied
verifier-work accounting function. -/
noncomputable def denseCostVerifierResourceSpecification
    (verifierWork : Nat → Nat → Nat)
    (verifierCoeff verifierDegree : Nat)
    (hVerifierWork :
      ∀ budget code : Nat,
        code < 2 ^ U.card →
          verifierWork budget code <=
            verifierCoeff *
              (U.card + budget + U.card + 1) ^
                verifierDegree) :
    CorrectedConcreteEncodedVerifierResourceSpecification
      (fun budget =>
        table.costFeasibleDecision budget = true) :=
  {
    specification :=
      table.costDecisionEncodedCertificateSpecification

    inputSize :=
      fun budget => U.card + budget

    certificateSize :=
      fun _ => U.card

    verifierWork :=
      verifierWork

    certificateCoeff :=
      1

    certificateDegree :=
      1

    verifierCoeff :=
      verifierCoeff

    verifierDegree :=
      verifierDegree

    certificateSize_le := by
      intro budget code hCode

      have hBasic :
          U.card <= U.card + (budget + 1) :=
        Nat.le_add_right U.card (budget + 1)

      simpa [Nat.add_assoc] using hBasic

    verifierWork_le := by
      intro budget code hCode

      apply hVerifierWork budget code

      simpa [
        costDecisionEncodedCertificateSpecification
      ] using hCode
  }

/-- The dense ordinary-cost resource specification uses the exact code bound
`2 ^ U.card`. -/
theorem denseCostVerifierResourceSpecification_codeBound
    (verifierWork : Nat → Nat → Nat)
    (verifierCoeff verifierDegree : Nat)
    (hVerifierWork :
      ∀ budget code : Nat,
        code < 2 ^ U.card →
          verifierWork budget code <=
            verifierCoeff *
              (U.card + budget + U.card + 1) ^
                verifierDegree)
    (budget : Nat) :
    (table.denseCostVerifierResourceSpecification
        verifierWork
        verifierCoeff
        verifierDegree
        hVerifierWork).specification.codeBound budget =
      2 ^ U.card := by

  rfl

/-- Every positive ordinary-cost decision has an accepted dense code with
linear certificate length and the supplied polynomial work bound. -/
theorem denseCostVerifier_exists_bounded_certificate
    (verifierWork : Nat → Nat → Nat)
    (verifierCoeff verifierDegree : Nat)
    (hVerifierWork :
      ∀ budget code : Nat,
        code < 2 ^ U.card →
          verifierWork budget code <=
            verifierCoeff *
              (U.card + budget + U.card + 1) ^
                verifierDegree)
    {budget : Nat}
    (hDecision :
      table.costFeasibleDecision budget = true) :
    ∃ code : Nat,
      code < 2 ^ U.card ∧
        table.verifiesDenseCostCertificateCode budget code =
          true ∧
        U.card <= U.card + budget + 1 ∧
        verifierWork budget code <=
          verifierCoeff *
            (U.card + budget + U.card + 1) ^
              verifierDegree := by

  let resources :=
    table.denseCostVerifierResourceSpecification
      verifierWork
      verifierCoeff
      verifierDegree
      hVerifierWork

  rcases
      resources.exists_verified_code_with_resource_bounds
        hDecision with
    ⟨code, hCode, hVerify, hCertificateSize, hWork⟩

  exact
    ⟨code,
      by
        simpa [
          resources,
          denseCostVerifierResourceSpecification,
          costDecisionEncodedCertificateSpecification
        ] using hCode,
      by
        simpa [
          resources,
          denseCostVerifierResourceSpecification,
          costDecisionEncodedCertificateSpecification
        ] using hVerify,
      by
        simpa [
          resources,
          denseCostVerifierResourceSpecification,
          Nat.add_assoc
        ] using hCertificateSize,
      by
        simpa [
          resources,
          denseCostVerifierResourceSpecification,
          Nat.add_assoc
        ] using hWork⟩

end DenseCostVerifierResources


section DenseParetoVerifierResources

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

/-- Dense Pareto-scalar verifier resource specification. -/
noncomputable def denseParetoVerifierResourceSpecification
    (verifierWork : Nat → Nat → Nat)
    (verifierCoeff verifierDegree : Nat)
    (hVerifierWork :
      ∀ budget code : Nat,
        code < 2 ^ U.card →
          verifierWork budget code <=
            verifierCoeff *
              (U.card + budget + U.card + 1) ^
                verifierDegree) :
    CorrectedConcreteEncodedVerifierResourceSpecification
      (fun budget =>
        table.paretoScalarFeasibleDecision budget = true) :=
  {
    specification :=
      table.paretoDecisionEncodedCertificateSpecification

    inputSize :=
      fun budget => U.card + budget

    certificateSize :=
      fun _ => U.card

    verifierWork :=
      verifierWork

    certificateCoeff :=
      1

    certificateDegree :=
      1

    verifierCoeff :=
      verifierCoeff

    verifierDegree :=
      verifierDegree

    certificateSize_le := by
      intro budget code hCode

      have hBasic :
          U.card <= U.card + (budget + 1) :=
        Nat.le_add_right U.card (budget + 1)

      simpa [Nat.add_assoc] using hBasic

    verifierWork_le := by
      intro budget code hCode

      apply hVerifierWork budget code

      simpa [
        paretoDecisionEncodedCertificateSpecification
      ] using hCode
  }

/-- Every positive Pareto-scalar decision has an accepted dense code with
linear certificate length and the supplied polynomial work bound. -/
theorem denseParetoVerifier_exists_bounded_certificate
    (verifierWork : Nat → Nat → Nat)
    (verifierCoeff verifierDegree : Nat)
    (hVerifierWork :
      ∀ budget code : Nat,
        code < 2 ^ U.card →
          verifierWork budget code <=
            verifierCoeff *
              (U.card + budget + U.card + 1) ^
                verifierDegree)
    {budget : Nat}
    (hDecision :
      table.paretoScalarFeasibleDecision budget = true) :
    ∃ code : Nat,
      code < 2 ^ U.card ∧
        table.verifiesDenseParetoScalarCertificateCode
              budget
              code =
          true ∧
        U.card <= U.card + budget + 1 ∧
        verifierWork budget code <=
          verifierCoeff *
            (U.card + budget + U.card + 1) ^
              verifierDegree := by

  let resources :=
    table.denseParetoVerifierResourceSpecification
      verifierWork
      verifierCoeff
      verifierDegree
      hVerifierWork

  rcases
      resources.exists_verified_code_with_resource_bounds
        hDecision with
    ⟨code, hCode, hVerify, hCertificateSize, hWork⟩

  exact
    ⟨code,
      by
        simpa [
          resources,
          denseParetoVerifierResourceSpecification,
          paretoDecisionEncodedCertificateSpecification
        ] using hCode,
      by
        simpa [
          resources,
          denseParetoVerifierResourceSpecification,
          paretoDecisionEncodedCertificateSpecification
        ] using hVerify,
      by
        simpa [
          resources,
          denseParetoVerifierResourceSpecification,
          Nat.add_assoc
        ] using hCertificateSize,
      by
        simpa [
          resources,
          denseParetoVerifierResourceSpecification,
          Nat.add_assoc
        ] using hWork⟩

end DenseParetoVerifierResources

end CorrectedConcreteObservationSelectionDecisionTable


section EncodedVerifierComplexityFinalPackage

variable {α : Type u}
variable {ι : Type v}
variable {M : Type w}
variable [DecidableEq ι]
variable [Monoid M]
variable (obsFamily : ι → α → M)
variable (f : Nat)
variable (coordinateWeight : ι → Nat)
variable (U : Finset ι)

/-- Final positive-additive verifier-resource package.

Given any concrete verifier-work measure satisfying the displayed polynomial
envelope on dense codes, the exact semantic minimum rank has a checked Pareto
certificate with bit-mask length `U.card` and verifier work within that
envelope. -/
theorem
    correctedConcreteWorkingGrammar_observationSelectionEncodedVerifierComplexity_package
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
    let minimumRank :=
      ambientTargetObservationSelectionPositiveAdditiveMinimumCost
        (z := z)
        obsFamily
        f
        coordinateWeight
        U
        hTarget
    ∃ code : Nat,
      code < 2 ^ U.card ∧
        table.verifiesDenseParetoScalarCertificateCode
              minimumRank
              code =
          true ∧
        U.card <= U.card + minimumRank + 1 ∧
        verifierWork minimumRank code <=
          verifierCoeff *
            (U.card + minimumRank + U.card + 1) ^
              verifierDegree := by

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

  have hDecision :
      table.paretoScalarFeasibleDecision minimumRank = true := by

    exact
      (table.positiveAdditiveParetoScalarDecision_eq_true_iff_minimumRank_le
        hTarget
        minimumRank).mpr
        (Nat.le_refl minimumRank)

  exact
    table.denseParetoVerifier_exists_bounded_certificate
      verifierWork
      verifierCoeff
      verifierDegree
      hVerifierWork
      hDecision

end EncodedVerifierComplexityFinalPackage

end MCFG
