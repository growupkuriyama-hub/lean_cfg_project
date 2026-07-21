/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG2.ConcreteCanonicalLearnerWorkingGrammarObservationSelectionEncodedVerifierComplexity

/-!
# ConcreteCanonicalLearnerWorkingGrammarObservationSelectionEncodedPolynomialVerifier.lean

The preceding file separates logical certificate correctness from explicit
certificate-size and verifier-work envelopes.  This file attaches those data to
one abstract verifier machine.

An encoded verifier machine records

* a Boolean execution function `run`;
* a natural-valued work counter;
* exact agreement of `run` with the logical Boolean verifier.

A polynomial verifier package then combines that machine with the resource
specification from the preceding file and identifies the machine work counter
with the work quantity occurring in the polynomial bound.

Consequently, every positive instance has one bounded certificate code such
that

```text
the machine accepts the code;
the certificate-size polynomial bound holds;
the same machine's work counter satisfies the verifier polynomial bound.
```

We instantiate this interface for ordinary cost feasibility, Pareto-scalar
feasibility, and the semantic positive-additive minimum-rank threshold.

This is the final abstract polynomial-verifier interface before choosing a
specific standard machine model.  It is deliberately not called an
NP-membership theorem: the remaining obligation is to interpret `work` as the
step count of a chosen encoded machine model.  No NP-hardness or
NP-completeness claim is made.

No target grammar is supplied to any learner.
No `sorry`, `admit`, or `axiom` is used.
-/

namespace MCFG

universe u v w z


section GenericEncodedVerifierMachine

/-- Abstract execution machine for a Boolean encoded verifier. -/
structure CorrectedConcreteEncodedVerifierMachine
    (verify : Nat → Nat → Bool) where

  run : Nat → Nat → Bool

  work : Nat → Nat → Nat

  run_eq_verify :
    ∀ budget code : Nat,
      run budget code = verify budget code

/-- A logical encoded certificate problem, its polynomial resource
specification, and one verifier machine realizing exactly that Boolean
verifier and work accounting. -/
structure CorrectedConcreteEncodedPolynomialVerifier
    (Question : Nat → Prop) where

  resources :
    CorrectedConcreteEncodedVerifierResourceSpecification
      Question

  machine :
    CorrectedConcreteEncodedVerifierMachine
      resources.specification.verify

  machineWork_eq :
    ∀ budget code : Nat,
      machine.work budget code =
        resources.verifierWork budget code

namespace CorrectedConcreteEncodedPolynomialVerifier

variable {Question : Nat → Prop}
variable
  (verifier :
    CorrectedConcreteEncodedPolynomialVerifier
      Question)

/-- Every positive instance has one machine-accepted code satisfying the
certificate-size and machine-work polynomial bounds. -/
theorem exists_machine_accepted_code_with_polynomial_bounds
    {budget : Nat}
    (hQuestion : Question budget) :
    ∃ code : Nat,
      code < verifier.resources.specification.codeBound budget ∧
        verifier.machine.run budget code = true ∧
        verifier.resources.certificateSize code <=
          verifier.resources.certificateCoeff *
            (verifier.resources.inputSize budget + 1) ^
              verifier.resources.certificateDegree ∧
        verifier.machine.work budget code <=
          verifier.resources.verifierCoeff *
            (verifier.resources.inputSize budget +
                verifier.resources.certificateSize code + 1) ^
              verifier.resources.verifierDegree := by

  rcases
      verifier.resources.exists_verified_code_with_resource_bounds
        hQuestion with
    ⟨code, hCode, hVerify, hCertificateSize, hWork⟩

  refine
    ⟨code,
      hCode,
      ?_,
      hCertificateSize,
      ?_⟩

  · calc
      verifier.machine.run budget code =
          verifier.resources.specification.verify budget code :=
        verifier.machine.run_eq_verify budget code

      _ = true :=
        hVerify

  · calc
      verifier.machine.work budget code =
          verifier.resources.verifierWork budget code :=
        verifier.machineWork_eq budget code

      _ <=
          verifier.resources.verifierCoeff *
            (verifier.resources.inputSize budget +
                verifier.resources.certificateSize code + 1) ^
              verifier.resources.verifierDegree :=
        hWork

/-- Every bounded machine-accepted certificate is logically sound. -/
theorem question_of_machine_accepted_code
    {budget code : Nat}
    (hCode :
      code < verifier.resources.specification.codeBound budget)
    (hRun :
      verifier.machine.run budget code = true) :
    Question budget := by

  have hVerify :
      verifier.resources.specification.verify budget code = true := by

    calc
      verifier.resources.specification.verify budget code =
          verifier.machine.run budget code :=
        (verifier.machine.run_eq_verify budget code).symm

      _ = true :=
        hRun

  exact
    verifier.resources.question_of_verified_code
      hCode
      hVerify

/-- Canonical abstract machine attached to any resource specification: it runs
the logical Boolean verifier itself and uses the declared verifier-work
quantity as its work counter. -/
def ofResourceSpecification
    (resources :
      CorrectedConcreteEncodedVerifierResourceSpecification
        Question) :
    CorrectedConcreteEncodedPolynomialVerifier
      Question :=
  {
    resources := resources

    machine :=
      {
        run := resources.specification.verify
        work := resources.verifierWork
        run_eq_verify := by
          intro budget code
          rfl
      }

    machineWork_eq := by
      intro budget code
      rfl
  }

/-- The canonical machine executes exactly the logical Boolean verifier. -/
theorem ofResourceSpecification_run
    (resources :
      CorrectedConcreteEncodedVerifierResourceSpecification
        Question)
    (budget code : Nat) :
    (ofResourceSpecification resources).machine.run budget code =
      resources.specification.verify budget code := by

  rfl

/-- The canonical machine uses exactly the declared work counter. -/
theorem ofResourceSpecification_work
    (resources :
      CorrectedConcreteEncodedVerifierResourceSpecification
        Question)
    (budget code : Nat) :
    (ofResourceSpecification resources).machine.work budget code =
      resources.verifierWork budget code := by

  rfl

end CorrectedConcreteEncodedPolynomialVerifier

end GenericEncodedVerifierMachine


namespace CorrectedConcreteObservationSelectionDecisionTable

section DenseCostPolynomialVerifier

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

/-- Abstract polynomial verifier for dense ordinary-cost certificates. -/
noncomputable def denseCostEncodedPolynomialVerifier
    (verifierWork : Nat → Nat → Nat)
    (verifierCoeff verifierDegree : Nat)
    (hVerifierWork :
      ∀ budget code : Nat,
        code < 2 ^ U.card →
          verifierWork budget code <=
            verifierCoeff *
              (U.card + budget + U.card + 1) ^
                verifierDegree) :
    CorrectedConcreteEncodedPolynomialVerifier
      (fun budget =>
        table.costFeasibleDecision budget = true) :=
  CorrectedConcreteEncodedPolynomialVerifier.ofResourceSpecification
    (table.denseCostVerifierResourceSpecification
      verifierWork
      verifierCoeff
      verifierDegree
      hVerifierWork)

/-- Every positive ordinary-cost decision has a machine-accepted dense code
with the declared polynomial bounds. -/
theorem denseCostEncodedPolynomialVerifier_complete
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
        (table.denseCostEncodedPolynomialVerifier
          verifierWork
          verifierCoeff
          verifierDegree
          hVerifierWork).machine.run budget code =
            true ∧
        U.card <= U.card + budget + 1 ∧
        (table.denseCostEncodedPolynomialVerifier
          verifierWork
          verifierCoeff
          verifierDegree
          hVerifierWork).machine.work budget code <=
            verifierCoeff *
              (U.card + budget + U.card + 1) ^
                verifierDegree := by

  let verifier :=
    table.denseCostEncodedPolynomialVerifier
      verifierWork
      verifierCoeff
      verifierDegree
      hVerifierWork

  rcases
      verifier.exists_machine_accepted_code_with_polynomial_bounds
        hDecision with
    ⟨code, hCode, hRun, hCertificateSize, hWork⟩

  exact
    ⟨code,
      by
        simpa [
          verifier,
          denseCostEncodedPolynomialVerifier,
          CorrectedConcreteEncodedPolynomialVerifier.ofResourceSpecification,
          denseCostVerifierResourceSpecification,
          costDecisionEncodedCertificateSpecification
        ] using hCode,
      hRun,
      by
        simpa [
          verifier,
          denseCostEncodedPolynomialVerifier,
          CorrectedConcreteEncodedPolynomialVerifier.ofResourceSpecification,
          denseCostVerifierResourceSpecification,
          Nat.add_assoc
        ] using hCertificateSize,
      by
        simpa [
          verifier,
          denseCostEncodedPolynomialVerifier,
          CorrectedConcreteEncodedPolynomialVerifier.ofResourceSpecification,
          denseCostVerifierResourceSpecification,
          Nat.add_assoc
        ] using hWork⟩

end DenseCostPolynomialVerifier


section DenseParetoPolynomialVerifier

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

/-- Abstract polynomial verifier for dense Pareto-scalar certificates. -/
noncomputable def denseParetoEncodedPolynomialVerifier
    (verifierWork : Nat → Nat → Nat)
    (verifierCoeff verifierDegree : Nat)
    (hVerifierWork :
      ∀ budget code : Nat,
        code < 2 ^ U.card →
          verifierWork budget code <=
            verifierCoeff *
              (U.card + budget + U.card + 1) ^
                verifierDegree) :
    CorrectedConcreteEncodedPolynomialVerifier
      (fun budget =>
        table.paretoScalarFeasibleDecision budget = true) :=
  CorrectedConcreteEncodedPolynomialVerifier.ofResourceSpecification
    (table.denseParetoVerifierResourceSpecification
      verifierWork
      verifierCoeff
      verifierDegree
      hVerifierWork)

/-- Every positive Pareto-scalar decision has a machine-accepted dense code
with the declared polynomial bounds. -/
theorem denseParetoEncodedPolynomialVerifier_complete
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
        (table.denseParetoEncodedPolynomialVerifier
          verifierWork
          verifierCoeff
          verifierDegree
          hVerifierWork).machine.run budget code =
            true ∧
        U.card <= U.card + budget + 1 ∧
        (table.denseParetoEncodedPolynomialVerifier
          verifierWork
          verifierCoeff
          verifierDegree
          hVerifierWork).machine.work budget code <=
            verifierCoeff *
              (U.card + budget + U.card + 1) ^
                verifierDegree := by

  let verifier :=
    table.denseParetoEncodedPolynomialVerifier
      verifierWork
      verifierCoeff
      verifierDegree
      hVerifierWork

  rcases
      verifier.exists_machine_accepted_code_with_polynomial_bounds
        hDecision with
    ⟨code, hCode, hRun, hCertificateSize, hWork⟩

  exact
    ⟨code,
      by
        simpa [
          verifier,
          denseParetoEncodedPolynomialVerifier,
          CorrectedConcreteEncodedPolynomialVerifier.ofResourceSpecification,
          denseParetoVerifierResourceSpecification,
          paretoDecisionEncodedCertificateSpecification
        ] using hCode,
      hRun,
      by
        simpa [
          verifier,
          denseParetoEncodedPolynomialVerifier,
          CorrectedConcreteEncodedPolynomialVerifier.ofResourceSpecification,
          denseParetoVerifierResourceSpecification,
          Nat.add_assoc
        ] using hCertificateSize,
      by
        simpa [
          verifier,
          denseParetoEncodedPolynomialVerifier,
          CorrectedConcreteEncodedPolynomialVerifier.ofResourceSpecification,
          denseParetoVerifierResourceSpecification,
          Nat.add_assoc
        ] using hWork⟩

end DenseParetoPolynomialVerifier


section PositiveAdditiveRankPolynomialVerifier

variable {α : Type u}
variable {ι : Type v}
variable {M : Type w}
variable [DecidableEq ι]
variable [Monoid M]
variable {obsFamily : ι → α → M}
variable {f : Nat}
variable {coordinateWeight : ι → Nat}
variable {U : Finset ι}
variable {language : Set (Word α)}
variable
  (table :
    CorrectedConcreteObservationSelectionDecisionTable
      (z := z)
      obsFamily
      f
      (correctedConcreteObservationSelectionAdditiveCost
        coordinateWeight)
      U
      language)
variable
  (hTarget :
    language ∈
      StartRootedCorrectedConcreteTargetClass
        (v := z)
        α
        (↥U → M)
        (selectedObservationProduct obsFamily U)
        f)

/-- Resource specification for the semantic positive-additive minimum-rank
threshold, using the dense Pareto verifier. -/
noncomputable def positiveAdditiveRankVerifierResourceSpecification
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
        ambientTargetObservationSelectionPositiveAdditiveMinimumCost
              (z := z)
              obsFamily
              f
              coordinateWeight
              U
              hTarget <=
            budget) :=
  {
    specification :=
      table.positiveAdditiveParetoRankEncodedCertificateSpecification
        hTarget

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
        positiveAdditiveParetoRankEncodedCertificateSpecification
      ] using hCode
  }

/-- Abstract polynomial verifier for the semantic positive-additive
minimum-rank threshold. -/
noncomputable def positiveAdditiveRankEncodedPolynomialVerifier
    (verifierWork : Nat → Nat → Nat)
    (verifierCoeff verifierDegree : Nat)
    (hVerifierWork :
      ∀ budget code : Nat,
        code < 2 ^ U.card →
          verifierWork budget code <=
            verifierCoeff *
              (U.card + budget + U.card + 1) ^
                verifierDegree) :
    CorrectedConcreteEncodedPolynomialVerifier
      (fun budget =>
        ambientTargetObservationSelectionPositiveAdditiveMinimumCost
              (z := z)
              obsFamily
              f
              coordinateWeight
              U
              hTarget <=
            budget) :=
  CorrectedConcreteEncodedPolynomialVerifier.ofResourceSpecification
    (table.positiveAdditiveRankVerifierResourceSpecification
      hTarget
      verifierWork
      verifierCoeff
      verifierDegree
      hVerifierWork)

end PositiveAdditiveRankPolynomialVerifier

end CorrectedConcreteObservationSelectionDecisionTable


section EncodedPolynomialVerifierFinalPackage

variable {α : Type u}
variable {ι : Type v}
variable {M : Type w}
variable [DecidableEq ι]
variable [Monoid M]
variable (obsFamily : ι → α → M)
variable (f : Nat)
variable (coordinateWeight : ι → Nat)
variable (U : Finset ι)

/-- Final positive-additive abstract polynomial-verifier package.

For any supplied verifier-work accounting satisfying the displayed polynomial
bound, we construct one verifier machine for the semantic minimum-rank
threshold.  At the exact minimum rank, that same machine accepts a dense code
below `2 ^ U.card`, with linear certificate length and the declared polynomial
machine-work bound. -/
theorem
    correctedConcreteWorkingGrammar_observationSelectionEncodedPolynomialVerifier_package
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
    let verifier :=
      table.positiveAdditiveRankEncodedPolynomialVerifier
        hTarget
        verifierWork
        verifierCoeff
        verifierDegree
        hVerifierWork
    ∃ code : Nat,
      code < 2 ^ U.card ∧
        verifier.machine.run minimumRank code = true ∧
        U.card <= U.card + minimumRank + 1 ∧
        verifier.machine.work minimumRank code <=
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

  let verifier :=
    table.positiveAdditiveRankEncodedPolynomialVerifier
      hTarget
      verifierWork
      verifierCoeff
      verifierDegree
      hVerifierWork

  have hQuestion :
      ambientTargetObservationSelectionPositiveAdditiveMinimumCost
            (z := z)
            obsFamily
            f
            coordinateWeight
            U
            hTarget <=
          minimumRank :=
    Nat.le_refl minimumRank

  rcases
      verifier.exists_machine_accepted_code_with_polynomial_bounds
        hQuestion with
    ⟨code, hCode, hRun, hCertificateSize, hWork⟩

  exact
    ⟨code,
      by
        simpa [
          verifier,
          CorrectedConcreteObservationSelectionDecisionTable.positiveAdditiveRankEncodedPolynomialVerifier,
          CorrectedConcreteObservationSelectionDecisionTable.positiveAdditiveRankVerifierResourceSpecification,
          CorrectedConcreteEncodedPolynomialVerifier.ofResourceSpecification,
          CorrectedConcreteObservationSelectionDecisionTable.positiveAdditiveParetoRankEncodedCertificateSpecification
        ] using hCode,
      hRun,
      by
        simpa [
          verifier,
          CorrectedConcreteObservationSelectionDecisionTable.positiveAdditiveRankEncodedPolynomialVerifier,
          CorrectedConcreteObservationSelectionDecisionTable.positiveAdditiveRankVerifierResourceSpecification,
          CorrectedConcreteEncodedPolynomialVerifier.ofResourceSpecification,
          Nat.add_assoc
        ] using hCertificateSize,
      by
        simpa [
          verifier,
          CorrectedConcreteObservationSelectionDecisionTable.positiveAdditiveRankEncodedPolynomialVerifier,
          CorrectedConcreteObservationSelectionDecisionTable.positiveAdditiveRankVerifierResourceSpecification,
          CorrectedConcreteEncodedPolynomialVerifier.ofResourceSpecification,
          Nat.add_assoc
        ] using hWork⟩

end EncodedPolynomialVerifierFinalPackage

end MCFG
