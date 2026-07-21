/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG2.ConcreteCanonicalLearnerWorkingGrammarObservationSelectionEncodedExecutableVerifier

/-!
# ConcreteCanonicalLearnerWorkingGrammarObservationSelectionEncodedExecutableVerifierComplexity.lean

The preceding file defines an executable verifier relative to a finite encoded
instance.  This file equips that verifier with an explicit elementary work
model.

For one certificate code, the work model counts

```text
one bound check
+ one linear scan through the relevant stored accepted-code table
+ one final Boolean combination.
```

Thus the ordinary and Pareto verifier work values are respectively

```text
costCertificateCodes.card + 2
paretoCertificateCodes.card + 2.
```

The explicit verifier-input sizes are

```text
codeBound + (costCertificateCodes.card + 2)
codeBound + (paretoCertificateCodes.card + 2).
```

We prove:

* one certificate verification has work at most its explicit input size;
* exhaustive verification performs exactly `codeBound` verifier calls;
* exhaustive work is at most the square of the corresponding explicit input
  size;
* for canonical observation-selection instances the candidate count remains
  exactly `2 ^ U.card`;
* at the exact semantic positive-additive minimum rank, the canonical Pareto
  witness is accepted with linear single-certificate work.

This is an explicit combinatorial work accounting for the verifier implemented
over a supplied finite table.  It is polynomial in the size of that explicit
table, but the table itself may contain up to `2 ^ U.card` codes.  Constructing
or serializing the semantic table from a compact grammar/observation input
remains open.  Consequently this file does not claim end-to-end polynomial
time, formal NP membership, NP-hardness, or NP-completeness.

No target grammar is supplied to any learner.
No `sorry`, `admit`, or `axiom` is used.
-/

namespace MCFG

universe u v w z


namespace CorrectedConcreteEncodedObservationSelectionInstance

section SingleCertificateWork

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

/-- Elementary work count for one ordinary-cost certificate verification. -/
def costCertificateVerifierWork
    (_code : Nat) : Nat :=
  instance.costCertificateCodes.card + 2

/-- Elementary work count for one Pareto certificate verification. -/
def paretoCertificateVerifierWork
    (_code : Nat) : Nat :=
  instance.paretoCertificateCodes.card + 2

/-- Explicit ordinary verifier-input size used by the work accounting. -/
def costVerifierInputSize : Nat :=
  instance.codeBound +
    (instance.costCertificateCodes.card + 2)

/-- Explicit Pareto verifier-input size used by the work accounting. -/
def paretoVerifierInputSize : Nat :=
  instance.codeBound +
    (instance.paretoCertificateCodes.card + 2)

/-- Executable ordinary verifier paired with its elementary work count. -/
def runCostCertificateVerifierWithWork
    (code : Nat) : Bool × Nat :=
  (instance.runCostCertificateVerifier code,
    instance.costCertificateVerifierWork code)

/-- Executable Pareto verifier paired with its elementary work count. -/
def runParetoCertificateVerifierWithWork
    (code : Nat) : Bool × Nat :=
  (instance.runParetoCertificateVerifier code,
    instance.paretoCertificateVerifierWork code)

@[simp]
theorem runCostCertificateVerifierWithWork_fst
    (code : Nat) :
    (instance.runCostCertificateVerifierWithWork code).1 =
      instance.runCostCertificateVerifier code := by

  rfl

@[simp]
theorem runCostCertificateVerifierWithWork_snd
    (code : Nat) :
    (instance.runCostCertificateVerifierWithWork code).2 =
      instance.costCertificateCodes.card + 2 := by

  rfl

@[simp]
theorem runParetoCertificateVerifierWithWork_fst
    (code : Nat) :
    (instance.runParetoCertificateVerifierWithWork code).1 =
      instance.runParetoCertificateVerifier code := by

  rfl

@[simp]
theorem runParetoCertificateVerifierWithWork_snd
    (code : Nat) :
    (instance.runParetoCertificateVerifierWithWork code).2 =
      instance.paretoCertificateCodes.card + 2 := by

  rfl

/-- The code bound is part of the ordinary explicit verifier input. -/
theorem codeBound_le_costVerifierInputSize :
    instance.codeBound <=
      instance.costVerifierInputSize := by

  unfold costVerifierInputSize

  exact
    Nat.le_add_right
      instance.codeBound
      (instance.costCertificateCodes.card + 2)

/-- The code bound is part of the Pareto explicit verifier input. -/
theorem codeBound_le_paretoVerifierInputSize :
    instance.codeBound <=
      instance.paretoVerifierInputSize := by

  unfold paretoVerifierInputSize

  exact
    Nat.le_add_right
      instance.codeBound
      (instance.paretoCertificateCodes.card + 2)

/-- One ordinary certificate verification is linear in the explicit ordinary
verifier-input size. -/
theorem costCertificateVerifierWork_le_inputSize
    (code : Nat) :
    instance.costCertificateVerifierWork code <=
      instance.costVerifierInputSize := by

  unfold costCertificateVerifierWork
  unfold costVerifierInputSize

  exact
    Nat.le_add_left
      (instance.costCertificateCodes.card + 2)
      instance.codeBound

/-- One Pareto certificate verification is linear in the explicit Pareto
verifier-input size. -/
theorem paretoCertificateVerifierWork_le_inputSize
    (code : Nat) :
    instance.paretoCertificateVerifierWork code <=
      instance.paretoVerifierInputSize := by

  unfold paretoCertificateVerifierWork
  unfold paretoVerifierInputSize

  exact
    Nat.le_add_left
      (instance.paretoCertificateCodes.card + 2)
      instance.codeBound

/-- Accepted ordinary certificates retain the same linear work bound. -/
theorem acceptedCostCertificate_work_package
    {code : Nat}
    (hRun :
      instance.runCostCertificateVerifier code = true) :
    (instance.runCostCertificateVerifierWithWork code).1 =
        true ∧
      (instance.runCostCertificateVerifierWithWork code).2 <=
        instance.costVerifierInputSize := by

  exact
    ⟨by
        simpa using hRun,
      by
        simpa using
          instance.costCertificateVerifierWork_le_inputSize
            code⟩

/-- Accepted Pareto certificates retain the same linear work bound. -/
theorem acceptedParetoCertificate_work_package
    {code : Nat}
    (hRun :
      instance.runParetoCertificateVerifier code = true) :
    (instance.runParetoCertificateVerifierWithWork code).1 =
        true ∧
      (instance.runParetoCertificateVerifierWithWork code).2 <=
        instance.paretoVerifierInputSize := by

  exact
    ⟨by
        simpa using hRun,
      by
        simpa using
          instance.paretoCertificateVerifierWork_le_inputSize
            code⟩

end SingleCertificateWork


section ExhaustiveVerifierWork

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

/-- Exact elementary work count for exhaustive ordinary verification. -/
def exhaustiveCostVerifierWork : Nat :=
  instance.codeBound *
    (instance.costCertificateCodes.card + 2)

/-- Exact elementary work count for exhaustive Pareto verification. -/
def exhaustiveParetoVerifierWork : Nat :=
  instance.codeBound *
    (instance.paretoCertificateCodes.card + 2)

/-- Executable ordinary decision paired with exhaustive verifier work. -/
def runCostDecisionWithWork : Bool × Nat :=
  (instance.runCostDecision,
    instance.exhaustiveCostVerifierWork)

/-- Executable Pareto decision paired with exhaustive verifier work. -/
def runParetoDecisionWithWork : Bool × Nat :=
  (instance.runParetoDecision,
    instance.exhaustiveParetoVerifierWork)

@[simp]
theorem runCostDecisionWithWork_fst :
    instance.runCostDecisionWithWork.1 =
      instance.runCostDecision := by

  rfl

@[simp]
theorem runCostDecisionWithWork_snd :
    instance.runCostDecisionWithWork.2 =
      instance.exhaustiveCostVerifierWork := by

  rfl

@[simp]
theorem runParetoDecisionWithWork_fst :
    instance.runParetoDecisionWithWork.1 =
      instance.runParetoDecision := by

  rfl

@[simp]
theorem runParetoDecisionWithWork_snd :
    instance.runParetoDecisionWithWork.2 =
      instance.exhaustiveParetoVerifierWork := by

  rfl

/-- Exhaustive ordinary work is bounded by code count times explicit ordinary
verifier-input size. -/
theorem exhaustiveCostVerifierWork_le_codeBound_mul_inputSize :
    instance.exhaustiveCostVerifierWork <=
      instance.codeBound *
        instance.costVerifierInputSize := by

  unfold exhaustiveCostVerifierWork

  exact
    Nat.mul_le_mul_left
      instance.codeBound
      (instance.costCertificateVerifierWork_le_inputSize
        0)

/-- Exhaustive Pareto work is bounded by code count times explicit Pareto
verifier-input size. -/
theorem exhaustiveParetoVerifierWork_le_codeBound_mul_inputSize :
    instance.exhaustiveParetoVerifierWork <=
      instance.codeBound *
        instance.paretoVerifierInputSize := by

  unfold exhaustiveParetoVerifierWork

  exact
    Nat.mul_le_mul_left
      instance.codeBound
      (instance.paretoCertificateVerifierWork_le_inputSize
        0)

/-- Exhaustive ordinary work is at most quadratic in the explicit ordinary
verifier-input size. -/
theorem exhaustiveCostVerifierWork_le_inputSize_sq :
    instance.exhaustiveCostVerifierWork <=
      instance.costVerifierInputSize *
        instance.costVerifierInputSize := by

  calc
    instance.exhaustiveCostVerifierWork <=
        instance.codeBound *
          instance.costVerifierInputSize :=
      instance.exhaustiveCostVerifierWork_le_codeBound_mul_inputSize

    _ <=
        instance.costVerifierInputSize *
          instance.costVerifierInputSize :=
      Nat.mul_le_mul_right
        instance.costVerifierInputSize
        instance.codeBound_le_costVerifierInputSize

/-- Exhaustive Pareto work is at most quadratic in the explicit Pareto
verifier-input size. -/
theorem exhaustiveParetoVerifierWork_le_inputSize_sq :
    instance.exhaustiveParetoVerifierWork <=
      instance.paretoVerifierInputSize *
        instance.paretoVerifierInputSize := by

  calc
    instance.exhaustiveParetoVerifierWork <=
        instance.codeBound *
          instance.paretoVerifierInputSize :=
      instance.exhaustiveParetoVerifierWork_le_codeBound_mul_inputSize

    _ <=
        instance.paretoVerifierInputSize *
          instance.paretoVerifierInputSize :=
      Nat.mul_le_mul_right
        instance.paretoVerifierInputSize
        instance.codeBound_le_paretoVerifierInputSize

/-- Exact candidate-call count and quadratic work bounds for both exhaustive
decisions. -/
theorem exhaustiveVerifierWork_package :
    instance.exhaustiveVerifierCallCount =
        instance.codeBound ∧
      instance.exhaustiveCostVerifierWork <=
        instance.costVerifierInputSize *
          instance.costVerifierInputSize ∧
      instance.exhaustiveParetoVerifierWork <=
        instance.paretoVerifierInputSize *
          instance.paretoVerifierInputSize := by

  exact
    ⟨rfl,
      instance.exhaustiveCostVerifierWork_le_inputSize_sq,
      instance.exhaustiveParetoVerifierWork_le_inputSize_sq⟩

end ExhaustiveVerifierWork


section CanonicalEncodedInstanceWorkFormulas

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

/-- Ordinary explicit verifier-input size is at most twice the dense code
universe plus two. -/
theorem costVerifierInputSize_le_two_mul_codeBound_add_two :
    instance.costVerifierInputSize <=
      instance.codeBound + instance.codeBound + 2 := by

  unfold costVerifierInputSize

  have hCard :
      instance.costCertificateCodes.card <=
        instance.codeBound :=
    instance.costCertificateCodes_card_le

  simpa [Nat.add_assoc] using
    Nat.add_le_add_left
      (Nat.add_le_add_right hCard 2)
      instance.codeBound

/-- Pareto explicit verifier-input size is at most twice the dense code
universe plus two. -/
theorem paretoVerifierInputSize_le_two_mul_codeBound_add_two :
    instance.paretoVerifierInputSize <=
      instance.codeBound + instance.codeBound + 2 := by

  unfold paretoVerifierInputSize

  have hCard :
      instance.paretoCertificateCodes.card <=
        instance.codeBound :=
    instance.paretoCertificateCodes_card_le

  simpa [Nat.add_assoc] using
    Nat.add_le_add_left
      (Nat.add_le_add_right hCard 2)
      instance.codeBound

/-- The explicit verifier-input bounds specialized to the dense
`2 ^ U.card` universe. -/
theorem denseVerifierInputSize_package :
    instance.costVerifierInputSize <=
        2 ^ U.card + 2 ^ U.card + 2 ∧
      instance.paretoVerifierInputSize <=
        2 ^ U.card + 2 ^ U.card + 2 := by

  constructor

  · simpa [instance.codeBound_correct] using
      instance.costVerifierInputSize_le_two_mul_codeBound_add_two

  · simpa [instance.codeBound_correct] using
      instance.paretoVerifierInputSize_le_two_mul_codeBound_add_two

/-- Exhaustive work retains an explicit exponential-in-coordinate-count
envelope. -/
theorem denseExhaustiveVerifierWork_package :
    instance.exhaustiveCostVerifierWork <=
        (2 ^ U.card + 2 ^ U.card + 2) *
          (2 ^ U.card + 2 ^ U.card + 2) ∧
      instance.exhaustiveParetoVerifierWork <=
        (2 ^ U.card + 2 ^ U.card + 2) *
          (2 ^ U.card + 2 ^ U.card + 2) := by

  have hCostDense :
      instance.costVerifierInputSize <=
        2 ^ U.card + 2 ^ U.card + 2 := by

    simpa [instance.codeBound_correct] using
      instance.costVerifierInputSize_le_two_mul_codeBound_add_two

  have hParetoDense :
      instance.paretoVerifierInputSize <=
        2 ^ U.card + 2 ^ U.card + 2 := by

    simpa [instance.codeBound_correct] using
      instance.paretoVerifierInputSize_le_two_mul_codeBound_add_two

  constructor

  · calc
      instance.exhaustiveCostVerifierWork <=
          instance.costVerifierInputSize *
            instance.costVerifierInputSize :=
        instance.exhaustiveCostVerifierWork_le_inputSize_sq

      _ <=
          (2 ^ U.card + 2 ^ U.card + 2) *
            (2 ^ U.card + 2 ^ U.card + 2) :=
        Nat.mul_le_mul hCostDense hCostDense

  · calc
      instance.exhaustiveParetoVerifierWork <=
          instance.paretoVerifierInputSize *
            instance.paretoVerifierInputSize :=
        instance.exhaustiveParetoVerifierWork_le_inputSize_sq

      _ <=
          (2 ^ U.card + 2 ^ U.card + 2) *
            (2 ^ U.card + 2 ^ U.card + 2) :=
        Nat.mul_le_mul hParetoDense hParetoDense

end CanonicalEncodedInstanceWorkFormulas

end CorrectedConcreteEncodedObservationSelectionInstance


namespace CorrectedConcreteObservationSelectionDecisionTable

section CanonicalEncodedVerifierComplexity

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

/-- Work bounds for the canonical encoded instance at any budget. -/
theorem encodedObservationSelectionInstance_verifierWork_package
    (budget : Nat) :
    let instance :=
      table.encodedObservationSelectionInstance budget
    instance.exhaustiveVerifierCallCount =
        2 ^ U.card ∧
      instance.costCertificateVerifierWork 0 <=
        instance.costVerifierInputSize ∧
      instance.paretoCertificateVerifierWork 0 <=
        instance.paretoVerifierInputSize ∧
      instance.exhaustiveCostVerifierWork <=
        instance.costVerifierInputSize *
          instance.costVerifierInputSize ∧
      instance.exhaustiveParetoVerifierWork <=
        instance.paretoVerifierInputSize *
          instance.paretoVerifierInputSize := by

  let instance :=
    table.encodedObservationSelectionInstance budget

  exact
    ⟨instance.exhaustiveVerifierCallCount_eq,
      instance.costCertificateVerifierWork_le_inputSize 0,
      instance.paretoCertificateVerifierWork_le_inputSize 0,
      instance.exhaustiveCostVerifierWork_le_inputSize_sq,
      instance.exhaustiveParetoVerifierWork_le_inputSize_sq⟩

end CanonicalEncodedVerifierComplexity

end CorrectedConcreteObservationSelectionDecisionTable


section EncodedExecutableVerifierComplexityFinalPackage

variable {α : Type u}
variable {ι : Type v}
variable {M : Type w}
variable [DecidableEq ι]
variable [Monoid M]
variable (obsFamily : ι → α → M)
variable (f : Nat)
variable (coordinateWeight : ι → Nat)
variable (U : Finset ι)

/-- Final positive-additive executable-verifier work package.

At the exact semantic minimum rank, the canonical Pareto dense code is accepted
by the finite executable verifier.  Its single-code work is linear in the
explicit Pareto verifier input, while exhaustive verification is quadratic in
that explicit input and still has exactly `2 ^ U.card` candidate calls. -/
theorem
    correctedConcreteWorkingGrammar_observationSelectionEncodedExecutableVerifierComplexity_package
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
    instance.runParetoCertificateVerifier canonicalCode =
        true ∧
      instance.paretoCertificateVerifierWork canonicalCode <=
        instance.paretoVerifierInputSize ∧
      instance.exhaustiveVerifierCallCount =
        2 ^ U.card ∧
      instance.exhaustiveParetoVerifierWork <=
        instance.paretoVerifierInputSize *
          instance.paretoVerifierInputSize ∧
      instance.paretoVerifierInputSize <=
        2 ^ U.card + 2 ^ U.card + 2 ∧
      correctedConcreteDenseCertificateDecode
            U
            canonicalCode =
        some
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

  have hBudgetEq :
      table.selectedMinimumAcceptedParetoScalarBudget
            maxBudget
            hAccepted =
        minimumRank :=
    table.selectedMinimumAcceptedParetoScalarBudget_eq_positiveAdditiveMinimum
      hTarget
      maxBudget
      hBound

  have hDenseVerify :
      table.verifiesDenseParetoScalarCertificateCode
            minimumRank
            canonicalCode =
          true := by

    rw [← hBudgetEq]

    exact
      table.selectedCanonicalDenseMinimumParetoScalarCode_verifies
        maxBudget
        hAccepted

  have hCodeBound :
      canonicalCode < instance.codeBound := by

    simpa [
      instance,
      CorrectedConcreteObservationSelectionDecisionTable.encodedObservationSelectionInstance
    ] using
      table.selectedCanonicalDenseMinimumParetoScalarCode_lt
        maxBudget
        hAccepted

  have hExecutable :
      instance.runParetoCertificateVerifier canonicalCode =
        true :=
    (instance.runParetoCertificateVerifier_eq_true_iff_denseVerifier
      canonicalCode).mpr
      ⟨hCodeBound, hDenseVerify⟩

  exact
    ⟨hExecutable,
      instance.paretoCertificateVerifierWork_le_inputSize
        canonicalCode,
      instance.exhaustiveVerifierCallCount_eq,
      instance.exhaustiveParetoVerifierWork_le_inputSize_sq,
      by
        simpa [instance.codeBound_correct] using
          instance.paretoVerifierInputSize_le_two_mul_codeBound_add_two,
      table.selectedCanonicalDenseMinimumParetoScalarCode_decode
        maxBudget
        hAccepted⟩

end EncodedExecutableVerifierComplexityFinalPackage

end MCFG
