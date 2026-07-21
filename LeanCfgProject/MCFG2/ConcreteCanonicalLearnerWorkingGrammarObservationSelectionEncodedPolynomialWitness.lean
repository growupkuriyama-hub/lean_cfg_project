/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG2.ConcreteCanonicalLearnerWorkingGrammarObservationSelectionEncodedPolynomialVerifier

/-!
# ConcreteCanonicalLearnerWorkingGrammarObservationSelectionEncodedPolynomialWitness.lean

The preceding file attaches the logical dense-certificate verifier to one
abstract machine and one polynomial resource accounting.  This file isolates
the resulting nondeterministic witness relation.

For a polynomial verifier `V`, define

```text
V.Witness budget code
```

to mean that the code lies in the declared finite code universe and that the
same verifier machine accepts it.  We prove the exact logical characterization

```text
Question budget ↔ ∃ code, V.Witness budget code.
```

We also construct the finite accepted-witness set, prove that it is nonempty
exactly for positive instances, bound its cardinality by the declared code
universe, and package witnesses together with the certificate-size and
machine-work polynomial bounds.

The observation-selection specialization uses the dense bit-mask universe of
size `2 ^ U.card`.  The final positive-additive theorem supplies a machine
witness at the exact semantic minimum observation-selection rank.

This is an NP-style witness relation, but it is deliberately not stated as
membership in a formal complexity class.  Interpreting the abstract machine
work counter as the step count of a chosen standard machine model remains a
separate obligation.  No NP-hardness or NP-completeness claim is made.

No target grammar is supplied to any learner.
No `sorry`, `admit`, or `axiom` is used.
-/

namespace MCFG

universe u v w z


namespace CorrectedConcreteEncodedPolynomialVerifier

section GenericPolynomialWitness

variable {Question : Nat → Prop}
variable
  (verifier :
    CorrectedConcreteEncodedPolynomialVerifier
      Question)

/-- A bounded machine-accepted certificate code. -/
def Witness
    (budget code : Nat) : Prop :=
  code < verifier.resources.specification.codeBound budget ∧
    verifier.machine.run budget code = true

/-- The finite set of all bounded machine-accepted certificate codes. -/
def witnessCodes
    (budget : Nat) : Finset Nat :=
  (Finset.range
      (verifier.resources.specification.codeBound budget)).filter
    (fun code =>
      verifier.machine.run budget code = true)

/-- Membership in the finite witness-code set is exactly the witness
relation. -/
theorem mem_witnessCodes_iff
    (budget code : Nat) :
    code ∈ verifier.witnessCodes budget ↔
      verifier.Witness budget code := by

  simp [witnessCodes, Witness]

/-- Exact soundness and completeness of the machine witness relation. -/
theorem question_iff_exists_witness
    (budget : Nat) :
    Question budget ↔
      ∃ code : Nat,
        verifier.Witness budget code := by

  constructor

  · intro hQuestion

    rcases
        verifier.exists_machine_accepted_code_with_polynomial_bounds
          hQuestion with
      ⟨code, hCode, hRun, hCertificateSize, hWork⟩

    exact
      ⟨code, hCode, hRun⟩

  · rintro ⟨code, hCode, hRun⟩

    exact
      verifier.question_of_machine_accepted_code
        hCode
        hRun

/-- The finite witness-code set is nonempty exactly for positive instances. -/
theorem witnessCodes_nonempty_iff
    (budget : Nat) :
    (verifier.witnessCodes budget).Nonempty ↔
      Question budget := by

  constructor

  · rintro ⟨code, hCode⟩

    exact
      (verifier.question_iff_exists_witness budget).mpr
        ⟨code,
          (verifier.mem_witnessCodes_iff
            budget
            code).mp
            hCode⟩

  · intro hQuestion

    rcases
        (verifier.question_iff_exists_witness budget).mp
          hQuestion with
      ⟨code, hWitness⟩

    exact
      ⟨code,
        (verifier.mem_witnessCodes_iff
          budget
          code).mpr
          hWitness⟩

/-- Negative instances have no bounded machine witness. -/
theorem no_witness_of_not_question
    {budget : Nat}
    (hQuestion : ¬ Question budget) :
    ¬ ∃ code : Nat,
        verifier.Witness budget code := by

  intro hWitness

  exact
    hQuestion
      ((verifier.question_iff_exists_witness budget).mpr
        hWitness)

/-- The finite witness family is bounded by the declared certificate-code
universe. -/
theorem witnessCodes_card_le
    (budget : Nat) :
    (verifier.witnessCodes budget).card <=
      verifier.resources.specification.codeBound budget := by

  calc
    (verifier.witnessCodes budget).card <=
        (Finset.range
          (verifier.resources.specification.codeBound budget)).card :=
      Finset.card_le_card
        (Finset.filter_subset _ _)

    _ =
        verifier.resources.specification.codeBound budget := by
      simp

/-- A witness together with the polynomial certificate-size and machine-work
bounds from the same verifier package. -/
structure PolynomialWitness
    (budget : Nat) where

  code : Nat

  code_lt :
    code < verifier.resources.specification.codeBound budget

  accepted :
    verifier.machine.run budget code = true

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

/-- Every positive instance has one polynomially bounded machine witness. -/
noncomputable def selectedPolynomialWitness
    {budget : Nat}
    (hQuestion : Question budget) :
    verifier.PolynomialWitness budget := by

  rcases
      verifier.exists_machine_accepted_code_with_polynomial_bounds
        hQuestion with
    ⟨code, hCode, hRun, hCertificateSize, hWork⟩

  exact
    {
      code := code
      code_lt := hCode
      accepted := hRun
      certificateSize_le := hCertificateSize
      machineWork_le := hWork
    }

/-- The selected polynomial witness satisfies the underlying witness
relation. -/
theorem selectedPolynomialWitness_isWitness
    {budget : Nat}
    (hQuestion : Question budget) :
    verifier.Witness
      budget
      (verifier.selectedPolynomialWitness hQuestion).code := by

  exact
    ⟨(verifier.selectedPolynomialWitness hQuestion).code_lt,
      (verifier.selectedPolynomialWitness hQuestion).accepted⟩

/-- Complete generic witness package. -/
theorem polynomialWitness_package
    (budget : Nat) :
    (Question budget ↔
        ∃ code : Nat,
          verifier.Witness budget code) ∧
      ((verifier.witnessCodes budget).Nonempty ↔
        Question budget) ∧
      (verifier.witnessCodes budget).card <=
        verifier.resources.specification.codeBound budget := by

  exact
    ⟨verifier.question_iff_exists_witness budget,
      verifier.witnessCodes_nonempty_iff budget,
      verifier.witnessCodes_card_le budget⟩

end GenericPolynomialWitness

end CorrectedConcreteEncodedPolynomialVerifier


namespace CorrectedConcreteObservationSelectionDecisionTable

section DenseCostPolynomialWitness

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

/-- Exact ordinary-cost decision characterization by a bounded dense machine
witness. -/
theorem denseCostDecision_iff_exists_polynomialWitness
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
    table.costFeasibleDecision budget = true ↔
      ∃ code : Nat,
        (table.denseCostEncodedPolynomialVerifier
          verifierWork
          verifierCoeff
          verifierDegree
          hVerifierWork).Witness
            budget
            code := by

  exact
    (table.denseCostEncodedPolynomialVerifier
      verifierWork
      verifierCoeff
      verifierDegree
      hVerifierWork).question_iff_exists_witness
        budget

/-- The ordinary-cost dense witness family has at most `2 ^ U.card`
members. -/
theorem denseCostPolynomialWitnessCodes_card_le
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
    ((table.denseCostEncodedPolynomialVerifier
      verifierWork
      verifierCoeff
      verifierDegree
      hVerifierWork).witnessCodes budget).card <=
        2 ^ U.card := by

  simpa [
    denseCostEncodedPolynomialVerifier,
    CorrectedConcreteEncodedPolynomialVerifier.ofResourceSpecification,
    denseCostVerifierResourceSpecification,
    costDecisionEncodedCertificateSpecification
  ] using
    (table.denseCostEncodedPolynomialVerifier
      verifierWork
      verifierCoeff
      verifierDegree
      hVerifierWork).witnessCodes_card_le
        budget

end DenseCostPolynomialWitness


section DenseParetoPolynomialWitness

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

/-- Exact Pareto-scalar decision characterization by a bounded dense machine
witness. -/
theorem denseParetoDecision_iff_exists_polynomialWitness
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
    table.paretoScalarFeasibleDecision budget = true ↔
      ∃ code : Nat,
        (table.denseParetoEncodedPolynomialVerifier
          verifierWork
          verifierCoeff
          verifierDegree
          hVerifierWork).Witness
            budget
            code := by

  exact
    (table.denseParetoEncodedPolynomialVerifier
      verifierWork
      verifierCoeff
      verifierDegree
      hVerifierWork).question_iff_exists_witness
        budget

/-- The Pareto-scalar dense witness family has at most `2 ^ U.card`
members. -/
theorem denseParetoPolynomialWitnessCodes_card_le
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
    ((table.denseParetoEncodedPolynomialVerifier
      verifierWork
      verifierCoeff
      verifierDegree
      hVerifierWork).witnessCodes budget).card <=
        2 ^ U.card := by

  simpa [
    denseParetoEncodedPolynomialVerifier,
    CorrectedConcreteEncodedPolynomialVerifier.ofResourceSpecification,
    denseParetoVerifierResourceSpecification,
    paretoDecisionEncodedCertificateSpecification
  ] using
    (table.denseParetoEncodedPolynomialVerifier
      verifierWork
      verifierCoeff
      verifierDegree
      hVerifierWork).witnessCodes_card_le
        budget

end DenseParetoPolynomialWitness


section PositiveAdditiveRankPolynomialWitness

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

/-- Exact semantic positive-additive rank-threshold characterization by the
dense Pareto machine witness relation. -/
theorem positiveAdditiveRank_le_iff_exists_polynomialWitness
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
    ambientTargetObservationSelectionPositiveAdditiveMinimumCost
          (z := z)
          obsFamily
          f
          coordinateWeight
          U
          hTarget <=
        budget ↔
      ∃ code : Nat,
        (table.positiveAdditiveRankEncodedPolynomialVerifier
          hTarget
          verifierWork
          verifierCoeff
          verifierDegree
          hVerifierWork).Witness
            budget
            code := by

  exact
    (table.positiveAdditiveRankEncodedPolynomialVerifier
      hTarget
      verifierWork
      verifierCoeff
      verifierDegree
      hVerifierWork).question_iff_exists_witness
        budget

end PositiveAdditiveRankPolynomialWitness

end CorrectedConcreteObservationSelectionDecisionTable


section EncodedPolynomialWitnessFinalPackage

variable {α : Type u}
variable {ι : Type v}
variable {M : Type w}
variable [DecidableEq ι]
variable [Monoid M]
variable (obsFamily : ι → α → M)
variable (f : Nat)
variable (coordinateWeight : ι → Nat)
variable (U : Finset ι)

/-- Final exact-minimum positive-additive machine-witness package.

At the semantic minimum rank there is a bounded machine-accepted dense code,
with the linear certificate-size and supplied polynomial machine-work bounds.
-/
theorem
    correctedConcreteWorkingGrammar_observationSelectionEncodedPolynomialWitness_package
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
    ∃ witness :
        verifier.PolynomialWitness minimumRank,
      verifier.Witness minimumRank witness.code ∧
        witness.code < 2 ^ U.card ∧
        U.card <= U.card + minimumRank + 1 ∧
        verifier.machine.work minimumRank witness.code <=
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

  let witness :=
    verifier.selectedPolynomialWitness hQuestion

  refine
    ⟨witness,
      verifier.selectedPolynomialWitness_isWitness hQuestion,
      ?_,
      ?_,
      ?_⟩

  · simpa [
      witness,
      verifier,
      CorrectedConcreteObservationSelectionDecisionTable.positiveAdditiveRankEncodedPolynomialVerifier,
      CorrectedConcreteObservationSelectionDecisionTable.positiveAdditiveRankVerifierResourceSpecification,
      CorrectedConcreteEncodedPolynomialVerifier.ofResourceSpecification,
      CorrectedConcreteObservationSelectionDecisionTable.positiveAdditiveParetoRankEncodedCertificateSpecification
    ] using witness.code_lt

  · have hBasic :
        U.card <= U.card + (minimumRank + 1) :=
      Nat.le_add_right U.card (minimumRank + 1)

    simpa [Nat.add_assoc] using hBasic

  · simpa [
      witness,
      verifier,
      CorrectedConcreteObservationSelectionDecisionTable.positiveAdditiveRankEncodedPolynomialVerifier,
      CorrectedConcreteObservationSelectionDecisionTable.positiveAdditiveRankVerifierResourceSpecification,
      CorrectedConcreteEncodedPolynomialVerifier.ofResourceSpecification,
      Nat.add_assoc
    ] using witness.machineWork_le

end EncodedPolynomialWitnessFinalPackage

end MCFG
