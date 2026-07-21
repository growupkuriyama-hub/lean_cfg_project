/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG.ConcreteCanonicalLearnerWorkingGrammarObservationSelectionEncodedInstance

/-!
# ConcreteCanonicalLearnerWorkingGrammarObservationSelectionEncodedExecutableVerifier.lean

The preceding file packages one budgeted observation-selection query as a
finite encoded instance containing only

* a budget;
* an exclusive natural-number code bound;
* finite ordinary-cost and Pareto accepted-code tables;
* proof-carrying links to the semantic dense verifiers.

This file defines the first verifier that reads only those finite encoded
fields.

For a candidate natural-number certificate code, the executable verifier checks

```text
code < instance.codeBound
```

and membership in the corresponding stored finite code table.  It does not
inspect selected subsets, observation products, grammars, or semantic target
membership.

We then exhaustively run the verifier on

```text
0, ..., instance.codeBound - 1
```

and prove that the resulting accepted-code sets are exactly the code tables
stored in the encoded instance.  Consequently the executable decisions agree
with

* the encoded-instance decisions;
* the previous semantic-table decisions;
* existence of a verifier-accepted bounded code.

At the exact semantic positive-additive minimum rank, both executable
decisions return `true`, and the previously selected canonical Pareto
polynomial-witness code is accepted by the executable verifier and appears in
its exhaustive accepted-code search.

The verifier is executable relative to a supplied finite encoded instance.
The canonical construction of that instance is still noncomputable because it
is extracted from the semantic decision table.  This file therefore does not
yet establish an end-to-end polynomial-time algorithm or formal NP membership.

No target grammar is supplied to any learner.
No `sorry`, `admit`, or `axiom` is used.
-/

namespace MCFG

universe u v w z


namespace CorrectedConcreteEncodedObservationSelectionInstance

section ExecutableCodeVerifier

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

/-- Executable ordinary-cost certificate verifier.

Only the code bound and the finite stored ordinary-cost code table are read. -/
def runCostCertificateVerifier
    (code : Nat) : Bool :=
  decide
    (code < instance.codeBound ∧
      code ∈ instance.costCertificateCodes)

/-- Executable Pareto-scalar certificate verifier.

Only the code bound and the finite stored Pareto code table are read. -/
def runParetoCertificateVerifier
    (code : Nat) : Bool :=
  decide
    (code < instance.codeBound ∧
      code ∈ instance.paretoCertificateCodes)

/-- Exact specification of the executable ordinary-cost verifier. -/
@[simp]
theorem runCostCertificateVerifier_eq_true_iff
    (code : Nat) :
    instance.runCostCertificateVerifier code = true ↔
      code < instance.codeBound ∧
        code ∈ instance.costCertificateCodes := by

  simp [runCostCertificateVerifier]

/-- Exact specification of the executable Pareto verifier. -/
@[simp]
theorem runParetoCertificateVerifier_eq_true_iff
    (code : Nat) :
    instance.runParetoCertificateVerifier code = true ↔
      code < instance.codeBound ∧
        code ∈ instance.paretoCertificateCodes := by

  simp [runParetoCertificateVerifier]

/-- The executable ordinary-cost verifier is equivalent to the previous dense
Boolean verifier on the encoded instance's budget. -/
theorem runCostCertificateVerifier_eq_true_iff_denseVerifier
    (code : Nat) :
    instance.runCostCertificateVerifier code = true ↔
      code < instance.codeBound ∧
        table.verifiesDenseCostCertificateCode
            instance.budget
            code =
          true := by

  rw [instance.runCostCertificateVerifier_eq_true_iff]

  constructor

  · rintro ⟨hBound, hStored⟩

    exact
      ⟨hBound,
        ((instance.costCodes_correct code).mp hStored).2⟩

  · rintro ⟨hBound, hVerify⟩

    exact
      ⟨hBound,
        (instance.costCodes_correct code).mpr
          ⟨hBound, hVerify⟩⟩

/-- The executable Pareto verifier is equivalent to the previous dense
Boolean verifier on the encoded instance's budget. -/
theorem runParetoCertificateVerifier_eq_true_iff_denseVerifier
    (code : Nat) :
    instance.runParetoCertificateVerifier code = true ↔
      code < instance.codeBound ∧
        table.verifiesDenseParetoScalarCertificateCode
            instance.budget
            code =
          true := by

  rw [instance.runParetoCertificateVerifier_eq_true_iff]

  constructor

  · rintro ⟨hBound, hStored⟩

    exact
      ⟨hBound,
        ((instance.paretoCodes_correct code).mp hStored).2⟩

  · rintro ⟨hBound, hVerify⟩

    exact
      ⟨hBound,
        (instance.paretoCodes_correct code).mpr
          ⟨hBound, hVerify⟩⟩

/-- Every executable ordinary-cost acceptance decodes to a checked subset
certificate. -/
theorem runCostCertificateVerifier_decode_package
    {code : Nat}
    (hRun :
      instance.runCostCertificateVerifier code = true) :
    ∃ certificate : Finset ι,
      correctedConcreteDenseCertificateDecode U code =
          some certificate ∧
        table.verifiesCostCertificate
            instance.budget
            certificate =
          true ∧
        certificate ⊆ U := by

  have hStored :
      code ∈ instance.costCertificateCodes :=
    (instance.runCostCertificateVerifier_eq_true_iff
      code).mp
      hRun
      |>.2

  exact
    instance.costCode_decode_package hStored

/-- Every executable Pareto acceptance decodes to a checked Pareto subset
certificate. -/
theorem runParetoCertificateVerifier_decode_package
    {code : Nat}
    (hRun :
      instance.runParetoCertificateVerifier code = true) :
    ∃ certificate : Finset ι,
      correctedConcreteDenseCertificateDecode U code =
          some certificate ∧
        table.verifiesParetoScalarCertificate
            instance.budget
            certificate =
          true ∧
        certificate ⊆ U := by

  have hStored :
      code ∈ instance.paretoCertificateCodes :=
    (instance.runParetoCertificateVerifier_eq_true_iff
      code).mp
      hRun
      |>.2

  exact
    instance.paretoCode_decode_package hStored

end ExecutableCodeVerifier


section ExhaustiveExecutableVerifierSearch

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

/-- Exhaustive ordinary-cost verifier search over the declared code universe. -/
def exhaustiveCostVerifierSearch : Finset Nat :=
  instance.codeUniverse.filter
    (fun code =>
      instance.runCostCertificateVerifier code = true)

/-- Exhaustive Pareto verifier search over the declared code universe. -/
def exhaustiveParetoVerifierSearch : Finset Nat :=
  instance.codeUniverse.filter
    (fun code =>
      instance.runParetoCertificateVerifier code = true)

/-- Membership characterization for the exhaustive ordinary-cost verifier
search. -/
theorem mem_exhaustiveCostVerifierSearch_iff
    (code : Nat) :
    code ∈ instance.exhaustiveCostVerifierSearch ↔
      code < instance.codeBound ∧
        instance.runCostCertificateVerifier code = true := by

  simp [
    exhaustiveCostVerifierSearch,
    CorrectedConcreteEncodedObservationSelectionInstance.codeUniverse
  ]

/-- Membership characterization for the exhaustive Pareto verifier search. -/
theorem mem_exhaustiveParetoVerifierSearch_iff
    (code : Nat) :
    code ∈ instance.exhaustiveParetoVerifierSearch ↔
      code < instance.codeBound ∧
        instance.runParetoCertificateVerifier code = true := by

  simp [
    exhaustiveParetoVerifierSearch,
    CorrectedConcreteEncodedObservationSelectionInstance.codeUniverse
  ]

/-- Exhaustive ordinary verifier search recovers exactly the stored accepted
ordinary-cost code table. -/
theorem exhaustiveCostVerifierSearch_eq :
    instance.exhaustiveCostVerifierSearch =
      instance.costCertificateCodes := by

  ext code

  constructor

  · intro hSearch

    have hParts :=
      (instance.mem_exhaustiveCostVerifierSearch_iff
        code).mp
        hSearch

    exact
      (instance.runCostCertificateVerifier_eq_true_iff
        code).mp
        hParts.2
        |>.2

  · intro hStored

    have hBound :
        code < instance.codeBound :=
      ((instance.costCodes_correct code).mp hStored).1

    exact
      (instance.mem_exhaustiveCostVerifierSearch_iff
        code).mpr
        ⟨hBound,
          (instance.runCostCertificateVerifier_eq_true_iff
            code).mpr
            ⟨hBound, hStored⟩⟩

/-- Exhaustive Pareto verifier search recovers exactly the stored accepted
Pareto code table. -/
theorem exhaustiveParetoVerifierSearch_eq :
    instance.exhaustiveParetoVerifierSearch =
      instance.paretoCertificateCodes := by

  ext code

  constructor

  · intro hSearch

    have hParts :=
      (instance.mem_exhaustiveParetoVerifierSearch_iff
        code).mp
        hSearch

    exact
      (instance.runParetoCertificateVerifier_eq_true_iff
        code).mp
        hParts.2
        |>.2

  · intro hStored

    have hBound :
        code < instance.codeBound :=
      ((instance.paretoCodes_correct code).mp hStored).1

    exact
      (instance.mem_exhaustiveParetoVerifierSearch_iff
        code).mpr
        ⟨hBound,
          (instance.runParetoCertificateVerifier_eq_true_iff
            code).mpr
            ⟨hBound, hStored⟩⟩

/-- The exhaustive ordinary verifier search contains at most the declared
number of candidate codes. -/
theorem exhaustiveCostVerifierSearch_card_le :
    instance.exhaustiveCostVerifierSearch.card <=
      instance.codeBound := by

  rw [instance.exhaustiveCostVerifierSearch_eq]

  exact
    instance.costCertificateCodes_card_le

/-- The exhaustive Pareto verifier search contains at most the declared number
of candidate codes. -/
theorem exhaustiveParetoVerifierSearch_card_le :
    instance.exhaustiveParetoVerifierSearch.card <=
      instance.codeBound := by

  rw [instance.exhaustiveParetoVerifierSearch_eq]

  exact
    instance.paretoCertificateCodes_card_le

/-- Number of candidate verifier invocations in one exhaustive scan. -/
def exhaustiveVerifierCallCount : Nat :=
  instance.codeBound

/-- Exact exhaustive verifier-call count for an observation-selection encoded
instance. -/
theorem exhaustiveVerifierCallCount_eq :
    instance.exhaustiveVerifierCallCount =
      2 ^ U.card := by

  exact instance.codeBound_correct

end ExhaustiveExecutableVerifierSearch


section ExecutableEncodedDecision

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

/-- Executable ordinary-cost decision obtained from the exhaustive verifier
search. -/
def runCostDecision : Bool :=
  decide instance.exhaustiveCostVerifierSearch.Nonempty

/-- Executable Pareto decision obtained from the exhaustive verifier search. -/
def runParetoDecision : Bool :=
  decide instance.exhaustiveParetoVerifierSearch.Nonempty

/-- Executable ordinary decision is positive exactly when an executable
ordinary certificate code is accepted. -/
theorem runCostDecision_eq_true_iff_exists_accepted_code :
    instance.runCostDecision = true ↔
      ∃ code : Nat,
        instance.runCostCertificateVerifier code = true := by

  unfold runCostDecision

  rw [decide_eq_true_eq]

  constructor

  · rintro ⟨code, hCode⟩

    exact
      ⟨code,
        ((instance.mem_exhaustiveCostVerifierSearch_iff
          code).mp
          hCode).2⟩

  · rintro ⟨code, hRun⟩

    have hBound :
        code < instance.codeBound :=
      ((instance.runCostCertificateVerifier_eq_true_iff
        code).mp
        hRun).1

    exact
      ⟨code,
        (instance.mem_exhaustiveCostVerifierSearch_iff
          code).mpr
          ⟨hBound, hRun⟩⟩

/-- Executable Pareto decision is positive exactly when an executable Pareto
certificate code is accepted. -/
theorem runParetoDecision_eq_true_iff_exists_accepted_code :
    instance.runParetoDecision = true ↔
      ∃ code : Nat,
        instance.runParetoCertificateVerifier code = true := by

  unfold runParetoDecision

  rw [decide_eq_true_eq]

  constructor

  · rintro ⟨code, hCode⟩

    exact
      ⟨code,
        ((instance.mem_exhaustiveParetoVerifierSearch_iff
          code).mp
          hCode).2⟩

  · rintro ⟨code, hRun⟩

    have hBound :
        code < instance.codeBound :=
      ((instance.runParetoCertificateVerifier_eq_true_iff
        code).mp
        hRun).1

    exact
      ⟨code,
        (instance.mem_exhaustiveParetoVerifierSearch_iff
          code).mpr
          ⟨hBound, hRun⟩⟩

/-- Executable ordinary decision agrees exactly with the encoded-instance
ordinary decision. -/
theorem runCostDecision_eq_true_iff_instanceDecision :
    instance.runCostDecision = true ↔
      instance.costDecision = true := by

  rw [instance.runCostDecision_eq_true_iff_exists_accepted_code]
  rw [instance.costDecision_eq_true_iff_exists_code]

  constructor

  · rintro ⟨code, hRun⟩

    exact
      ⟨code,
        ((instance.runCostCertificateVerifier_eq_true_iff
          code).mp
          hRun).2⟩

  · rintro ⟨code, hStored⟩

    have hBound :
        code < instance.codeBound :=
      ((instance.costCodes_correct code).mp hStored).1

    exact
      ⟨code,
        (instance.runCostCertificateVerifier_eq_true_iff
          code).mpr
          ⟨hBound, hStored⟩⟩

/-- Executable Pareto decision agrees exactly with the encoded-instance Pareto
decision. -/
theorem runParetoDecision_eq_true_iff_instanceDecision :
    instance.runParetoDecision = true ↔
      instance.paretoDecision = true := by

  rw [instance.runParetoDecision_eq_true_iff_exists_accepted_code]
  rw [instance.paretoDecision_eq_true_iff_exists_code]

  constructor

  · rintro ⟨code, hRun⟩

    exact
      ⟨code,
        ((instance.runParetoCertificateVerifier_eq_true_iff
          code).mp
          hRun).2⟩

  · rintro ⟨code, hStored⟩

    have hBound :
        code < instance.codeBound :=
      ((instance.paretoCodes_correct code).mp hStored).1

    exact
      ⟨code,
        (instance.runParetoCertificateVerifier_eq_true_iff
          code).mpr
          ⟨hBound, hStored⟩⟩

/-- Executable ordinary decision agrees exactly with the semantic-table
ordinary decision. -/
theorem runCostDecision_eq_true_iff_tableDecision :
    instance.runCostDecision = true ↔
      table.costFeasibleDecision instance.budget = true := by

  exact
    instance.runCostDecision_eq_true_iff_instanceDecision.trans
      instance.costDecision_eq_true_iff_tableDecision

/-- Executable Pareto decision agrees exactly with the semantic-table Pareto
decision. -/
theorem runParetoDecision_eq_true_iff_tableDecision :
    instance.runParetoDecision = true ↔
      table.paretoScalarFeasibleDecision
          instance.budget =
        true := by

  exact
    instance.runParetoDecision_eq_true_iff_instanceDecision.trans
      instance.paretoDecision_eq_true_iff_tableDecision

/-- Complete executable-verifier package for one finite encoded instance. -/
theorem executableVerifier_package :
    instance.exhaustiveCostVerifierSearch =
        instance.costCertificateCodes ∧
      instance.exhaustiveParetoVerifierSearch =
        instance.paretoCertificateCodes ∧
      instance.exhaustiveVerifierCallCount =
        2 ^ U.card ∧
      instance.exhaustiveCostVerifierSearch.card <=
        2 ^ U.card ∧
      instance.exhaustiveParetoVerifierSearch.card <=
        2 ^ U.card ∧
      (instance.runCostDecision = true ↔
        table.costFeasibleDecision instance.budget = true) ∧
      (instance.runParetoDecision = true ↔
        table.paretoScalarFeasibleDecision
            instance.budget =
          true) := by

  exact
    ⟨instance.exhaustiveCostVerifierSearch_eq,
      instance.exhaustiveParetoVerifierSearch_eq,
      instance.exhaustiveVerifierCallCount_eq,
      by
        calc
          instance.exhaustiveCostVerifierSearch.card <=
              instance.codeBound :=
            instance.exhaustiveCostVerifierSearch_card_le

          _ = 2 ^ U.card :=
            instance.codeBound_correct,
      by
        calc
          instance.exhaustiveParetoVerifierSearch.card <=
              instance.codeBound :=
            instance.exhaustiveParetoVerifierSearch_card_le

          _ = 2 ^ U.card :=
            instance.codeBound_correct,
      instance.runCostDecision_eq_true_iff_tableDecision,
      instance.runParetoDecision_eq_true_iff_tableDecision⟩

end ExecutableEncodedDecision

end CorrectedConcreteEncodedObservationSelectionInstance


namespace CorrectedConcreteObservationSelectionDecisionTable

section CanonicalExecutableEncodedInstance

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

/-- The executable ordinary decision of the canonical encoded instance agrees
with the original table decision. -/
theorem encodedObservationSelectionInstance_runCostDecision
    (budget : Nat) :
    (table.encodedObservationSelectionInstance
      budget).runCostDecision = true ↔
        table.costFeasibleDecision budget = true := by

  exact
    (table.encodedObservationSelectionInstance
      budget).runCostDecision_eq_true_iff_tableDecision

/-- The executable Pareto decision of the canonical encoded instance agrees
with the original table decision. -/
theorem encodedObservationSelectionInstance_runParetoDecision
    (budget : Nat) :
    (table.encodedObservationSelectionInstance
      budget).runParetoDecision = true ↔
        table.paretoScalarFeasibleDecision budget = true := by

  exact
    (table.encodedObservationSelectionInstance
      budget).runParetoDecision_eq_true_iff_tableDecision

/-- The exhaustive executable searches on the canonical instance are exactly
the previous dense verified-code searches. -/
theorem encodedObservationSelectionInstance_exhaustiveSearch_package
    (budget : Nat) :
    let instance :=
      table.encodedObservationSelectionInstance budget
    instance.exhaustiveCostVerifierSearch =
        table.verifiedDenseCostCertificateCodes budget ∧
      instance.exhaustiveParetoVerifierSearch =
        table.verifiedDenseParetoScalarCertificateCodes budget ∧
      instance.exhaustiveVerifierCallCount =
        2 ^ U.card := by

  let instance :=
    table.encodedObservationSelectionInstance budget

  exact
    ⟨by
        rw [instance.exhaustiveCostVerifierSearch_eq]

        rfl,
      by
        rw [instance.exhaustiveParetoVerifierSearch_eq]

        rfl,
      instance.exhaustiveVerifierCallCount_eq⟩

end CanonicalExecutableEncodedInstance

end CorrectedConcreteObservationSelectionDecisionTable


section EncodedExecutableVerifierFinalPackage

variable {α : Type u}
variable {ι : Type v}
variable {M : Type w}
variable [DecidableEq ι]
variable [Monoid M]
variable (obsFamily : ι → α → M)
variable (f : Nat)
variable (coordinateWeight : ι → Nat)
variable (U : Finset ι)

/-- Final positive-additive executable-verifier package.

At the exact semantic minimum rank, both exhaustive encoded decisions return
`true`.  The canonical least Pareto polynomial-witness code is accepted by the
finite executable verifier, belongs to the exhaustive Pareto search, and
decodes to the same Pareto-optimal certificate selected previously. -/
theorem
    correctedConcreteWorkingGrammar_observationSelectionEncodedExecutableVerifier_package
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
    let canonical :=
      table.denseParetoCanonicalPolynomialWitness
        verifierWork
        verifierCoeff
        verifierDegree
        hVerifierWork
        maxBudget
        hAccepted
    instance.runCostDecision = true ∧
      instance.runParetoDecision = true ∧
      instance.exhaustiveVerifierCallCount =
        2 ^ U.card ∧
      instance.exhaustiveCostVerifierSearch.card <=
        2 ^ U.card ∧
      instance.exhaustiveParetoVerifierSearch.card <=
        2 ^ U.card ∧
      instance.runParetoCertificateVerifier
          canonical.code =
        true ∧
      canonical.code ∈
        instance.exhaustiveParetoVerifierSearch ∧
      correctedConcreteDenseCertificateDecode
            U
            canonical.code =
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

  let canonical :=
    table.denseParetoCanonicalPolynomialWitness
      verifierWork
      verifierCoeff
      verifierDegree
      hVerifierWork
      maxBudget
      hAccepted

  have hInstancePackage :=
    correctedConcreteWorkingGrammar_observationSelectionEncodedInstance_package
      (z := z)
      obsFamily
      f
      coordinateWeight
      U
      language
      hTarget
      verifierWork
      verifierCoeff
      verifierDegree
      hVerifierWork

  have hRunCost :
      instance.runCostDecision = true :=
    instance.runCostDecision_eq_true_iff_instanceDecision.mpr
      hInstancePackage.2.1

  have hRunPareto :
      instance.runParetoDecision = true :=
    instance.runParetoDecision_eq_true_iff_instanceDecision.mpr
      hInstancePackage.2.2.1

  have hCanonicalStored :
      canonical.code ∈
        instance.paretoCertificateCodes :=
    hInstancePackage.2.2.2.2.2.2.2.1

  have hCanonicalBound :
      canonical.code < instance.codeBound :=
    ((instance.paretoCodes_correct canonical.code).mp
      hCanonicalStored).1

  have hCanonicalRun :
      instance.runParetoCertificateVerifier
          canonical.code =
        true :=
    (instance.runParetoCertificateVerifier_eq_true_iff
      canonical.code).mpr
      ⟨hCanonicalBound, hCanonicalStored⟩

  have hCanonicalSearch :
      canonical.code ∈
        instance.exhaustiveParetoVerifierSearch :=
    (instance.mem_exhaustiveParetoVerifierSearch_iff
      canonical.code).mpr
      ⟨hCanonicalBound, hCanonicalRun⟩

  exact
    ⟨hRunCost,
      hRunPareto,
      instance.exhaustiveVerifierCallCount_eq,
      by
        calc
          instance.exhaustiveCostVerifierSearch.card <=
              instance.codeBound :=
            instance.exhaustiveCostVerifierSearch_card_le

          _ = 2 ^ U.card :=
            instance.codeBound_correct,
      by
        calc
          instance.exhaustiveParetoVerifierSearch.card <=
              instance.codeBound :=
            instance.exhaustiveParetoVerifierSearch_card_le

          _ = 2 ^ U.card :=
            instance.codeBound_correct,
      hCanonicalRun,
      hCanonicalSearch,
      hInstancePackage.2.2.2.2.2.2.2.2⟩

end EncodedExecutableVerifierFinalPackage

end MCFG
