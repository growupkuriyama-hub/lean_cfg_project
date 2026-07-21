/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG.ConcreteCanonicalLearnerWorkingGrammarObservationSelectionEncodedCanonicalPolynomialWitness

/-!
# ConcreteCanonicalLearnerWorkingGrammarObservationSelectionEncodedInstance.lean

The preceding observation-selection development constructs

* a proof-carrying semantic decision table;
* dense natural-number certificate codes;
* finite verified code searches;
* total optimization procedures;
* abstract polynomial verifier machines;
* canonical least machine witnesses.

The remaining executable-complexity route should no longer expose the original
finite families of selected subsets as its input.  This file therefore packages
one budgeted query as a finite encoded instance.

An encoded instance stores only

```text
the queried budget;
an exclusive natural-number certificate-code bound;
the finite ordinary-cost accepted-code table;
the finite Pareto-scalar accepted-code table;
proofs identifying table membership with the existing Boolean code verifiers.
```

The canonical encoded instance has code universe size exactly

```text
2 ^ U.card.
```

All decisions below inspect only the stored finite natural-number code tables.
The semantic observation-selection decision table occurs only in the
proof-carrying correctness fields.

We prove:

* every stored code lies below the declared bound;
* both stored code families have cardinality at most the declared bound;
* encoded ordinary and Pareto decisions are sound and complete;
* the encoded decisions agree exactly with the preceding table decisions;
* the canonical encoded instance at the semantic positive-additive minimum rank
  has nonempty ordinary and Pareto witness families;
* its Pareto family contains the previously selected canonical polynomial
  witness code.

This is the finite encoded-input layer for the next executable verifier.  It
does not yet serialize the observation family, grammar/language representation,
or semantic decision-table construction itself.  Consequently no formal NP
membership or hardness claim is made here.

No target grammar is supplied to any learner.
No `sorry`, `admit`, or `axiom` is used.
-/

namespace MCFG

universe u v w z


section EncodedObservationSelectionInstanceDefinition

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

/-- Finite proof-carrying encoded input for one budgeted
observation-selection query.

The computational fields are natural numbers and finite sets of natural
numbers.  The correctness fields connect those data to the already verified
dense Boolean certificate verifiers. -/
structure CorrectedConcreteEncodedObservationSelectionInstance where

  budget : Nat

  codeBound : Nat

  costCertificateCodes : Finset Nat

  paretoCertificateCodes : Finset Nat

  codeBound_correct :
    codeBound = 2 ^ U.card

  costCodes_correct :
    ∀ code : Nat,
      code ∈ costCertificateCodes ↔
        code < codeBound ∧
          table.verifiesDenseCostCertificateCode
              budget
              code =
            true

  paretoCodes_correct :
    ∀ code : Nat,
      code ∈ paretoCertificateCodes ↔
        code < codeBound ∧
          table.verifiesDenseParetoScalarCertificateCode
              budget
              code =
            true

end EncodedObservationSelectionInstanceDefinition


namespace CorrectedConcreteEncodedObservationSelectionInstance

section BasicEncodedInstanceOperations

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

/-- The explicit finite natural-number code universe declared by the encoded
instance. -/
def codeUniverse : Finset Nat :=
  Finset.range instance.codeBound

/-- Encoded ordinary-cost decision.  It reads only the stored finite natural
code family. -/
def costDecision : Bool :=
  decide instance.costCertificateCodes.Nonempty

/-- Encoded Pareto-scalar decision.  It reads only the stored finite natural
code family. -/
def paretoDecision : Bool :=
  decide instance.paretoCertificateCodes.Nonempty

@[simp]
theorem mem_codeUniverse_iff
    (code : Nat) :
    code ∈ instance.codeUniverse ↔
      code < instance.codeBound := by

  simp [codeUniverse]

/-- Every stored ordinary-cost code lies in the declared finite universe. -/
theorem costCertificateCodes_subset_codeUniverse :
    instance.costCertificateCodes ⊆
      instance.codeUniverse := by

  intro code hCode

  exact
    (instance.mem_codeUniverse_iff code).mpr
      ((instance.costCodes_correct code).mp hCode).1

/-- Every stored Pareto-scalar code lies in the declared finite universe. -/
theorem paretoCertificateCodes_subset_codeUniverse :
    instance.paretoCertificateCodes ⊆
      instance.codeUniverse := by

  intro code hCode

  exact
    (instance.mem_codeUniverse_iff code).mpr
      ((instance.paretoCodes_correct code).mp hCode).1

/-- Exact size of the declared code universe. -/
theorem codeUniverse_card :
    instance.codeUniverse.card =
      instance.codeBound := by

  simp [codeUniverse]

/-- Ordinary accepted-code family cardinality bound. -/
theorem costCertificateCodes_card_le :
    instance.costCertificateCodes.card <=
      instance.codeBound := by

  calc
    instance.costCertificateCodes.card <=
        instance.codeUniverse.card :=
      Finset.card_le_card
        instance.costCertificateCodes_subset_codeUniverse

    _ = instance.codeBound :=
      instance.codeUniverse_card

/-- Pareto accepted-code family cardinality bound. -/
theorem paretoCertificateCodes_card_le :
    instance.paretoCertificateCodes.card <=
      instance.codeBound := by

  calc
    instance.paretoCertificateCodes.card <=
        instance.codeUniverse.card :=
      Finset.card_le_card
        instance.paretoCertificateCodes_subset_codeUniverse

    _ = instance.codeBound :=
      instance.codeUniverse_card

/-- Exact existential characterization of the encoded ordinary-cost decision. -/
theorem costDecision_eq_true_iff_exists_code :
    instance.costDecision = true ↔
      ∃ code : Nat,
        code ∈ instance.costCertificateCodes := by

  unfold costDecision

  rw [decide_eq_true_eq]

  rfl

/-- Exact existential characterization of the encoded Pareto decision. -/
theorem paretoDecision_eq_true_iff_exists_code :
    instance.paretoDecision = true ↔
      ∃ code : Nat,
        code ∈ instance.paretoCertificateCodes := by

  unfold paretoDecision

  rw [decide_eq_true_eq]

  rfl

/-- Soundness and completeness of the encoded ordinary-cost decision with
respect to the dense Boolean verifier. -/
theorem costDecision_eq_true_iff_verified :
    instance.costDecision = true ↔
      ∃ code : Nat,
        code < instance.codeBound ∧
          table.verifiesDenseCostCertificateCode
              instance.budget
              code =
            true := by

  rw [instance.costDecision_eq_true_iff_exists_code]

  constructor

  · rintro ⟨code, hCode⟩

    exact
      ⟨code,
        (instance.costCodes_correct code).mp hCode⟩

  · rintro ⟨code, hCode⟩

    exact
      ⟨code,
        (instance.costCodes_correct code).mpr hCode⟩

/-- Soundness and completeness of the encoded Pareto-scalar decision with
respect to the dense Boolean verifier. -/
theorem paretoDecision_eq_true_iff_verified :
    instance.paretoDecision = true ↔
      ∃ code : Nat,
        code < instance.codeBound ∧
          table.verifiesDenseParetoScalarCertificateCode
              instance.budget
              code =
            true := by

  rw [instance.paretoDecision_eq_true_iff_exists_code]

  constructor

  · rintro ⟨code, hCode⟩

    exact
      ⟨code,
        (instance.paretoCodes_correct code).mp hCode⟩

  · rintro ⟨code, hCode⟩

    exact
      ⟨code,
        (instance.paretoCodes_correct code).mpr hCode⟩

/-- The encoded ordinary-cost decision agrees exactly with the original
finite-table decision at the stored budget. -/
theorem costDecision_eq_true_iff_tableDecision :
    instance.costDecision = true ↔
      table.costFeasibleDecision instance.budget = true := by

  rw [instance.costDecision_eq_true_iff_exists_code]

  constructor

  · rintro ⟨code, hCode⟩

    exact
      (table.costFeasibleDecision_eq_true_iff_exists_verifiedDenseCode
        instance.budget).mpr
        ⟨code,
          (table.mem_verifiedDenseCostCertificateCodes_iff
            instance.budget
            code).mpr
            (by
              simpa [instance.codeBound_correct] using
                (instance.costCodes_correct code).mp hCode)⟩

  · intro hDecision

    rcases
        (table.costFeasibleDecision_eq_true_iff_exists_verifiedDenseCode
          instance.budget).mp
          hDecision with
      ⟨code, hCode⟩

    have hCodeParts :=
      (table.mem_verifiedDenseCostCertificateCodes_iff
        instance.budget
        code).mp
        hCode

    exact
      ⟨code,
        (instance.costCodes_correct code).mpr
          (by
            simpa [instance.codeBound_correct] using hCodeParts)⟩

/-- The encoded Pareto-scalar decision agrees exactly with the original
finite-table decision at the stored budget. -/
theorem paretoDecision_eq_true_iff_tableDecision :
    instance.paretoDecision = true ↔
      table.paretoScalarFeasibleDecision instance.budget = true := by

  rw [instance.paretoDecision_eq_true_iff_exists_code]

  constructor

  · rintro ⟨code, hCode⟩

    exact
      (table.paretoScalarFeasibleDecision_eq_true_iff_exists_verifiedDenseCode
        instance.budget).mpr
        ⟨code,
          (table.mem_verifiedDenseParetoScalarCertificateCodes_iff
            instance.budget
            code).mpr
            (by
              simpa [instance.codeBound_correct] using
                (instance.paretoCodes_correct code).mp hCode)⟩

  · intro hDecision

    rcases
        (table.paretoScalarFeasibleDecision_eq_true_iff_exists_verifiedDenseCode
          instance.budget).mp
          hDecision with
      ⟨code, hCode⟩

    have hCodeParts :=
      (table.mem_verifiedDenseParetoScalarCertificateCodes_iff
        instance.budget
        code).mp
        hCode

    exact
      ⟨code,
        (instance.paretoCodes_correct code).mpr
          (by
            simpa [instance.codeBound_correct] using hCodeParts)⟩

/-- Every encoded ordinary accepted code decodes to a checked subset
certificate contained in the ambient coordinate universe. -/
theorem costCode_decode_package
    {code : Nat}
    (hCode :
      code ∈ instance.costCertificateCodes) :
    ∃ certificate : Finset ι,
      correctedConcreteDenseCertificateDecode U code =
          some certificate ∧
        table.verifiesCostCertificate
            instance.budget
            certificate =
          true ∧
        certificate ⊆ U := by

  have hVerify :
      table.verifiesDenseCostCertificateCode
            instance.budget
            code =
          true :=
    ((instance.costCodes_correct code).mp hCode).2

  exact
    table.verifiesDenseCostCertificateCode_decode_package
      instance.budget
      hVerify

/-- Every encoded Pareto accepted code decodes to a checked Pareto subset
certificate contained in the ambient coordinate universe. -/
theorem paretoCode_decode_package
    {code : Nat}
    (hCode :
      code ∈ instance.paretoCertificateCodes) :
    ∃ certificate : Finset ι,
      correctedConcreteDenseCertificateDecode U code =
          some certificate ∧
        table.verifiesParetoScalarCertificate
            instance.budget
            certificate =
          true ∧
        certificate ⊆ U := by

  have hVerify :
      table.verifiesDenseParetoScalarCertificateCode
            instance.budget
            code =
          true :=
    ((instance.paretoCodes_correct code).mp hCode).2

  exact
    table.verifiesDenseParetoScalarCertificateCode_decode_package
      instance.budget
      hVerify

/-- Finite encoded-instance summary. -/
theorem finite_package :
    instance.codeBound = 2 ^ U.card ∧
      instance.costCertificateCodes.card <=
        instance.codeBound ∧
      instance.paretoCertificateCodes.card <=
        instance.codeBound ∧
      (instance.costDecision = true ↔
        table.costFeasibleDecision instance.budget = true) ∧
      (instance.paretoDecision = true ↔
        table.paretoScalarFeasibleDecision
            instance.budget =
          true) := by

  exact
    ⟨instance.codeBound_correct,
      instance.costCertificateCodes_card_le,
      instance.paretoCertificateCodes_card_le,
      instance.costDecision_eq_true_iff_tableDecision,
      instance.paretoDecision_eq_true_iff_tableDecision⟩

end BasicEncodedInstanceOperations

end CorrectedConcreteEncodedObservationSelectionInstance


namespace CorrectedConcreteObservationSelectionDecisionTable

section CanonicalEncodedInstance

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

/-- Canonical finite encoded instance extracted from the existing dense code
searches at one budget. -/
noncomputable def encodedObservationSelectionInstance
    (budget : Nat) :
    CorrectedConcreteEncodedObservationSelectionInstance
      table :=
  {
    budget := budget

    codeBound := 2 ^ U.card

    costCertificateCodes :=
      table.verifiedDenseCostCertificateCodes budget

    paretoCertificateCodes :=
      table.verifiedDenseParetoScalarCertificateCodes budget

    codeBound_correct := rfl

    costCodes_correct := by
      intro code

      exact
        table.mem_verifiedDenseCostCertificateCodes_iff
          budget
          code

    paretoCodes_correct := by
      intro code

      exact
        table.mem_verifiedDenseParetoScalarCertificateCodes_iff
          budget
          code
  }

/-- The canonical encoded instance stores exactly the existing ordinary dense
certificate search. -/
theorem encodedObservationSelectionInstance_costCodes
    (budget : Nat) :
    (table.encodedObservationSelectionInstance
      budget).costCertificateCodes =
        table.verifiedDenseCostCertificateCodes budget := by

  rfl

/-- The canonical encoded instance stores exactly the existing Pareto dense
certificate search. -/
theorem encodedObservationSelectionInstance_paretoCodes
    (budget : Nat) :
    (table.encodedObservationSelectionInstance
      budget).paretoCertificateCodes =
        table.verifiedDenseParetoScalarCertificateCodes budget := by

  rfl

/-- Its encoded ordinary decision is exactly the table decision. -/
theorem encodedObservationSelectionInstance_costDecision
    (budget : Nat) :
    (table.encodedObservationSelectionInstance
      budget).costDecision = true ↔
        table.costFeasibleDecision budget = true := by

  exact
    (table.encodedObservationSelectionInstance
      budget).costDecision_eq_true_iff_tableDecision

/-- Its encoded Pareto decision is exactly the table decision. -/
theorem encodedObservationSelectionInstance_paretoDecision
    (budget : Nat) :
    (table.encodedObservationSelectionInstance
      budget).paretoDecision = true ↔
        table.paretoScalarFeasibleDecision budget = true := by

  exact
    (table.encodedObservationSelectionInstance
      budget).paretoDecision_eq_true_iff_tableDecision

/-- Complete canonical encoded-instance package at an arbitrary budget. -/
theorem encodedObservationSelectionInstance_package
    (budget : Nat) :
    let instance :=
      table.encodedObservationSelectionInstance budget
    instance.codeBound = 2 ^ U.card ∧
      instance.costCertificateCodes =
        table.verifiedDenseCostCertificateCodes budget ∧
      instance.paretoCertificateCodes =
        table.verifiedDenseParetoScalarCertificateCodes budget ∧
      instance.costCertificateCodes.card <=
        2 ^ U.card ∧
      instance.paretoCertificateCodes.card <=
        2 ^ U.card ∧
      (instance.costDecision = true ↔
        table.costFeasibleDecision budget = true) ∧
      (instance.paretoDecision = true ↔
        table.paretoScalarFeasibleDecision budget = true) := by

  let instance :=
    table.encodedObservationSelectionInstance budget

  exact
    ⟨rfl,
      rfl,
      rfl,
      by
        simpa [instance] using
          instance.costCertificateCodes_card_le,
      by
        simpa [instance] using
          instance.paretoCertificateCodes_card_le,
      instance.costDecision_eq_true_iff_tableDecision,
      instance.paretoDecision_eq_true_iff_tableDecision⟩

end CanonicalEncodedInstance

end CorrectedConcreteObservationSelectionDecisionTable


section EncodedInstanceFinalPackage

variable {α : Type u}
variable {ι : Type v}
variable {M : Type w}
variable [DecidableEq ι]
variable [Monoid M]
variable (obsFamily : ι → α → M)
variable (f : Nat)
variable (coordinateWeight : ι → Nat)
variable (U : Finset ι)

/-- Final positive-additive encoded-instance package.

At the exact semantic minimum rank, the canonical finite encoded instance has
positive ordinary and Pareto decisions.  Both stored accepted-code families are
nonempty and have at most `2 ^ U.card` entries.  The canonical least Pareto
polynomial-witness code from the previous file is a member of the stored
Pareto-code family. -/
theorem
    correctedConcreteWorkingGrammar_observationSelectionEncodedInstance_package
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
    instance.codeBound = 2 ^ U.card ∧
      instance.costDecision = true ∧
      instance.paretoDecision = true ∧
      instance.costCertificateCodes.Nonempty ∧
      instance.paretoCertificateCodes.Nonempty ∧
      instance.costCertificateCodes.card <=
        2 ^ U.card ∧
      instance.paretoCertificateCodes.card <=
        2 ^ U.card ∧
      canonical.code ∈
        instance.paretoCertificateCodes ∧
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

  have hCostTable :
      table.costFeasibleDecision minimumRank = true := by

    change
      table.minimumRankAtMostDecision minimumRank = true

    exact
      (table.minimumRankAtMostDecision_eq_true_iff
        hTarget
        minimumRank).mpr
        (Nat.le_refl minimumRank)

  have hParetoTable :
      table.paretoScalarFeasibleDecision minimumRank = true := by

    exact
      (table.positiveAdditiveParetoScalarDecision_eq_true_iff_minimumRank_le
        hTarget
        minimumRank).mpr
        (Nat.le_refl minimumRank)

  have hCostInstance :
      instance.costDecision = true :=
    (instance.costDecision_eq_true_iff_tableDecision).mpr
      hCostTable

  have hParetoInstance :
      instance.paretoDecision = true :=
    (instance.paretoDecision_eq_true_iff_tableDecision).mpr
      hParetoTable

  have hCostNonempty :
      instance.costCertificateCodes.Nonempty := by

    exact
      (instance.costDecision_eq_true_iff_exists_code).mp
        hCostInstance

  have hParetoNonempty :
      instance.paretoCertificateCodes.Nonempty := by

    exact
      (instance.paretoDecision_eq_true_iff_exists_code).mp
        hParetoInstance

  have hBudgetEq :
      table.selectedMinimumAcceptedParetoScalarBudget
            maxBudget
            hAccepted =
        minimumRank :=
    table.selectedMinimumAcceptedParetoScalarBudget_eq_positiveAdditiveMinimum
      hTarget
      maxBudget
      hBound

  have hCanonicalCodeEq :
      canonical.code =
        table.selectedCanonicalDenseMinimumParetoScalarCode
          maxBudget
          hAccepted := by

    exact
      table.denseParetoCanonicalPolynomialWitness_code
        verifierWork
        verifierCoeff
        verifierDegree
        hVerifierWork
        maxBudget
        hAccepted

  have hCanonicalCodeLtTwoPow :
      canonical.code < 2 ^ U.card := by

    rw [hCanonicalCodeEq]

    exact
      table.selectedCanonicalDenseMinimumParetoScalarCode_lt
        maxBudget
        hAccepted

  have hCanonicalCodeLt :
      canonical.code < instance.codeBound := by

    rw [instance.codeBound_correct]

    exact hCanonicalCodeLtTwoPow

  have hCanonicalVerifyAtSelectedBudget :
      table.verifiesDenseParetoScalarCertificateCode
            (table.selectedMinimumAcceptedParetoScalarBudget
              maxBudget
              hAccepted)
            canonical.code =
          true := by

    rw [hCanonicalCodeEq]

    exact
      table.selectedCanonicalDenseMinimumParetoScalarCode_verifies
        maxBudget
        hAccepted

  have hCanonicalVerify :
      table.verifiesDenseParetoScalarCertificateCode
            minimumRank
            canonical.code =
          true := by

    rw [← hBudgetEq]

    exact hCanonicalVerifyAtSelectedBudget

  have hCanonicalMem :
      canonical.code ∈
        instance.paretoCertificateCodes :=
    (instance.paretoCodes_correct canonical.code).mpr
      ⟨hCanonicalCodeLt,
        hCanonicalVerify⟩

  exact
    ⟨rfl,
      hCostInstance,
      hParetoInstance,
      hCostNonempty,
      hParetoNonempty,
      by
        simpa [instance] using
          instance.costCertificateCodes_card_le,
      by
        simpa [instance] using
          instance.paretoCertificateCodes_card_le,
      hCanonicalMem,
      by
        rw [hCanonicalCodeEq]

        exact
          table.selectedCanonicalDenseMinimumParetoScalarCode_decode
            maxBudget
            hAccepted⟩

end EncodedInstanceFinalPackage

end MCFG
