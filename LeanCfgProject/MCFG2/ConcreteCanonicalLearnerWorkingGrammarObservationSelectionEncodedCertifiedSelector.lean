/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG.ConcreteCanonicalLearnerWorkingGrammarObservationSelectionEncodedCanonicalSelector

/-!
# ConcreteCanonicalLearnerWorkingGrammarObservationSelectionEncodedCertifiedSelector.lean

The preceding files construct a bounded dense code universe, a checked decoder,
finite encoded verifier searches, and least accepted dense-code selectors.
This file packages the selected budget, selected dense code, decoded certificate,
and their correctness proofs into certificate-carrying output records.

Two records are provided.

* `CorrectedConcreteEncodedMinimumCostSelectionOutput` stores an ordinary
  minimum-cost selection.
* `CorrectedConcreteEncodedMinimumParetoScalarSelectionOutput` stores a
  minimum Pareto-scalar selection.

Each output carries:

```text
selected budget and proof of bounded budget minimality;
selected dense code and proof that it lies below 2 ^ U.card;
decoded finite observation subset;
checked decoding and re-encoding equations;
Boolean certificate verification;
certificate containment and cardinality bounds;
least-code optimality among all accepted codes at the selected budget.
```

The Pareto record additionally carries semantic Pareto optimality and the
scalar-budget inequality.  The final positive-additive theorem constructs this
record from the semantic decision table and identifies its selected budget and
certificate scalar exactly with the minimum positive-additive observation rank.

This is a proof-carrying finite selector layer.  It does not yet attach a
machine-time model to table construction or verification, and it makes no
NP-hardness claim.

No target grammar is supplied to any learner.
No `sorry`, `admit`, or `axiom` is used.
-/

namespace MCFG

universe u v w z

namespace CorrectedConcreteObservationSelectionDecisionTable

section EncodedMinimumCostOutput

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

/-- Certificate-carrying output of the encoded ordinary minimum-cost selector. -/
structure CorrectedConcreteEncodedMinimumCostSelectionOutput
    (maxBudget : Nat) where

  budget : Nat

  code : Nat

  certificate : Finset ι

  budget_le_max :
    budget <= maxBudget

  budget_decision :
    table.costFeasibleDecision budget = true

  certificate_verifies :
    table.verifiesCostCertificate budget certificate = true

  certificate_subset :
    certificate ⊆ U

  certificate_card_le :
    certificate.card <= U.card

  code_lt :
    code < 2 ^ U.card

  decode_eq :
    correctedConcreteDenseCertificateDecode U code =
      some certificate

  reencode_eq :
    correctedConcreteDenseCertificateCode U certificate = code

  budget_minimal :
    ∀ competingBudget : Nat,
      competingBudget <= maxBudget →
        table.costFeasibleDecision competingBudget = true →
          budget <= competingBudget

  code_minimal :
    ∀ competingCode : Nat,
      competingCode ∈
          table.verifiedDenseCostCertificateCodes budget →
        code <= competingCode

/-- The selected ordinary-cost budget, dense code, and decoded certificate,
packaged together with all bounded-minimum and checked-code proofs. -/
noncomputable def selectedEncodedMinimumCostSelectionOutput
    (maxBudget : Nat)
    (hAccepted :
      table.HasAcceptedCostBudgetUpTo maxBudget) :
    table.CorrectedConcreteEncodedMinimumCostSelectionOutput
      maxBudget where

  budget :=
    table.selectedMinimumAcceptedCostBudget
      maxBudget
      hAccepted

  code :=
    table.selectedCanonicalDenseMinimumCostCode
      maxBudget
      hAccepted

  certificate :=
    table.canonicalMinimumCostCertificate
      (correctedConcreteDenseCertificateCode U)
      maxBudget
      hAccepted

  budget_le_max :=
    (table.selectedMinimumAcceptedCostBudget_spec
      maxBudget
      hAccepted).1

  budget_decision :=
    (table.selectedMinimumAcceptedCostBudget_spec
      maxBudget
      hAccepted).2

  certificate_verifies :=
    table.canonicalMinimumCostCertificate_verifies
      (correctedConcreteDenseCertificateCode U)
      maxBudget
      hAccepted

  certificate_subset :=
    table.verifiedCostCertificate_subset
      (table.canonicalMinimumCostCertificate_verifies
        (correctedConcreteDenseCertificateCode U)
        maxBudget
        hAccepted)

  certificate_card_le :=
    table.verifiedCostCertificate_card_le
      (table.canonicalMinimumCostCertificate_verifies
        (correctedConcreteDenseCertificateCode U)
        maxBudget
        hAccepted)

  code_lt :=
    table.selectedCanonicalDenseMinimumCostCode_lt
      maxBudget
      hAccepted

  decode_eq :=
    table.selectedCanonicalDenseMinimumCostCode_decode
      maxBudget
      hAccepted

  reencode_eq :=
    correctedConcreteDenseCertificateCode_decode_eq
      U
      (table.selectedCanonicalDenseMinimumCostCode_decode
        maxBudget
        hAccepted)

  budget_minimal := by
    intro competingBudget hBudget hDecision

    exact
      table.selectedMinimumAcceptedCostBudget_le
        maxBudget
        hAccepted
        hBudget
        hDecision

  code_minimal := by
    intro competingCode hCompeting

    exact
      table.selectedCanonicalDenseMinimumCostCode_le
        maxBudget
        hAccepted
        hCompeting

/-- The certified ordinary-cost output uses exactly the previously selected
minimum budget. -/
theorem selectedEncodedMinimumCostSelectionOutput_budget_eq
    (maxBudget : Nat)
    (hAccepted :
      table.HasAcceptedCostBudgetUpTo maxBudget) :
    (table.selectedEncodedMinimumCostSelectionOutput
        maxBudget
        hAccepted).budget =
      table.selectedMinimumAcceptedCostBudget
        maxBudget
        hAccepted := by

  rfl

/-- The certified ordinary-cost output uses exactly the previously selected
least accepted dense code. -/
theorem selectedEncodedMinimumCostSelectionOutput_code_eq
    (maxBudget : Nat)
    (hAccepted :
      table.HasAcceptedCostBudgetUpTo maxBudget) :
    (table.selectedEncodedMinimumCostSelectionOutput
        maxBudget
        hAccepted).code =
      table.selectedCanonicalDenseMinimumCostCode
        maxBudget
        hAccepted := by

  rfl

/-- The certified ordinary-cost output decodes to exactly the previously
selected canonical minimum certificate. -/
theorem selectedEncodedMinimumCostSelectionOutput_certificate_eq
    (maxBudget : Nat)
    (hAccepted :
      table.HasAcceptedCostBudgetUpTo maxBudget) :
    (table.selectedEncodedMinimumCostSelectionOutput
        maxBudget
        hAccepted).certificate =
      table.canonicalMinimumCostCertificate
        (correctedConcreteDenseCertificateCode U)
        maxBudget
        hAccepted := by

  rfl

/-- Complete projection package for the encoded ordinary-cost output. -/
theorem selectedEncodedMinimumCostSelectionOutput_package
    (maxBudget : Nat)
    (hAccepted :
      table.HasAcceptedCostBudgetUpTo maxBudget) :
    let output :=
      table.selectedEncodedMinimumCostSelectionOutput
        maxBudget
        hAccepted
    output.budget <= maxBudget ∧
      table.costFeasibleDecision output.budget = true ∧
      table.verifiesCostCertificate
            output.budget
            output.certificate =
        true ∧
      output.certificate ⊆ U ∧
      output.certificate.card <= U.card ∧
      output.code < 2 ^ U.card ∧
      correctedConcreteDenseCertificateDecode U output.code =
        some output.certificate ∧
      correctedConcreteDenseCertificateCode U output.certificate =
        output.code ∧
      (∀ competingBudget : Nat,
        competingBudget <= maxBudget →
          table.costFeasibleDecision competingBudget = true →
            output.budget <= competingBudget) ∧
      (∀ competingCode : Nat,
        competingCode ∈
            table.verifiedDenseCostCertificateCodes output.budget →
          output.code <= competingCode) := by

  let output :=
    table.selectedEncodedMinimumCostSelectionOutput
      maxBudget
      hAccepted

  exact
    ⟨output.budget_le_max,
      output.budget_decision,
      output.certificate_verifies,
      output.certificate_subset,
      output.certificate_card_le,
      output.code_lt,
      output.decode_eq,
      output.reencode_eq,
      output.budget_minimal,
      output.code_minimal⟩

end EncodedMinimumCostOutput


section EncodedMinimumParetoScalarOutput

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

/-- Certificate-carrying output of the encoded minimum Pareto-scalar selector. -/
structure CorrectedConcreteEncodedMinimumParetoScalarSelectionOutput
    (maxBudget : Nat) where

  budget : Nat

  code : Nat

  certificate : Finset ι

  budget_le_max :
    budget <= maxBudget

  budget_decision :
    table.paretoScalarFeasibleDecision budget = true

  certificate_verifies :
    table.verifiesParetoScalarCertificate budget certificate = true

  pareto_optimal :
    CorrectedConcreteObservationSelectionParetoOptimal
      (z := z)
      obsFamily
      f
      selectionCost
      U
      language
      certificate

  scalar_le_budget :
    correctedConcreteObservationSelectionParetoScalarCost
          selectionCost
          certificate <=
      budget

  certificate_subset :
    certificate ⊆ U

  certificate_card_le :
    certificate.card <= U.card

  code_lt :
    code < 2 ^ U.card

  decode_eq :
    correctedConcreteDenseCertificateDecode U code =
      some certificate

  reencode_eq :
    correctedConcreteDenseCertificateCode U certificate = code

  budget_minimal :
    ∀ competingBudget : Nat,
      competingBudget <= maxBudget →
        table.paretoScalarFeasibleDecision competingBudget = true →
          budget <= competingBudget

  code_minimal :
    ∀ competingCode : Nat,
      competingCode ∈
          table.verifiedDenseParetoScalarCertificateCodes budget →
        code <= competingCode

/-- The selected Pareto-scalar budget, dense code, and decoded certificate,
packaged together with Pareto optimality and all minimum proofs. -/
noncomputable def selectedEncodedMinimumParetoScalarSelectionOutput
    (maxBudget : Nat)
    (hAccepted :
      table.HasAcceptedParetoScalarBudgetUpTo maxBudget) :
    table.CorrectedConcreteEncodedMinimumParetoScalarSelectionOutput
      maxBudget where

  budget :=
    table.selectedMinimumAcceptedParetoScalarBudget
      maxBudget
      hAccepted

  code :=
    table.selectedCanonicalDenseMinimumParetoScalarCode
      maxBudget
      hAccepted

  certificate :=
    table.canonicalMinimumParetoScalarCertificate
      (correctedConcreteDenseCertificateCode U)
      maxBudget
      hAccepted

  budget_le_max :=
    (table.selectedMinimumAcceptedParetoScalarBudget_spec
      maxBudget
      hAccepted).1

  budget_decision :=
    (table.selectedMinimumAcceptedParetoScalarBudget_spec
      maxBudget
      hAccepted).2

  certificate_verifies :=
    table.canonicalMinimumParetoScalarCertificate_verifies
      (correctedConcreteDenseCertificateCode U)
      maxBudget
      hAccepted

  pareto_optimal :=
    ((table.verifiesParetoScalarCertificate_eq_true_iff
      (table.selectedMinimumAcceptedParetoScalarBudget
        maxBudget
        hAccepted)
      (table.canonicalMinimumParetoScalarCertificate
        (correctedConcreteDenseCertificateCode U)
        maxBudget
        hAccepted)).mp
      (table.canonicalMinimumParetoScalarCertificate_verifies
        (correctedConcreteDenseCertificateCode U)
        maxBudget
        hAccepted)).1

  scalar_le_budget :=
    ((table.verifiesParetoScalarCertificate_eq_true_iff
      (table.selectedMinimumAcceptedParetoScalarBudget
        maxBudget
        hAccepted)
      (table.canonicalMinimumParetoScalarCertificate
        (correctedConcreteDenseCertificateCode U)
        maxBudget
        hAccepted)).mp
      (table.canonicalMinimumParetoScalarCertificate_verifies
        (correctedConcreteDenseCertificateCode U)
        maxBudget
        hAccepted)).2

  certificate_subset :=
    (((table.verifiesParetoScalarCertificate_eq_true_iff
      (table.selectedMinimumAcceptedParetoScalarBudget
        maxBudget
        hAccepted)
      (table.canonicalMinimumParetoScalarCertificate
        (correctedConcreteDenseCertificateCode U)
        maxBudget
        hAccepted)).mp
      (table.canonicalMinimumParetoScalarCertificate_verifies
        (correctedConcreteDenseCertificateCode U)
        maxBudget
        hAccepted)).1).1

  certificate_card_le :=
    table.verifiedParetoScalarCertificate_card_le
      (table.canonicalMinimumParetoScalarCertificate_verifies
        (correctedConcreteDenseCertificateCode U)
        maxBudget
        hAccepted)

  code_lt :=
    table.selectedCanonicalDenseMinimumParetoScalarCode_lt
      maxBudget
      hAccepted

  decode_eq :=
    table.selectedCanonicalDenseMinimumParetoScalarCode_decode
      maxBudget
      hAccepted

  reencode_eq :=
    correctedConcreteDenseCertificateCode_decode_eq
      U
      (table.selectedCanonicalDenseMinimumParetoScalarCode_decode
        maxBudget
        hAccepted)

  budget_minimal := by
    intro competingBudget hBudget hDecision

    exact
      table.selectedMinimumAcceptedParetoScalarBudget_le
        maxBudget
        hAccepted
        hBudget
        hDecision

  code_minimal := by
    intro competingCode hCompeting

    exact
      table.selectedCanonicalDenseMinimumParetoScalarCode_le
        maxBudget
        hAccepted
        hCompeting

/-- The certified Pareto-scalar output uses exactly the previously selected
minimum scalar budget. -/
theorem selectedEncodedMinimumParetoScalarSelectionOutput_budget_eq
    (maxBudget : Nat)
    (hAccepted :
      table.HasAcceptedParetoScalarBudgetUpTo maxBudget) :
    (table.selectedEncodedMinimumParetoScalarSelectionOutput
        maxBudget
        hAccepted).budget =
      table.selectedMinimumAcceptedParetoScalarBudget
        maxBudget
        hAccepted := by

  rfl

/-- The certified Pareto-scalar output uses exactly the previously selected
least accepted dense code. -/
theorem selectedEncodedMinimumParetoScalarSelectionOutput_code_eq
    (maxBudget : Nat)
    (hAccepted :
      table.HasAcceptedParetoScalarBudgetUpTo maxBudget) :
    (table.selectedEncodedMinimumParetoScalarSelectionOutput
        maxBudget
        hAccepted).code =
      table.selectedCanonicalDenseMinimumParetoScalarCode
        maxBudget
        hAccepted := by

  rfl

/-- The certified Pareto-scalar output decodes to exactly the previously
selected canonical minimum Pareto certificate. -/
theorem selectedEncodedMinimumParetoScalarSelectionOutput_certificate_eq
    (maxBudget : Nat)
    (hAccepted :
      table.HasAcceptedParetoScalarBudgetUpTo maxBudget) :
    (table.selectedEncodedMinimumParetoScalarSelectionOutput
        maxBudget
        hAccepted).certificate =
      table.canonicalMinimumParetoScalarCertificate
        (correctedConcreteDenseCertificateCode U)
        maxBudget
        hAccepted := by

  rfl

/-- Complete projection package for the encoded Pareto-scalar output. -/
theorem selectedEncodedMinimumParetoScalarSelectionOutput_package
    (maxBudget : Nat)
    (hAccepted :
      table.HasAcceptedParetoScalarBudgetUpTo maxBudget) :
    let output :=
      table.selectedEncodedMinimumParetoScalarSelectionOutput
        maxBudget
        hAccepted
    output.budget <= maxBudget ∧
      table.paretoScalarFeasibleDecision output.budget = true ∧
      table.verifiesParetoScalarCertificate
            output.budget
            output.certificate =
        true ∧
      CorrectedConcreteObservationSelectionParetoOptimal
        (z := z)
        obsFamily
        f
        selectionCost
        U
        language
        output.certificate ∧
      correctedConcreteObservationSelectionParetoScalarCost
            selectionCost
            output.certificate <=
        output.budget ∧
      output.certificate ⊆ U ∧
      output.certificate.card <= U.card ∧
      output.code < 2 ^ U.card ∧
      correctedConcreteDenseCertificateDecode U output.code =
        some output.certificate ∧
      correctedConcreteDenseCertificateCode U output.certificate =
        output.code ∧
      (∀ competingBudget : Nat,
        competingBudget <= maxBudget →
          table.paretoScalarFeasibleDecision competingBudget = true →
            output.budget <= competingBudget) ∧
      (∀ competingCode : Nat,
        competingCode ∈
            table.verifiedDenseParetoScalarCertificateCodes output.budget →
          output.code <= competingCode) := by

  let output :=
    table.selectedEncodedMinimumParetoScalarSelectionOutput
      maxBudget
      hAccepted

  exact
    ⟨output.budget_le_max,
      output.budget_decision,
      output.certificate_verifies,
      output.pareto_optimal,
      output.scalar_le_budget,
      output.certificate_subset,
      output.certificate_card_le,
      output.code_lt,
      output.decode_eq,
      output.reencode_eq,
      output.budget_minimal,
      output.code_minimal⟩

end EncodedMinimumParetoScalarOutput

end CorrectedConcreteObservationSelectionDecisionTable


section EncodedCertifiedSelectorFinalPackage

variable {α : Type u}
variable {ι : Type v}
variable {M : Type w}
variable [DecidableEq ι]
variable [Monoid M]
variable (obsFamily : ι → α → M)
variable (f : Nat)
variable (coordinateWeight : ι → Nat)
variable (U : Finset ι)

/-- Final positive-additive certificate-carrying encoded selector package.
The selected output carries the exact minimum positive-additive rank, a
Pareto-optimal observation subset realizing that rank, and a least accepted
dense code for the subset. -/
theorem
    correctedConcreteWorkingGrammar_observationSelectionEncodedCertifiedSelector_package
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
    let maxBudget :=
      correctedConcreteObservationSelectionPositiveAdditiveCost
        coordinateWeight
        U
    let hBound :
        ambientTargetObservationSelectionPositiveAdditiveMinimumCost
              (z := z)
              obsFamily
              f
              coordinateWeight
              U
              hTarget <=
            maxBudget :=
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
    let output :=
      table.selectedEncodedMinimumParetoScalarSelectionOutput
        maxBudget
        hAccepted
    output.budget =
        ambientTargetObservationSelectionPositiveAdditiveMinimumCost
          (z := z)
          obsFamily
          f
          coordinateWeight
          U
          hTarget ∧
      correctedConcreteObservationSelectionParetoScalarCost
            (correctedConcreteObservationSelectionAdditiveCost
              coordinateWeight)
            output.certificate =
        output.budget ∧
      CorrectedConcreteObservationSelectionParetoOptimal
        (z := z)
        obsFamily
        f
        (correctedConcreteObservationSelectionAdditiveCost
          coordinateWeight)
        U
        language
        output.certificate ∧
      output.code < 2 ^ U.card ∧
      correctedConcreteDenseCertificateDecode U output.code =
        some output.certificate ∧
      (∀ competingCode : Nat,
        competingCode ∈
            table.verifiedDenseParetoScalarCertificateCodes
              output.budget →
          output.code <= competingCode) := by

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

  let hBound :
      ambientTargetObservationSelectionPositiveAdditiveMinimumCost
            (z := z)
            obsFamily
            f
            coordinateWeight
            U
            hTarget <=
          maxBudget :=
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

  let output :=
    table.selectedEncodedMinimumParetoScalarSelectionOutput
      maxBudget
      hAccepted

  have hBudgetEq :
      output.budget =
        ambientTargetObservationSelectionPositiveAdditiveMinimumCost
          (z := z)
          obsFamily
          f
          coordinateWeight
          U
          hTarget := by

    change
      table.selectedMinimumAcceptedParetoScalarBudget
            maxBudget
            hAccepted =
        ambientTargetObservationSelectionPositiveAdditiveMinimumCost
          (z := z)
          obsFamily
          f
          coordinateWeight
          U
          hTarget

    exact
      table.selectedMinimumAcceptedParetoScalarBudget_eq_positiveAdditiveMinimum
        hTarget
        maxBudget
        hBound

  have hCanonical :=
    correctedConcreteWorkingGrammar_observationSelectionCanonicalMinimumCertificate_package
      (z := z)
      obsFamily
      f
      coordinateWeight
      U
      (correctedConcreteDenseCertificateCode U)
      language
      hTarget

  have hScalarEq :
      correctedConcreteObservationSelectionParetoScalarCost
            (correctedConcreteObservationSelectionAdditiveCost
              coordinateWeight)
            output.certificate =
        output.budget := by

    rw [hBudgetEq]

    exact hCanonical.2.1

  exact
    ⟨hBudgetEq,
      hScalarEq,
      output.pareto_optimal,
      output.code_lt,
      output.decode_eq,
      output.code_minimal⟩

end EncodedCertifiedSelectorFinalPackage

end MCFG
