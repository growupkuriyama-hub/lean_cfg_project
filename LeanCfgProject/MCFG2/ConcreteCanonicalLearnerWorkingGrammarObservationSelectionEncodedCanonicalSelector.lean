/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG2.ConcreteCanonicalLearnerWorkingGrammarObservationSelectionEncodedCertificateSearch

/-!
# ConcreteCanonicalLearnerWorkingGrammarObservationSelectionEncodedCanonicalSelector.lean

The preceding file replaces direct powerset search by a bounded natural-number
search over the exact dense code universe

```text
0, 1, ..., 2 ^ U.card - 1.
```

It also proves that the code of the previously constructed canonical minimum
certificate belongs to the encoded verifier search.  This file turns that
membership result into an encoded canonical selector theorem.

The first missing algebraic fact is the converse round trip: whenever a dense
code successfully decodes to a certificate, re-encoding that certificate gives
back the original code.  Together with the least-code property of the canonical
certificate, this implies that its dense code is no larger than every accepted
encoded competitor at the selected minimum budget.

For ordinary cost and Pareto scalar cost we define explicit selected dense
codes and prove:

```text
selected code < 2 ^ U.card;
selected code decodes to the canonical minimum certificate;
selected code is accepted at the selected minimum budget;
selected code belongs to the finite encoded search;
selected code is no larger than every accepted encoded competitor;
any accepted competitor below the selected code is equal to it;
the canonical code search is exactly the singleton containing the selector.
```

The final positive-additive package connects the encoded selector to the
semantic minimum positive-additive rank and to a Pareto-optimal selected
observation interface.

The dense equivalence still uses `Fintype.equivFin`, so this is a canonical
finite encoded selector theorem rather than a machine-time or NP-membership
theorem.  No hardness claim is made here.

No target grammar is supplied to any learner.
No `sorry`, `admit`, or `axiom` is used.
-/

namespace MCFG

universe u v w z

section DenseCertificateDecodeReencode

variable {ι : Type v}
variable [DecidableEq ι]

/-- Successful dense decoding is also a left inverse: re-encoding the decoded
certificate recovers the original bounded natural-number code. -/
theorem correctedConcreteDenseCertificateCode_decode_eq
    (U : Finset ι)
    {code : Nat}
    {certificate : Finset ι}
    (hDecode :
      correctedConcreteDenseCertificateDecode U code =
        some certificate) :
    correctedConcreteDenseCertificateCode U certificate = code := by

  by_cases hCode : code < Fintype.card (Finset ↥U)

  · have hLift :
        correctedConcreteDenseCertificateLift U
            ((Fintype.equivFin (Finset ↥U)).symm
              ⟨code, hCode⟩) =
          certificate := by

      rw [
        correctedConcreteDenseCertificateDecode,
        dif_pos hCode
      ] at hDecode

      exact Option.some.inj hDecode

    have hRestriction :
        correctedConcreteDenseCertificateRestriction U certificate =
          (Fintype.equivFin (Finset ↥U)).symm
            ⟨code, hCode⟩ := by

      rw [← hLift]

      exact
        correctedConcreteDenseCertificateRestriction_lift_eq
          U
          ((Fintype.equivFin (Finset ↥U)).symm
            ⟨code, hCode⟩)

    rw [
      correctedConcreteDenseCertificateCode,
      hRestriction,
      Equiv.apply_symm_apply
    ]

  · rw [
      correctedConcreteDenseCertificateDecode,
      dif_neg hCode
    ] at hDecode

    simp at hDecode

/-- A successful decoding lies in the exact dense range and is uniquely
recovered by its re-encoding. -/
theorem correctedConcreteDenseCertificateDecode_reencode_package
    (U : Finset ι)
    {code : Nat}
    {certificate : Finset ι}
    (hDecode :
      correctedConcreteDenseCertificateDecode U code =
        some certificate) :
    certificate ⊆ U ∧
      correctedConcreteDenseCertificateCode U certificate = code ∧
      code < 2 ^ U.card := by

  have hSubset : certificate ⊆ U :=
    correctedConcreteDenseCertificateDecode_subset
      U
      hDecode

  have hCodeEq :
      correctedConcreteDenseCertificateCode U certificate = code :=
    correctedConcreteDenseCertificateCode_decode_eq
      U
      hDecode

  exact
    ⟨hSubset,
      hCodeEq,
      hCodeEq ▸
        correctedConcreteDenseCertificateCode_lt_two_pow
          U
          certificate⟩

end DenseCertificateDecodeReencode


namespace CorrectedConcreteObservationSelectionDecisionTable

section EncodedMinimumCostSelector

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

/-- The selected encoded canonical ordinary-cost certificate code. -/
noncomputable def selectedCanonicalDenseMinimumCostCode
    (maxBudget : Nat)
    (hAccepted :
      table.HasAcceptedCostBudgetUpTo maxBudget) :
    Nat :=
  correctedConcreteDenseCertificateCode U
    (table.canonicalMinimumCostCertificate
      (correctedConcreteDenseCertificateCode U)
      maxBudget
      hAccepted)

/-- The selected ordinary-cost code lies in the exact dense universe. -/
theorem selectedCanonicalDenseMinimumCostCode_lt
    (maxBudget : Nat)
    (hAccepted :
      table.HasAcceptedCostBudgetUpTo maxBudget) :
    table.selectedCanonicalDenseMinimumCostCode
          maxBudget
          hAccepted <
        2 ^ U.card := by

  exact
    correctedConcreteDenseCertificateCode_lt_two_pow
      U
      (table.canonicalMinimumCostCertificate
        (correctedConcreteDenseCertificateCode U)
        maxBudget
        hAccepted)

/-- The selected ordinary-cost code decodes exactly to the selected canonical
minimum certificate. -/
theorem selectedCanonicalDenseMinimumCostCode_decode
    (maxBudget : Nat)
    (hAccepted :
      table.HasAcceptedCostBudgetUpTo maxBudget) :
    correctedConcreteDenseCertificateDecode U
          (table.selectedCanonicalDenseMinimumCostCode
            maxBudget
            hAccepted) =
        some
          (table.canonicalMinimumCostCertificate
            (correctedConcreteDenseCertificateCode U)
            maxBudget
            hAccepted) := by

  have hVerify :=
    table.canonicalMinimumCostCertificate_verifies
      (correctedConcreteDenseCertificateCode U)
      maxBudget
      hAccepted

  have hSubset :
      table.canonicalMinimumCostCertificate
            (correctedConcreteDenseCertificateCode U)
            maxBudget
            hAccepted ⊆
        U :=
    table.verifiedCostCertificate_subset hVerify

  exact
    correctedConcreteDenseCertificateDecode_encode_of_subset
      U
      hSubset

/-- The selected ordinary-cost code is accepted by the encoded verifier at the
selected minimum budget. -/
theorem selectedCanonicalDenseMinimumCostCode_verifies
    (maxBudget : Nat)
    (hAccepted :
      table.HasAcceptedCostBudgetUpTo maxBudget) :
    table.verifiesDenseCostCertificateCode
          (table.selectedMinimumAcceptedCostBudget
            maxBudget
            hAccepted)
          (table.selectedCanonicalDenseMinimumCostCode
            maxBudget
            hAccepted) =
        true := by

  exact
    table.verifiesDenseCostCertificateCode_encode_of_verify
      (table.selectedMinimumAcceptedCostBudget
        maxBudget
        hAccepted)
      (table.canonicalMinimumCostCertificate_verifies
        (correctedConcreteDenseCertificateCode U)
        maxBudget
        hAccepted)

/-- The selected ordinary-cost code belongs to the finite encoded search. -/
theorem selectedCanonicalDenseMinimumCostCode_mem
    (maxBudget : Nat)
    (hAccepted :
      table.HasAcceptedCostBudgetUpTo maxBudget) :
    table.selectedCanonicalDenseMinimumCostCode
          maxBudget
          hAccepted ∈
        table.verifiedDenseCostCertificateCodes
          (table.selectedMinimumAcceptedCostBudget
            maxBudget
            hAccepted) := by

  exact
    table.canonicalMinimumCostCertificate_denseCode_mem_verifiedSearch
      maxBudget
      hAccepted

/-- The selected ordinary-cost code is no larger than every accepted encoded
competitor at the selected minimum budget. -/
theorem selectedCanonicalDenseMinimumCostCode_le
    (maxBudget : Nat)
    (hAccepted :
      table.HasAcceptedCostBudgetUpTo maxBudget)
    {competingCode : Nat}
    (hCompeting :
      competingCode ∈
        table.verifiedDenseCostCertificateCodes
          (table.selectedMinimumAcceptedCostBudget
            maxBudget
            hAccepted)) :
    table.selectedCanonicalDenseMinimumCostCode
          maxBudget
          hAccepted <=
        competingCode := by

  have hVerifyCode :
      table.verifiesDenseCostCertificateCode
            (table.selectedMinimumAcceptedCostBudget
              maxBudget
              hAccepted)
            competingCode =
          true :=
    (table.mem_verifiedDenseCostCertificateCodes_iff
      (table.selectedMinimumAcceptedCostBudget
        maxBudget
        hAccepted)
      competingCode).mp hCompeting |>.2

  rcases
      table.verifiesDenseCostCertificateCode_decode_package
        (table.selectedMinimumAcceptedCostBudget
          maxBudget
          hAccepted)
        hVerifyCode with
    ⟨certificate,
      hDecode,
      hVerifyCertificate,
      hSubset⟩

  have hCanonicalLe :
      correctedConcreteDenseCertificateCode U
            (table.canonicalMinimumCostCertificate
              (correctedConcreteDenseCertificateCode U)
              maxBudget
              hAccepted) <=
        correctedConcreteDenseCertificateCode U certificate :=
    table.canonicalMinimumCostCertificate_code_le
      (correctedConcreteDenseCertificateCode U)
      maxBudget
      hAccepted
      hVerifyCertificate

  have hReencode :
      correctedConcreteDenseCertificateCode U certificate =
        competingCode :=
    correctedConcreteDenseCertificateCode_decode_eq
      U
      hDecode

  exact hReencode ▸ hCanonicalLe

/-- Any accepted encoded ordinary-cost competitor lying below the selected code
must be the selected code itself. -/
theorem eq_selectedCanonicalDenseMinimumCostCode_of_mem_of_le
    (maxBudget : Nat)
    (hAccepted :
      table.HasAcceptedCostBudgetUpTo maxBudget)
    {competingCode : Nat}
    (hCompeting :
      competingCode ∈
        table.verifiedDenseCostCertificateCodes
          (table.selectedMinimumAcceptedCostBudget
            maxBudget
            hAccepted))
    (hLe :
      competingCode <=
        table.selectedCanonicalDenseMinimumCostCode
          maxBudget
          hAccepted) :
    competingCode =
      table.selectedCanonicalDenseMinimumCostCode
        maxBudget
        hAccepted := by

  exact
    Nat.le_antisymm
      hLe
      (table.selectedCanonicalDenseMinimumCostCode_le
        maxBudget
        hAccepted
        hCompeting)

/-- The canonical ordinary-cost code search is the singleton containing the
encoded selector. -/
theorem canonicalDenseMinimumCostCodeSearch_eq_selected_singleton
    (maxBudget : Nat)
    (hAccepted :
      table.HasAcceptedCostBudgetUpTo maxBudget) :
    table.canonicalDenseMinimumCostCodeSearch
          maxBudget
          hAccepted =
        {table.selectedCanonicalDenseMinimumCostCode
          maxBudget
          hAccepted} := by

  exact
    table.canonicalDenseMinimumCostCodeSearch_eq_singleton
      maxBudget
      hAccepted

/-- Complete ordinary-cost encoded selector package. -/
theorem selectedCanonicalDenseMinimumCostCode_package
    (maxBudget : Nat)
    (hAccepted :
      table.HasAcceptedCostBudgetUpTo maxBudget) :
    let selectedCode :=
      table.selectedCanonicalDenseMinimumCostCode
        maxBudget
        hAccepted
    let selectedCertificate :=
      table.canonicalMinimumCostCertificate
        (correctedConcreteDenseCertificateCode U)
        maxBudget
        hAccepted
    selectedCode < 2 ^ U.card ∧
      correctedConcreteDenseCertificateDecode U selectedCode =
        some selectedCertificate ∧
      selectedCode ∈
        table.verifiedDenseCostCertificateCodes
          (table.selectedMinimumAcceptedCostBudget
            maxBudget
            hAccepted) ∧
      (∀ competingCode : Nat,
        competingCode ∈
            table.verifiedDenseCostCertificateCodes
              (table.selectedMinimumAcceptedCostBudget
                maxBudget
                hAccepted) →
          selectedCode <= competingCode) ∧
      table.canonicalDenseMinimumCostCodeSearch
            maxBudget
            hAccepted =
          {selectedCode} := by

  exact
    ⟨table.selectedCanonicalDenseMinimumCostCode_lt
        maxBudget
        hAccepted,
      table.selectedCanonicalDenseMinimumCostCode_decode
        maxBudget
        hAccepted,
      table.selectedCanonicalDenseMinimumCostCode_mem
        maxBudget
        hAccepted,
      fun competingCode hCompeting =>
        table.selectedCanonicalDenseMinimumCostCode_le
          maxBudget
          hAccepted
          hCompeting,
      table.canonicalDenseMinimumCostCodeSearch_eq_selected_singleton
        maxBudget
        hAccepted⟩

end EncodedMinimumCostSelector


section EncodedMinimumParetoScalarSelector

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

/-- The selected encoded canonical Pareto-scalar certificate code. -/
noncomputable def selectedCanonicalDenseMinimumParetoScalarCode
    (maxBudget : Nat)
    (hAccepted :
      table.HasAcceptedParetoScalarBudgetUpTo maxBudget) :
    Nat :=
  correctedConcreteDenseCertificateCode U
    (table.canonicalMinimumParetoScalarCertificate
      (correctedConcreteDenseCertificateCode U)
      maxBudget
      hAccepted)

/-- The selected Pareto-scalar code lies in the exact dense universe. -/
theorem selectedCanonicalDenseMinimumParetoScalarCode_lt
    (maxBudget : Nat)
    (hAccepted :
      table.HasAcceptedParetoScalarBudgetUpTo maxBudget) :
    table.selectedCanonicalDenseMinimumParetoScalarCode
          maxBudget
          hAccepted <
        2 ^ U.card := by

  exact
    correctedConcreteDenseCertificateCode_lt_two_pow
      U
      (table.canonicalMinimumParetoScalarCertificate
        (correctedConcreteDenseCertificateCode U)
        maxBudget
        hAccepted)

/-- The selected Pareto-scalar code decodes exactly to the canonical minimum
Pareto certificate. -/
theorem selectedCanonicalDenseMinimumParetoScalarCode_decode
    (maxBudget : Nat)
    (hAccepted :
      table.HasAcceptedParetoScalarBudgetUpTo maxBudget) :
    correctedConcreteDenseCertificateDecode U
          (table.selectedCanonicalDenseMinimumParetoScalarCode
            maxBudget
            hAccepted) =
        some
          (table.canonicalMinimumParetoScalarCertificate
            (correctedConcreteDenseCertificateCode U)
            maxBudget
            hAccepted) := by

  have hVerify :=
    table.canonicalMinimumParetoScalarCertificate_verifies
      (correctedConcreteDenseCertificateCode U)
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
    ((table.verifiesParetoScalarCertificate_eq_true_iff
      (table.selectedMinimumAcceptedParetoScalarBudget
        maxBudget
        hAccepted)
      (table.canonicalMinimumParetoScalarCertificate
        (correctedConcreteDenseCertificateCode U)
        maxBudget
        hAccepted)).mp hVerify).1

  exact
    correctedConcreteDenseCertificateDecode_encode_of_subset
      U
      hPareto.1

/-- The selected Pareto-scalar code is accepted by the encoded verifier at the
selected minimum scalar budget. -/
theorem selectedCanonicalDenseMinimumParetoScalarCode_verifies
    (maxBudget : Nat)
    (hAccepted :
      table.HasAcceptedParetoScalarBudgetUpTo maxBudget) :
    table.verifiesDenseParetoScalarCertificateCode
          (table.selectedMinimumAcceptedParetoScalarBudget
            maxBudget
            hAccepted)
          (table.selectedCanonicalDenseMinimumParetoScalarCode
            maxBudget
            hAccepted) =
        true := by

  exact
    table.verifiesDenseParetoScalarCertificateCode_encode_of_verify
      (table.selectedMinimumAcceptedParetoScalarBudget
        maxBudget
        hAccepted)
      (table.canonicalMinimumParetoScalarCertificate_verifies
        (correctedConcreteDenseCertificateCode U)
        maxBudget
        hAccepted)

/-- The selected Pareto-scalar code belongs to the finite encoded search. -/
theorem selectedCanonicalDenseMinimumParetoScalarCode_mem
    (maxBudget : Nat)
    (hAccepted :
      table.HasAcceptedParetoScalarBudgetUpTo maxBudget) :
    table.selectedCanonicalDenseMinimumParetoScalarCode
          maxBudget
          hAccepted ∈
        table.verifiedDenseParetoScalarCertificateCodes
          (table.selectedMinimumAcceptedParetoScalarBudget
            maxBudget
            hAccepted) := by

  exact
    table.canonicalMinimumParetoScalarCertificate_denseCode_mem_verifiedSearch
      maxBudget
      hAccepted

/-- The selected Pareto-scalar code is no larger than every accepted encoded
competitor at the selected minimum scalar budget. -/
theorem selectedCanonicalDenseMinimumParetoScalarCode_le
    (maxBudget : Nat)
    (hAccepted :
      table.HasAcceptedParetoScalarBudgetUpTo maxBudget)
    {competingCode : Nat}
    (hCompeting :
      competingCode ∈
        table.verifiedDenseParetoScalarCertificateCodes
          (table.selectedMinimumAcceptedParetoScalarBudget
            maxBudget
            hAccepted)) :
    table.selectedCanonicalDenseMinimumParetoScalarCode
          maxBudget
          hAccepted <=
        competingCode := by

  have hVerifyCode :
      table.verifiesDenseParetoScalarCertificateCode
            (table.selectedMinimumAcceptedParetoScalarBudget
              maxBudget
              hAccepted)
            competingCode =
          true :=
    (table.mem_verifiedDenseParetoScalarCertificateCodes_iff
      (table.selectedMinimumAcceptedParetoScalarBudget
        maxBudget
        hAccepted)
      competingCode).mp hCompeting |>.2

  rcases
      table.verifiesDenseParetoScalarCertificateCode_decode_package
        (table.selectedMinimumAcceptedParetoScalarBudget
          maxBudget
          hAccepted)
        hVerifyCode with
    ⟨certificate,
      hDecode,
      hVerifyCertificate,
      hSubset⟩

  have hCanonicalLe :
      correctedConcreteDenseCertificateCode U
            (table.canonicalMinimumParetoScalarCertificate
              (correctedConcreteDenseCertificateCode U)
              maxBudget
              hAccepted) <=
        correctedConcreteDenseCertificateCode U certificate :=
    table.canonicalMinimumParetoScalarCertificate_code_le
      (correctedConcreteDenseCertificateCode U)
      maxBudget
      hAccepted
      hVerifyCertificate

  have hReencode :
      correctedConcreteDenseCertificateCode U certificate =
        competingCode :=
    correctedConcreteDenseCertificateCode_decode_eq
      U
      hDecode

  exact hReencode ▸ hCanonicalLe

/-- Any accepted encoded Pareto-scalar competitor lying below the selected code
must be the selected code itself. -/
theorem eq_selectedCanonicalDenseMinimumParetoScalarCode_of_mem_of_le
    (maxBudget : Nat)
    (hAccepted :
      table.HasAcceptedParetoScalarBudgetUpTo maxBudget)
    {competingCode : Nat}
    (hCompeting :
      competingCode ∈
        table.verifiedDenseParetoScalarCertificateCodes
          (table.selectedMinimumAcceptedParetoScalarBudget
            maxBudget
            hAccepted))
    (hLe :
      competingCode <=
        table.selectedCanonicalDenseMinimumParetoScalarCode
          maxBudget
          hAccepted) :
    competingCode =
      table.selectedCanonicalDenseMinimumParetoScalarCode
        maxBudget
        hAccepted := by

  exact
    Nat.le_antisymm
      hLe
      (table.selectedCanonicalDenseMinimumParetoScalarCode_le
        maxBudget
        hAccepted
        hCompeting)

/-- The canonical Pareto-scalar code search is the singleton containing the
encoded selector. -/
theorem canonicalDenseMinimumParetoScalarCodeSearch_eq_selected_singleton
    (maxBudget : Nat)
    (hAccepted :
      table.HasAcceptedParetoScalarBudgetUpTo maxBudget) :
    table.canonicalDenseMinimumParetoScalarCodeSearch
          maxBudget
          hAccepted =
        {table.selectedCanonicalDenseMinimumParetoScalarCode
          maxBudget
          hAccepted} := by

  exact
    table.canonicalDenseMinimumParetoScalarCodeSearch_eq_singleton
      maxBudget
      hAccepted

/-- Complete Pareto-scalar encoded selector package. -/
theorem selectedCanonicalDenseMinimumParetoScalarCode_package
    (maxBudget : Nat)
    (hAccepted :
      table.HasAcceptedParetoScalarBudgetUpTo maxBudget) :
    let selectedCode :=
      table.selectedCanonicalDenseMinimumParetoScalarCode
        maxBudget
        hAccepted
    let selectedCertificate :=
      table.canonicalMinimumParetoScalarCertificate
        (correctedConcreteDenseCertificateCode U)
        maxBudget
        hAccepted
    selectedCode < 2 ^ U.card ∧
      correctedConcreteDenseCertificateDecode U selectedCode =
        some selectedCertificate ∧
      selectedCode ∈
        table.verifiedDenseParetoScalarCertificateCodes
          (table.selectedMinimumAcceptedParetoScalarBudget
            maxBudget
            hAccepted) ∧
      (∀ competingCode : Nat,
        competingCode ∈
            table.verifiedDenseParetoScalarCertificateCodes
              (table.selectedMinimumAcceptedParetoScalarBudget
                maxBudget
                hAccepted) →
          selectedCode <= competingCode) ∧
      table.canonicalDenseMinimumParetoScalarCodeSearch
            maxBudget
            hAccepted =
          {selectedCode} := by

  exact
    ⟨table.selectedCanonicalDenseMinimumParetoScalarCode_lt
        maxBudget
        hAccepted,
      table.selectedCanonicalDenseMinimumParetoScalarCode_decode
        maxBudget
        hAccepted,
      table.selectedCanonicalDenseMinimumParetoScalarCode_mem
        maxBudget
        hAccepted,
      fun competingCode hCompeting =>
        table.selectedCanonicalDenseMinimumParetoScalarCode_le
          maxBudget
          hAccepted
          hCompeting,
      table.canonicalDenseMinimumParetoScalarCodeSearch_eq_selected_singleton
        maxBudget
        hAccepted⟩

end EncodedMinimumParetoScalarSelector

end CorrectedConcreteObservationSelectionDecisionTable


section EncodedCanonicalSelectorFinalPackage

variable {α : Type u}
variable {ι : Type v}
variable {M : Type w}
variable [DecidableEq ι]
variable [Monoid M]
variable (obsFamily : ι → α → M)
variable (f : Nat)
variable (coordinateWeight : ι → Nat)
variable (U : Finset ι)

/-- Final positive-additive encoded canonical-selector package.  The selected
bounded natural-number code decodes to a Pareto-optimal minimum-rank interface,
belongs to the finite encoded verifier search, and is the least accepted dense
code at the exact semantic positive-additive rank. -/
theorem
    correctedConcreteWorkingGrammar_observationSelectionEncodedCanonicalSelector_package
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
    let certificate :=
      table.canonicalMinimumParetoScalarCertificate
        (correctedConcreteDenseCertificateCode U)
        maxBudget
        hAccepted
    let selectedCode :=
      table.selectedCanonicalDenseMinimumParetoScalarCode
        maxBudget
        hAccepted
    selectedCode < 2 ^ U.card ∧
      correctedConcreteDenseCertificateDecode U selectedCode =
        some certificate ∧
      selectedCode ∈
        table.verifiedDenseParetoScalarCertificateCodes
          (ambientTargetObservationSelectionPositiveAdditiveMinimumCost
            (z := z)
            obsFamily
            f
            coordinateWeight
            U
            hTarget) ∧
      (∀ competingCode : Nat,
        competingCode ∈
            table.verifiedDenseParetoScalarCertificateCodes
              (ambientTargetObservationSelectionPositiveAdditiveMinimumCost
                (z := z)
                obsFamily
                f
                coordinateWeight
                U
                hTarget) →
          selectedCode <= competingCode) ∧
      CorrectedConcreteObservationSelectionParetoOptimal
        (z := z)
        obsFamily
        f
        (correctedConcreteObservationSelectionAdditiveCost
          coordinateWeight)
        U
        language
        certificate ∧
      correctedConcreteObservationSelectionParetoScalarCost
            (correctedConcreteObservationSelectionAdditiveCost
              coordinateWeight)
            certificate =
        ambientTargetObservationSelectionPositiveAdditiveMinimumCost
          (z := z)
          obsFamily
          f
          coordinateWeight
          U
          hTarget := by

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

  let certificate :=
    table.canonicalMinimumParetoScalarCertificate
      (correctedConcreteDenseCertificateCode U)
      maxBudget
      hAccepted

  let selectedCode :=
    table.selectedCanonicalDenseMinimumParetoScalarCode
      maxBudget
      hAccepted

  have hSelector :=
    table.selectedCanonicalDenseMinimumParetoScalarCode_package
      maxBudget
      hAccepted

  have hBudgetEq :
      table.selectedMinimumAcceptedParetoScalarBudget
            maxBudget
            hAccepted =
        ambientTargetObservationSelectionPositiveAdditiveMinimumCost
          (z := z)
          obsFamily
          f
          coordinateWeight
          U
          hTarget :=
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

  exact
    ⟨hSelector.1,
      hSelector.2.1,
      hBudgetEq ▸ hSelector.2.2.1,
      fun competingCode hCompeting =>
        hSelector.2.2.2.1
          competingCode
          (hBudgetEq.symm ▸ hCompeting),
      hCanonical.1,
      hCanonical.2.1⟩

end EncodedCanonicalSelectorFinalPackage

end MCFG
