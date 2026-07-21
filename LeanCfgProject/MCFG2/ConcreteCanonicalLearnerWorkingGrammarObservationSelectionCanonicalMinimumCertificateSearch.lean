/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG.ConcreteCanonicalLearnerWorkingGrammarObservationSelectionCanonicalMinimumCertificate

/-!
# ConcreteCanonicalLearnerWorkingGrammarObservationSelectionCanonicalMinimumCertificateSearch.lean

The preceding file chooses a least-code certificate from the finite family of
certificates accepted at the selected minimum budget.

This file exposes that choice as an explicit finite search result.  The search
filters the exact minimum-budget certificate family by the least realized
external code.  Thus it keeps precisely the accepted minimum-budget
certificates whose code is canonical.

For both ordinary cost and Pareto-scalar certificates we prove:

```text
the canonical certificate belongs to the finite search;
the search is nonempty;
membership is exactly verification at the selected minimum budget together
  with equality to the least realized code;
if the external certificate code is injective, the search is the singleton
  containing the canonical certificate, and consequently has cardinality one.
```

The final theorem specializes the Pareto search to positive-additive
observation selection and identifies its unique certificate with the exact
minimum-rank canonical certificate.

The external code is still abstract.  A later file may instantiate it by a
checked dense encoding of subsets of the ambient finite coordinate set.
No machine-cost, NP-membership, or hardness claim is made here.

No target grammar is supplied to any learner.
No `sorry`, `admit`, or `axiom` is used.
-/

namespace MCFG

universe u v w z

namespace CorrectedConcreteObservationSelectionDecisionTable

section CanonicalMinimumCostCertificateSearch

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
variable (certificateCode : Finset ι → Nat)

/-- Explicit finite search result for canonical ordinary-cost certificates.
It filters the exact selected-minimum-budget certificate family by the least
external code realized in that family. -/
def canonicalMinimumCostCertificateSearch
    (maxBudget : Nat)
    (hAccepted :
      table.HasAcceptedCostBudgetUpTo maxBudget) :
    Finset (Finset ι) :=
  (table.minimumCostCertificateFamily
      maxBudget
      hAccepted).filter
    (fun certificate =>
      certificateCode certificate =
        table.canonicalMinimumCostCertificateCode
          certificateCode
          maxBudget
          hAccepted)

/-- Membership in the canonical ordinary-cost search is exactly verification
at the selected minimum budget plus equality to the least realized code. -/
theorem mem_canonicalMinimumCostCertificateSearch_iff
    (maxBudget : Nat)
    (hAccepted :
      table.HasAcceptedCostBudgetUpTo maxBudget)
    (certificate : Finset ι) :
    certificate ∈
        table.canonicalMinimumCostCertificateSearch
          certificateCode
          maxBudget
          hAccepted ↔
      table.verifiesCostCertificate
            (table.selectedMinimumAcceptedCostBudget
              maxBudget
              hAccepted)
            certificate =
          true ∧
        certificateCode certificate =
          table.canonicalMinimumCostCertificateCode
            certificateCode
            maxBudget
            hAccepted := by

  simp only [
    canonicalMinimumCostCertificateSearch,
    Finset.mem_filter,
    minimumCostCertificateFamily,
    table.mem_verifiedCostCertificates_iff
  ]

/-- The selected canonical ordinary-cost certificate occurs in the explicit
finite canonical search. -/
theorem canonicalMinimumCostCertificate_mem_search
    (maxBudget : Nat)
    (hAccepted :
      table.HasAcceptedCostBudgetUpTo maxBudget) :
    table.canonicalMinimumCostCertificate
          certificateCode
          maxBudget
          hAccepted ∈
        table.canonicalMinimumCostCertificateSearch
          certificateCode
          maxBudget
          hAccepted := by

  exact
    (table.mem_canonicalMinimumCostCertificateSearch_iff
      certificateCode
      maxBudget
      hAccepted
      (table.canonicalMinimumCostCertificate
        certificateCode
        maxBudget
        hAccepted)).mpr
      ⟨table.canonicalMinimumCostCertificate_verifies
          certificateCode
          maxBudget
          hAccepted,
        table.canonicalMinimumCostCertificate_code_eq
          certificateCode
          maxBudget
          hAccepted⟩

/-- The explicit canonical ordinary-cost certificate search is nonempty. -/
theorem canonicalMinimumCostCertificateSearch_nonempty
    (maxBudget : Nat)
    (hAccepted :
      table.HasAcceptedCostBudgetUpTo maxBudget) :
    (table.canonicalMinimumCostCertificateSearch
      certificateCode
      maxBudget
      hAccepted).Nonempty := by

  exact
    ⟨table.canonicalMinimumCostCertificate
        certificateCode
        maxBudget
        hAccepted,
      table.canonicalMinimumCostCertificate_mem_search
        certificateCode
        maxBudget
        hAccepted⟩

/-- Every result of the canonical ordinary-cost search is accepted at the
selected minimum budget. -/
theorem canonicalMinimumCostCertificateSearch_verifies
    (maxBudget : Nat)
    (hAccepted :
      table.HasAcceptedCostBudgetUpTo maxBudget)
    {certificate : Finset ι}
    (hCertificate :
      certificate ∈
        table.canonicalMinimumCostCertificateSearch
          certificateCode
          maxBudget
          hAccepted) :
    table.verifiesCostCertificate
          (table.selectedMinimumAcceptedCostBudget
            maxBudget
            hAccepted)
          certificate =
        true := by

  exact
    (table.mem_canonicalMinimumCostCertificateSearch_iff
      certificateCode
      maxBudget
      hAccepted
      certificate).mp
      hCertificate |>.1

/-- Every result of the canonical ordinary-cost search realizes the least
external code. -/
theorem canonicalMinimumCostCertificateSearch_code_eq
    (maxBudget : Nat)
    (hAccepted :
      table.HasAcceptedCostBudgetUpTo maxBudget)
    {certificate : Finset ι}
    (hCertificate :
      certificate ∈
        table.canonicalMinimumCostCertificateSearch
          certificateCode
          maxBudget
          hAccepted) :
    certificateCode certificate =
      table.canonicalMinimumCostCertificateCode
        certificateCode
        maxBudget
        hAccepted := by

  exact
    (table.mem_canonicalMinimumCostCertificateSearch_iff
      certificateCode
      maxBudget
      hAccepted
      certificate).mp
      hCertificate |>.2

/-- With an injective external code, the explicit canonical ordinary-cost
search consists of exactly the selected canonical certificate. -/
theorem canonicalMinimumCostCertificateSearch_eq_singleton
    (hCodeInjective : Function.Injective certificateCode)
    (maxBudget : Nat)
    (hAccepted :
      table.HasAcceptedCostBudgetUpTo maxBudget) :
    table.canonicalMinimumCostCertificateSearch
          certificateCode
          maxBudget
          hAccepted =
        {table.canonicalMinimumCostCertificate
          certificateCode
          maxBudget
          hAccepted} := by

  apply Finset.ext
  intro certificate
  constructor

  · intro hCertificate

    have hCanonicalEq :
        table.canonicalMinimumCostCertificate
              certificateCode
              maxBudget
              hAccepted =
            certificate :=
      table.canonicalMinimumCostCertificate_unique
        certificateCode
        hCodeInjective
        maxBudget
        hAccepted
        (table.canonicalMinimumCostCertificateSearch_verifies
          certificateCode
          maxBudget
          hAccepted
          hCertificate)
        (table.canonicalMinimumCostCertificateSearch_code_eq
          certificateCode
          maxBudget
          hAccepted
          hCertificate)

    exact Finset.mem_singleton.mpr hCanonicalEq.symm

  · intro hCertificate

    have hCertificateEq :
        certificate =
          table.canonicalMinimumCostCertificate
            certificateCode
            maxBudget
            hAccepted :=
      Finset.mem_singleton.mp hCertificate

    subst certificate

    exact
      table.canonicalMinimumCostCertificate_mem_search
        certificateCode
        maxBudget
        hAccepted

/-- With an injective external code, the canonical ordinary-cost search has
exactly one element. -/
theorem canonicalMinimumCostCertificateSearch_card_eq_one
    (hCodeInjective : Function.Injective certificateCode)
    (maxBudget : Nat)
    (hAccepted :
      table.HasAcceptedCostBudgetUpTo maxBudget) :
    (table.canonicalMinimumCostCertificateSearch
      certificateCode
      maxBudget
      hAccepted).card = 1 := by

  rw [
    table.canonicalMinimumCostCertificateSearch_eq_singleton
      certificateCode
      hCodeInjective
      maxBudget
      hAccepted,
    Finset.card_singleton
  ]

end CanonicalMinimumCostCertificateSearch


section CanonicalMinimumParetoScalarCertificateSearch

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
variable (certificateCode : Finset ι → Nat)

/-- Explicit finite search result for canonical Pareto-scalar certificates. -/
def canonicalMinimumParetoScalarCertificateSearch
    (maxBudget : Nat)
    (hAccepted :
      table.HasAcceptedParetoScalarBudgetUpTo maxBudget) :
    Finset (Finset ι) :=
  (table.minimumParetoScalarCertificateFamily
      maxBudget
      hAccepted).filter
    (fun certificate =>
      certificateCode certificate =
        table.canonicalMinimumParetoScalarCertificateCode
          certificateCode
          maxBudget
          hAccepted)

/-- Membership in the canonical Pareto-scalar search is exactly verification
at the selected minimum scalar budget plus equality to the least code. -/
theorem mem_canonicalMinimumParetoScalarCertificateSearch_iff
    (maxBudget : Nat)
    (hAccepted :
      table.HasAcceptedParetoScalarBudgetUpTo maxBudget)
    (certificate : Finset ι) :
    certificate ∈
        table.canonicalMinimumParetoScalarCertificateSearch
          certificateCode
          maxBudget
          hAccepted ↔
      table.verifiesParetoScalarCertificate
            (table.selectedMinimumAcceptedParetoScalarBudget
              maxBudget
              hAccepted)
            certificate =
          true ∧
        certificateCode certificate =
          table.canonicalMinimumParetoScalarCertificateCode
            certificateCode
            maxBudget
            hAccepted := by

  simp only [
    canonicalMinimumParetoScalarCertificateSearch,
    Finset.mem_filter,
    minimumParetoScalarCertificateFamily,
    table.mem_verifiedParetoScalarCertificates_iff
  ]

/-- The selected canonical Pareto certificate belongs to its explicit search. -/
theorem canonicalMinimumParetoScalarCertificate_mem_search
    (maxBudget : Nat)
    (hAccepted :
      table.HasAcceptedParetoScalarBudgetUpTo maxBudget) :
    table.canonicalMinimumParetoScalarCertificate
          certificateCode
          maxBudget
          hAccepted ∈
        table.canonicalMinimumParetoScalarCertificateSearch
          certificateCode
          maxBudget
          hAccepted := by

  exact
    (table.mem_canonicalMinimumParetoScalarCertificateSearch_iff
      certificateCode
      maxBudget
      hAccepted
      (table.canonicalMinimumParetoScalarCertificate
        certificateCode
        maxBudget
        hAccepted)).mpr
      ⟨table.canonicalMinimumParetoScalarCertificate_verifies
          certificateCode
          maxBudget
          hAccepted,
        table.canonicalMinimumParetoScalarCertificate_code_eq
          certificateCode
          maxBudget
          hAccepted⟩

/-- The explicit canonical Pareto-scalar certificate search is nonempty. -/
theorem canonicalMinimumParetoScalarCertificateSearch_nonempty
    (maxBudget : Nat)
    (hAccepted :
      table.HasAcceptedParetoScalarBudgetUpTo maxBudget) :
    (table.canonicalMinimumParetoScalarCertificateSearch
      certificateCode
      maxBudget
      hAccepted).Nonempty := by

  exact
    ⟨table.canonicalMinimumParetoScalarCertificate
        certificateCode
        maxBudget
        hAccepted,
      table.canonicalMinimumParetoScalarCertificate_mem_search
        certificateCode
        maxBudget
        hAccepted⟩

/-- Every explicit canonical Pareto-search result verifies at the selected
minimum scalar budget. -/
theorem canonicalMinimumParetoScalarCertificateSearch_verifies
    (maxBudget : Nat)
    (hAccepted :
      table.HasAcceptedParetoScalarBudgetUpTo maxBudget)
    {certificate : Finset ι}
    (hCertificate :
      certificate ∈
        table.canonicalMinimumParetoScalarCertificateSearch
          certificateCode
          maxBudget
          hAccepted) :
    table.verifiesParetoScalarCertificate
          (table.selectedMinimumAcceptedParetoScalarBudget
            maxBudget
            hAccepted)
          certificate =
        true := by

  exact
    (table.mem_canonicalMinimumParetoScalarCertificateSearch_iff
      certificateCode
      maxBudget
      hAccepted
      certificate).mp
      hCertificate |>.1

/-- Every explicit canonical Pareto-search result realizes the least code. -/
theorem canonicalMinimumParetoScalarCertificateSearch_code_eq
    (maxBudget : Nat)
    (hAccepted :
      table.HasAcceptedParetoScalarBudgetUpTo maxBudget)
    {certificate : Finset ι}
    (hCertificate :
      certificate ∈
        table.canonicalMinimumParetoScalarCertificateSearch
          certificateCode
          maxBudget
          hAccepted) :
    certificateCode certificate =
      table.canonicalMinimumParetoScalarCertificateCode
        certificateCode
        maxBudget
        hAccepted := by

  exact
    (table.mem_canonicalMinimumParetoScalarCertificateSearch_iff
      certificateCode
      maxBudget
      hAccepted
      certificate).mp
      hCertificate |>.2

/-- With an injective external code, the explicit canonical Pareto search is a
singleton. -/
theorem canonicalMinimumParetoScalarCertificateSearch_eq_singleton
    (hCodeInjective : Function.Injective certificateCode)
    (maxBudget : Nat)
    (hAccepted :
      table.HasAcceptedParetoScalarBudgetUpTo maxBudget) :
    table.canonicalMinimumParetoScalarCertificateSearch
          certificateCode
          maxBudget
          hAccepted =
        {table.canonicalMinimumParetoScalarCertificate
          certificateCode
          maxBudget
          hAccepted} := by

  apply Finset.ext
  intro certificate
  constructor

  · intro hCertificate

    have hCanonicalEq :
        table.canonicalMinimumParetoScalarCertificate
              certificateCode
              maxBudget
              hAccepted =
            certificate :=
      table.canonicalMinimumParetoScalarCertificate_unique
        certificateCode
        hCodeInjective
        maxBudget
        hAccepted
        (table.canonicalMinimumParetoScalarCertificateSearch_verifies
          certificateCode
          maxBudget
          hAccepted
          hCertificate)
        (table.canonicalMinimumParetoScalarCertificateSearch_code_eq
          certificateCode
          maxBudget
          hAccepted
          hCertificate)

    exact Finset.mem_singleton.mpr hCanonicalEq.symm

  · intro hCertificate

    have hCertificateEq :
        certificate =
          table.canonicalMinimumParetoScalarCertificate
            certificateCode
            maxBudget
            hAccepted :=
      Finset.mem_singleton.mp hCertificate

    subst certificate

    exact
      table.canonicalMinimumParetoScalarCertificate_mem_search
        certificateCode
        maxBudget
        hAccepted

/-- With an injective external code, the explicit canonical Pareto search has
cardinality one. -/
theorem canonicalMinimumParetoScalarCertificateSearch_card_eq_one
    (hCodeInjective : Function.Injective certificateCode)
    (maxBudget : Nat)
    (hAccepted :
      table.HasAcceptedParetoScalarBudgetUpTo maxBudget) :
    (table.canonicalMinimumParetoScalarCertificateSearch
      certificateCode
      maxBudget
      hAccepted).card = 1 := by

  rw [
    table.canonicalMinimumParetoScalarCertificateSearch_eq_singleton
      certificateCode
      hCodeInjective
      maxBudget
      hAccepted,
    Finset.card_singleton
  ]

end CanonicalMinimumParetoScalarCertificateSearch

end CorrectedConcreteObservationSelectionDecisionTable


section CanonicalMinimumCertificateSearchFinalPackage

variable {α : Type u}
variable {ι : Type v}
variable {M : Type w}
variable [DecidableEq ι]
variable [Monoid M]
variable (obsFamily : ι → α → M)
variable (f : Nat)
variable (coordinateWeight : ι → Nat)
variable (U : Finset ι)
variable (certificateCode : Finset ι → Nat)

/-- Final finite-search package for positive-additive observation selection.
Under an injective external subset code, the canonical minimum-rank Pareto
certificate is the unique member of the explicit least-code search. -/
theorem
    correctedConcreteWorkingGrammar_observationSelectionCanonicalMinimumCertificateSearch_package
    (hCodeInjective : Function.Injective certificateCode)
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
        certificateCode
        maxBudget
        hAccepted
    table.canonicalMinimumParetoScalarCertificateSearch
          certificateCode
          maxBudget
          hAccepted =
        {certificate} ∧
      (table.canonicalMinimumParetoScalarCertificateSearch
        certificateCode
        maxBudget
        hAccepted).card = 1 ∧
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
      certificateCode
      maxBudget
      hAccepted

  have hCanonicalPackage :=
    correctedConcreteWorkingGrammar_observationSelectionCanonicalMinimumCertificate_package
      (z := z)
      obsFamily
      f
      coordinateWeight
      U
      certificateCode
      language
      hTarget

  exact
    ⟨table.canonicalMinimumParetoScalarCertificateSearch_eq_singleton
        certificateCode
        hCodeInjective
        maxBudget
        hAccepted,
      table.canonicalMinimumParetoScalarCertificateSearch_card_eq_one
        certificateCode
        hCodeInjective
        maxBudget
        hAccepted,
      hCanonicalPackage.1,
      hCanonicalPackage.2.1⟩

end CanonicalMinimumCertificateSearchFinalPackage

end MCFG
