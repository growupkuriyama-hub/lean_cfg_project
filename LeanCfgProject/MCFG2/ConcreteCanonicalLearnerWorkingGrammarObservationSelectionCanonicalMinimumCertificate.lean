/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG2.ConcreteCanonicalLearnerWorkingGrammarObservationSelectionMinimumCertificateSelector

/-!
# ConcreteCanonicalLearnerWorkingGrammarObservationSelectionCanonicalMinimumCertificate.lean

The preceding file selects one minimum-budget observation certificate by
classical witness choice.  Distinct minimum certificates may exist, so that
choice is intentionally not canonical.

This file adds an encoded tie-breaker.  For any nonempty finite certificate
family and any natural-valued certificate code, it selects a member whose code
is least among all members.  Applied to the exact accepted family at the
selected minimum budget, this gives canonical ordinary-cost and Pareto-scalar
certificates.

The main facts are:

```text
canonical certificate is accepted;
its cost or Pareto scalar is exactly the selected minimum budget;
its code is no larger than the code of every competing accepted certificate;
if the supplied code is injective, the canonical minimum-code certificate is
unique.
```

The code is still an abstract external encoding.  A later executable file may
instantiate it by a checked dense code for ambient subsets.  No machine-cost or
complexity-class claim is made here.

No target grammar is supplied to any learner.
No `sorry`, `admit`, or `axiom` is used.
-/

namespace MCFG

universe u v w z

section GenericFiniteFamilyCanonicalSelector

variable {Certificate : Type v}
variable [DecidableEq Certificate]
variable (family : Finset Certificate)
variable (certificateCode : Certificate → Nat)

/-- A natural number is realized as the code of a member of the finite
certificate family. -/
def CorrectedConcreteFiniteCertificateCodeRealized
    (code : Nat) :
    Prop :=
  ∃ certificate : Certificate,
    certificate ∈ family ∧
      certificateCode certificate = code

/-- Every nonempty finite certificate family realizes at least one natural
certificate code. -/
theorem exists_correctedConcreteFiniteCertificateCodeRealized
    (hFamily : family.Nonempty) :
    ∃ code : Nat,
      CorrectedConcreteFiniteCertificateCodeRealized
        family
        certificateCode
        code := by

  rcases hFamily with
    ⟨certificate, hCertificate⟩

  exact
    ⟨certificateCode certificate,
      certificate,
      hCertificate,
      rfl⟩

/-- Least code realized by a member of a nonempty finite certificate family. -/
noncomputable def correctedConcreteFiniteCertificateLeastCode
    (hFamily : family.Nonempty) :
    Nat :=
  Nat.find
    (exists_correctedConcreteFiniteCertificateCodeRealized
      family
      certificateCode
      hFamily)

/-- The least realized code is itself realized by a family member. -/
theorem correctedConcreteFiniteCertificateLeastCode_spec
    (hFamily : family.Nonempty) :
    CorrectedConcreteFiniteCertificateCodeRealized
      family
      certificateCode
      (correctedConcreteFiniteCertificateLeastCode
        family
        certificateCode
        hFamily) := by

  exact
    Nat.find_spec
      (exists_correctedConcreteFiniteCertificateCodeRealized
        family
        certificateCode
        hFamily)

/-- The least realized family code is no larger than the code of every family
member. -/
theorem correctedConcreteFiniteCertificateLeastCode_le
    (hFamily : family.Nonempty)
    {certificate : Certificate}
    (hCertificate : certificate ∈ family) :
    correctedConcreteFiniteCertificateLeastCode
          family
          certificateCode
          hFamily <=
        certificateCode certificate := by

  exact
    Nat.find_min'
      (exists_correctedConcreteFiniteCertificateCodeRealized
        family
        certificateCode
        hFamily)
      ⟨certificate,
        hCertificate,
        rfl⟩

/-- A canonical member of a nonempty finite certificate family: choose one
member realizing the least family code. -/
noncomputable def correctedConcreteFiniteCanonicalCertificate
    (hFamily : family.Nonempty) :
    Certificate :=
  Classical.choose
    (correctedConcreteFiniteCertificateLeastCode_spec
      family
      certificateCode
      hFamily)

/-- The canonical finite certificate belongs to the supplied family. -/
theorem correctedConcreteFiniteCanonicalCertificate_mem
    (hFamily : family.Nonempty) :
    correctedConcreteFiniteCanonicalCertificate
          family
          certificateCode
          hFamily ∈
        family := by

  exact
    (Classical.choose_spec
      (correctedConcreteFiniteCertificateLeastCode_spec
        family
        certificateCode
        hFamily)).1

/-- The canonical certificate realizes exactly the least family code. -/
theorem correctedConcreteFiniteCanonicalCertificate_code_eq
    (hFamily : family.Nonempty) :
    certificateCode
          (correctedConcreteFiniteCanonicalCertificate
            family
            certificateCode
            hFamily) =
        correctedConcreteFiniteCertificateLeastCode
          family
          certificateCode
          hFamily := by

  exact
    (Classical.choose_spec
      (correctedConcreteFiniteCertificateLeastCode_spec
        family
        certificateCode
        hFamily)).2

/-- The canonical certificate code is no larger than the code of every family
member. -/
theorem correctedConcreteFiniteCanonicalCertificate_code_le
    (hFamily : family.Nonempty)
    {certificate : Certificate}
    (hCertificate : certificate ∈ family) :
    certificateCode
          (correctedConcreteFiniteCanonicalCertificate
            family
            certificateCode
            hFamily) <=
        certificateCode certificate := by

  rw [
    correctedConcreteFiniteCanonicalCertificate_code_eq
      family
      certificateCode
      hFamily
  ]

  exact
    correctedConcreteFiniteCertificateLeastCode_le
      family
      certificateCode
      hFamily
      hCertificate

/-- Under an injective certificate code, any family member with the canonical
minimum code is equal to the canonical certificate. -/
theorem correctedConcreteFiniteCanonicalCertificate_eq_of_code_eq
    (hFamily : family.Nonempty)
    (hCodeInjective : Function.Injective certificateCode)
    {certificate : Certificate}
    (_hCertificate : certificate ∈ family)
    (hCode :
      certificateCode certificate =
        correctedConcreteFiniteCertificateLeastCode
          family
          certificateCode
          hFamily) :
    correctedConcreteFiniteCanonicalCertificate
          family
          certificateCode
          hFamily =
        certificate := by

  apply hCodeInjective

  exact
    (correctedConcreteFiniteCanonicalCertificate_code_eq
      family
      certificateCode
      hFamily).trans
      hCode.symm

/-- Complete generic package for the finite minimum-code selector. -/
theorem correctedConcreteFiniteCanonicalCertificate_package
    (hFamily : family.Nonempty) :
    let canonical :=
      correctedConcreteFiniteCanonicalCertificate
        family
        certificateCode
        hFamily
    canonical ∈ family ∧
      certificateCode canonical =
        correctedConcreteFiniteCertificateLeastCode
          family
          certificateCode
          hFamily ∧
      ∀ certificate : Certificate,
        certificate ∈ family →
          certificateCode canonical <=
            certificateCode certificate := by

  exact
    ⟨correctedConcreteFiniteCanonicalCertificate_mem
        family
        certificateCode
        hFamily,
      correctedConcreteFiniteCanonicalCertificate_code_eq
        family
        certificateCode
        hFamily,
      fun certificate hCertificate =>
        correctedConcreteFiniteCanonicalCertificate_code_le
          family
          certificateCode
          hFamily
          hCertificate⟩

end GenericFiniteFamilyCanonicalSelector


namespace CorrectedConcreteObservationSelectionDecisionTable

section CanonicalMinimumCostCertificate

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

/-- Exact accepted cost-certificate family at the selected minimum accepted
ordinary budget. -/
def minimumCostCertificateFamily
    (maxBudget : Nat)
    (hAccepted :
      table.HasAcceptedCostBudgetUpTo maxBudget) :
    Finset (Finset ι) :=
  table.verifiedCostCertificates
    (table.selectedMinimumAcceptedCostBudget
      maxBudget
      hAccepted)

/-- The exact minimum-cost certificate family is nonempty. -/
theorem minimumCostCertificateFamily_nonempty
    (maxBudget : Nat)
    (hAccepted :
      table.HasAcceptedCostBudgetUpTo maxBudget) :
    (table.minimumCostCertificateFamily
      maxBudget
      hAccepted).Nonempty := by

  apply
    (table.verifiedCostCertificates_nonempty_iff
      (table.selectedMinimumAcceptedCostBudget
        maxBudget
        hAccepted)).mpr

  exact
    (table.selectedMinimumAcceptedCostBudget_spec
      maxBudget
      hAccepted).2

/-- Least external code among all certificates accepted at the selected
minimum ordinary budget. -/
noncomputable def canonicalMinimumCostCertificateCode
    (maxBudget : Nat)
    (hAccepted :
      table.HasAcceptedCostBudgetUpTo maxBudget) :
    Nat :=
  correctedConcreteFiniteCertificateLeastCode
    (table.minimumCostCertificateFamily
      maxBudget
      hAccepted)
    certificateCode
    (table.minimumCostCertificateFamily_nonempty
      maxBudget
      hAccepted)

/-- Canonical minimum ordinary-cost certificate, selected by the least external
certificate code. -/
noncomputable def canonicalMinimumCostCertificate
    (maxBudget : Nat)
    (hAccepted :
      table.HasAcceptedCostBudgetUpTo maxBudget) :
    Finset ι :=
  correctedConcreteFiniteCanonicalCertificate
    (table.minimumCostCertificateFamily
      maxBudget
      hAccepted)
    certificateCode
    (table.minimumCostCertificateFamily_nonempty
      maxBudget
      hAccepted)

/-- The canonical ordinary certificate is accepted at the selected minimum
budget. -/
theorem canonicalMinimumCostCertificate_verifies
    (maxBudget : Nat)
    (hAccepted :
      table.HasAcceptedCostBudgetUpTo maxBudget) :
    table.verifiesCostCertificate
          (table.selectedMinimumAcceptedCostBudget
            maxBudget
            hAccepted)
          (table.canonicalMinimumCostCertificate
            certificateCode
            maxBudget
            hAccepted) =
        true := by

  exact
    (table.mem_verifiedCostCertificates_iff
      (table.selectedMinimumAcceptedCostBudget
        maxBudget
        hAccepted)).mp
      (correctedConcreteFiniteCanonicalCertificate_mem
        (table.minimumCostCertificateFamily
          maxBudget
          hAccepted)
        certificateCode
        (table.minimumCostCertificateFamily_nonempty
          maxBudget
          hAccepted))

/-- The canonical ordinary certificate realizes exactly the least external
code among minimum-budget certificates. -/
theorem canonicalMinimumCostCertificate_code_eq
    (maxBudget : Nat)
    (hAccepted :
      table.HasAcceptedCostBudgetUpTo maxBudget) :
    certificateCode
          (table.canonicalMinimumCostCertificate
            certificateCode
            maxBudget
            hAccepted) =
        table.canonicalMinimumCostCertificateCode
          certificateCode
          maxBudget
          hAccepted := by

  exact
    correctedConcreteFiniteCanonicalCertificate_code_eq
      (table.minimumCostCertificateFamily
        maxBudget
        hAccepted)
      certificateCode
      (table.minimumCostCertificateFamily_nonempty
        maxBudget
        hAccepted)

/-- The canonical ordinary certificate code is no larger than every competing
certificate accepted at the selected minimum budget. -/
theorem canonicalMinimumCostCertificate_code_le
    (maxBudget : Nat)
    (hAccepted :
      table.HasAcceptedCostBudgetUpTo maxBudget)
    {certificate : Finset ι}
    (hVerify :
      table.verifiesCostCertificate
            (table.selectedMinimumAcceptedCostBudget
              maxBudget
              hAccepted)
            certificate =
          true) :
    certificateCode
          (table.canonicalMinimumCostCertificate
            certificateCode
            maxBudget
            hAccepted) <=
        certificateCode certificate := by

  apply
    correctedConcreteFiniteCanonicalCertificate_code_le
      (table.minimumCostCertificateFamily
        maxBudget
        hAccepted)
      certificateCode
      (table.minimumCostCertificateFamily_nonempty
        maxBudget
        hAccepted)

  exact
    (table.mem_verifiedCostCertificates_iff
      (table.selectedMinimumAcceptedCostBudget
        maxBudget
        hAccepted)).mpr
      hVerify

/-- Every certificate accepted at the selected minimum budget has cost exactly
that budget and represents the target language. -/
theorem verifiedCostCertificate_at_selectedMinimum_semantic_package
    (maxBudget : Nat)
    (hAccepted :
      table.HasAcceptedCostBudgetUpTo maxBudget)
    {certificate : Finset ι}
    (hVerify :
      table.verifiesCostCertificate
            (table.selectedMinimumAcceptedCostBudget
              maxBudget
              hAccepted)
            certificate =
          true) :
    certificate ⊆ U ∧
      selectionCost certificate =
        table.selectedMinimumAcceptedCostBudget
          maxBudget
          hAccepted ∧
      language ∈
        StartRootedCorrectedConcreteTargetClass
          (v := z)
          α
          (↥certificate → M)
          (selectedObservationProduct obsFamily certificate)
          f := by

  let selectedBudget :=
    table.selectedMinimumAcceptedCostBudget
      maxBudget
      hAccepted

  rcases
      (table.verifiesCostCertificate_eq_true_iff
        selectedBudget
        certificate).mp
        hVerify with
    ⟨hSubset, hCostLe, hTarget⟩

  have hVerifyAtExactCost :
      table.verifiesCostCertificate
            (selectionCost certificate)
            certificate =
          true := by

    exact
      (table.verifiesCostCertificate_eq_true_iff
        (selectionCost certificate)
        certificate).mpr
        ⟨hSubset,
          Nat.le_refl _,
          hTarget⟩

  have hDecisionAtExactCost :
      table.costFeasibleDecision
            (selectionCost certificate) =
          true := by

    exact
      (table.costFeasibleDecision_eq_true_iff_exists_verifiedCostCertificate
        (selectionCost certificate)).mpr
        ⟨certificate,
          hVerifyAtExactCost⟩

  have hSelectedBudgetLeMax :
      selectedBudget <= maxBudget :=
    (table.selectedMinimumAcceptedCostBudget_spec
      maxBudget
      hAccepted).1

  have hCostLeMax :
      selectionCost certificate <= maxBudget :=
    Nat.le_trans
      hCostLe
      hSelectedBudgetLeMax

  have hSelectedLeCost :
      selectedBudget <= selectionCost certificate :=
    table.selectedMinimumAcceptedCostBudget_le
      maxBudget
      hAccepted
      hCostLeMax
      hDecisionAtExactCost

  exact
    ⟨hSubset,
      Nat.le_antisymm
        hCostLe
        hSelectedLeCost,
      hTarget⟩

/-- Semantic and minimum-code package for the canonical ordinary-cost
certificate. -/
theorem canonicalMinimumCostCertificate_package
    (maxBudget : Nat)
    (hAccepted :
      table.HasAcceptedCostBudgetUpTo maxBudget) :
    let certificate :=
      table.canonicalMinimumCostCertificate
        certificateCode
        maxBudget
        hAccepted
    let selectedBudget :=
      table.selectedMinimumAcceptedCostBudget
        maxBudget
        hAccepted
    table.verifiesCostCertificate
          selectedBudget
          certificate =
        true ∧
      certificate ⊆ U ∧
      selectionCost certificate = selectedBudget ∧
      language ∈
        StartRootedCorrectedConcreteTargetClass
          (v := z)
          α
          (↥certificate → M)
          (selectedObservationProduct obsFamily certificate)
          f ∧
      certificate.card <= U.card ∧
      certificateCode certificate =
        table.canonicalMinimumCostCertificateCode
          certificateCode
          maxBudget
          hAccepted ∧
      ∀ competing : Finset ι,
        table.verifiesCostCertificate
              selectedBudget
              competing =
            true →
          certificateCode certificate <=
            certificateCode competing := by

  let certificate :=
    table.canonicalMinimumCostCertificate
      certificateCode
      maxBudget
      hAccepted

  let selectedBudget :=
    table.selectedMinimumAcceptedCostBudget
      maxBudget
      hAccepted

  have hVerify :
      table.verifiesCostCertificate
            selectedBudget
            certificate =
          true :=
    table.canonicalMinimumCostCertificate_verifies
      certificateCode
      maxBudget
      hAccepted

  have hSemantic :=
    table.verifiedCostCertificate_at_selectedMinimum_semantic_package
      maxBudget
      hAccepted
      hVerify

  exact
    ⟨hVerify,
      hSemantic.1,
      hSemantic.2.1,
      hSemantic.2.2,
      table.verifiedCostCertificate_card_le hVerify,
      table.canonicalMinimumCostCertificate_code_eq
        certificateCode
        maxBudget
        hAccepted,
      fun competing hCompeting =>
        table.canonicalMinimumCostCertificate_code_le
          certificateCode
          maxBudget
          hAccepted
          hCompeting⟩

/-- If the external certificate code is injective, the canonical ordinary
certificate is the unique accepted certificate with the canonical least code. -/
theorem canonicalMinimumCostCertificate_unique
    (hCodeInjective : Function.Injective certificateCode)
    (maxBudget : Nat)
    (hAccepted :
      table.HasAcceptedCostBudgetUpTo maxBudget)
    {certificate : Finset ι}
    (hVerify :
      table.verifiesCostCertificate
            (table.selectedMinimumAcceptedCostBudget
              maxBudget
              hAccepted)
            certificate =
          true)
    (hCode :
      certificateCode certificate =
        table.canonicalMinimumCostCertificateCode
          certificateCode
          maxBudget
          hAccepted) :
    table.canonicalMinimumCostCertificate
          certificateCode
          maxBudget
          hAccepted =
        certificate := by

  apply
    correctedConcreteFiniteCanonicalCertificate_eq_of_code_eq
      (table.minimumCostCertificateFamily
        maxBudget
        hAccepted)
      certificateCode
      (table.minimumCostCertificateFamily_nonempty
        maxBudget
        hAccepted)
      hCodeInjective
      ((table.mem_verifiedCostCertificates_iff
        (table.selectedMinimumAcceptedCostBudget
          maxBudget
          hAccepted)).mpr
        hVerify)

  exact hCode

end CanonicalMinimumCostCertificate


section CanonicalMinimumParetoCertificate

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

/-- Exact accepted Pareto certificate family at the selected minimum scalar
budget. -/
def minimumParetoScalarCertificateFamily
    (maxBudget : Nat)
    (hAccepted :
      table.HasAcceptedParetoScalarBudgetUpTo maxBudget) :
    Finset (Finset ι) :=
  table.verifiedParetoScalarCertificates
    (table.selectedMinimumAcceptedParetoScalarBudget
      maxBudget
      hAccepted)

/-- The exact minimum Pareto-scalar certificate family is nonempty. -/
theorem minimumParetoScalarCertificateFamily_nonempty
    (maxBudget : Nat)
    (hAccepted :
      table.HasAcceptedParetoScalarBudgetUpTo maxBudget) :
    (table.minimumParetoScalarCertificateFamily
      maxBudget
      hAccepted).Nonempty := by

  apply
    (table.verifiedParetoScalarCertificates_nonempty_iff
      (table.selectedMinimumAcceptedParetoScalarBudget
        maxBudget
        hAccepted)).mpr

  exact
    (table.selectedMinimumAcceptedParetoScalarBudget_spec
      maxBudget
      hAccepted).2

/-- Least external code among all Pareto certificates accepted at the selected
minimum scalar budget. -/
noncomputable def canonicalMinimumParetoScalarCertificateCode
    (maxBudget : Nat)
    (hAccepted :
      table.HasAcceptedParetoScalarBudgetUpTo maxBudget) :
    Nat :=
  correctedConcreteFiniteCertificateLeastCode
    (table.minimumParetoScalarCertificateFamily
      maxBudget
      hAccepted)
    certificateCode
    (table.minimumParetoScalarCertificateFamily_nonempty
      maxBudget
      hAccepted)

/-- Canonical minimum Pareto-scalar certificate selected by least external
certificate code. -/
noncomputable def canonicalMinimumParetoScalarCertificate
    (maxBudget : Nat)
    (hAccepted :
      table.HasAcceptedParetoScalarBudgetUpTo maxBudget) :
    Finset ι :=
  correctedConcreteFiniteCanonicalCertificate
    (table.minimumParetoScalarCertificateFamily
      maxBudget
      hAccepted)
    certificateCode
    (table.minimumParetoScalarCertificateFamily_nonempty
      maxBudget
      hAccepted)

/-- The canonical Pareto certificate is accepted at the selected minimum scalar
budget. -/
theorem canonicalMinimumParetoScalarCertificate_verifies
    (maxBudget : Nat)
    (hAccepted :
      table.HasAcceptedParetoScalarBudgetUpTo maxBudget) :
    table.verifiesParetoScalarCertificate
          (table.selectedMinimumAcceptedParetoScalarBudget
            maxBudget
            hAccepted)
          (table.canonicalMinimumParetoScalarCertificate
            certificateCode
            maxBudget
            hAccepted) =
        true := by

  exact
    (table.mem_verifiedParetoScalarCertificates_iff
      (table.selectedMinimumAcceptedParetoScalarBudget
        maxBudget
        hAccepted)).mp
      (correctedConcreteFiniteCanonicalCertificate_mem
        (table.minimumParetoScalarCertificateFamily
          maxBudget
          hAccepted)
        certificateCode
        (table.minimumParetoScalarCertificateFamily_nonempty
          maxBudget
          hAccepted))

/-- The canonical Pareto certificate realizes the least external code among all
minimum-scalar Pareto certificates. -/
theorem canonicalMinimumParetoScalarCertificate_code_eq
    (maxBudget : Nat)
    (hAccepted :
      table.HasAcceptedParetoScalarBudgetUpTo maxBudget) :
    certificateCode
          (table.canonicalMinimumParetoScalarCertificate
            certificateCode
            maxBudget
            hAccepted) =
        table.canonicalMinimumParetoScalarCertificateCode
          certificateCode
          maxBudget
          hAccepted := by

  exact
    correctedConcreteFiniteCanonicalCertificate_code_eq
      (table.minimumParetoScalarCertificateFamily
        maxBudget
        hAccepted)
      certificateCode
      (table.minimumParetoScalarCertificateFamily_nonempty
        maxBudget
        hAccepted)

/-- The canonical Pareto certificate code is no larger than every competing
certificate accepted at the selected minimum scalar budget. -/
theorem canonicalMinimumParetoScalarCertificate_code_le
    (maxBudget : Nat)
    (hAccepted :
      table.HasAcceptedParetoScalarBudgetUpTo maxBudget)
    {certificate : Finset ι}
    (hVerify :
      table.verifiesParetoScalarCertificate
            (table.selectedMinimumAcceptedParetoScalarBudget
              maxBudget
              hAccepted)
            certificate =
          true) :
    certificateCode
          (table.canonicalMinimumParetoScalarCertificate
            certificateCode
            maxBudget
            hAccepted) <=
        certificateCode certificate := by

  apply
    correctedConcreteFiniteCanonicalCertificate_code_le
      (table.minimumParetoScalarCertificateFamily
        maxBudget
        hAccepted)
      certificateCode
      (table.minimumParetoScalarCertificateFamily_nonempty
        maxBudget
        hAccepted)

  exact
    (table.mem_verifiedParetoScalarCertificates_iff
      (table.selectedMinimumAcceptedParetoScalarBudget
        maxBudget
        hAccepted)).mpr
      hVerify

/-- Every Pareto certificate accepted at the selected minimum scalar budget has
scalar value exactly that budget. -/
theorem verifiedParetoScalarCertificate_at_selectedMinimum_semantic_package
    (maxBudget : Nat)
    (hAccepted :
      table.HasAcceptedParetoScalarBudgetUpTo maxBudget)
    {certificate : Finset ι}
    (hVerify :
      table.verifiesParetoScalarCertificate
            (table.selectedMinimumAcceptedParetoScalarBudget
              maxBudget
              hAccepted)
            certificate =
          true) :
    CorrectedConcreteObservationSelectionParetoOptimal
        (z := z)
        obsFamily
        f
        selectionCost
        U
        language
        certificate ∧
      correctedConcreteObservationSelectionParetoScalarCost
            selectionCost certificate =
        table.selectedMinimumAcceptedParetoScalarBudget
          maxBudget
          hAccepted := by

  let selectedBudget :=
    table.selectedMinimumAcceptedParetoScalarBudget
      maxBudget
      hAccepted

  rcases
      (table.verifiesParetoScalarCertificate_eq_true_iff
        selectedBudget
        certificate).mp
        hVerify with
    ⟨hPareto, hScalarLe⟩

  have hVerifyAtExactScalar :
      table.verifiesParetoScalarCertificate
            (correctedConcreteObservationSelectionParetoScalarCost
              selectionCost certificate)
            certificate =
          true := by

    exact
      (table.verifiesParetoScalarCertificate_eq_true_iff
        (correctedConcreteObservationSelectionParetoScalarCost
          selectionCost certificate)
        certificate).mpr
        ⟨hPareto,
          Nat.le_refl _⟩

  have hDecisionAtExactScalar :
      table.paretoScalarFeasibleDecision
            (correctedConcreteObservationSelectionParetoScalarCost
              selectionCost certificate) =
          true := by

    exact
      (table.paretoScalarFeasibleDecision_eq_true_iff_exists_verifiedCertificate
        (correctedConcreteObservationSelectionParetoScalarCost
          selectionCost certificate)).mpr
        ⟨certificate,
          hVerifyAtExactScalar⟩

  have hSelectedBudgetLeMax :
      selectedBudget <= maxBudget :=
    (table.selectedMinimumAcceptedParetoScalarBudget_spec
      maxBudget
      hAccepted).1

  have hScalarLeMax :
      correctedConcreteObservationSelectionParetoScalarCost
            selectionCost certificate <=
          maxBudget :=
    Nat.le_trans
      hScalarLe
      hSelectedBudgetLeMax

  have hSelectedLeScalar :
      selectedBudget <=
        correctedConcreteObservationSelectionParetoScalarCost
          selectionCost certificate :=
    table.selectedMinimumAcceptedParetoScalarBudget_le
      maxBudget
      hAccepted
      hScalarLeMax
      hDecisionAtExactScalar

  exact
    ⟨hPareto,
      Nat.le_antisymm
        hScalarLe
        hSelectedLeScalar⟩

/-- Semantic and minimum-code package for the canonical Pareto-scalar
certificate. -/
theorem canonicalMinimumParetoScalarCertificate_package
    (maxBudget : Nat)
    (hAccepted :
      table.HasAcceptedParetoScalarBudgetUpTo maxBudget) :
    let certificate :=
      table.canonicalMinimumParetoScalarCertificate
        certificateCode
        maxBudget
        hAccepted
    let selectedBudget :=
      table.selectedMinimumAcceptedParetoScalarBudget
        maxBudget
        hAccepted
    table.verifiesParetoScalarCertificate
          selectedBudget
          certificate =
        true ∧
      CorrectedConcreteObservationSelectionParetoOptimal
        (z := z)
        obsFamily
        f
        selectionCost
        U
        language
        certificate ∧
      correctedConcreteObservationSelectionParetoScalarCost
            selectionCost certificate =
        selectedBudget ∧
      certificate.card <= U.card ∧
      certificateCode certificate =
        table.canonicalMinimumParetoScalarCertificateCode
          certificateCode
          maxBudget
          hAccepted ∧
      ∀ competing : Finset ι,
        table.verifiesParetoScalarCertificate
              selectedBudget
              competing =
            true →
          certificateCode certificate <=
            certificateCode competing := by

  let certificate :=
    table.canonicalMinimumParetoScalarCertificate
      certificateCode
      maxBudget
      hAccepted

  let selectedBudget :=
    table.selectedMinimumAcceptedParetoScalarBudget
      maxBudget
      hAccepted

  have hVerify :
      table.verifiesParetoScalarCertificate
            selectedBudget
            certificate =
          true :=
    table.canonicalMinimumParetoScalarCertificate_verifies
      certificateCode
      maxBudget
      hAccepted

  have hSemantic :=
    table.verifiedParetoScalarCertificate_at_selectedMinimum_semantic_package
      maxBudget
      hAccepted
      hVerify

  exact
    ⟨hVerify,
      hSemantic.1,
      hSemantic.2,
      table.verifiedParetoScalarCertificate_card_le hVerify,
      table.canonicalMinimumParetoScalarCertificate_code_eq
        certificateCode
        maxBudget
        hAccepted,
      fun competing hCompeting =>
        table.canonicalMinimumParetoScalarCertificate_code_le
          certificateCode
          maxBudget
          hAccepted
          hCompeting⟩

/-- If the external code is injective, the canonical Pareto certificate is the
unique accepted certificate with the canonical least code. -/
theorem canonicalMinimumParetoScalarCertificate_unique
    (hCodeInjective : Function.Injective certificateCode)
    (maxBudget : Nat)
    (hAccepted :
      table.HasAcceptedParetoScalarBudgetUpTo maxBudget)
    {certificate : Finset ι}
    (hVerify :
      table.verifiesParetoScalarCertificate
            (table.selectedMinimumAcceptedParetoScalarBudget
              maxBudget
              hAccepted)
            certificate =
          true)
    (hCode :
      certificateCode certificate =
        table.canonicalMinimumParetoScalarCertificateCode
          certificateCode
          maxBudget
          hAccepted) :
    table.canonicalMinimumParetoScalarCertificate
          certificateCode
          maxBudget
          hAccepted =
        certificate := by

  apply
    correctedConcreteFiniteCanonicalCertificate_eq_of_code_eq
      (table.minimumParetoScalarCertificateFamily
        maxBudget
        hAccepted)
      certificateCode
      (table.minimumParetoScalarCertificateFamily_nonempty
        maxBudget
        hAccepted)
      hCodeInjective
      ((table.mem_verifiedParetoScalarCertificates_iff
        (table.selectedMinimumAcceptedParetoScalarBudget
          maxBudget
          hAccepted)).mpr
        hVerify)

  exact hCode

end CanonicalMinimumParetoCertificate

end CorrectedConcreteObservationSelectionDecisionTable


section CanonicalMinimumCertificateFinalPackage

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

/-- Final canonical positive-additive certificate package for the canonical
semantic decision table.  The selected certificate is Pareto optimal, realizes
the exact semantic positive-additive minimum rank, and has least external code
among every minimum-rank Pareto certificate. -/
theorem
    correctedConcreteWorkingGrammar_observationSelectionCanonicalMinimumCertificate_package
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
          hTarget ∧
      certificate.card <= U.card ∧
      certificateCode certificate =
        table.canonicalMinimumParetoScalarCertificateCode
          certificateCode
          maxBudget
          hAccepted ∧
      ∀ competing : Finset ι,
        table.verifiesParetoScalarCertificate
              (ambientTargetObservationSelectionPositiveAdditiveMinimumCost
                (z := z)
                obsFamily
                f
                coordinateWeight
                U
                hTarget)
              competing =
            true →
          certificateCode certificate <=
            certificateCode competing := by

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

  have hPackage :=
    table.canonicalMinimumParetoScalarCertificate_package
      certificateCode
      maxBudget
      hAccepted

  have hBudgetExact :=
    table.selectedMinimumAcceptedParetoScalarBudget_eq_positiveAdditiveMinimum
      hTarget
      maxBudget
      hBound

  exact
    ⟨hPackage.2.1,
      hPackage.2.2.1.trans hBudgetExact,
      hPackage.2.2.2.1,
      hPackage.2.2.2.2.1,
      fun competing hCompeting =>
        hPackage.2.2.2.2.2 competing
          (by
            rw [hBudgetExact]
            exact hCompeting)⟩

end CanonicalMinimumCertificateFinalPackage

end MCFG
