/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG2.ConcreteCanonicalLearnerWorkingGrammarObservationSelectionCanonicalMinimumCertificateSearch
import Mathlib.Data.Fintype.Powerset

/-!
# ConcreteCanonicalLearnerWorkingGrammarObservationSelectionDenseCertificateEncoding.lean

The preceding observation-selection files construct finite Boolean decision
procedures, bounded subset certificates, minimum-budget selectors, least-code
canonical certificates, and finite canonical searches.  Their last uniqueness
theorem still receives an external function

```text
certificateCode : Finset ι → Nat
```

and assumes that this function is injective on all finite subsets of `ι`.
That assumption is unnecessarily strong because every verified certificate is
contained in the fixed finite ambient coordinate set `U`.

This file removes the external coding hypothesis.  A certificate is first
restricted to the finite subtype `↥U`.  The finite type `Finset ↥U` has exactly
`2 ^ U.card` elements, so `Fintype.equivFin` gives a dense code in
`Fin (2 ^ U.card)`.  The resulting natural-number code has the following
properties:

```text
code certificate < 2 ^ U.card;
certificates contained in U are separated by the code;
a checked decoder recovers every certificate contained in U;
every successfully decoded certificate is contained in U.
```

The restricted injectivity theorem is exactly what the canonical search needs:
all members of the verified search, including its selected canonical member,
are already known to be subsets of `U`.  We therefore prove singleton search
results for ordinary-cost and Pareto-scalar certificates without any external
coding function or injectivity assumption.

The final positive-additive package supplies the intrinsic dense code, its
checked decoder, the exact `2 ^ U.card` range bound, the singleton canonical
search, Pareto optimality, and equality with the semantic minimum rank.

The use of `Fintype.equivFin` is noncomputable because no ordering of the
arbitrary coordinate type `ι` has been chosen.  The code is nevertheless
intrinsic to the finite universe and removes the previous *logical* external
coding assumption.  A later executable layer may replace this classical
finite equivalence by a list- or index-based coordinate representation.

No machine-cost, NP-membership, or hardness claim is made here.
No target grammar is supplied to any learner.
No `sorry`, `admit`, or `axiom` is used.
-/

namespace MCFG

universe u v w z

section DenseCertificateCore

variable {ι : Type v}
variable [DecidableEq ι]

/-- Restrict an arbitrary finite certificate to the finite subtype `↥U`. -/
def correctedConcreteDenseCertificateRestriction
    (U : Finset ι)
    (certificate : Finset ι) :
    Finset ↥U :=
  U.attach.filter
    (fun coordinate => (coordinate : ι) ∈ certificate)

/-- Forget the subtype proofs of a finite certificate over `↥U`. -/
def correctedConcreteDenseCertificateLift
    (U : Finset ι)
    (certificate : Finset ↥U) :
    Finset ι :=
  certificate.image (fun coordinate => (coordinate : ι))

@[simp]
theorem mem_correctedConcreteDenseCertificateRestriction
    (U : Finset ι)
    (certificate : Finset ι)
    (coordinate : ↥U) :
    coordinate ∈
        correctedConcreteDenseCertificateRestriction U certificate ↔
      (coordinate : ι) ∈ certificate := by

  simp [correctedConcreteDenseCertificateRestriction]

@[simp]
theorem mem_correctedConcreteDenseCertificateLift
    (U : Finset ι)
    (certificate : Finset ↥U)
    (coordinate : ↥U) :
    (coordinate : ι) ∈
        correctedConcreteDenseCertificateLift U certificate ↔
      coordinate ∈ certificate := by

  classical
  simp [correctedConcreteDenseCertificateLift]

/-- Every lifted subtype certificate is contained in its ambient universe. -/
theorem correctedConcreteDenseCertificateLift_subset
    (U : Finset ι)
    (certificate : Finset ↥U) :
    correctedConcreteDenseCertificateLift U certificate ⊆ U := by

  intro coordinate hCoordinate

  rcases Finset.mem_image.mp hCoordinate with
    ⟨typedCoordinate, hTypedCoordinate, rfl⟩

  exact typedCoordinate.property

/-- Restricting and then lifting recovers every certificate already contained
in `U`. -/
theorem correctedConcreteDenseCertificateLift_restriction_eq_of_subset
    (U : Finset ι)
    {certificate : Finset ι}
    (hSubset : certificate ⊆ U) :
    correctedConcreteDenseCertificateLift U
        (correctedConcreteDenseCertificateRestriction U certificate) =
      certificate := by

  classical
  ext coordinate
  constructor

  · intro hCoordinate

    rcases Finset.mem_image.mp hCoordinate with
      ⟨typedCoordinate, hTypedCoordinate, rfl⟩

    exact
      (Finset.mem_filter.mp hTypedCoordinate).2

  · intro hCoordinate

    have hAmbient : coordinate ∈ U :=
      hSubset hCoordinate

    apply Finset.mem_image.mpr

    refine
      ⟨⟨coordinate, hAmbient⟩,
        ?_,
        rfl⟩

    exact
      Finset.mem_filter.mpr
        ⟨by simp,
          hCoordinate⟩

/-- Lifting and then restricting is exactly the identity on subtype
certificates. -/
theorem correctedConcreteDenseCertificateRestriction_lift_eq
    (U : Finset ι)
    (certificate : Finset ↥U) :
    correctedConcreteDenseCertificateRestriction U
        (correctedConcreteDenseCertificateLift U certificate) =
      certificate := by

  classical
  ext coordinate
  constructor

  · intro hCoordinate

    have hLifted :
        (coordinate : ι) ∈
          correctedConcreteDenseCertificateLift U certificate :=
      (Finset.mem_filter.mp hCoordinate).2

    rcases Finset.mem_image.mp hLifted with
      ⟨otherCoordinate, hOtherCoordinate, hValue⟩

    have hCoordinateEq : otherCoordinate = coordinate :=
      Subtype.ext hValue

    simpa [hCoordinateEq] using hOtherCoordinate

  · intro hCoordinate

    exact
      Finset.mem_filter.mpr
        ⟨by simp,
          Finset.mem_image.mpr
            ⟨coordinate,
              hCoordinate,
              rfl⟩⟩

/-- The intrinsic dense code of an observation-subset certificate.

The certificate is first restricted to `U`, then viewed as an element of the
finite type `Finset ↥U`, and finally sent to its canonical finite index supplied
by `Fintype.equivFin`. -/
noncomputable def correctedConcreteDenseCertificateCode
    (U : Finset ι)
    (certificate : Finset ι) :
    Nat :=
  ((Fintype.equivFin (Finset ↥U))
      (correctedConcreteDenseCertificateRestriction U certificate)).val

/-- The dense code lies below the cardinality of the finite certificate type. -/
theorem correctedConcreteDenseCertificateCode_lt_card
    (U : Finset ι)
    (certificate : Finset ι) :
    correctedConcreteDenseCertificateCode U certificate <
      Fintype.card (Finset ↥U) := by

  exact
    ((Fintype.equivFin (Finset ↥U))
      (correctedConcreteDenseCertificateRestriction U certificate)).isLt

/-- The finite certificate type has exactly `2 ^ U.card` elements. -/
theorem correctedConcreteDenseCertificateType_card
    (U : Finset ι) :
    Fintype.card (Finset ↥U) = 2 ^ U.card := by

  simp

/-- Paper-facing dense-code range bound. -/
theorem correctedConcreteDenseCertificateCode_lt_two_pow
    (U : Finset ι)
    (certificate : Finset ι) :
    correctedConcreteDenseCertificateCode U certificate <
      2 ^ U.card := by

  simpa [correctedConcreteDenseCertificateType_card] using
    correctedConcreteDenseCertificateCode_lt_card U certificate

/-- The intrinsic dense code is injective on the only domain relevant to the
selection problem: certificates contained in `U`. -/
theorem correctedConcreteDenseCertificateCode_injective_on_subsets
    (U : Finset ι)
    {first second : Finset ι}
    (hFirst : first ⊆ U)
    (hSecond : second ⊆ U)
    (hCode :
      correctedConcreteDenseCertificateCode U first =
        correctedConcreteDenseCertificateCode U second) :
    first = second := by

  have hFinValue :
      ((Fintype.equivFin (Finset ↥U))
          (correctedConcreteDenseCertificateRestriction U first)).val =
        ((Fintype.equivFin (Finset ↥U))
          (correctedConcreteDenseCertificateRestriction U second)).val := by

    simpa [correctedConcreteDenseCertificateCode] using hCode

  have hFin :
      (Fintype.equivFin (Finset ↥U))
          (correctedConcreteDenseCertificateRestriction U first) =
        (Fintype.equivFin (Finset ↥U))
          (correctedConcreteDenseCertificateRestriction U second) :=
    Fin.ext hFinValue

  have hRestriction :
      correctedConcreteDenseCertificateRestriction U first =
        correctedConcreteDenseCertificateRestriction U second :=
    (Fintype.equivFin (Finset ↥U)).injective hFin

  calc
    first =
        correctedConcreteDenseCertificateLift U
          (correctedConcreteDenseCertificateRestriction U first) :=
      (correctedConcreteDenseCertificateLift_restriction_eq_of_subset
        U
        hFirst).symm
    _ =
        correctedConcreteDenseCertificateLift U
          (correctedConcreteDenseCertificateRestriction U second) := by
      rw [hRestriction]
    _ = second :=
      correctedConcreteDenseCertificateLift_restriction_eq_of_subset
        U
        hSecond

/-- Checked decoder for the intrinsic dense certificate code. -/
noncomputable def correctedConcreteDenseCertificateDecode
    (U : Finset ι)
    (code : Nat) :
    Option (Finset ι) :=
  if hCode : code < Fintype.card (Finset ↥U) then
    some
      (correctedConcreteDenseCertificateLift U
        ((Fintype.equivFin (Finset ↥U)).symm
          ⟨code, hCode⟩))
  else
    none

/-- Every certificate contained in `U` survives the dense checked
encode/decode round trip. -/
theorem correctedConcreteDenseCertificateDecode_encode_of_subset
    (U : Finset ι)
    {certificate : Finset ι}
    (hSubset : certificate ⊆ U) :
    correctedConcreteDenseCertificateDecode U
        (correctedConcreteDenseCertificateCode U certificate) =
      some certificate := by

  let encodedFin : Fin (Fintype.card (Finset ↥U)) :=
    (Fintype.equivFin (Finset ↥U))
      (correctedConcreteDenseCertificateRestriction U certificate)

  have hBound :
      correctedConcreteDenseCertificateCode U certificate <
        Fintype.card (Finset ↥U) :=
    correctedConcreteDenseCertificateCode_lt_card U certificate

  have hEncodedFin :
      (⟨correctedConcreteDenseCertificateCode U certificate,
          hBound⟩ :
        Fin (Fintype.card (Finset ↥U))) =
        encodedFin := by

    apply Fin.ext
    simp [
      encodedFin,
      correctedConcreteDenseCertificateCode
    ]

  rw [
    correctedConcreteDenseCertificateDecode,
    dif_pos hBound
  ]

  apply congrArg some

  rw [hEncodedFin]

  change
    correctedConcreteDenseCertificateLift U
        ((Fintype.equivFin (Finset ↥U)).symm
          ((Fintype.equivFin (Finset ↥U))
            (correctedConcreteDenseCertificateRestriction U certificate))) =
      certificate

  rw [Equiv.symm_apply_apply]

  exact
    correctedConcreteDenseCertificateLift_restriction_eq_of_subset
      U
      hSubset

/-- Every successful dense decoding is an ambient certificate contained in
`U`. -/
theorem correctedConcreteDenseCertificateDecode_subset
    (U : Finset ι)
    {code : Nat}
    {certificate : Finset ι}
    (hDecode :
      correctedConcreteDenseCertificateDecode U code =
        some certificate) :
    certificate ⊆ U := by

  by_cases hCode : code < Fintype.card (Finset ↥U)

  · rw [
      correctedConcreteDenseCertificateDecode,
      dif_pos hCode
    ] at hDecode

    have hCertificate :
        correctedConcreteDenseCertificateLift U
            ((Fintype.equivFin (Finset ↥U)).symm
              ⟨code, hCode⟩) =
          certificate :=
      Option.some.inj hDecode

    rw [← hCertificate]

    exact
      correctedConcreteDenseCertificateLift_subset
        U
        ((Fintype.equivFin (Finset ↥U)).symm
          ⟨code, hCode⟩)

  · rw [
      correctedConcreteDenseCertificateDecode,
      dif_neg hCode
    ] at hDecode

    simp at hDecode

/-- The dense decoder rejects every natural number outside its exact finite
range. -/
theorem correctedConcreteDenseCertificateDecode_eq_none_of_le
    (U : Finset ι)
    {code : Nat}
    (hCode : 2 ^ U.card <= code) :
    correctedConcreteDenseCertificateDecode U code = none := by

  rw [correctedConcreteDenseCertificateDecode]
  apply dif_neg

  intro hContradiction

  have hRange : code < 2 ^ U.card := by
    simpa [correctedConcreteDenseCertificateType_card] using hContradiction

  exact (not_lt_of_ge hCode) hRange

/-- Core dense-code package. -/
theorem correctedConcreteDenseCertificateEncoding_package
    (U : Finset ι)
    {certificate : Finset ι}
    (hSubset : certificate ⊆ U) :
    correctedConcreteDenseCertificateCode U certificate <
        2 ^ U.card ∧
      correctedConcreteDenseCertificateDecode U
          (correctedConcreteDenseCertificateCode U certificate) =
        some certificate ∧
      ∀ competing : Finset ι,
        competing ⊆ U →
        correctedConcreteDenseCertificateCode U competing =
          correctedConcreteDenseCertificateCode U certificate →
        competing = certificate := by

  exact
    ⟨correctedConcreteDenseCertificateCode_lt_two_pow
        U
        certificate,
      correctedConcreteDenseCertificateDecode_encode_of_subset
        U
        hSubset,
      fun competing hCompeting hCode =>
        correctedConcreteDenseCertificateCode_injective_on_subsets
          U
          hCompeting
          hSubset
          hCode⟩

end DenseCertificateCore


namespace CorrectedConcreteObservationSelectionDecisionTable

section DenseCanonicalMinimumCostCertificateSearch

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

/-- The ordinary-cost canonical search is a singleton for the intrinsic dense
certificate code.  Only restricted injectivity is needed because verification
already proves that every search result is contained in `U`. -/
theorem canonicalMinimumCostCertificateSearch_dense_eq_singleton
    (maxBudget : Nat)
    (hAccepted :
      table.HasAcceptedCostBudgetUpTo maxBudget) :
    table.canonicalMinimumCostCertificateSearch
          (correctedConcreteDenseCertificateCode U)
          maxBudget
          hAccepted =
        {table.canonicalMinimumCostCertificate
          (correctedConcreteDenseCertificateCode U)
          maxBudget
          hAccepted} := by

  apply Finset.ext
  intro certificate
  constructor

  · intro hCertificate

    have hVerify :
        table.verifiesCostCertificate
              (table.selectedMinimumAcceptedCostBudget
                maxBudget
                hAccepted)
              certificate =
            true :=
      table.canonicalMinimumCostCertificateSearch_verifies
        (correctedConcreteDenseCertificateCode U)
        maxBudget
        hAccepted
        hCertificate

    have hSubset : certificate ⊆ U :=
      table.verifiedCostCertificate_subset hVerify

    have hCanonicalVerify :
        table.verifiesCostCertificate
              (table.selectedMinimumAcceptedCostBudget
                maxBudget
                hAccepted)
              (table.canonicalMinimumCostCertificate
                (correctedConcreteDenseCertificateCode U)
                maxBudget
                hAccepted) =
            true :=
      table.canonicalMinimumCostCertificate_verifies
        (correctedConcreteDenseCertificateCode U)
        maxBudget
        hAccepted

    have hCanonicalSubset :
        table.canonicalMinimumCostCertificate
              (correctedConcreteDenseCertificateCode U)
              maxBudget
              hAccepted ⊆
            U :=
      table.verifiedCostCertificate_subset hCanonicalVerify

    have hCode :
        correctedConcreteDenseCertificateCode U certificate =
          correctedConcreteDenseCertificateCode U
            (table.canonicalMinimumCostCertificate
              (correctedConcreteDenseCertificateCode U)
              maxBudget
              hAccepted) :=
      (table.canonicalMinimumCostCertificateSearch_code_eq
        (correctedConcreteDenseCertificateCode U)
        maxBudget
        hAccepted
        hCertificate).trans
        (table.canonicalMinimumCostCertificate_code_eq
          (correctedConcreteDenseCertificateCode U)
          maxBudget
          hAccepted).symm

    have hCertificateEq :
        certificate =
          table.canonicalMinimumCostCertificate
            (correctedConcreteDenseCertificateCode U)
            maxBudget
            hAccepted :=
      correctedConcreteDenseCertificateCode_injective_on_subsets
        U
        hSubset
        hCanonicalSubset
        hCode

    exact
      Finset.mem_singleton.mpr hCertificateEq

  · intro hCertificate

    have hCertificateEq :
        certificate =
          table.canonicalMinimumCostCertificate
            (correctedConcreteDenseCertificateCode U)
            maxBudget
            hAccepted :=
      Finset.mem_singleton.mp hCertificate

    subst certificate

    exact
      table.canonicalMinimumCostCertificate_mem_search
        (correctedConcreteDenseCertificateCode U)
        maxBudget
        hAccepted

/-- The intrinsic dense ordinary-cost canonical search has exactly one
member. -/
theorem canonicalMinimumCostCertificateSearch_dense_card_eq_one
    (maxBudget : Nat)
    (hAccepted :
      table.HasAcceptedCostBudgetUpTo maxBudget) :
    (table.canonicalMinimumCostCertificateSearch
      (correctedConcreteDenseCertificateCode U)
      maxBudget
      hAccepted).card = 1 := by

  simp only [
    table.canonicalMinimumCostCertificateSearch_dense_eq_singleton
      maxBudget
      hAccepted,
    Finset.card_singleton
  ]

end DenseCanonicalMinimumCostCertificateSearch


section DenseCanonicalMinimumParetoScalarCertificateSearch

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

/-- The Pareto-scalar canonical search is a singleton for the intrinsic dense
certificate code. -/
theorem canonicalMinimumParetoScalarCertificateSearch_dense_eq_singleton
    (maxBudget : Nat)
    (hAccepted :
      table.HasAcceptedParetoScalarBudgetUpTo maxBudget) :
    table.canonicalMinimumParetoScalarCertificateSearch
          (correctedConcreteDenseCertificateCode U)
          maxBudget
          hAccepted =
        {table.canonicalMinimumParetoScalarCertificate
          (correctedConcreteDenseCertificateCode U)
          maxBudget
          hAccepted} := by

  apply Finset.ext
  intro certificate
  constructor

  · intro hCertificate

    have hVerify :
        table.verifiesParetoScalarCertificate
              (table.selectedMinimumAcceptedParetoScalarBudget
                maxBudget
                hAccepted)
              certificate =
            true :=
      table.canonicalMinimumParetoScalarCertificateSearch_verifies
        (correctedConcreteDenseCertificateCode U)
        maxBudget
        hAccepted
        hCertificate

    have hSubset : certificate ⊆ U :=
      ((table.verifiesParetoScalarCertificate_eq_true_iff
        (table.selectedMinimumAcceptedParetoScalarBudget
          maxBudget
          hAccepted)
        certificate).mp
        hVerify).1.1

    have hCanonicalVerify :
        table.verifiesParetoScalarCertificate
              (table.selectedMinimumAcceptedParetoScalarBudget
                maxBudget
                hAccepted)
              (table.canonicalMinimumParetoScalarCertificate
                (correctedConcreteDenseCertificateCode U)
                maxBudget
                hAccepted) =
            true :=
      table.canonicalMinimumParetoScalarCertificate_verifies
        (correctedConcreteDenseCertificateCode U)
        maxBudget
        hAccepted

    have hCanonicalSubset :
        table.canonicalMinimumParetoScalarCertificate
              (correctedConcreteDenseCertificateCode U)
              maxBudget
              hAccepted ⊆
            U :=
      ((table.verifiesParetoScalarCertificate_eq_true_iff
        (table.selectedMinimumAcceptedParetoScalarBudget
          maxBudget
          hAccepted)
        (table.canonicalMinimumParetoScalarCertificate
          (correctedConcreteDenseCertificateCode U)
          maxBudget
          hAccepted)).mp
        hCanonicalVerify).1.1

    have hCode :
        correctedConcreteDenseCertificateCode U certificate =
          correctedConcreteDenseCertificateCode U
            (table.canonicalMinimumParetoScalarCertificate
              (correctedConcreteDenseCertificateCode U)
              maxBudget
              hAccepted) :=
      (table.canonicalMinimumParetoScalarCertificateSearch_code_eq
        (correctedConcreteDenseCertificateCode U)
        maxBudget
        hAccepted
        hCertificate).trans
        (table.canonicalMinimumParetoScalarCertificate_code_eq
          (correctedConcreteDenseCertificateCode U)
          maxBudget
          hAccepted).symm

    have hCertificateEq :
        certificate =
          table.canonicalMinimumParetoScalarCertificate
            (correctedConcreteDenseCertificateCode U)
            maxBudget
            hAccepted :=
      correctedConcreteDenseCertificateCode_injective_on_subsets
        U
        hSubset
        hCanonicalSubset
        hCode

    exact
      Finset.mem_singleton.mpr hCertificateEq

  · intro hCertificate

    have hCertificateEq :
        certificate =
          table.canonicalMinimumParetoScalarCertificate
            (correctedConcreteDenseCertificateCode U)
            maxBudget
            hAccepted :=
      Finset.mem_singleton.mp hCertificate

    subst certificate

    exact
      table.canonicalMinimumParetoScalarCertificate_mem_search
        (correctedConcreteDenseCertificateCode U)
        maxBudget
        hAccepted

/-- The intrinsic dense Pareto-scalar canonical search has exactly one
member. -/
theorem canonicalMinimumParetoScalarCertificateSearch_dense_card_eq_one
    (maxBudget : Nat)
    (hAccepted :
      table.HasAcceptedParetoScalarBudgetUpTo maxBudget) :
    (table.canonicalMinimumParetoScalarCertificateSearch
      (correctedConcreteDenseCertificateCode U)
      maxBudget
      hAccepted).card = 1 := by

  simp only [
    table.canonicalMinimumParetoScalarCertificateSearch_dense_eq_singleton
      maxBudget
      hAccepted,
    Finset.card_singleton
  ]

end DenseCanonicalMinimumParetoScalarCertificateSearch

end CorrectedConcreteObservationSelectionDecisionTable


section DenseCertificateEncodingFinalPackage

variable {α : Type u}
variable {ι : Type v}
variable {M : Type w}
variable [DecidableEq ι]
variable [Monoid M]
variable (obsFamily : ι → α → M)
variable (f : Nat)
variable (coordinateWeight : ι → Nat)
variable (U : Finset ι)

/-- Final intrinsic dense-certificate package for positive-additive observation
selection.  No external certificate code and no external injectivity hypothesis
remain. -/
theorem
    correctedConcreteWorkingGrammar_observationSelectionDenseCertificateEncoding_package
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
    table.canonicalMinimumParetoScalarCertificateSearch
          (correctedConcreteDenseCertificateCode U)
          maxBudget
          hAccepted =
        {certificate} ∧
      (table.canonicalMinimumParetoScalarCertificateSearch
        (correctedConcreteDenseCertificateCode U)
        maxBudget
        hAccepted).card = 1 ∧
      correctedConcreteDenseCertificateCode U certificate <
        2 ^ U.card ∧
      correctedConcreteDenseCertificateDecode U
          (correctedConcreteDenseCertificateCode U certificate) =
        some certificate ∧
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

  have hCanonicalPackage :=
    correctedConcreteWorkingGrammar_observationSelectionCanonicalMinimumCertificate_package
      (z := z)
      obsFamily
      f
      coordinateWeight
      U
      (correctedConcreteDenseCertificateCode U)
      language
      hTarget

  have hSubset : certificate ⊆ U :=
    hCanonicalPackage.1.1

  exact
    ⟨table.canonicalMinimumParetoScalarCertificateSearch_dense_eq_singleton
        maxBudget
        hAccepted,
      table.canonicalMinimumParetoScalarCertificateSearch_dense_card_eq_one
        maxBudget
        hAccepted,
      correctedConcreteDenseCertificateCode_lt_two_pow
        U
        certificate,
      correctedConcreteDenseCertificateDecode_encode_of_subset
        U
        hSubset,
      hCanonicalPackage.1,
      hCanonicalPackage.2.1⟩

end DenseCertificateEncodingFinalPackage

end MCFG
