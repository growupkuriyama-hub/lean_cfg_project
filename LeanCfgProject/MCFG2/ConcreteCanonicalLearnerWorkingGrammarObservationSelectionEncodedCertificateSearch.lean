/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG2.ConcreteCanonicalLearnerWorkingGrammarObservationSelectionDenseCertificateEncoding

/-!
# ConcreteCanonicalLearnerWorkingGrammarObservationSelectionEncodedCertificateSearch.lean

The preceding file gives an intrinsic dense code and checked decoder for every
observation-selection certificate contained in the finite coordinate universe
`U`.  This file turns that code into the actual finite search space used by the
decision layer.

Instead of enumerating `Finset ι` directly, the search ranges over

```text
0, 1, ..., 2 ^ U.card - 1.
```

A code is accepted exactly when the dense decoder succeeds and the decoded
certificate passes the existing Boolean verifier.  We construct both the
ordinary-cost and Pareto-scalar code searches and prove:

```text
membership = range membership + successful encoded verification;
semantic Boolean decision = existence of an accepted dense code;
accepted code search is nonempty exactly on positive instances;
accepted code search has cardinality at most 2 ^ U.card;
the code of every accepted subset certificate occurs in the encoded search;
every accepted code decodes to a verified certificate contained in U.
```

At the selected minimum budget, the intrinsic code of the previously selected
canonical certificate belongs to the encoded search.  Filtering by that code
gives an explicit singleton canonical code search, for ordinary cost and for
Pareto scalar cost.

This removes direct powerset objects from the *search index*: the search index
is now a bounded natural number.  The underlying dense equivalence still uses
`Fintype.equivFin`, so this is a finite encoded search theorem rather than a
machine-time or fully executable implementation theorem.  No NP-membership or
hardness claim is made here.

No target grammar is supplied to any learner.
No `sorry`, `admit`, or `axiom` is used.
-/

namespace MCFG

universe u v w z

section DenseCertificateCodeUniverse

variable {ι : Type v}

/-- Exact finite universe of intrinsic dense certificate codes. -/
def correctedConcreteDenseCertificateCodeUniverse
    (U : Finset ι) :
    Finset Nat :=
  Finset.range (2 ^ U.card)

@[simp]
theorem mem_correctedConcreteDenseCertificateCodeUniverse
    (U : Finset ι)
    (code : Nat) :
    code ∈ correctedConcreteDenseCertificateCodeUniverse U ↔
      code < 2 ^ U.card := by

  simp [correctedConcreteDenseCertificateCodeUniverse]

/-- The dense code universe has exactly the expected number of members. -/
theorem correctedConcreteDenseCertificateCodeUniverse_card
    (U : Finset ι) :
    (correctedConcreteDenseCertificateCodeUniverse U).card =
      2 ^ U.card := by

  simp [correctedConcreteDenseCertificateCodeUniverse]

end DenseCertificateCodeUniverse


namespace CorrectedConcreteObservationSelectionDecisionTable

section EncodedCostCertificateSearch

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

/-- Boolean verification of a bounded natural-number code as an ordinary-cost
observation-selection certificate. -/
noncomputable def verifiesDenseCostCertificateCode
    (costBudget : Nat)
    (code : Nat) :
    Bool :=
  match correctedConcreteDenseCertificateDecode U code with
  | some certificate =>
      table.verifiesCostCertificate costBudget certificate
  | none => false

/-- A dense cost code is accepted exactly when it decodes to an accepted subset
certificate. -/
theorem verifiesDenseCostCertificateCode_eq_true_iff
    (costBudget : Nat)
    (code : Nat) :
    table.verifiesDenseCostCertificateCode costBudget code = true ↔
      ∃ certificate : Finset ι,
        correctedConcreteDenseCertificateDecode U code =
            some certificate ∧
          table.verifiesCostCertificate
              costBudget
              certificate =
            true := by

  cases hDecode : correctedConcreteDenseCertificateDecode U code with
  | none =>
      simp [verifiesDenseCostCertificateCode, hDecode]
  | some certificate =>
      simp [verifiesDenseCostCertificateCode, hDecode]

/-- Encoding any accepted ordinary-cost certificate produces an accepted dense
code. -/
theorem verifiesDenseCostCertificateCode_encode_of_verify
    (costBudget : Nat)
    {certificate : Finset ι}
    (hVerify :
      table.verifiesCostCertificate
          costBudget
          certificate =
        true) :
    table.verifiesDenseCostCertificateCode
          costBudget
          (correctedConcreteDenseCertificateCode U certificate) =
        true := by

  have hSubset : certificate ⊆ U :=
    table.verifiedCostCertificate_subset hVerify

  simp [
    verifiesDenseCostCertificateCode,
    correctedConcreteDenseCertificateDecode_encode_of_subset
      U
      hSubset,
    hVerify
  ]

/-- Every accepted dense ordinary-cost code decodes to an accepted certificate
contained in `U`. -/
theorem verifiesDenseCostCertificateCode_decode_package
    (costBudget : Nat)
    {code : Nat}
    (hVerify :
      table.verifiesDenseCostCertificateCode
          costBudget
          code =
        true) :
    ∃ certificate : Finset ι,
      correctedConcreteDenseCertificateDecode U code =
          some certificate ∧
        table.verifiesCostCertificate
            costBudget
            certificate =
          true ∧
        certificate ⊆ U := by

  rcases
      (table.verifiesDenseCostCertificateCode_eq_true_iff
        costBudget
        code).mp hVerify with
    ⟨certificate, hDecode, hCertificate⟩

  exact
    ⟨certificate,
      hDecode,
      hCertificate,
      table.verifiedCostCertificate_subset hCertificate⟩

/-- Explicit finite natural-number search for all accepted ordinary-cost
certificate codes. -/
noncomputable def verifiedDenseCostCertificateCodes
    (costBudget : Nat) :
    Finset Nat :=
  (correctedConcreteDenseCertificateCodeUniverse U).filter
    (fun code =>
      table.verifiesDenseCostCertificateCode
          costBudget
          code =
        true)

/-- Exact membership theorem for the encoded ordinary-cost search. -/
theorem mem_verifiedDenseCostCertificateCodes_iff
    (costBudget : Nat)
    (code : Nat) :
    code ∈ table.verifiedDenseCostCertificateCodes costBudget ↔
      code < 2 ^ U.card ∧
        table.verifiesDenseCostCertificateCode
            costBudget
            code =
          true := by

  simp [
    verifiedDenseCostCertificateCodes,
    correctedConcreteDenseCertificateCodeUniverse
  ]

/-- Every accepted subset certificate contributes its intrinsic dense code to
the encoded ordinary-cost search. -/
theorem denseCostCertificateCode_mem_search_of_verify
    (costBudget : Nat)
    {certificate : Finset ι}
    (hVerify :
      table.verifiesCostCertificate
          costBudget
          certificate =
        true) :
    correctedConcreteDenseCertificateCode U certificate ∈
      table.verifiedDenseCostCertificateCodes costBudget := by

  exact
    (table.mem_verifiedDenseCostCertificateCodes_iff
      costBudget
      (correctedConcreteDenseCertificateCode U certificate)).mpr
      ⟨correctedConcreteDenseCertificateCode_lt_two_pow
          U
          certificate,
        table.verifiesDenseCostCertificateCode_encode_of_verify
          costBudget
          hVerify⟩

/-- The ordinary-cost Boolean decision is equivalent to existence of an
accepted dense natural-number code. -/
theorem costFeasibleDecision_eq_true_iff_exists_verifiedDenseCode
    (costBudget : Nat) :
    table.costFeasibleDecision costBudget = true ↔
      ∃ code : Nat,
        code ∈ table.verifiedDenseCostCertificateCodes costBudget := by

  constructor

  · intro hDecision

    rcases
        (table.costFeasibleDecision_eq_true_iff_exists_verifiedCostCertificate
          costBudget).mp hDecision with
      ⟨certificate, hVerify⟩

    exact
      ⟨correctedConcreteDenseCertificateCode U certificate,
        table.denseCostCertificateCode_mem_search_of_verify
          costBudget
          hVerify⟩

  · intro hCode

    rcases hCode with
      ⟨code, hCode⟩

    have hVerifyCode :
        table.verifiesDenseCostCertificateCode
            costBudget
            code =
          true :=
      (table.mem_verifiedDenseCostCertificateCodes_iff
        costBudget
        code).mp hCode |>.2

    rcases
        (table.verifiesDenseCostCertificateCode_eq_true_iff
          costBudget
          code).mp hVerifyCode with
      ⟨certificate, hDecode, hVerify⟩

    exact
      (table.costFeasibleDecision_eq_true_iff_exists_verifiedCostCertificate
        costBudget).mpr
        ⟨certificate, hVerify⟩

/-- The encoded ordinary-cost search is nonempty exactly on positive decision
instances. -/
theorem verifiedDenseCostCertificateCodes_nonempty_iff
    (costBudget : Nat) :
    (table.verifiedDenseCostCertificateCodes costBudget).Nonempty ↔
      table.costFeasibleDecision costBudget = true := by

  constructor

  · intro hNonempty

    rcases hNonempty with
      ⟨code, hCode⟩

    exact
      (table.costFeasibleDecision_eq_true_iff_exists_verifiedDenseCode
        costBudget).mpr
        ⟨code, hCode⟩

  · intro hDecision

    rcases
        (table.costFeasibleDecision_eq_true_iff_exists_verifiedDenseCode
          costBudget).mp hDecision with
      ⟨code, hCode⟩

    exact ⟨code, hCode⟩

/-- The encoded ordinary-cost search never exceeds its exact dense universe. -/
theorem verifiedDenseCostCertificateCodes_card_le
    (costBudget : Nat) :
    (table.verifiedDenseCostCertificateCodes costBudget).card <=
      2 ^ U.card := by

  calc
    (table.verifiedDenseCostCertificateCodes costBudget).card <=
        (correctedConcreteDenseCertificateCodeUniverse U).card :=
      Finset.card_le_card
        (Finset.filter_subset _ _)
    _ = 2 ^ U.card :=
      correctedConcreteDenseCertificateCodeUniverse_card U

/-- Code-space version of the canonical minimum ordinary-cost search.  It
keeps the unique intrinsic code selected by the preceding canonical
certificate construction. -/
noncomputable def canonicalDenseMinimumCostCodeSearch
    (maxBudget : Nat)
    (hAccepted :
      table.HasAcceptedCostBudgetUpTo maxBudget) :
    Finset Nat :=
  (table.verifiedDenseCostCertificateCodes
      (table.selectedMinimumAcceptedCostBudget
        maxBudget
        hAccepted)).filter
    (fun code =>
      code =
        correctedConcreteDenseCertificateCode U
          (table.canonicalMinimumCostCertificate
            (correctedConcreteDenseCertificateCode U)
            maxBudget
            hAccepted))

/-- The selected canonical ordinary-cost certificate code belongs to the
encoded search at the selected minimum budget. -/
theorem canonicalMinimumCostCertificate_denseCode_mem_verifiedSearch
    (maxBudget : Nat)
    (hAccepted :
      table.HasAcceptedCostBudgetUpTo maxBudget) :
    correctedConcreteDenseCertificateCode U
        (table.canonicalMinimumCostCertificate
          (correctedConcreteDenseCertificateCode U)
          maxBudget
          hAccepted) ∈
      table.verifiedDenseCostCertificateCodes
        (table.selectedMinimumAcceptedCostBudget
          maxBudget
          hAccepted) := by

  exact
    table.denseCostCertificateCode_mem_search_of_verify
      (table.selectedMinimumAcceptedCostBudget
        maxBudget
        hAccepted)
      (table.canonicalMinimumCostCertificate_verifies
        (correctedConcreteDenseCertificateCode U)
        maxBudget
        hAccepted)

/-- The canonical ordinary-cost search in dense code space is exactly a
singleton. -/
theorem canonicalDenseMinimumCostCodeSearch_eq_singleton
    (maxBudget : Nat)
    (hAccepted :
      table.HasAcceptedCostBudgetUpTo maxBudget) :
    table.canonicalDenseMinimumCostCodeSearch
          maxBudget
          hAccepted =
        {correctedConcreteDenseCertificateCode U
          (table.canonicalMinimumCostCertificate
            (correctedConcreteDenseCertificateCode U)
            maxBudget
            hAccepted)} := by

  apply Finset.ext
  intro code
  constructor

  · intro hCode

    exact
      Finset.mem_singleton.mpr
        (Finset.mem_filter.mp hCode).2

  · intro hCode

    have hCodeEq :
        code =
          correctedConcreteDenseCertificateCode U
            (table.canonicalMinimumCostCertificate
              (correctedConcreteDenseCertificateCode U)
              maxBudget
              hAccepted) :=
      Finset.mem_singleton.mp hCode

    subst code

    exact
      Finset.mem_filter.mpr
        ⟨table.canonicalMinimumCostCertificate_denseCode_mem_verifiedSearch
            maxBudget
            hAccepted,
          rfl⟩

/-- The canonical ordinary-cost dense-code search has cardinality one. -/
theorem canonicalDenseMinimumCostCodeSearch_card_eq_one
    (maxBudget : Nat)
    (hAccepted :
      table.HasAcceptedCostBudgetUpTo maxBudget) :
    (table.canonicalDenseMinimumCostCodeSearch
      maxBudget
      hAccepted).card = 1 := by

  rw [
    table.canonicalDenseMinimumCostCodeSearch_eq_singleton
      maxBudget
      hAccepted,
    Finset.card_singleton
  ]

end EncodedCostCertificateSearch


section EncodedParetoScalarCertificateSearch

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

/-- Boolean verification of a dense natural-number code as a Pareto-scalar
certificate. -/
noncomputable def verifiesDenseParetoScalarCertificateCode
    (scalarBudget : Nat)
    (code : Nat) :
    Bool :=
  match correctedConcreteDenseCertificateDecode U code with
  | some certificate =>
      table.verifiesParetoScalarCertificate
        scalarBudget
        certificate
  | none => false

/-- A dense Pareto-scalar code is accepted exactly when it decodes to an
accepted Pareto certificate. -/
theorem verifiesDenseParetoScalarCertificateCode_eq_true_iff
    (scalarBudget : Nat)
    (code : Nat) :
    table.verifiesDenseParetoScalarCertificateCode
          scalarBudget
          code =
        true ↔
      ∃ certificate : Finset ι,
        correctedConcreteDenseCertificateDecode U code =
            some certificate ∧
          table.verifiesParetoScalarCertificate
              scalarBudget
              certificate =
            true := by

  cases hDecode : correctedConcreteDenseCertificateDecode U code with
  | none =>
      simp [verifiesDenseParetoScalarCertificateCode, hDecode]
  | some certificate =>
      simp [verifiesDenseParetoScalarCertificateCode, hDecode]

/-- Encoding any accepted Pareto-scalar certificate produces an accepted dense
code. -/
theorem verifiesDenseParetoScalarCertificateCode_encode_of_verify
    (scalarBudget : Nat)
    {certificate : Finset ι}
    (hVerify :
      table.verifiesParetoScalarCertificate
          scalarBudget
          certificate =
        true) :
    table.verifiesDenseParetoScalarCertificateCode
          scalarBudget
          (correctedConcreteDenseCertificateCode U certificate) =
        true := by

  have hPareto :
      CorrectedConcreteObservationSelectionParetoOptimal
        (z := z)
        obsFamily
        f
        selectionCost
        U
        language
        certificate :=
    ((table.verifiesParetoScalarCertificate_eq_true_iff
      scalarBudget
      certificate).mp hVerify).1

  have hSubset : certificate ⊆ U :=
    hPareto.1

  simp [
    verifiesDenseParetoScalarCertificateCode,
    correctedConcreteDenseCertificateDecode_encode_of_subset
      U
      hSubset,
    hVerify
  ]

/-- Every accepted dense Pareto-scalar code decodes to an accepted Pareto
certificate contained in `U`. -/
theorem verifiesDenseParetoScalarCertificateCode_decode_package
    (scalarBudget : Nat)
    {code : Nat}
    (hVerify :
      table.verifiesDenseParetoScalarCertificateCode
          scalarBudget
          code =
        true) :
    ∃ certificate : Finset ι,
      correctedConcreteDenseCertificateDecode U code =
          some certificate ∧
        table.verifiesParetoScalarCertificate
            scalarBudget
            certificate =
          true ∧
        certificate ⊆ U := by

  rcases
      (table.verifiesDenseParetoScalarCertificateCode_eq_true_iff
        scalarBudget
        code).mp hVerify with
    ⟨certificate, hDecode, hCertificate⟩

  have hPareto :
      CorrectedConcreteObservationSelectionParetoOptimal
        (z := z)
        obsFamily
        f
        selectionCost
        U
        language
        certificate :=
    ((table.verifiesParetoScalarCertificate_eq_true_iff
      scalarBudget
      certificate).mp hCertificate).1

  exact
    ⟨certificate,
      hDecode,
      hCertificate,
      hPareto.1⟩

/-- Explicit finite natural-number search for all accepted Pareto-scalar
certificate codes. -/
noncomputable def verifiedDenseParetoScalarCertificateCodes
    (scalarBudget : Nat) :
    Finset Nat :=
  (correctedConcreteDenseCertificateCodeUniverse U).filter
    (fun code =>
      table.verifiesDenseParetoScalarCertificateCode
          scalarBudget
          code =
        true)

/-- Exact membership theorem for the encoded Pareto-scalar search. -/
theorem mem_verifiedDenseParetoScalarCertificateCodes_iff
    (scalarBudget : Nat)
    (code : Nat) :
    code ∈
        table.verifiedDenseParetoScalarCertificateCodes scalarBudget ↔
      code < 2 ^ U.card ∧
        table.verifiesDenseParetoScalarCertificateCode
            scalarBudget
            code =
          true := by

  simp [
    verifiedDenseParetoScalarCertificateCodes,
    correctedConcreteDenseCertificateCodeUniverse
  ]

/-- Every accepted Pareto subset certificate contributes its intrinsic dense
code to the encoded Pareto search. -/
theorem denseParetoScalarCertificateCode_mem_search_of_verify
    (scalarBudget : Nat)
    {certificate : Finset ι}
    (hVerify :
      table.verifiesParetoScalarCertificate
          scalarBudget
          certificate =
        true) :
    correctedConcreteDenseCertificateCode U certificate ∈
      table.verifiedDenseParetoScalarCertificateCodes scalarBudget := by

  exact
    (table.mem_verifiedDenseParetoScalarCertificateCodes_iff
      scalarBudget
      (correctedConcreteDenseCertificateCode U certificate)).mpr
      ⟨correctedConcreteDenseCertificateCode_lt_two_pow
          U
          certificate,
        table.verifiesDenseParetoScalarCertificateCode_encode_of_verify
          scalarBudget
          hVerify⟩

/-- The Pareto-scalar Boolean decision is equivalent to existence of an
accepted dense natural-number code. -/
theorem paretoScalarFeasibleDecision_eq_true_iff_exists_verifiedDenseCode
    (scalarBudget : Nat) :
    table.paretoScalarFeasibleDecision scalarBudget = true ↔
      ∃ code : Nat,
        code ∈
          table.verifiedDenseParetoScalarCertificateCodes scalarBudget := by

  constructor

  · intro hDecision

    rcases
        (table.paretoScalarFeasibleDecision_eq_true_iff_exists_verifiedCertificate
          scalarBudget).mp hDecision with
      ⟨certificate, hVerify⟩

    exact
      ⟨correctedConcreteDenseCertificateCode U certificate,
        table.denseParetoScalarCertificateCode_mem_search_of_verify
          scalarBudget
          hVerify⟩

  · intro hCode

    rcases hCode with
      ⟨code, hCode⟩

    have hVerifyCode :
        table.verifiesDenseParetoScalarCertificateCode
            scalarBudget
            code =
          true :=
      (table.mem_verifiedDenseParetoScalarCertificateCodes_iff
        scalarBudget
        code).mp hCode |>.2

    rcases
        (table.verifiesDenseParetoScalarCertificateCode_eq_true_iff
          scalarBudget
          code).mp hVerifyCode with
      ⟨certificate, hDecode, hVerify⟩

    exact
      (table.paretoScalarFeasibleDecision_eq_true_iff_exists_verifiedCertificate
        scalarBudget).mpr
        ⟨certificate, hVerify⟩

/-- The encoded Pareto-scalar search is nonempty exactly on positive decision
instances. -/
theorem verifiedDenseParetoScalarCertificateCodes_nonempty_iff
    (scalarBudget : Nat) :
    (table.verifiedDenseParetoScalarCertificateCodes
      scalarBudget).Nonempty ↔
      table.paretoScalarFeasibleDecision scalarBudget = true := by

  constructor

  · intro hNonempty

    rcases hNonempty with
      ⟨code, hCode⟩

    exact
      (table.paretoScalarFeasibleDecision_eq_true_iff_exists_verifiedDenseCode
        scalarBudget).mpr
        ⟨code, hCode⟩

  · intro hDecision

    rcases
        (table.paretoScalarFeasibleDecision_eq_true_iff_exists_verifiedDenseCode
          scalarBudget).mp hDecision with
      ⟨code, hCode⟩

    exact ⟨code, hCode⟩

/-- The encoded Pareto-scalar search never exceeds its exact dense universe. -/
theorem verifiedDenseParetoScalarCertificateCodes_card_le
    (scalarBudget : Nat) :
    (table.verifiedDenseParetoScalarCertificateCodes
      scalarBudget).card <=
      2 ^ U.card := by

  calc
    (table.verifiedDenseParetoScalarCertificateCodes scalarBudget).card <=
        (correctedConcreteDenseCertificateCodeUniverse U).card :=
      Finset.card_le_card
        (Finset.filter_subset _ _)
    _ = 2 ^ U.card :=
      correctedConcreteDenseCertificateCodeUniverse_card U

/-- Code-space version of the canonical minimum Pareto-scalar search. -/
noncomputable def canonicalDenseMinimumParetoScalarCodeSearch
    (maxBudget : Nat)
    (hAccepted :
      table.HasAcceptedParetoScalarBudgetUpTo maxBudget) :
    Finset Nat :=
  (table.verifiedDenseParetoScalarCertificateCodes
      (table.selectedMinimumAcceptedParetoScalarBudget
        maxBudget
        hAccepted)).filter
    (fun code =>
      code =
        correctedConcreteDenseCertificateCode U
          (table.canonicalMinimumParetoScalarCertificate
            (correctedConcreteDenseCertificateCode U)
            maxBudget
            hAccepted))

/-- The selected canonical Pareto certificate code belongs to the encoded
search at the selected minimum scalar budget. -/
theorem canonicalMinimumParetoScalarCertificate_denseCode_mem_verifiedSearch
    (maxBudget : Nat)
    (hAccepted :
      table.HasAcceptedParetoScalarBudgetUpTo maxBudget) :
    correctedConcreteDenseCertificateCode U
        (table.canonicalMinimumParetoScalarCertificate
          (correctedConcreteDenseCertificateCode U)
          maxBudget
          hAccepted) ∈
      table.verifiedDenseParetoScalarCertificateCodes
        (table.selectedMinimumAcceptedParetoScalarBudget
          maxBudget
          hAccepted) := by

  exact
    table.denseParetoScalarCertificateCode_mem_search_of_verify
      (table.selectedMinimumAcceptedParetoScalarBudget
        maxBudget
        hAccepted)
      (table.canonicalMinimumParetoScalarCertificate_verifies
        (correctedConcreteDenseCertificateCode U)
        maxBudget
        hAccepted)

/-- The canonical Pareto-scalar search in dense code space is exactly a
singleton. -/
theorem canonicalDenseMinimumParetoScalarCodeSearch_eq_singleton
    (maxBudget : Nat)
    (hAccepted :
      table.HasAcceptedParetoScalarBudgetUpTo maxBudget) :
    table.canonicalDenseMinimumParetoScalarCodeSearch
          maxBudget
          hAccepted =
        {correctedConcreteDenseCertificateCode U
          (table.canonicalMinimumParetoScalarCertificate
            (correctedConcreteDenseCertificateCode U)
            maxBudget
            hAccepted)} := by

  apply Finset.ext
  intro code
  constructor

  · intro hCode

    exact
      Finset.mem_singleton.mpr
        (Finset.mem_filter.mp hCode).2

  · intro hCode

    have hCodeEq :
        code =
          correctedConcreteDenseCertificateCode U
            (table.canonicalMinimumParetoScalarCertificate
              (correctedConcreteDenseCertificateCode U)
              maxBudget
              hAccepted) :=
      Finset.mem_singleton.mp hCode

    subst code

    exact
      Finset.mem_filter.mpr
        ⟨table.canonicalMinimumParetoScalarCertificate_denseCode_mem_verifiedSearch
            maxBudget
            hAccepted,
          rfl⟩

/-- The canonical Pareto-scalar dense-code search has cardinality one. -/
theorem canonicalDenseMinimumParetoScalarCodeSearch_card_eq_one
    (maxBudget : Nat)
    (hAccepted :
      table.HasAcceptedParetoScalarBudgetUpTo maxBudget) :
    (table.canonicalDenseMinimumParetoScalarCodeSearch
      maxBudget
      hAccepted).card = 1 := by

  rw [
    table.canonicalDenseMinimumParetoScalarCodeSearch_eq_singleton
      maxBudget
      hAccepted,
    Finset.card_singleton
  ]

end EncodedParetoScalarCertificateSearch

end CorrectedConcreteObservationSelectionDecisionTable


section EncodedCertificateSearchFinalPackage

variable {α : Type u}
variable {ι : Type v}
variable {M : Type w}
variable [DecidableEq ι]
variable [Monoid M]
variable (obsFamily : ι → α → M)
variable (f : Nat)
variable (coordinateWeight : ι → Nat)
variable (U : Finset ι)

/-- Final positive-additive encoded-search package.  The selected canonical
Pareto certificate is represented by a bounded natural-number code, belongs to
the finite encoded verifier search at the exact minimum rank, decodes back to
the selected certificate, and is the sole member of the canonical code search.
-/
theorem
    correctedConcreteWorkingGrammar_observationSelectionEncodedCertificateSearch_package
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
    let code :=
      correctedConcreteDenseCertificateCode U certificate
    code < 2 ^ U.card ∧
      correctedConcreteDenseCertificateDecode U code =
        some certificate ∧
      code ∈
        table.verifiedDenseParetoScalarCertificateCodes
          (table.selectedMinimumAcceptedParetoScalarBudget
            maxBudget
            hAccepted) ∧
      table.canonicalDenseMinimumParetoScalarCodeSearch
            maxBudget
            hAccepted =
          {code} ∧
      (table.canonicalDenseMinimumParetoScalarCodeSearch
        maxBudget
        hAccepted).card = 1 ∧
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

  let code :=
    correctedConcreteDenseCertificateCode U certificate

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
    ⟨correctedConcreteDenseCertificateCode_lt_two_pow
        U
        certificate,
      correctedConcreteDenseCertificateDecode_encode_of_subset
        U
        hSubset,
      table.canonicalMinimumParetoScalarCertificate_denseCode_mem_verifiedSearch
        maxBudget
        hAccepted,
      table.canonicalDenseMinimumParetoScalarCodeSearch_eq_singleton
        maxBudget
        hAccepted,
      table.canonicalDenseMinimumParetoScalarCodeSearch_card_eq_one
        maxBudget
        hAccepted,
      hCanonicalPackage.2.1⟩

end EncodedCertificateSearchFinalPackage

end MCFG
