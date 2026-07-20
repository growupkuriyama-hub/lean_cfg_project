/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG.ConcreteCanonicalLearnerWorkingGrammarObservationSelectionDecisionProblem

/-!
# ConcreteCanonicalLearnerWorkingGrammarObservationSelectionComplexity.lean

The preceding file isolates semantic observation-selection feasibility behind a
finite proof-carrying decision table and defines Boolean decision procedures.

This file adds the certificate layer needed before a genuine complexity-class
formalization.

## Certificates

A certificate is simply a finite selected subset of observation coordinates.
For a supplied correct decision table, the verifier checks only

* membership of the selected subset in the stored feasible or Pareto table;
* the appropriate natural-number budget inequality.

The verifier itself therefore does not inspect semantic target-class
membership.

## Verified facts

For the ordinary cost-budget problem and the Pareto-scalar problem we prove:

```text
Boolean acceptance
  iff
there exists an accepted finite certificate.
```

Every accepted certificate is a subset of the ambient coordinate set `U`, so
its cardinality is at most `U.card`.  The complete accepted-certificate family
is contained in `U.powerset`, hence has at most `2 ^ U.card` elements.

We package these facts in a generic bounded-certificate interface.  Under a
full-product target witness, the same certificate interface decides the
minimum observation-selection rank threshold.  For positive additive cost, a
Pareto certificate also decides the same minimum-rank threshold.

## Boundary

This is an NP-style certificate interface, not yet a theorem of membership in a
formal complexity class.  In particular, this file does not provide an encoded
input model, a Turing-machine or RAM cost semantics, or a polynomial-time
construction of a correct table.  Those are deliberately left for the next
executable complexity layer.

No target grammar is supplied to any learner.
No `sorry`, `admit`, or `axiom` is used.
-/

namespace MCFG

universe u v w z


section GenericBoundedCertificateInterface

/-- A small generic interface for a Boolean verifier with bounded witnesses.

This record intentionally separates certificate soundness/completeness and
certificate-size bounds from any particular machine-cost model. -/
structure CorrectedConcreteBoundedCertificateInterface
    (Question : Nat → Prop) where

  Certificate : Type v

  certificateSize : Certificate → Nat

  certificateBound : Nat → Nat

  verify : Nat → Certificate → Bool

  correct :
    ∀ budget : Nat,
      Question budget ↔
        ∃ certificate : Certificate,
          verify budget certificate = true

  bounded :
    ∀ (budget : Nat) (certificate : Certificate),
      verify budget certificate = true →
        certificateSize certificate <=
          certificateBound budget

namespace CorrectedConcreteBoundedCertificateInterface

variable {Question : Nat → Prop}
variable
  (certificateInterface :
    CorrectedConcreteBoundedCertificateInterface
      (v := v)
      Question)

/-- A positive answer supplies an accepted bounded certificate. -/
theorem exists_bounded_certificate
    {budget : Nat}
    (hQuestion : Question budget) :
    ∃ certificate : certificateInterface.Certificate,
      certificateInterface.verify budget certificate = true ∧
        certificateInterface.certificateSize certificate <=
          certificateInterface.certificateBound budget := by

  rcases
      (certificateInterface.correct budget).mp
        hQuestion with
    ⟨certificate, hVerify⟩

  exact
    ⟨certificate,
      hVerify,
      certificateInterface.bounded
        budget
        certificate
        hVerify⟩

/-- An accepted certificate proves the corresponding positive answer. -/
theorem question_of_verified
    {budget : Nat}
    {certificate : certificateInterface.Certificate}
    (hVerify :
      certificateInterface.verify budget certificate = true) :
    Question budget := by

  exact
    (certificateInterface.correct budget).mpr
      ⟨certificate, hVerify⟩

end CorrectedConcreteBoundedCertificateInterface

end GenericBoundedCertificateInterface


namespace CorrectedConcreteObservationSelectionDecisionTable

section CostCertificateVerifier

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

/-- A cost certificate is an explicitly supplied selected coordinate subset.
The verifier inspects only the finite feasible table and the cost inequality. -/
def verifiesCostCertificate
    (costBudget : Nat)
    (certificate : Finset ι) :
    Bool :=
  decide
    (certificate ∈ table.feasibleSelections ∧
      selectionCost certificate <= costBudget)

/-- Semantic correctness of one accepted cost certificate. -/
theorem verifiesCostCertificate_eq_true_iff
    (costBudget : Nat)
    (certificate : Finset ι) :
    table.verifiesCostCertificate costBudget certificate = true ↔
      certificate ⊆ U ∧
        selectionCost certificate <= costBudget ∧
        language ∈
          StartRootedCorrectedConcreteTargetClass
            (v := z)
            α
            (↥certificate → M)
            (selectedObservationProduct obsFamily certificate)
            f := by

  unfold verifiesCostCertificate

  rw [decide_eq_true_eq]

  constructor

  · intro hCertificate

    rcases hCertificate with
      ⟨hStored, hCost⟩

    rcases
        (table.feasible_correct certificate).mp
          hStored with
      ⟨hSubset, hTarget⟩

    exact
      ⟨hSubset,
        hCost,
        hTarget⟩

  · intro hCertificate

    rcases hCertificate with
      ⟨hSubset, hCost, hTarget⟩

    exact
      ⟨(table.feasible_correct certificate).mpr
          ⟨hSubset, hTarget⟩,
        hCost⟩

/-- The Boolean cost decision accepts exactly when some finite cost certificate
is accepted. -/
theorem costFeasibleDecision_eq_true_iff_exists_verifiedCostCertificate
    (costBudget : Nat) :
    table.costFeasibleDecision costBudget = true ↔
      ∃ certificate : Finset ι,
        table.verifiesCostCertificate
            costBudget
            certificate =
          true := by

  rw [table.costFeasibleDecision_eq_true_iff]

  constructor

  · intro hSelection

    rcases hSelection with
      ⟨certificate,
        hSubset,
        hCost,
        hTarget⟩

    exact
      ⟨certificate,
        (table.verifiesCostCertificate_eq_true_iff
          costBudget
          certificate).mpr
          ⟨hSubset,
            hCost,
            hTarget⟩⟩

  · intro hCertificate

    rcases hCertificate with
      ⟨certificate, hVerify⟩

    rcases
        (table.verifiesCostCertificate_eq_true_iff
          costBudget
          certificate).mp
          hVerify with
      ⟨hSubset, hCost, hTarget⟩

    exact
      ⟨certificate,
        hSubset,
        hCost,
        hTarget⟩

/-- Every accepted cost certificate is contained in the ambient coordinate
set. -/
theorem verifiedCostCertificate_subset
    {costBudget : Nat}
    {certificate : Finset ι}
    (hVerify :
      table.verifiesCostCertificate
          costBudget
          certificate =
        true) :
    certificate ⊆ U := by

  exact
    ((table.verifiesCostCertificate_eq_true_iff
      costBudget
      certificate).mp
      hVerify).1

/-- Every accepted cost certificate has cardinality at most `U.card`. -/
theorem verifiedCostCertificate_card_le
    {costBudget : Nat}
    {certificate : Finset ι}
    (hVerify :
      table.verifiesCostCertificate
          costBudget
          certificate =
        true) :
    certificate.card <= U.card := by

  exact
    Finset.card_le_card
      (table.verifiedCostCertificate_subset hVerify)

/-- Explicit finite family of all accepted ambient cost certificates. -/
def verifiedCostCertificates
    (costBudget : Nat) :
    Finset (Finset ι) :=
  U.powerset.filter
    (fun certificate =>
      table.verifiesCostCertificate
          costBudget
          certificate =
        true)

/-- Exact membership theorem for the accepted cost-certificate family. -/
theorem mem_verifiedCostCertificates_iff
    (costBudget : Nat)
    {certificate : Finset ι} :
    certificate ∈
        table.verifiedCostCertificates costBudget ↔
      table.verifiesCostCertificate
          costBudget
          certificate =
        true := by

  constructor

  · intro hCertificate

    exact
      (Finset.mem_filter.mp hCertificate).2

  · intro hVerify

    exact
      Finset.mem_filter.mpr
        ⟨Finset.mem_powerset.mpr
            (table.verifiedCostCertificate_subset hVerify),
          hVerify⟩

/-- The accepted cost-certificate family is nonempty exactly on positive
instances. -/
theorem verifiedCostCertificates_nonempty_iff
    (costBudget : Nat) :
    (table.verifiedCostCertificates costBudget).Nonempty ↔
      table.costFeasibleDecision costBudget = true := by

  constructor

  · intro hNonempty

    rcases hNonempty with
      ⟨certificate, hCertificate⟩

    exact
      (table.costFeasibleDecision_eq_true_iff_exists_verifiedCostCertificate
        costBudget).mpr
        ⟨certificate,
          (table.mem_verifiedCostCertificates_iff
            costBudget).mp
            hCertificate⟩

  · intro hDecision

    rcases
        (table.costFeasibleDecision_eq_true_iff_exists_verifiedCostCertificate
          costBudget).mp
          hDecision with
      ⟨certificate, hVerify⟩

    exact
      ⟨certificate,
        (table.mem_verifiedCostCertificates_iff
          costBudget).mpr
          hVerify⟩

/-- There are at most `2 ^ U.card` accepted cost certificates. -/
theorem verifiedCostCertificates_card_le
    (costBudget : Nat) :
    (table.verifiedCostCertificates costBudget).card <=
      2 ^ U.card := by

  calc
    (table.verifiedCostCertificates costBudget).card <=
        U.powerset.card :=
      Finset.card_le_card
        (Finset.filter_subset _ _)

    _ = 2 ^ U.card := by
      simpa using
        Finset.card_powerset U

/-- Generic bounded-certificate interface for the table-based cost decision. -/
def costDecisionBoundedCertificateInterface :
    CorrectedConcreteBoundedCertificateInterface
      (v := v)
      (fun costBudget =>
        table.costFeasibleDecision costBudget = true) :=
  {
    Certificate := Finset ι
    certificateSize := Finset.card
    certificateBound := fun _ => U.card
    verify := table.verifiesCostCertificate
    correct :=
      table.costFeasibleDecision_eq_true_iff_exists_verifiedCostCertificate
    bounded := by
      intro costBudget certificate hVerify
      exact
        table.verifiedCostCertificate_card_le hVerify
  }

end CostCertificateVerifier


section ParetoCertificateVerifier

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

/-- Pareto-scalar certificate verifier using only the finite stored Pareto table
and the scalar budget. -/
def verifiesParetoScalarCertificate
    (scalarBudget : Nat)
    (certificate : Finset ι) :
    Bool :=
  decide
    (certificate ∈ table.paretoSelections ∧
      correctedConcreteObservationSelectionParetoScalarCost
          selectionCost certificate <=
        scalarBudget)

/-- Semantic correctness of one accepted Pareto-scalar certificate. -/
theorem verifiesParetoScalarCertificate_eq_true_iff
    (scalarBudget : Nat)
    (certificate : Finset ι) :
    table.verifiesParetoScalarCertificate
          scalarBudget
          certificate =
        true ↔
      CorrectedConcreteObservationSelectionParetoOptimal
          (z := z)
          obsFamily
          f
          selectionCost
          U
          language
          certificate ∧
        correctedConcreteObservationSelectionParetoScalarCost
            selectionCost certificate <=
          scalarBudget := by

  unfold verifiesParetoScalarCertificate

  rw [decide_eq_true_eq]

  constructor

  · intro hCertificate

    exact
      ⟨(table.pareto_correct certificate).mp
          hCertificate.1,
        hCertificate.2⟩

  · intro hCertificate

    exact
      ⟨(table.pareto_correct certificate).mpr
          hCertificate.1,
        hCertificate.2⟩

/-- The Boolean Pareto-scalar decision accepts exactly when some finite Pareto
certificate is accepted. -/
theorem paretoScalarFeasibleDecision_eq_true_iff_exists_verifiedCertificate
    (scalarBudget : Nat) :
    table.paretoScalarFeasibleDecision scalarBudget = true ↔
      ∃ certificate : Finset ι,
        table.verifiesParetoScalarCertificate
            scalarBudget
            certificate =
          true := by

  rw [table.paretoScalarFeasibleDecision_eq_true_iff]

  constructor

  · intro hExists

    rcases hExists with
      ⟨certificate, hPareto, hScalar⟩

    exact
      ⟨certificate,
        (table.verifiesParetoScalarCertificate_eq_true_iff
          scalarBudget
          certificate).mpr
          ⟨hPareto, hScalar⟩⟩

  · intro hExists

    rcases hExists with
      ⟨certificate, hVerify⟩

    exact
      ⟨certificate,
        (table.verifiesParetoScalarCertificate_eq_true_iff
          scalarBudget
          certificate).mp
          hVerify⟩

/-- Every accepted Pareto-scalar certificate has cardinality at most `U.card`. -/
theorem verifiedParetoScalarCertificate_card_le
    {scalarBudget : Nat}
    {certificate : Finset ι}
    (hVerify :
      table.verifiesParetoScalarCertificate
          scalarBudget
          certificate =
        true) :
    certificate.card <= U.card := by

  have hPareto :=
    ((table.verifiesParetoScalarCertificate_eq_true_iff
      scalarBudget
      certificate).mp
      hVerify).1

  exact
    Finset.card_le_card
      hPareto.1

/-- Explicit finite family of all accepted ambient Pareto-scalar certificates. -/
def verifiedParetoScalarCertificates
    (scalarBudget : Nat) :
    Finset (Finset ι) :=
  U.powerset.filter
    (fun certificate =>
      table.verifiesParetoScalarCertificate
          scalarBudget
          certificate =
        true)

/-- Exact membership theorem for accepted Pareto-scalar certificates. -/
theorem mem_verifiedParetoScalarCertificates_iff
    (scalarBudget : Nat)
    {certificate : Finset ι} :
    certificate ∈
        table.verifiedParetoScalarCertificates scalarBudget ↔
      table.verifiesParetoScalarCertificate
          scalarBudget
          certificate =
        true := by

  constructor

  · intro hCertificate

    exact
      (Finset.mem_filter.mp hCertificate).2

  · intro hVerify

    have hPareto :=
      ((table.verifiesParetoScalarCertificate_eq_true_iff
        scalarBudget
        certificate).mp
        hVerify).1

    exact
      Finset.mem_filter.mpr
        ⟨Finset.mem_powerset.mpr hPareto.1,
          hVerify⟩

/-- The accepted Pareto-certificate family is nonempty exactly on a positive
Pareto-scalar instance. -/
theorem verifiedParetoScalarCertificates_nonempty_iff
    (scalarBudget : Nat) :
    (table.verifiedParetoScalarCertificates scalarBudget).Nonempty ↔
      table.paretoScalarFeasibleDecision scalarBudget = true := by

  constructor

  · intro hNonempty

    rcases hNonempty with
      ⟨certificate, hCertificate⟩

    exact
      (table.paretoScalarFeasibleDecision_eq_true_iff_exists_verifiedCertificate
        scalarBudget).mpr
        ⟨certificate,
          (table.mem_verifiedParetoScalarCertificates_iff
            scalarBudget).mp
            hCertificate⟩

  · intro hDecision

    rcases
        (table.paretoScalarFeasibleDecision_eq_true_iff_exists_verifiedCertificate
          scalarBudget).mp
          hDecision with
      ⟨certificate, hVerify⟩

    exact
      ⟨certificate,
        (table.mem_verifiedParetoScalarCertificates_iff
          scalarBudget).mpr
          hVerify⟩

/-- There are at most `2 ^ U.card` accepted Pareto-scalar certificates. -/
theorem verifiedParetoScalarCertificates_card_le
    (scalarBudget : Nat) :
    (table.verifiedParetoScalarCertificates scalarBudget).card <=
      2 ^ U.card := by

  calc
    (table.verifiedParetoScalarCertificates scalarBudget).card <=
        U.powerset.card :=
      Finset.card_le_card
        (Finset.filter_subset _ _)

    _ = 2 ^ U.card := by
      simpa using
        Finset.card_powerset U

/-- Generic bounded-certificate interface for the Pareto-scalar decision. -/
def paretoDecisionBoundedCertificateInterface :
    CorrectedConcreteBoundedCertificateInterface
      (v := v)
      (fun scalarBudget =>
        table.paretoScalarFeasibleDecision scalarBudget = true) :=
  {
    Certificate := Finset ι
    certificateSize := Finset.card
    certificateBound := fun _ => U.card
    verify := table.verifiesParetoScalarCertificate
    correct :=
      table.paretoScalarFeasibleDecision_eq_true_iff_exists_verifiedCertificate
    bounded := by
      intro scalarBudget certificate hVerify
      exact
        table.verifiedParetoScalarCertificate_card_le hVerify
  }

end ParetoCertificateVerifier


section MinimumRankCertificateInterface

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
variable
  (hTarget :
    language ∈
      StartRootedCorrectedConcreteTargetClass
        (v := z)
        α
        (↥U → M)
        (selectedObservationProduct obsFamily U)
        f)

/-- The same finite subset certificate decides the exact minimum-cost rank
threshold under a full-product target witness. -/
theorem minimumRank_le_iff_exists_verifiedCostCertificate
    (rankBudget : Nat) :
    ambientTargetObservationSelectionMinimumCost
          (z := z)
          obsFamily
          f
          selectionCost
          U
          hTarget <=
        rankBudget ↔
      ∃ certificate : Finset ι,
        table.verifiesCostCertificate
            rankBudget
            certificate =
          true := by

  rw [← table.minimumRankAtMostDecision_eq_true_iff
      hTarget
      rankBudget]

  exact
    table.costFeasibleDecision_eq_true_iff_exists_verifiedCostCertificate
      rankBudget

/-- Bounded-certificate interface for the minimum observation-selection rank
threshold itself. -/
def minimumRankBoundedCertificateInterface :
    CorrectedConcreteBoundedCertificateInterface
      (v := v)
      (fun rankBudget =>
        ambientTargetObservationSelectionMinimumCost
            (z := z)
            obsFamily
            f
            selectionCost
            U
            hTarget <=
          rankBudget) :=
  {
    Certificate := Finset ι
    certificateSize := Finset.card
    certificateBound := fun _ => U.card
    verify := table.verifiesCostCertificate
    correct :=
      table.minimumRank_le_iff_exists_verifiedCostCertificate
        hTarget
    bounded := by
      intro rankBudget certificate hVerify
      exact
        table.verifiedCostCertificate_card_le hVerify
  }

end MinimumRankCertificateInterface

end CorrectedConcreteObservationSelectionDecisionTable


section PositiveAdditiveParetoCertificateInterface

variable {α : Type u}
variable {ι : Type v}
variable {M : Type w}
variable [DecidableEq ι]
variable [Monoid M]
variable (obsFamily : ι → α → M)
variable (f : Nat)
variable (coordinateWeight : ι → Nat)
variable (U : Finset ι)
variable (language : Set (Word α))
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

/-- Under positive additive cost, a verified Pareto certificate is equivalent
to the minimum positive-additive-rank threshold. -/
theorem positiveAdditiveMinimumRank_le_iff_exists_verifiedParetoCertificate
    (rankBudget : Nat) :
    ambientTargetObservationSelectionPositiveAdditiveMinimumCost
          (z := z)
          obsFamily
          f
          coordinateWeight
          U
          hTarget <=
        rankBudget ↔
      ∃ certificate : Finset ι,
        table.verifiesParetoScalarCertificate
            rankBudget
            certificate =
          true := by

  rw [← table.positiveAdditiveParetoScalarDecision_eq_true_iff_minimumRank_le
      hTarget
      rankBudget]

  exact
    table.paretoScalarFeasibleDecision_eq_true_iff_exists_verifiedCertificate
      rankBudget

/-- Bounded Pareto-certificate interface for the positive-additive rank
threshold. -/
def positiveAdditiveParetoRankBoundedCertificateInterface :
    CorrectedConcreteBoundedCertificateInterface
      (v := v)
      (fun rankBudget =>
        ambientTargetObservationSelectionPositiveAdditiveMinimumCost
            (z := z)
            obsFamily
            f
            coordinateWeight
            U
            hTarget <=
          rankBudget) :=
  {
    Certificate := Finset ι
    certificateSize := Finset.card
    certificateBound := fun _ => U.card
    verify := table.verifiesParetoScalarCertificate
    correct :=
      positiveAdditiveMinimumRank_le_iff_exists_verifiedParetoCertificate
        (z := z)
        obsFamily
        f
        coordinateWeight
        U
        language
        table
        hTarget
    bounded := by
      intro rankBudget certificate hVerify
      exact
        table.verifiedParetoScalarCertificate_card_le hVerify
  }

end PositiveAdditiveParetoCertificateInterface


section ComplexityCertificateFinalPackage

variable {α : Type u}
variable {ι : Type v}
variable {M : Type w}
variable [DecidableEq ι]
variable [Monoid M]
variable (obsFamily : ι → α → M)
variable (f : Nat)
variable (coordinateWeight : ι → Nat)
variable (U : Finset ι)

/-- Final certificate-complexity package for the canonical semantic table.

The theorem records certificate existence, the linear-in-coordinate-count
certificate bound, the exhaustive powerset bound, and equivalence of ordinary,
minimum-rank, and Pareto certificate views. -/
theorem
    correctedConcreteWorkingGrammar_observationSelectionComplexityCertificate_package
    (language : Set (Word α))
    (hTarget :
      language ∈
        StartRootedCorrectedConcreteTargetClass
          (v := z)
          α
          (↥U → M)
          (selectedObservationProduct obsFamily U)
          f)
    (rankBudget : Nat) :
    let table :=
      correctedConcreteObservationSelectionSemanticDecisionTable
        (z := z)
        obsFamily
        f
        (correctedConcreteObservationSelectionAdditiveCost
          coordinateWeight)
        U
        language
    (table.costFeasibleDecision rankBudget = true ↔
      ∃ certificate : Finset ι,
        table.verifiesCostCertificate
            rankBudget
            certificate =
          true) ∧
      (∀ certificate : Finset ι,
        table.verifiesCostCertificate
              rankBudget
              certificate =
            true →
          certificate.card <= U.card) ∧
      (table.verifiedCostCertificates rankBudget).card <=
        2 ^ U.card ∧
      (ambientTargetObservationSelectionMinimumCost
            (z := z)
            obsFamily
            f
            (correctedConcreteObservationSelectionAdditiveCost
              coordinateWeight)
            U
            hTarget <=
          rankBudget ↔
        ∃ certificate : Finset ι,
          table.verifiesCostCertificate
              rankBudget
              certificate =
            true) ∧
      (ambientTargetObservationSelectionPositiveAdditiveMinimumCost
            (z := z)
            obsFamily
            f
            coordinateWeight
            U
            hTarget <=
          rankBudget ↔
        ∃ certificate : Finset ι,
          table.verifiesParetoScalarCertificate
              rankBudget
              certificate =
            true) ∧
      (∀ certificate : Finset ι,
        table.verifiesParetoScalarCertificate
              rankBudget
              certificate =
            true →
          certificate.card <= U.card) ∧
      (table.verifiedParetoScalarCertificates rankBudget).card <=
        2 ^ U.card := by

  let table :=
    correctedConcreteObservationSelectionSemanticDecisionTable
      (z := z)
      obsFamily
      f
      (correctedConcreteObservationSelectionAdditiveCost
        coordinateWeight)
      U
      language

  exact
    ⟨table.costFeasibleDecision_eq_true_iff_exists_verifiedCostCertificate
        rankBudget,
      fun certificate hVerify =>
        table.verifiedCostCertificate_card_le hVerify,
      table.verifiedCostCertificates_card_le rankBudget,
      table.minimumRank_le_iff_exists_verifiedCostCertificate
        hTarget
        rankBudget,
      positiveAdditiveMinimumRank_le_iff_exists_verifiedParetoCertificate
        (z := z)
        obsFamily
        f
        coordinateWeight
        U
        language
        table
        hTarget
        rankBudget,
      fun certificate hVerify =>
        table.verifiedParetoScalarCertificate_card_le hVerify,
      table.verifiedParetoScalarCertificates_card_le rankBudget⟩

end ComplexityCertificateFinalPackage

end MCFG
