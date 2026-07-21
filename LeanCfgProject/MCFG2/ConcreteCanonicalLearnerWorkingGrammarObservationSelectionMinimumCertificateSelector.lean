/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG.ConcreteCanonicalLearnerWorkingGrammarObservationSelectionMinimumBudgetSelector

/-!
# ConcreteCanonicalLearnerWorkingGrammarObservationSelectionMinimumCertificateSelector.lean

The preceding file selects the least accepted ordinary cost budget and the least
accepted Pareto-scalar budget below a supplied finite ceiling.

This file selects actual finite observation interfaces witnessing those minimum
budgets.

## Ordinary cost witness

From acceptance of the selected minimum cost budget, the finite certificate
interface supplies one selected subset.  Minimality of the budget upgrades the
verifier's weak inequality to the exact equation

```text
selectionCost certificate = selected minimum accepted budget.
```

The selected certificate is an ambient subset, represents the target language,
and has cardinality at most the ambient coordinate count.

## Pareto witness

The same construction selects one Pareto-optimal subset at the selected minimum
Pareto-scalar budget.  Its scalar value is proved exactly equal to that budget.
No uniqueness of the selected subset is asserted: distinct minimum witnesses may
have the same cost or scalar value.

For positive additive observation cost, the selected Pareto certificate realizes
exactly the semantic minimum positive-additive rank.

The selectors are noncomputable witness choices over already finite verified
certificate families.  They do not yet supply a canonical encoded tie-breaker or
a machine-cost analysis.

No target grammar is supplied to any learner.
No `sorry`, `admit`, or `axiom` is used.
-/

namespace MCFG

universe u v w z

namespace CorrectedConcreteObservationSelectionDecisionTable

section MinimumCostCertificateSelector

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

/-- One accepted finite subset certificate at the selected minimum ordinary
cost budget. -/
noncomputable def selectedMinimumCostCertificate
    (maxBudget : Nat)
    (hAccepted :
      table.HasAcceptedCostBudgetUpTo maxBudget) :
    Finset ι :=
  Classical.choose
    ((table.costFeasibleDecision_eq_true_iff_exists_verifiedCostCertificate
      (table.selectedMinimumAcceptedCostBudget
        maxBudget
        hAccepted)).mp
      (table.selectedMinimumAcceptedCostBudget_spec
        maxBudget
        hAccepted).2)

/-- The chosen minimum-cost certificate is accepted at the selected minimum
budget. -/
theorem selectedMinimumCostCertificate_verifies
    (maxBudget : Nat)
    (hAccepted :
      table.HasAcceptedCostBudgetUpTo maxBudget) :
    table.verifiesCostCertificate
          (table.selectedMinimumAcceptedCostBudget
            maxBudget
            hAccepted)
          (table.selectedMinimumCostCertificate
            maxBudget
            hAccepted) =
        true := by

  unfold selectedMinimumCostCertificate

  exact
    Classical.choose_spec
      ((table.costFeasibleDecision_eq_true_iff_exists_verifiedCostCertificate
        (table.selectedMinimumAcceptedCostBudget
          maxBudget
          hAccepted)).mp
        (table.selectedMinimumAcceptedCostBudget_spec
          maxBudget
          hAccepted).2)

/-- The selected minimum-cost certificate has cardinality at most the ambient
coordinate count. -/
theorem selectedMinimumCostCertificate_card_le
    (maxBudget : Nat)
    (hAccepted :
      table.HasAcceptedCostBudgetUpTo maxBudget) :
    (table.selectedMinimumCostCertificate
        maxBudget
        hAccepted).card <=
      U.card := by

  exact
    table.verifiedCostCertificate_card_le
      (table.selectedMinimumCostCertificate_verifies
        maxBudget
        hAccepted)

/-- The selected certificate represents the target and has cost exactly equal
to the selected minimum accepted budget. -/
theorem selectedMinimumCostCertificate_semantic_package
    (maxBudget : Nat)
    (hAccepted :
      table.HasAcceptedCostBudgetUpTo maxBudget) :
    let certificate :=
      table.selectedMinimumCostCertificate
        maxBudget
        hAccepted
    let selectedBudget :=
      table.selectedMinimumAcceptedCostBudget
        maxBudget
        hAccepted
    certificate ⊆ U ∧
      selectionCost certificate = selectedBudget ∧
      language ∈
        StartRootedCorrectedConcreteTargetClass
          (v := z)
          α
          (↥certificate → M)
          (selectedObservationProduct obsFamily certificate)
          f := by

  let certificate :=
    table.selectedMinimumCostCertificate
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
          true := by
    exact
      table.selectedMinimumCostCertificate_verifies
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

/-- Combined verifier, exact-cost, semantic, and size package for the selected
minimum ordinary cost certificate. -/
theorem selectedMinimumCostCertificate_package
    (maxBudget : Nat)
    (hAccepted :
      table.HasAcceptedCostBudgetUpTo maxBudget) :
    let certificate :=
      table.selectedMinimumCostCertificate
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
      certificate.card <= U.card := by

  let certificate :=
    table.selectedMinimumCostCertificate
      maxBudget
      hAccepted

  let selectedBudget :=
    table.selectedMinimumAcceptedCostBudget
      maxBudget
      hAccepted

  have hSemantic :=
    table.selectedMinimumCostCertificate_semantic_package
      maxBudget
      hAccepted

  exact
    ⟨table.selectedMinimumCostCertificate_verifies
        maxBudget
        hAccepted,
      hSemantic.1,
      hSemantic.2.1,
      hSemantic.2.2,
      table.selectedMinimumCostCertificate_card_le
        maxBudget
        hAccepted⟩

end MinimumCostCertificateSelector


section MinimumParetoCertificateSelector

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

/-- One accepted finite Pareto certificate at the selected minimum scalar
budget. -/
noncomputable def selectedMinimumParetoScalarCertificate
    (maxBudget : Nat)
    (hAccepted :
      table.HasAcceptedParetoScalarBudgetUpTo maxBudget) :
    Finset ι :=
  Classical.choose
    ((table.paretoScalarFeasibleDecision_eq_true_iff_exists_verifiedCertificate
      (table.selectedMinimumAcceptedParetoScalarBudget
        maxBudget
        hAccepted)).mp
      (table.selectedMinimumAcceptedParetoScalarBudget_spec
        maxBudget
        hAccepted).2)

/-- The chosen minimum Pareto certificate is accepted at the selected minimum
scalar budget. -/
theorem selectedMinimumParetoScalarCertificate_verifies
    (maxBudget : Nat)
    (hAccepted :
      table.HasAcceptedParetoScalarBudgetUpTo maxBudget) :
    table.verifiesParetoScalarCertificate
          (table.selectedMinimumAcceptedParetoScalarBudget
            maxBudget
            hAccepted)
          (table.selectedMinimumParetoScalarCertificate
            maxBudget
            hAccepted) =
        true := by

  unfold selectedMinimumParetoScalarCertificate

  exact
    Classical.choose_spec
      ((table.paretoScalarFeasibleDecision_eq_true_iff_exists_verifiedCertificate
        (table.selectedMinimumAcceptedParetoScalarBudget
          maxBudget
          hAccepted)).mp
        (table.selectedMinimumAcceptedParetoScalarBudget_spec
          maxBudget
          hAccepted).2)

/-- The selected minimum Pareto certificate has cardinality at most the ambient
coordinate count. -/
theorem selectedMinimumParetoScalarCertificate_card_le
    (maxBudget : Nat)
    (hAccepted :
      table.HasAcceptedParetoScalarBudgetUpTo maxBudget) :
    (table.selectedMinimumParetoScalarCertificate
        maxBudget
        hAccepted).card <=
      U.card := by

  exact
    table.verifiedParetoScalarCertificate_card_le
      (table.selectedMinimumParetoScalarCertificate_verifies
        maxBudget
        hAccepted)

/-- The selected Pareto certificate is semantically Pareto optimal and has
scalar value exactly equal to the selected minimum accepted scalar budget. -/
theorem selectedMinimumParetoScalarCertificate_semantic_package
    (maxBudget : Nat)
    (hAccepted :
      table.HasAcceptedParetoScalarBudgetUpTo maxBudget) :
    let certificate :=
      table.selectedMinimumParetoScalarCertificate
        maxBudget
        hAccepted
    let selectedBudget :=
      table.selectedMinimumAcceptedParetoScalarBudget
        maxBudget
        hAccepted
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
        selectedBudget := by

  let certificate :=
    table.selectedMinimumParetoScalarCertificate
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
          true := by
    exact
      table.selectedMinimumParetoScalarCertificate_verifies
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

/-- Combined verifier, exact-scalar, Pareto, and size package for the selected
minimum Pareto certificate. -/
theorem selectedMinimumParetoScalarCertificate_package
    (maxBudget : Nat)
    (hAccepted :
      table.HasAcceptedParetoScalarBudgetUpTo maxBudget) :
    let certificate :=
      table.selectedMinimumParetoScalarCertificate
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
      certificate.card <= U.card := by

  let certificate :=
    table.selectedMinimumParetoScalarCertificate
      maxBudget
      hAccepted

  let selectedBudget :=
    table.selectedMinimumAcceptedParetoScalarBudget
      maxBudget
      hAccepted

  have hSemantic :=
    table.selectedMinimumParetoScalarCertificate_semantic_package
      maxBudget
      hAccepted

  exact
    ⟨table.selectedMinimumParetoScalarCertificate_verifies
        maxBudget
        hAccepted,
      hSemantic.1,
      hSemantic.2,
      table.selectedMinimumParetoScalarCertificate_card_le
        maxBudget
        hAccepted⟩

end MinimumParetoCertificateSelector


section PositiveAdditiveMinimumParetoCertificate

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

/-- The selected minimum Pareto certificate realizes exactly the semantic
minimum positive-additive observation-selection rank. -/
theorem selectedMinimumParetoScalarCertificate_eq_positiveAdditiveMinimum
    (maxBudget : Nat)
    (hBound :
      ambientTargetObservationSelectionPositiveAdditiveMinimumCost
            (z := z)
            obsFamily
            f
            coordinateWeight
            U
            hTarget <=
          maxBudget) :
    let hAccepted :=
      table.hasAcceptedParetoScalarBudgetUpTo_of_positiveAdditiveMinimum_le
        hTarget
        maxBudget
        hBound
    let certificate :=
      table.selectedMinimumParetoScalarCertificate
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
      certificate.card <= U.card := by

  let hAccepted :=
    table.hasAcceptedParetoScalarBudgetUpTo_of_positiveAdditiveMinimum_le
      hTarget
      maxBudget
      hBound

  let certificate :=
    table.selectedMinimumParetoScalarCertificate
      maxBudget
      hAccepted

  have hSemantic :=
    table.selectedMinimumParetoScalarCertificate_semantic_package
      maxBudget
      hAccepted

  have hBudgetExact :=
    table.selectedMinimumAcceptedParetoScalarBudget_eq_positiveAdditiveMinimum
      hTarget
      maxBudget
      hBound

  exact
    ⟨hSemantic.1,
      hSemantic.2.trans hBudgetExact,
      table.selectedMinimumParetoScalarCertificate_card_le
        maxBudget
        hAccepted⟩

end PositiveAdditiveMinimumParetoCertificate

end CorrectedConcreteObservationSelectionDecisionTable


section MinimumCertificateSelectorFinalPackage

variable {α : Type u}
variable {ι : Type v}
variable {M : Type w}
variable [DecidableEq ι]
variable [Monoid M]
variable (obsFamily : ι → α → M)
variable (f : Nat)
variable (coordinateWeight : ι → Nat)
variable (U : Finset ι)

/-- Final selected-certificate package for the canonical semantic decision
table.  The full-interface positive-additive cost is a sufficient finite search
ceiling, and the selected Pareto certificate realizes the exact semantic
minimum rank. -/
theorem
    correctedConcreteWorkingGrammar_observationSelectionMinimumCertificateSelector_package
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
      table.selectedMinimumParetoScalarCertificate
        maxBudget
        hAccepted
    table.verifiesParetoScalarCertificate
          (table.selectedMinimumAcceptedParetoScalarBudget
            maxBudget
            hAccepted)
          certificate =
        true ∧
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
      certificate.card <= U.card := by

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
    table.selectedMinimumParetoScalarCertificate
      maxBudget
      hAccepted

  have hExact :=
    table.selectedMinimumParetoScalarCertificate_eq_positiveAdditiveMinimum
      hTarget
      maxBudget
      hBound

  exact
    ⟨table.selectedMinimumParetoScalarCertificate_verifies
        maxBudget
        hAccepted,
      hExact.1,
      hExact.2.1,
      hExact.2.2⟩

end MinimumCertificateSelectorFinalPackage

end MCFG
