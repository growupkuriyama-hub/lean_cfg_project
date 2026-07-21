/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG2.ConcreteCanonicalLearnerWorkingGrammarObservationSelectionEncodedDecisionOptimization

/-!
# ConcreteCanonicalLearnerWorkingGrammarObservationSelectionEncodedCertificateSpecification.lean

The preceding files construct total encoded decision and optimization searches.
This file isolates the exact logical verifier specification needed before a
machine-model complexity theorem.

A finite encoded certificate specification for a budget-indexed question
consists of

```text
a natural-number certificate code;
an explicit code bound;
a Boolean verifier;
soundness and completeness:
  Question budget
    iff
  some code below the bound is accepted.
```

The observation-selection instances use the intrinsic dense certificate code.
Their code space has the exact bound

```text
code < 2 ^ U.card.
```

We construct encoded certificate specifications for

* ordinary finite-table cost feasibility;
* finite-table Pareto-scalar feasibility;
* the semantic minimum observation-selection rank threshold;
* the semantic positive-additive minimum-rank threshold using a Pareto
  certificate.

The final package extracts a bounded dense Pareto certificate for the exact
semantic positive-additive minimum rank and records its checked decoding.

This is the logical certificate specification required by an NP-membership
proof, but it is not itself a theorem about a formal complexity class.  A
machine model, encoded input size, and polynomial verification-time theorem
are still required.  No NP-hardness or NP-completeness claim is made.

No target grammar is supplied to any learner.
No `sorry`, `admit`, or `axiom` is used.
-/

namespace MCFG

universe u v w z


section GenericEncodedCertificateSpecification

/-- Generic natural-number certificate specification for a budget-indexed
decision problem.

`codeBound budget` is an exclusive upper bound on accepted certificate codes.
The correctness field combines verifier soundness and completeness. -/
structure CorrectedConcreteEncodedCertificateSpecification
    (Question : Nat → Prop) where

  codeBound : Nat → Nat

  verify : Nat → Nat → Bool

  correct :
    ∀ budget : Nat,
      Question budget ↔
        ∃ code : Nat,
          code < codeBound budget ∧
            verify budget code = true

namespace CorrectedConcreteEncodedCertificateSpecification

variable {Question : Nat → Prop}
variable
  (specification :
    CorrectedConcreteEncodedCertificateSpecification
      Question)

/-- Every positive instance has a verifier-accepted code below the declared
bound. -/
theorem exists_bounded_verified_code
    {budget : Nat}
    (hQuestion : Question budget) :
    ∃ code : Nat,
      code < specification.codeBound budget ∧
        specification.verify budget code = true := by

  exact
    (specification.correct budget).mp
      hQuestion

/-- Every accepted bounded code proves the corresponding positive instance. -/
theorem question_of_bounded_verified_code
    {budget code : Nat}
    (hCode :
      code < specification.codeBound budget)
    (hVerify :
      specification.verify budget code = true) :
    Question budget := by

  exact
    (specification.correct budget).mpr
      ⟨code, hCode, hVerify⟩

/-- Negative instances have no bounded accepted certificate code. -/
theorem no_bounded_verified_code
    {budget : Nat}
    (hQuestion : ¬ Question budget) :
    ¬ ∃ code : Nat,
        code < specification.codeBound budget ∧
          specification.verify budget code = true := by

  intro hCode

  exact
    hQuestion
      ((specification.correct budget).mpr hCode)

/-- The finite bounded verifier search is nonempty exactly for positive
instances. -/
theorem bounded_verified_codes_nonempty_iff
    (budget : Nat) :
    (Finset.range
        (specification.codeBound budget)).filter
          (fun code =>
            specification.verify budget code = true)
        |>.Nonempty ↔
      Question budget := by

  constructor

  · rintro ⟨code, hCode⟩

    have hCodeParts :=
      Finset.mem_filter.mp hCode

    exact
      specification.question_of_bounded_verified_code
        (Finset.mem_range.mp hCodeParts.1)
        hCodeParts.2

  · intro hQuestion

    rcases
        specification.exists_bounded_verified_code
          hQuestion with
      ⟨code, hCode, hVerify⟩

    exact
      ⟨code,
        Finset.mem_filter.mpr
          ⟨Finset.mem_range.mpr hCode,
            hVerify⟩⟩

/-- The explicit bounded verifier search has no more entries than its declared
code universe. -/
theorem bounded_verified_codes_card_le
    (budget : Nat) :
    ((Finset.range
        (specification.codeBound budget)).filter
          (fun code =>
            specification.verify budget code = true)).card <=
      specification.codeBound budget := by

  calc
    ((Finset.range
        (specification.codeBound budget)).filter
          (fun code =>
            specification.verify budget code = true)).card <=
        (Finset.range
          (specification.codeBound budget)).card :=
      Finset.card_le_card
        (Finset.filter_subset _ _)

    _ = specification.codeBound budget := by
      simp

end CorrectedConcreteEncodedCertificateSpecification

end GenericEncodedCertificateSpecification


namespace CorrectedConcreteObservationSelectionDecisionTable

section CostEncodedCertificateSpecification

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

/-- Dense natural-code certificate specification for ordinary cost
feasibility. -/
noncomputable def costDecisionEncodedCertificateSpecification :
    CorrectedConcreteEncodedCertificateSpecification
      (fun costBudget =>
        table.costFeasibleDecision costBudget = true) :=
  {
    codeBound := fun _ => 2 ^ U.card
    verify := table.verifiesDenseCostCertificateCode
    correct := by
      intro costBudget

      constructor

      · intro hDecision

        rcases
            (table.costFeasibleDecision_eq_true_iff_exists_verifiedDenseCode
              costBudget).mp
              hDecision with
          ⟨code, hCode⟩

        exact
          ⟨code,
            (table.mem_verifiedDenseCostCertificateCodes_iff
              costBudget
              code).mp
              hCode⟩

      · rintro ⟨code, hCode, hVerify⟩

        exact
          (table.costFeasibleDecision_eq_true_iff_exists_verifiedDenseCode
            costBudget).mpr
            ⟨code,
              (table.mem_verifiedDenseCostCertificateCodes_iff
                costBudget
                code).mpr
                ⟨hCode, hVerify⟩⟩
  }

/-- Paper-facing exact dense-code bound for ordinary cost certificates. -/
theorem costDecisionEncodedCertificateSpecification_bound
    (costBudget : Nat) :
    (table.costDecisionEncodedCertificateSpecification).codeBound
        costBudget =
      2 ^ U.card := by

  rfl

/-- The generic bounded-code search coincides extensionally with the
previously constructed dense ordinary-cost search. -/
theorem costDecisionEncodedCertificateSpecification_search_eq
    (costBudget : Nat) :
    (Finset.range
        ((table.costDecisionEncodedCertificateSpecification).codeBound
          costBudget)).filter
      (fun code =>
        (table.costDecisionEncodedCertificateSpecification).verify
              costBudget
              code =
          true) =
      table.verifiedDenseCostCertificateCodes costBudget := by

  ext code

  simp [
    costDecisionEncodedCertificateSpecification,
    verifiedDenseCostCertificateCodes,
    correctedConcreteDenseCertificateCodeUniverse
  ]

end CostEncodedCertificateSpecification


section ParetoEncodedCertificateSpecification

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

/-- Dense natural-code certificate specification for Pareto-scalar
feasibility. -/
noncomputable def paretoDecisionEncodedCertificateSpecification :
    CorrectedConcreteEncodedCertificateSpecification
      (fun scalarBudget =>
        table.paretoScalarFeasibleDecision scalarBudget = true) :=
  {
    codeBound := fun _ => 2 ^ U.card
    verify := table.verifiesDenseParetoScalarCertificateCode
    correct := by
      intro scalarBudget

      constructor

      · intro hDecision

        rcases
            (table.paretoScalarFeasibleDecision_eq_true_iff_exists_verifiedDenseCode
              scalarBudget).mp
              hDecision with
          ⟨code, hCode⟩

        exact
          ⟨code,
            (table.mem_verifiedDenseParetoScalarCertificateCodes_iff
              scalarBudget
              code).mp
              hCode⟩

      · rintro ⟨code, hCode, hVerify⟩

        exact
          (table.paretoScalarFeasibleDecision_eq_true_iff_exists_verifiedDenseCode
            scalarBudget).mpr
            ⟨code,
              (table.mem_verifiedDenseParetoScalarCertificateCodes_iff
                scalarBudget
                code).mpr
                ⟨hCode, hVerify⟩⟩
  }

/-- Paper-facing exact dense-code bound for Pareto-scalar certificates. -/
theorem paretoDecisionEncodedCertificateSpecification_bound
    (scalarBudget : Nat) :
    (table.paretoDecisionEncodedCertificateSpecification).codeBound
        scalarBudget =
      2 ^ U.card := by

  rfl

/-- The generic bounded-code search coincides extensionally with the
previously constructed dense Pareto-scalar search. -/
theorem paretoDecisionEncodedCertificateSpecification_search_eq
    (scalarBudget : Nat) :
    (Finset.range
        ((table.paretoDecisionEncodedCertificateSpecification).codeBound
          scalarBudget)).filter
      (fun code =>
        (table.paretoDecisionEncodedCertificateSpecification).verify
              scalarBudget
              code =
          true) =
      table.verifiedDenseParetoScalarCertificateCodes scalarBudget := by

  ext code

  simp [
    paretoDecisionEncodedCertificateSpecification,
    verifiedDenseParetoScalarCertificateCodes,
    correctedConcreteDenseCertificateCodeUniverse
  ]

end ParetoEncodedCertificateSpecification


section MinimumRankEncodedCertificateSpecification

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

/-- Dense natural-code certificate specification for the semantic minimum
observation-selection rank threshold. -/
noncomputable def minimumRankEncodedCertificateSpecification :
    CorrectedConcreteEncodedCertificateSpecification
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
    codeBound := fun _ => 2 ^ U.card
    verify := table.verifiesDenseCostCertificateCode
    correct := by
      intro rankBudget

      rw [
        ← table.minimumRankAtMostDecision_eq_true_iff
          hTarget
          rankBudget
      ]

      simpa [minimumRankAtMostDecision] using
        (table.costDecisionEncodedCertificateSpecification).correct
          rankBudget
  }

end MinimumRankEncodedCertificateSpecification


section PositiveAdditiveParetoRankEncodedCertificateSpecification

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

/-- Dense Pareto-code certificate specification for the semantic
positive-additive minimum-rank threshold. -/
noncomputable def
    positiveAdditiveParetoRankEncodedCertificateSpecification :
    CorrectedConcreteEncodedCertificateSpecification
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
    codeBound := fun _ => 2 ^ U.card
    verify := table.verifiesDenseParetoScalarCertificateCode
    correct := by
      intro rankBudget

      rw [
        ← table.positiveAdditiveParetoScalarDecision_eq_true_iff_minimumRank_le
          hTarget
          rankBudget
      ]

      exact
        (table.paretoDecisionEncodedCertificateSpecification).correct
          rankBudget
  }

end PositiveAdditiveParetoRankEncodedCertificateSpecification

end CorrectedConcreteObservationSelectionDecisionTable


section EncodedCertificateSpecificationFinalPackage

variable {α : Type u}
variable {ι : Type v}
variable {M : Type w}
variable [DecidableEq ι]
variable [Monoid M]
variable (obsFamily : ι → α → M)
variable (f : Nat)
variable (coordinateWeight : ι → Nat)
variable (U : Finset ι)

/-- Final positive-additive encoded-certificate specification package.

At the exact semantic minimum rank, there exists a checked Pareto certificate
code below `2 ^ U.card`.  The code decodes to a Pareto-optimal selected
coordinate subset. -/
theorem
    correctedConcreteWorkingGrammar_observationSelectionEncodedCertificateSpecification_package
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
    let minimumRank :=
      ambientTargetObservationSelectionPositiveAdditiveMinimumCost
        (z := z)
        obsFamily
        f
        coordinateWeight
        U
        hTarget
    ∃ code : Nat,
      code < 2 ^ U.card ∧
        table.verifiesDenseParetoScalarCertificateCode
              minimumRank
              code =
          true ∧
        ∃ certificate : Finset ι,
          correctedConcreteDenseCertificateDecode U code =
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
                certificate <=
              minimumRank := by

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

  let specification :=
    table.positiveAdditiveParetoRankEncodedCertificateSpecification
      hTarget

  have hQuestion :
      ambientTargetObservationSelectionPositiveAdditiveMinimumCost
            (z := z)
            obsFamily
            f
            coordinateWeight
            U
            hTarget <=
          minimumRank :=
    Nat.le_refl minimumRank

  rcases
      specification.exists_bounded_verified_code
        hQuestion with
    ⟨code, hCode, hVerify⟩

  have hCodeBound :
      code < 2 ^ U.card := by

    simpa [
      CorrectedConcreteObservationSelectionDecisionTable.positiveAdditiveParetoRankEncodedCertificateSpecification
    ] using hCode

  rcases
      (table.verifiesDenseParetoScalarCertificateCode_eq_true_iff
        minimumRank
        code).mp
        hVerify with
    ⟨certificate, hDecode, hCertificateVerify⟩

  have hCertificateSemantics :=
    (table.verifiesParetoScalarCertificate_eq_true_iff
      minimumRank
      certificate).mp
      hCertificateVerify

  exact
    ⟨code,
      hCodeBound,
      hVerify,
      certificate,
      hDecode,
      hCertificateSemantics.1,
      hCertificateSemantics.2⟩

end EncodedCertificateSpecificationFinalPackage

end MCFG
