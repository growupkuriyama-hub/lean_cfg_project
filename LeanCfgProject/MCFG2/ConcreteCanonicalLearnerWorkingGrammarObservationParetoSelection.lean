/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG.ConcreteCanonicalLearnerWorkingGrammarObservationWeightedSelection

/-!
# ConcreteCanonicalLearnerWorkingGrammarObservationParetoSelection.lean

The preceding file defines minimum-cost finite observation selection for an
arbitrary natural-number cost function.

This file treats observation design as a two-criterion optimization problem:

```text
number of selected coordinates,
selection cost.
```

## Dominance

For two selected sets `R` and `S`, `R` weakly dominates `S` when

```text
R.card ≤ S.card
and
selectionCost R ≤ selectionCost S.
```

It strictly dominates `S` when at least one of those inequalities is strict.

A feasible selection is Pareto optimal when no other feasible ambient
selection strictly dominates it.

## Existence of Pareto selections

Define the scalarized cost

```text
S.card + selectionCost S.
```

Any strict Pareto improvement strictly decreases this scalar cost.  Therefore
an attained minimum of the scalarized cost is Pareto optimal.

For every language represented by the full ambient product, we obtain an
actual Pareto-optimal selected subset.  Its own certified learner identifies
the target and returns one exact checked output at the selected product's
minimum certified-description rank.

This argument proves existence without asserting that every Pareto point is
obtained by one scalarization, and without assuming convexity.

## Pareto frontier

The Pareto frontier is the set of all Pareto-optimal selected subsets.  For
every ambient-product target it is nonempty.

The corresponding profile map records

```text
(S.card, selectionCost S).
```

Distinct selected sets may have the same profile; no uniqueness is claimed.

## Irredundancy under monotone cost

A cost is subset-monotone when

```text
R ⊆ S
⇒
selectionCost R ≤ selectionCost S.
```

Under this assumption, every Pareto-optimal selection is inclusion-irredundant.
Indeed, any proper subset representing the same target would use strictly fewer
coordinates and no greater cost, hence would strictly dominate the selection.

Consequently every coordinate of a Pareto-optimal selection is essential, and
restoring any deleted coordinate gives a strict observation refinement whose
gain class contains the target.

The ordinary cardinality cost and the constant-zero cost are subset-monotone.

## Boundary

Pareto existence is semantic and finite.  This file does not provide an
executable enumeration algorithm, complexity classification, or guarantee that
the Pareto frontier has polynomial size.

No target grammar is supplied to any learner.
No `sorry`, `admit`, or `axiom` is used.
-/

namespace MCFG

universe u v w z


section ObservationSelectionParetoDefinitions

variable {ι : Type v}

/-- A finite selection cost is monotone under subset. -/
def CorrectedConcreteObservationSelectionCostMonotone
    (selectionCost : Finset ι → Nat) :
    Prop :=
  ∀ ⦃R S : Finset ι⦄,
    R ⊆ S →
      selectionCost R <= selectionCost S

/-- Two-criterion profile: selected-coordinate count and external selection
cost. -/
def correctedConcreteObservationSelectionProfile
    (selectionCost : Finset ι → Nat)
    (S : Finset ι) :
    Nat × Nat :=
  (S.card, selectionCost S)

/-- Weak Pareto dominance between two selected subsets. -/
def CorrectedConcreteObservationSelectionWeaklyDominates
    (selectionCost : Finset ι → Nat)
    (R S : Finset ι) :
    Prop :=
  R.card <= S.card ∧
    selectionCost R <= selectionCost S

/-- Strict Pareto dominance: weak dominance with at least one strict
improvement. -/
def CorrectedConcreteObservationSelectionStrictlyDominates
    (selectionCost : Finset ι → Nat)
    (R S : Finset ι) :
    Prop :=
  CorrectedConcreteObservationSelectionWeaklyDominates
      selectionCost R S ∧
    (R.card < S.card ∨
      selectionCost R < selectionCost S)

/-- Scalar cost used only to prove existence of a Pareto point. -/
def correctedConcreteObservationSelectionParetoScalarCost
    (selectionCost : Finset ι → Nat)
    (S : Finset ι) :
    Nat :=
  S.card + selectionCost S

/-- Ordinary cardinality cost is subset-monotone. -/
theorem
    correctedConcreteObservationSelectionCardinalityCost_monotone :
    CorrectedConcreteObservationSelectionCostMonotone
      (correctedConcreteObservationSelectionCardinalityCost :
        Finset ι → Nat) := by

  intro R S hRS

  exact
    Finset.card_le_card hRS

/-- The constant-zero cost is subset-monotone. -/
theorem correctedConcreteObservationSelectionZeroCost_monotone :
    CorrectedConcreteObservationSelectionCostMonotone
      (fun _ : Finset ι => 0) := by

  intro R S hRS

  exact
    Nat.le_refl 0

/-- Strict dominance strictly decreases the scalarized cost. -/
theorem
    observationSelection_strictDominance_implies_scalarCost_lt
    {selectionCost : Finset ι → Nat}
    {R S : Finset ι}
    (hDominates :
      CorrectedConcreteObservationSelectionStrictlyDominates
        selectionCost R S) :
    correctedConcreteObservationSelectionParetoScalarCost
        selectionCost R <
      correctedConcreteObservationSelectionParetoScalarCost
        selectionCost S := by

  rcases hDominates with
    ⟨⟨hcard, hcost⟩,
      hstrict⟩

  unfold
    correctedConcreteObservationSelectionParetoScalarCost

  rcases hstrict with
    hcardStrict | hcostStrict

  · omega

  · omega

/-- Strict dominance is irreflexive. -/
theorem observationSelection_strictDominance_irrefl
    (selectionCost : Finset ι → Nat)
    (S : Finset ι) :
    ¬
      CorrectedConcreteObservationSelectionStrictlyDominates
        selectionCost S S := by

  intro hDominates

  have hScalar :
      correctedConcreteObservationSelectionParetoScalarCost
          selectionCost S <
        correctedConcreteObservationSelectionParetoScalarCost
          selectionCost S :=
    observationSelection_strictDominance_implies_scalarCost_lt
      hDominates

  omega

/-- Strict dominance is transitive. -/
theorem observationSelection_strictDominance_trans
    {selectionCost : Finset ι → Nat}
    {R S T : Finset ι}
    (hRS :
      CorrectedConcreteObservationSelectionStrictlyDominates
        selectionCost R S)
    (hST :
      CorrectedConcreteObservationSelectionStrictlyDominates
        selectionCost S T) :
    CorrectedConcreteObservationSelectionStrictlyDominates
      selectionCost R T := by

  rcases hRS with
    ⟨⟨hcardRS, hcostRS⟩,
      hstrictRS⟩

  rcases hST with
    ⟨⟨hcardST, hcostST⟩,
      hstrictST⟩

  refine
    ⟨⟨hcardRS.trans hcardST,
        hcostRS.trans hcostST⟩,
      ?_⟩

  rcases hstrictRS with
    hcardStrict | hcostStrict

  · exact
      Or.inl
        (lt_of_lt_of_le
          hcardStrict hcardST)

  · exact
      Or.inr
        (lt_of_lt_of_le
          hcostStrict hcostST)

end ObservationSelectionParetoDefinitions


section ObservationSelectionParetoOptimality

variable {α : Type u}
variable {ι : Type v}
variable {M : Type w}
variable [Monoid M]
variable (obsFamily : ι → α → M)
variable (f : Nat)
variable (selectionCost : Finset ι → Nat)

/-- A feasible selected product is Pareto optimal within ambient candidate set
`U` for the target language. -/
def CorrectedConcreteObservationSelectionParetoOptimal
    (U : Finset ι)
    (language : Set (Word α))
    (S : Finset ι) :
    Prop :=
  S ⊆ U ∧
    language ∈
      StartRootedCorrectedConcreteTargetClass
        (v := z)
        α
        (↥S → M)
        (selectedObservationProduct obsFamily S)
        f ∧
    ∀ R : Finset ι,
      R ⊆ U →
      language ∈
        StartRootedCorrectedConcreteTargetClass
          (v := z)
          α
          (↥R → M)
          (selectedObservationProduct obsFamily R)
          f →
      ¬
        CorrectedConcreteObservationSelectionStrictlyDominates
          selectionCost R S

/-- Set of all Pareto-optimal selected subsets. -/
def CorrectedConcreteObservationSelectionParetoFrontier
    (U : Finset ι)
    (language : Set (Word α)) :
    Set (Finset ι) :=
  {S |
    CorrectedConcreteObservationSelectionParetoOptimal
      (z := z)
      obsFamily f selectionCost U language S}

/-- Two-criterion profiles achieved by Pareto-optimal selections. -/
def CorrectedConcreteObservationSelectionParetoProfileSet
    (U : Finset ι)
    (language : Set (Word α)) :
    Set (Nat × Nat) :=
  {profile |
    ∃ S : Finset ι,
      S ∈
          CorrectedConcreteObservationSelectionParetoFrontier
            (z := z)
            obsFamily f selectionCost U language ∧
        profile =
          correctedConcreteObservationSelectionProfile
            selectionCost S}

end ObservationSelectionParetoOptimality


section ScalarMinimumIsPareto

variable {α : Type u}
variable {ι : Type v}
variable {M : Type w}
variable [Monoid M]
variable {obsFamily : ι → α → M}
variable {f : Nat}
variable {selectionCost : Finset ι → Nat}
variable {U : Finset ι}
variable {language : Set (Word α)}

/-- An exact minimum of the scalarized profile cost is Pareto optimal. -/
theorem observationSelection_exactScalarMinimum_isPareto
    (hSelection :
      HasCorrectedConcreteObservationSelectionCost
        (obsFamily := obsFamily)
        (f := f)
        (correctedConcreteObservationSelectionParetoScalarCost
          selectionCost)
        U language)
    {S : Finset ι}
    (hSU : S ⊆ U)
    (hScalar :
      correctedConcreteObservationSelectionParetoScalarCost
          selectionCost S =
        correctedConcreteObservationSelectionMinimumCost
          (correctedConcreteObservationSelectionParetoScalarCost
            selectionCost)
          hSelection)
    (hTarget :
      language ∈
        StartRootedCorrectedConcreteTargetClass
          (v := z)
          α
          (↥S → M)
          (selectedObservationProduct obsFamily S)
          f) :
    CorrectedConcreteObservationSelectionParetoOptimal
      (z := z)
      obsFamily f selectionCost U language S := by

  refine
    ⟨hSU,
      hTarget,
      ?_⟩

  intro R hRU hRTarget hDominates

  have hMinimum :
      correctedConcreteObservationSelectionMinimumCost
          (correctedConcreteObservationSelectionParetoScalarCost
            selectionCost)
          hSelection <=
        correctedConcreteObservationSelectionParetoScalarCost
          selectionCost R := by

    apply
      hSelection.minimumCost_le_of_selection

    exact
      ⟨R,
        hRU,
        Nat.le_refl _,
        hRTarget⟩

  have hStrict :
      correctedConcreteObservationSelectionParetoScalarCost
          selectionCost R <
        correctedConcreteObservationSelectionParetoScalarCost
          selectionCost S :=
    observationSelection_strictDominance_implies_scalarCost_lt
      hDominates

  rw [hScalar] at hStrict

  omega

/-- Every feasible finite observation-selection problem has a Pareto-optimal
solution. -/
theorem observationSelection_exists_paretoOptimal
    (hSelection :
      HasCorrectedConcreteObservationSelectionCost
        (obsFamily := obsFamily)
        (f := f)
        (correctedConcreteObservationSelectionParetoScalarCost
          selectionCost)
        U language) :
    ∃ S : Finset ι,
      CorrectedConcreteObservationSelectionParetoOptimal
        (z := z)
        obsFamily f selectionCost U language S := by

  rcases hSelection.exists_selection_exact_minimumCost with
    ⟨S, hSU, hScalar, hTarget⟩

  exact
    ⟨S,
      observationSelection_exactScalarMinimum_isPareto
        (z := z)
        hSelection hSU hScalar hTarget⟩

/-- The Pareto frontier is nonempty whenever the scalarized selection problem
is feasible. -/
theorem observationSelection_paretoFrontier_nonempty
    (hSelection :
      HasCorrectedConcreteObservationSelectionCost
        (obsFamily := obsFamily)
        (f := f)
        (correctedConcreteObservationSelectionParetoScalarCost
          selectionCost)
        U language) :
    ∃ S : Finset ι,
      S ∈
        CorrectedConcreteObservationSelectionParetoFrontier
          (z := z)
          obsFamily f selectionCost U language := by

  exact
    observationSelection_exists_paretoOptimal
      (z := z)
      hSelection

/-- The Pareto profile set is nonempty whenever the selection problem is
feasible. -/
theorem observationSelection_paretoProfileSet_nonempty
    (hSelection :
      HasCorrectedConcreteObservationSelectionCost
        (obsFamily := obsFamily)
        (f := f)
        (correctedConcreteObservationSelectionParetoScalarCost
          selectionCost)
        U language) :
    ∃ profile : Nat × Nat,
      profile ∈
        CorrectedConcreteObservationSelectionParetoProfileSet
          (z := z)
          obsFamily f selectionCost U language := by

  rcases
      observationSelection_exists_paretoOptimal
        (z := z)
        hSelection with
    ⟨S, hPareto⟩

  exact
    ⟨correctedConcreteObservationSelectionProfile
        selectionCost S,
      S,
      hPareto,
      rfl⟩

end ScalarMinimumIsPareto


section AmbientParetoSelection

variable {α : Type u}
variable {ι : Type v}
variable {M : Type w}
variable [Monoid M]
variable (obsFamily : ι → α → M)
variable (f : Nat)
variable (selectionCost : Finset ι → Nat)
variable (U : Finset ι)

/-- Every target represented by the full ambient product has a
Pareto-optimal selected observation subset. -/
theorem ambientTarget_exists_paretoObservationSelection
    {language : Set (Word α)}
    (hTarget :
      language ∈
        StartRootedCorrectedConcreteTargetClass
          (v := z)
          α
          (↥U → M)
          (selectedObservationProduct obsFamily U)
          f) :
    ∃ S : Finset ι,
      CorrectedConcreteObservationSelectionParetoOptimal
        (z := z)
        obsFamily f selectionCost U language S := by

  let hSelection :=
    hasCorrectedConcreteObservationSelectionCost_of_fullProductTarget
      (obsFamily := obsFamily)
      (f := f)
      (correctedConcreteObservationSelectionParetoScalarCost
        selectionCost)
      hTarget

  exact
    observationSelection_exists_paretoOptimal
      (z := z)
      hSelection

/-- The Pareto frontier is nonempty for every ambient-product target. -/
theorem ambientTarget_paretoFrontier_nonempty
    {language : Set (Word α)}
    (hTarget :
      language ∈
        StartRootedCorrectedConcreteTargetClass
          (v := z)
          α
          (↥U → M)
          (selectedObservationProduct obsFamily U)
          f) :
    ∃ S : Finset ι,
      S ∈
        CorrectedConcreteObservationSelectionParetoFrontier
          (z := z)
          obsFamily f selectionCost U language := by

  exact
    ambientTarget_exists_paretoObservationSelection
      (z := z)
      obsFamily f selectionCost U hTarget

/-- The Pareto profile set is nonempty for every ambient-product target. -/
theorem ambientTarget_paretoProfileSet_nonempty
    {language : Set (Word α)}
    (hTarget :
      language ∈
        StartRootedCorrectedConcreteTargetClass
          (v := z)
          α
          (↥U → M)
          (selectedObservationProduct obsFamily U)
          f) :
    ∃ profile : Nat × Nat,
      profile ∈
        CorrectedConcreteObservationSelectionParetoProfileSet
          (z := z)
          obsFamily f selectionCost U language := by

  let hSelection :=
    hasCorrectedConcreteObservationSelectionCost_of_fullProductTarget
      (obsFamily := obsFamily)
      (f := f)
      (correctedConcreteObservationSelectionParetoScalarCost
        selectionCost)
      hTarget

  exact
    observationSelection_paretoProfileSet_nonempty
      (z := z)
      hSelection

end AmbientParetoSelection


section ParetoIrredundancy

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

/-- Under subset-monotone cost, every Pareto-optimal selection is
inclusion-irredundant. -/
theorem observationSelection_paretoOptimal_irredundant
    (hCostMonotone :
      CorrectedConcreteObservationSelectionCostMonotone
        selectionCost)
    {S : Finset ι}
    (hPareto :
      CorrectedConcreteObservationSelectionParetoOptimal
        (z := z)
        obsFamily f selectionCost U language S) :
    CorrectedConcreteObservationSelectionIrredundant
      (z := z)
      α ι M obsFamily f language S := by

  refine
    ⟨hPareto.2.1,
      ?_⟩

  intro R hRS hRTarget

  have hSubsetNe :
      R ⊆ S ∧
        R ≠ S :=
    Finset.ssubset_iff_subset_ne.mp
      hRS

  have hRU :
      R ⊆ U := by

    intro index hindex

    exact
      hPareto.1
        (hSubsetNe.1 hindex)

  have hCardStrict :
      R.card < S.card :=
    Finset.card_lt_card
      hRS

  have hCost :
      selectionCost R <=
        selectionCost S :=
    hCostMonotone
      hSubsetNe.1

  have hDominates :
      CorrectedConcreteObservationSelectionStrictlyDominates
        selectionCost R S :=
    ⟨⟨Nat.le_of_lt hCardStrict,
        hCost⟩,
      Or.inl hCardStrict⟩

  exact
    hPareto.2.2
      R hRU hRTarget hDominates

/-- Every coordinate of a Pareto-optimal selection is essential when the cost
is subset-monotone. -/
theorem observationSelection_paretoOptimal_coordinateEssential
    (hCostMonotone :
      CorrectedConcreteObservationSelectionCostMonotone
        selectionCost)
    {S : Finset ι}
    (hPareto :
      CorrectedConcreteObservationSelectionParetoOptimal
        (z := z)
        obsFamily f selectionCost U language S)
    {index : ι}
    (hindex : index ∈ S) :
    CorrectedConcreteSelectedObservationCoordinateEssential
      (z := z)
      α ι M obsFamily f language S index := by

  exact
    observationSelection_irredundant_coordinateEssential
      (z := z)
      (observationSelection_paretoOptimal_irredundant
        (z := z)
        hCostMonotone hPareto)
      hindex

/-- Restoring a deleted coordinate of a Pareto-optimal selection is an
essential refinement when cost is subset-monotone. -/
theorem
    observationSelection_paretoOptimal_coordinateRefinementEssential
    (hCostMonotone :
      CorrectedConcreteObservationSelectionCostMonotone
        selectionCost)
    {S : Finset ι}
    (hPareto :
      CorrectedConcreteObservationSelectionParetoOptimal
        (z := z)
        obsFamily f selectionCost U language S)
    {index : ι}
    (hindex : index ∈ S) :
    CorrectedConcreteObservationRefinementEssential
      (z := z)
      α
      (↥(S.erase index) → M)
      (↥S → M)
      (selectedObservationProduct obsFamily (S.erase index))
      (selectedObservationProduct obsFamily S)
      f := by

  exact
    observationSelection_irredundant_coordinateRefinementEssential
      (z := z)
      (observationSelection_paretoOptimal_irredundant
        (z := z)
        hCostMonotone hPareto)
      hindex

/-- A Pareto-optimal target belongs to the strict gain created by restoring any
selected coordinate, under subset-monotone cost. -/
theorem observationSelection_paretoOptimal_target_mem_coordinateGain
    (hCostMonotone :
      CorrectedConcreteObservationSelectionCostMonotone
        selectionCost)
    {S : Finset ι}
    (hPareto :
      CorrectedConcreteObservationSelectionParetoOptimal
        (z := z)
        obsFamily f selectionCost U language S)
    {index : ι}
    (hindex : index ∈ S) :
    language ∈
      StartRootedCorrectedConcreteSelectedObservationExtensionGainClass
        (z := z)
        obsFamily f
        (S.erase index)
        S := by

  exact
    observationSelection_irredundant_target_mem_coordinateGain
      (z := z)
      (observationSelection_paretoOptimal_irredundant
        (z := z)
        hCostMonotone hPareto)
      hindex

end ParetoIrredundancy


section ParetoCertifiedLearner

variable {α : Type u}
variable {ι : Type v}
variable {M : Type w}
variable [Fintype M]
variable [DecidableEq α]
variable [DecidableEq ι]
variable [DecidableEq M]
variable [Monoid M]
variable (hα : Nonempty α)
variable (obsFamily : ι → α → M)
variable (f : Nat)
variable (selectionCost : Finset ι → Nat)
variable (U : Finset ι)

/-- Every ambient-product target has a Pareto-optimal selected product whose own
certified learner identifies the target and returns an exact minimum-rank
checked description. -/
theorem ambientTarget_exists_paretoCertifiedObservationSelection
    {language : Set (Word α)}
    (hTarget :
      language ∈
        StartRootedCorrectedConcreteTargetClass
          (v := z)
          α
          (↥U → M)
          (selectedObservationProduct obsFamily U)
          f) :
    ∃
      (S : Finset ι)
      (hPareto :
        CorrectedConcreteObservationSelectionParetoOptimal
          (z := z)
          obsFamily f selectionCost U language S),
      IdentifiesLanguageFromPositiveData
          (correctedConcreteCertifiedWorkingGrammarHypLanguage
            (selectedObservationProduct obsFamily S)
            f)
          (correctedConcreteCertifiedWorkingGrammarLearner
            hα
            (selectedObservationProduct obsFamily S)
            f)
          language ∧
        language ∈
          CorrectedConcreteCertifiedRankProfileClass
            (α := α)
            (M := ↥S → M)
            (selectedObservationProduct obsFamily S)
            f
            (startRootedTargetCertifiedDescriptionRank
              (v := z)
              hα
              (selectedObservationProduct obsFamily S)
              f
              hPareto.2.1) ∧
        ∃
          C :
            CorrectedConcreteCertifiedWorkingGrammarHypothesis
              α
              (↥S → M)
              (selectedObservationProduct obsFamily S)
              f,
          C.output.grammar.StringLanguage =
              language ∧
            C.bits.length <=
              correctedConcreteCertifiedRankBitBudget
                (startRootedTargetCertifiedDescriptionRank
                  (v := z)
                  hα
                  (selectedObservationProduct obsFamily S)
                  f
                  hPareto.2.1)
                f ∧
            C.canonicalSearch.length <=
              correctedConcreteCertifiedRankSearchBudget
                (startRootedTargetCertifiedDescriptionRank
                  (v := z)
                  hα
                  (selectedObservationProduct obsFamily S)
                  f
                  hPareto.2.1)
                f := by

  let scalarCost :=
    correctedConcreteObservationSelectionParetoScalarCost
      selectionCost

  let hSelection :=
    hasCorrectedConcreteObservationSelectionCost_of_fullProductTarget
      (obsFamily := obsFamily)
      (f := f)
      scalarCost
      hTarget

  rcases hSelection.exists_selection_exact_minimumCost with
    ⟨S, hSU, hScalar, hSelected⟩

  have hPareto :
      CorrectedConcreteObservationSelectionParetoOptimal
        (z := z)
        obsFamily f selectionCost U language S := by

    apply
      observationSelection_exactScalarMinimum_isPareto
        (z := z)
        hSelection hSU

    · simpa [scalarCost] using hScalar

    · exact hSelected

  exact
    ⟨S,
      hPareto,
      selectedProductCertifiedLearner_identifies_targetClass
        (z := z)
        hα obsFamily f S
        language hSelected,
      startRootedTarget_mem_minimumCertifiedDescriptionRankProfile
        (v := z)
        hα
        (selectedObservationProduct obsFamily S)
        f
        hSelected,
      startRootedTarget_exists_output_at_minimumCertifiedDescriptionRank
        (v := z)
        hα
        (selectedObservationProduct obsFamily S)
        f
        hSelected⟩

/-- Under subset-monotone cost, the certified Pareto selection can additionally
be chosen inclusion-irredundant and coordinatewise essential. -/
theorem
    ambientTarget_exists_irredundantParetoCertifiedObservationSelection
    (hCostMonotone :
      CorrectedConcreteObservationSelectionCostMonotone
        selectionCost)
    {language : Set (Word α)}
    (hTarget :
      language ∈
        StartRootedCorrectedConcreteTargetClass
          (v := z)
          α
          (↥U → M)
          (selectedObservationProduct obsFamily U)
          f) :
    ∃
      (S : Finset ι)
      (hPareto :
        CorrectedConcreteObservationSelectionParetoOptimal
          (z := z)
          obsFamily f selectionCost U language S)
      (hSelected :
        language ∈
          StartRootedCorrectedConcreteTargetClass
            (v := z)
            α
            (↥S → M)
            (selectedObservationProduct obsFamily S)
            f),
      CorrectedConcreteObservationSelectionIrredundant
          (z := z)
          α ι M obsFamily f language S ∧
        (∀ index : ι,
          index ∈ S →
          CorrectedConcreteObservationRefinementEssential
            (z := z)
            α
            (↥(S.erase index) → M)
            (↥S → M)
            (selectedObservationProduct obsFamily (S.erase index))
            (selectedObservationProduct obsFamily S)
            f) ∧
        IdentifiesLanguageFromPositiveData
          (correctedConcreteCertifiedWorkingGrammarHypLanguage
            (selectedObservationProduct obsFamily S)
            f)
          (correctedConcreteCertifiedWorkingGrammarLearner
            hα
            (selectedObservationProduct obsFamily S)
            f)
          language ∧
        ∃
          C :
            CorrectedConcreteCertifiedWorkingGrammarHypothesis
              α
              (↥S → M)
              (selectedObservationProduct obsFamily S)
              f,
          C.output.grammar.StringLanguage =
              language ∧
            C.bits.length <=
              correctedConcreteCertifiedRankBitBudget
                (startRootedTargetCertifiedDescriptionRank
                  (v := z)
                  hα
                  (selectedObservationProduct obsFamily S)
                  f
                  hSelected)
                f ∧
            C.canonicalSearch.length <=
              correctedConcreteCertifiedRankSearchBudget
                (startRootedTargetCertifiedDescriptionRank
                  (v := z)
                  hα
                  (selectedObservationProduct obsFamily S)
                  f
                  hSelected)
                f := by

  rcases
      ambientTarget_exists_paretoCertifiedObservationSelection
        (z := z)
        hα obsFamily f selectionCost U hTarget with
    ⟨S,
      hPareto,
      hIdentifies,
      hProfile,
      C,
      hLanguage,
      hBits,
      hSearch⟩

  let hSelected :=
    hPareto.2.1

  have hIrredundant :
      CorrectedConcreteObservationSelectionIrredundant
        (z := z)
        α ι M obsFamily f language S :=
    observationSelection_paretoOptimal_irredundant
      (z := z)
      hCostMonotone hPareto

  exact
    ⟨S,
      hPareto,
      hSelected,
      hIrredundant,
      fun index hindex =>
        observationSelection_irredundant_coordinateRefinementEssential
          (z := z)
          hIrredundant hindex,
      hIdentifies,
      C,
      hLanguage,
      hBits,
      hSearch⟩

end ParetoCertifiedLearner


section ObservationParetoSelectionFinalPackage

variable {α : Type u}
variable {ι : Type v}
variable {M : Type w}
variable [Fintype M]
variable [DecidableEq α]
variable [DecidableEq ι]
variable [DecidableEq M]
variable [Monoid M]
variable (hα : Nonempty α)
variable (obsFamily : ι → α → M)
variable (f : Nat)
variable (selectionCost : Finset ι → Nat)
variable (U : Finset ι)

/-- Final Pareto-frontier existence and certified-learning package. -/
theorem
    correctedConcreteCertifiedWorkingGrammar_observationParetoSelection_package :
    (∀
      language : Set (Word α),
      ∀ hTarget :
        language ∈
          StartRootedCorrectedConcreteTargetClass
            (v := z)
            α
            (↥U → M)
            (selectedObservationProduct obsFamily U)
            f,
      ∃ S : Finset ι,
        S ∈
          CorrectedConcreteObservationSelectionParetoFrontier
            (z := z)
            obsFamily f selectionCost U language) ∧
      (∀
        language : Set (Word α),
        ∀ hTarget :
          language ∈
            StartRootedCorrectedConcreteTargetClass
              (v := z)
              α
              (↥U → M)
              (selectedObservationProduct obsFamily U)
              f,
        ∃ profile : Nat × Nat,
          profile ∈
            CorrectedConcreteObservationSelectionParetoProfileSet
              (z := z)
              obsFamily f selectionCost U language) ∧
      (∀
        language : Set (Word α),
        ∀ hTarget :
          language ∈
            StartRootedCorrectedConcreteTargetClass
              (v := z)
              α
              (↥U → M)
              (selectedObservationProduct obsFamily U)
              f,
        ∃
          (S : Finset ι)
          (hPareto :
            CorrectedConcreteObservationSelectionParetoOptimal
              (z := z)
              obsFamily f selectionCost U language S),
          IdentifiesLanguageFromPositiveData
              (correctedConcreteCertifiedWorkingGrammarHypLanguage
                (selectedObservationProduct obsFamily S)
                f)
              (correctedConcreteCertifiedWorkingGrammarLearner
                hα
                (selectedObservationProduct obsFamily S)
                f)
              language ∧
            ∃
              C :
                CorrectedConcreteCertifiedWorkingGrammarHypothesis
                  α
                  (↥S → M)
                  (selectedObservationProduct obsFamily S)
                  f,
              C.output.grammar.StringLanguage =
                  language ∧
                C.bits.length <=
                  correctedConcreteCertifiedRankBitBudget
                    (startRootedTargetCertifiedDescriptionRank
                      (v := z)
                      hα
                      (selectedObservationProduct obsFamily S)
                      f
                      hPareto.2.1)
                    f ∧
                C.canonicalSearch.length <=
                  correctedConcreteCertifiedRankSearchBudget
                    (startRootedTargetCertifiedDescriptionRank
                      (v := z)
                      hα
                      (selectedObservationProduct obsFamily S)
                      f
                      hPareto.2.1)
                    f) := by

  refine
    ⟨?_,
      ?_,
      ?_⟩

  · intro language hTarget

    exact
      ambientTarget_paretoFrontier_nonempty
        (z := z)
        obsFamily f selectionCost U hTarget

  · intro language hTarget

    exact
      ambientTarget_paretoProfileSet_nonempty
        (z := z)
        obsFamily f selectionCost U hTarget

  · intro language hTarget

    rcases
        ambientTarget_exists_paretoCertifiedObservationSelection
          (z := z)
          hα obsFamily f selectionCost U hTarget with
      ⟨S,
        hPareto,
        hIdentifies,
        hProfile,
        C,
        hLanguage,
        hBits,
        hSearch⟩

    exact
      ⟨S,
        hPareto,
        hIdentifies,
        C,
        hLanguage,
        hBits,
        hSearch⟩

/-- Final irredundant Pareto-certified package under subset-monotone cost. -/
theorem
    correctedConcreteCertifiedWorkingGrammar_observationMonotoneCostParetoSelection_package
    (hCostMonotone :
      CorrectedConcreteObservationSelectionCostMonotone
        selectionCost) :
    ∀
      language : Set (Word α),
      ∀ hTarget :
        language ∈
          StartRootedCorrectedConcreteTargetClass
            (v := z)
            α
            (↥U → M)
            (selectedObservationProduct obsFamily U)
            f,
      ∃
        (S : Finset ι)
        (hPareto :
          CorrectedConcreteObservationSelectionParetoOptimal
            (z := z)
            obsFamily f selectionCost U language S),
        CorrectedConcreteObservationSelectionIrredundant
            (z := z)
            α ι M obsFamily f language S ∧
          (∀ index : ι,
            index ∈ S →
            CorrectedConcreteObservationRefinementEssential
              (z := z)
              α
              (↥(S.erase index) → M)
              (↥S → M)
              (selectedObservationProduct obsFamily (S.erase index))
              (selectedObservationProduct obsFamily S)
              f) ∧
          IdentifiesLanguageFromPositiveData
            (correctedConcreteCertifiedWorkingGrammarHypLanguage
              (selectedObservationProduct obsFamily S)
              f)
            (correctedConcreteCertifiedWorkingGrammarLearner
              hα
              (selectedObservationProduct obsFamily S)
              f)
            language ∧
          ∃
            C :
              CorrectedConcreteCertifiedWorkingGrammarHypothesis
                α
                (↥S → M)
                (selectedObservationProduct obsFamily S)
                f,
            C.output.grammar.StringLanguage =
                language ∧
              C.bits.length <=
                correctedConcreteCertifiedRankBitBudget
                  (startRootedTargetCertifiedDescriptionRank
                    (v := z)
                    hα
                    (selectedObservationProduct obsFamily S)
                    f
                    hPareto.2.1)
                  f ∧
              C.canonicalSearch.length <=
                correctedConcreteCertifiedRankSearchBudget
                  (startRootedTargetCertifiedDescriptionRank
                    (v := z)
                    hα
                    (selectedObservationProduct obsFamily S)
                    f
                    hPareto.2.1)
                  f := by

  intro language hTarget

  rcases
      ambientTarget_exists_irredundantParetoCertifiedObservationSelection
        (z := z)
        hα obsFamily f selectionCost U hCostMonotone hTarget with
    ⟨S,
      hPareto,
      hSelected,
      hIrredundant,
      hEssential,
      hIdentifies,
      C,
      hLanguage,
      hBits,
      hSearch⟩

  exact
    ⟨S,
      hPareto,
      hIrredundant,
      hEssential,
      hIdentifies,
      C,
      hLanguage,
      hBits,
      hSearch⟩

end ObservationParetoSelectionFinalPackage

end MCFG
