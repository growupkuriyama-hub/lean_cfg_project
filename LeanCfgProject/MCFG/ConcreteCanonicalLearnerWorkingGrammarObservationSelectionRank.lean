/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG.ConcreteCanonicalLearnerWorkingGrammarObservationBudgetFiltration

/-!
# ConcreteCanonicalLearnerWorkingGrammarObservationSelectionRank.lean

The preceding file organizes cost-bounded finite observation searches into a
monotone budget filtration and proves that the semantic minimum cost is exactly
the first nonempty budget.

This file lifts that pointwise filtration to a hierarchy of language classes.

## Cost-profile classes

For a finite ambient candidate set `U`, observation family `obsFamily`, and
selection cost `selectionCost`, define

```lean
CorrectedConcreteObservationSelectionCostProfileClass ... budget
```

to be the class of all languages representable by some selected product
`Product(S)` with

```text
S ⊆ U
and
selectionCost S ≤ budget.
```

The profile classes are monotone in the budget and are contained in the target
class of the full ambient product.

Every full-product target belongs to the profile at budget `selectionCost U`.

## Exact observation-selection rank shells

The exact shell at rank `r` contains exactly the languages

```text
representable within budget r,
but not representable within any smaller budget.
```

Every selectable language belongs to exactly one shell: the shell indexed by
its semantic minimum selection cost.

Distinct exact shells are disjoint.

The full ambient-product target class decomposes exactly as the union of all
exact cost-rank shells.

## Rank obstruction

For a selectable language with minimum cost `rank`,

```text
language is outside profile budget b
  ↔
b < rank.
```

Thus exclusion from a bounded observation-selection profile is an exact lower
bound on observation-selection cost.

This is the language-class version of the pointwise budget-filtration theorem
and is intended as the interface for future reductions and lower bounds.

## Certified minimum-rank selection

For every full ambient-product target, the finite minimum-cost selector chooses
a subset `S` at the exact observation-selection rank.  Its selected-product
certified learner identifies the target and returns one exact checked output at
the selected product's minimum certified-description rank.

The result therefore carries two separate ranks:

```text
observation-selection cost rank,
certified grammar-description rank after the observation is selected.
```

No relation between those two ranks is asserted in this file.

## Positive additive specialization

The hierarchy is specialized to the positive additive coordinate cost

```text
|S| + ∑ i ∈ S, coordinateWeight i.
```

This yields an exact positive-additive observation-selection rank hierarchy.

## Boundary

The profile classes use semantic target membership and are noncomputable.
This file establishes exact rank structure, not an executable decision
procedure or complexity classification.

No target grammar is supplied to any learner.
No `sorry`, `admit`, or `axiom` is used.
-/

namespace MCFG

universe u v w z


section ObservationSelectionCostProfileDefinition

variable (α : Type u)
variable (ι : Type v)
variable (M : Type w)
variable [Monoid M]
variable (obsFamily : ι → α → M)
variable (f : Nat)
variable (selectionCost : Finset ι → Nat)
variable (U : Finset ι)

/-- Languages representable by an ambient observation selection within one
cost budget. -/
def CorrectedConcreteObservationSelectionCostProfileClass
    (costBudget : Nat) :
    Set (Set (Word α)) :=
  {language |
    CorrectedConcreteObservationSelectionAtCost
      (obsFamily := obsFamily)
      (f := f)
      selectionCost
      U
      language
      costBudget}

/-- Languages of exact observation-selection cost rank `rank`. -/
def CorrectedConcreteObservationSelectionExactCostRankClass
    (rank : Nat) :
    Set (Set (Word α)) :=
  {language |
    CorrectedConcreteObservationSelectionAtCost
        (obsFamily := obsFamily)
        (f := f)
        selectionCost
        U
        language
        rank ∧
      ∀ costBudget : Nat,
        costBudget < rank →
          ¬
            CorrectedConcreteObservationSelectionAtCost
              (obsFamily := obsFamily)
              (f := f)
              selectionCost
              U
              language
              costBudget}

end ObservationSelectionCostProfileDefinition


section ObservationSelectionCostProfileBasicProperties

variable {α : Type u}
variable {ι : Type v}
variable {M : Type w}
variable [Monoid M]
variable {obsFamily : ι → α → M}
variable {f : Nat}
variable {selectionCost : Finset ι → Nat}
variable {U : Finset ι}

/-- Membership in a cost-profile class is exactly bounded-cost observation
selection feasibility. -/
theorem mem_observationSelectionCostProfileClass_iff
    {language : Set (Word α)}
    {costBudget : Nat} :
    language ∈
        CorrectedConcreteObservationSelectionCostProfileClass
          (z := z)
          α
          ι
          M
          obsFamily
          f
          selectionCost
          U
          costBudget ↔
      CorrectedConcreteObservationSelectionAtCost
        (obsFamily := obsFamily)
        (f := f)
        selectionCost
        U
        language
        costBudget := by

  rfl

/-- Membership in an exact shell is bounded feasibility at `rank` together
with failure at every smaller budget. -/
theorem mem_observationSelectionExactCostRankClass_iff
    {language : Set (Word α)}
    {rank : Nat} :
    language ∈
        CorrectedConcreteObservationSelectionExactCostRankClass
          (z := z)
          α
          ι
          M
          obsFamily
          f
          selectionCost
          U
          rank ↔
      CorrectedConcreteObservationSelectionAtCost
          (obsFamily := obsFamily)
          (f := f)
          selectionCost
          U
          language
          rank ∧
        ∀ costBudget : Nat,
          costBudget < rank →
            ¬
              CorrectedConcreteObservationSelectionAtCost
                (obsFamily := obsFamily)
                (f := f)
                selectionCost
                U
                language
                costBudget := by

  rfl

/-- Observation-selection profile classes are monotone in the cost budget. -/
theorem observationSelectionCostProfileClass_mono
    {costBudget costBudget' : Nat}
    (hBudget :
      costBudget <= costBudget') :
    CorrectedConcreteObservationSelectionCostProfileClass
        (z := z)
        α
        ι
        M
        obsFamily
        f
        selectionCost
        U
        costBudget ⊆
      CorrectedConcreteObservationSelectionCostProfileClass
        (z := z)
        α
        ι
        M
        obsFamily
        f
        selectionCost
        U
        costBudget' := by

  intro language hLanguage

  exact
    correctedConcreteObservationSelectionAtCost_mono
      selectionCost
      hBudget
      hLanguage

/-- Every exact-rank shell is contained in the cumulative profile at the same
rank. -/
theorem observationSelectionExactCostRankClass_subset_profileClass
    (rank : Nat) :
    CorrectedConcreteObservationSelectionExactCostRankClass
        (z := z)
        α
        ι
        M
        obsFamily
        f
        selectionCost
        U
        rank ⊆
      CorrectedConcreteObservationSelectionCostProfileClass
        (z := z)
        α
        ι
        M
        obsFamily
        f
        selectionCost
        U
        rank := by

  intro language hLanguage

  exact
    hLanguage.1

/-- Every bounded selection target is also a target of the full ambient
selected product. -/
theorem observationSelectionCostProfileClass_subset_fullProductTargetClass
    (costBudget : Nat) :
    CorrectedConcreteObservationSelectionCostProfileClass
        (z := z)
        α
        ι
        M
        obsFamily
        f
        selectionCost
        U
        costBudget ⊆
      StartRootedCorrectedConcreteTargetClass
        (v := z)
        α
        (↥U → M)
        (selectedObservationProduct obsFamily U)
        f := by

  intro language hLanguage

  rcases hLanguage with
    ⟨S, hSU, hCost, hTarget⟩

  exact
    selectedObservationProductTargetClass_mono
      (z := z)
      obsFamily
      f
      hSU
      hTarget

/-- Every full ambient-product target belongs to the cumulative profile at the
cost of selecting all ambient coordinates. -/
theorem fullProductTarget_mem_observationSelectionCostProfileClass
    {language : Set (Word α)}
    (hTarget :
      language ∈
        StartRootedCorrectedConcreteTargetClass
          (v := z)
          α
          (↥U → M)
          (selectedObservationProduct obsFamily U)
          f) :
    language ∈
      CorrectedConcreteObservationSelectionCostProfileClass
        (z := z)
        α
        ι
        M
        obsFamily
        f
        selectionCost
        U
        (selectionCost U) := by

  exact
    ⟨U,
      by
        intro index hindex
        exact hindex,
      Nat.le_refl _,
      hTarget⟩

end ObservationSelectionCostProfileBasicProperties


section ExactCostRankShellTheorems

variable {α : Type u}
variable {ι : Type v}
variable {M : Type w}
variable [Monoid M]
variable {obsFamily : ι → α → M}
variable {f : Nat}
variable {selectionCost : Finset ι → Nat}
variable {U : Finset ι}
variable {language : Set (Word α)}

/-- Every selectable language lies in the exact shell indexed by its semantic
minimum selection cost. -/
theorem observationSelection_mem_exactMinimumCostRankClass
    (hSelection :
      HasCorrectedConcreteObservationSelectionCost
        (obsFamily := obsFamily)
        (f := f)
        selectionCost
        U
        language) :
    language ∈
      CorrectedConcreteObservationSelectionExactCostRankClass
        (z := z)
        α
        ι
        M
        obsFamily
        f
        selectionCost
        U
        (correctedConcreteObservationSelectionMinimumCost
          selectionCost
          hSelection) := by

  refine
    ⟨hSelection.minimumCost_spec,
      ?_⟩

  intro costBudget hBudget

  exact
    (observationSelection_not_atCost_iff_lt_minimumCost
      hSelection
      costBudget).mpr
      hBudget

/-- Exact shell membership is equivalent to equality with the semantic minimum
selection cost. -/
theorem observationSelection_mem_exactCostRankClass_iff_rank_eq_minimum
    (hSelection :
      HasCorrectedConcreteObservationSelectionCost
        (obsFamily := obsFamily)
        (f := f)
        selectionCost
        U
        language)
    (rank : Nat) :
    language ∈
        CorrectedConcreteObservationSelectionExactCostRankClass
          (z := z)
          α
          ι
          M
          obsFamily
          f
          selectionCost
          U
          rank ↔
      rank =
        correctedConcreteObservationSelectionMinimumCost
          selectionCost
          hSelection := by

  constructor

  · intro hRank

    have hMinimumLe :
        correctedConcreteObservationSelectionMinimumCost
            selectionCost
            hSelection <=
          rank :=
      hSelection.minimumCost_le_of_selection
        hRank.1

    by_contra hNe

    have hMinimumLt :
        correctedConcreteObservationSelectionMinimumCost
            selectionCost
            hSelection <
          rank := by
      omega

    exact
      hRank.2
        (correctedConcreteObservationSelectionMinimumCost
          selectionCost
          hSelection)
        hMinimumLt
        hSelection.minimumCost_spec

  · intro hRank

    subst rank

    exact
      observationSelection_mem_exactMinimumCostRankClass
        (z := z)
        hSelection

/-- Cumulative profile membership is exactly the threshold condition against
the semantic minimum cost. -/
theorem observationSelection_mem_costProfileClass_iff_minimum_le
    (hSelection :
      HasCorrectedConcreteObservationSelectionCost
        (obsFamily := obsFamily)
        (f := f)
        selectionCost
        U
        language)
    (costBudget : Nat) :
    language ∈
        CorrectedConcreteObservationSelectionCostProfileClass
          (z := z)
          α
          ι
          M
          obsFamily
          f
          selectionCost
          U
          costBudget ↔
      correctedConcreteObservationSelectionMinimumCost
          selectionCost
          hSelection <=
        costBudget := by

  exact
    hSelection.selectionAtCost_iff_minimumCost_le
      costBudget

/-- Exclusion from a cumulative profile is exactly a strict lower bound on the
minimum observation-selection cost. -/
theorem observationSelection_not_mem_costProfileClass_iff_lt_minimum
    (hSelection :
      HasCorrectedConcreteObservationSelectionCost
        (obsFamily := obsFamily)
        (f := f)
        selectionCost
        U
        language)
    (costBudget : Nat) :
    language ∉
        CorrectedConcreteObservationSelectionCostProfileClass
          (z := z)
          α
          ι
          M
          obsFamily
          f
          selectionCost
          U
          costBudget ↔
      costBudget <
        correctedConcreteObservationSelectionMinimumCost
          selectionCost
          hSelection := by

  exact
    observationSelection_not_atCost_iff_lt_minimumCost
      hSelection
      costBudget

end ExactCostRankShellTheorems


section ExactCostRankShellDisjointness

variable {α : Type u}
variable {ι : Type v}
variable {M : Type w}
variable [Monoid M]
variable {obsFamily : ι → α → M}
variable {f : Nat}
variable {selectionCost : Finset ι → Nat}
variable {U : Finset ι}

/-- Distinct exact observation-selection cost-rank shells are disjoint. -/
theorem observationSelectionExactCostRankClasses_disjoint
    {rank rank' : Nat}
    (hNe :
      rank ≠ rank') :
    Set.Disjoint
      (CorrectedConcreteObservationSelectionExactCostRankClass
        (z := z)
        α
        ι
        M
        obsFamily
        f
        selectionCost
        U
        rank)
      (CorrectedConcreteObservationSelectionExactCostRankClass
        (z := z)
        α
        ι
        M
        obsFamily
        f
        selectionCost
        U
        rank') := by

  rw [Set.disjoint_left]

  intro language hRank hRank'

  by_cases hLess :
      rank < rank'

  · exact
      hRank'.2
        rank
        hLess
        hRank.1

  · have hReverse :
        rank' < rank := by
      omega

    exact
      hRank.2
        rank'
        hReverse
        hRank'.1

end ExactCostRankShellDisjointness


section FullTargetClassShellDecomposition

variable {α : Type u}
variable {ι : Type v}
variable {M : Type w}
variable [Monoid M]
variable {obsFamily : ι → α → M}
variable {f : Nat}
variable {selectionCost : Finset ι → Nat}
variable {U : Finset ι}

/-- The full ambient-product target class is exactly the union of all exact
observation-selection cost-rank shells. -/
theorem fullProductTargetClass_eq_exists_exactObservationSelectionCostRank :
    StartRootedCorrectedConcreteTargetClass
        (v := z)
        α
        (↥U → M)
        (selectedObservationProduct obsFamily U)
        f =
      {language : Set (Word α) |
        ∃ rank : Nat,
          language ∈
            CorrectedConcreteObservationSelectionExactCostRankClass
              (z := z)
              α
              ι
              M
              obsFamily
              f
              selectionCost
              U
              rank} := by

  ext language

  constructor

  · intro hTarget

    let hSelection :=
      hasCorrectedConcreteObservationSelectionCost_of_fullProductTarget
        (obsFamily := obsFamily)
        (f := f)
        selectionCost
        hTarget

    exact
      ⟨correctedConcreteObservationSelectionMinimumCost
          selectionCost
          hSelection,
        observationSelection_mem_exactMinimumCostRankClass
          (z := z)
          hSelection⟩

  · intro hRank

    rcases hRank with
      ⟨rank, hLanguage⟩

    exact
      observationSelectionCostProfileClass_subset_fullProductTargetClass
        (z := z)
        rank
        hLanguage.1

/-- Every full ambient-product target belongs to a unique exact cost-rank
shell. -/
theorem fullProductTarget_existsUnique_exactObservationSelectionCostRank
    {language : Set (Word α)}
    (hTarget :
      language ∈
        StartRootedCorrectedConcreteTargetClass
          (v := z)
          α
          (↥U → M)
          (selectedObservationProduct obsFamily U)
          f) :
    ∃! rank : Nat,
      language ∈
        CorrectedConcreteObservationSelectionExactCostRankClass
          (z := z)
          α
          ι
          M
          obsFamily
          f
          selectionCost
          U
          rank := by

  let hSelection :=
    hasCorrectedConcreteObservationSelectionCost_of_fullProductTarget
      (obsFamily := obsFamily)
      (f := f)
      selectionCost
      hTarget

  refine
    ⟨correctedConcreteObservationSelectionMinimumCost
        selectionCost
        hSelection,
      observationSelection_mem_exactMinimumCostRankClass
        (z := z)
        hSelection,
      ?_⟩

  intro rank hRank

  exact
    (observationSelection_mem_exactCostRankClass_iff_rank_eq_minimum
      (z := z)
      hSelection
      rank).mp
      hRank

end FullTargetClassShellDecomposition


section AmbientObservationSelectionCostRank

variable {α : Type u}
variable {ι : Type v}
variable {M : Type w}
variable [Monoid M]
variable (obsFamily : ι → α → M)
variable (f : Nat)
variable (selectionCost : Finset ι → Nat)
variable (U : Finset ι)

/-- Paper-facing observation-selection cost rank of a target represented by the
full ambient selected product. -/
noncomputable def ambientTargetObservationSelectionCostRank
    {language : Set (Word α)}
    (hTarget :
      language ∈
        StartRootedCorrectedConcreteTargetClass
          (v := z)
          α
          (↥U → M)
          (selectedObservationProduct obsFamily U)
          f) :
    Nat :=
  ambientTargetObservationSelectionMinimumCost
    (z := z)
    obsFamily
    f
    selectionCost
    U
    hTarget

/-- The observation-selection cost rank is no greater than the cost of the full
ambient candidate set. -/
theorem ambientTargetObservationSelectionCostRank_le_fullCost
    {language : Set (Word α)}
    (hTarget :
      language ∈
        StartRootedCorrectedConcreteTargetClass
          (v := z)
          α
          (↥U → M)
          (selectedObservationProduct obsFamily U)
          f) :
    ambientTargetObservationSelectionCostRank
        (z := z)
        obsFamily
        f
        selectionCost
        U
        hTarget <=
      selectionCost U := by

  exact
    ambientTargetObservationSelectionMinimumCost_le
      (z := z)
      obsFamily
      f
      selectionCost
      U
      hTarget

/-- A full-product target belongs to the exact shell at its observation-
selection cost rank. -/
theorem ambientTarget_mem_exactObservationSelectionCostRankClass
    {language : Set (Word α)}
    (hTarget :
      language ∈
        StartRootedCorrectedConcreteTargetClass
          (v := z)
          α
          (↥U → M)
          (selectedObservationProduct obsFamily U)
          f) :
    language ∈
      CorrectedConcreteObservationSelectionExactCostRankClass
        (z := z)
        α
        ι
        M
        obsFamily
        f
        selectionCost
        U
        (ambientTargetObservationSelectionCostRank
          (z := z)
          obsFamily
          f
          selectionCost
          U
          hTarget) := by

  let hSelection :=
    hasCorrectedConcreteObservationSelectionCost_of_fullProductTarget
      (obsFamily := obsFamily)
      (f := f)
      selectionCost
      hTarget

  simpa [
    ambientTargetObservationSelectionCostRank,
    ambientTargetObservationSelectionMinimumCost,
    hSelection
  ] using
    observationSelection_mem_exactMinimumCostRankClass
      (z := z)
      hSelection

/-- Profile threshold theorem stated using the paper-facing target rank. -/
theorem ambientTarget_mem_costProfileClass_iff_rank_le
    {language : Set (Word α)}
    (hTarget :
      language ∈
        StartRootedCorrectedConcreteTargetClass
          (v := z)
          α
          (↥U → M)
          (selectedObservationProduct obsFamily U)
          f)
    (costBudget : Nat) :
    language ∈
        CorrectedConcreteObservationSelectionCostProfileClass
          (z := z)
          α
          ι
          M
          obsFamily
          f
          selectionCost
          U
          costBudget ↔
      ambientTargetObservationSelectionCostRank
          (z := z)
          obsFamily
          f
          selectionCost
          U
          hTarget <=
        costBudget := by

  let hSelection :=
    hasCorrectedConcreteObservationSelectionCost_of_fullProductTarget
      (obsFamily := obsFamily)
      (f := f)
      selectionCost
      hTarget

  simpa [
    ambientTargetObservationSelectionCostRank,
    ambientTargetObservationSelectionMinimumCost,
    hSelection
  ] using
    observationSelection_mem_costProfileClass_iff_minimum_le
      (z := z)
      hSelection
      costBudget

/-- Rank obstruction theorem stated using the paper-facing target rank. -/
theorem ambientTarget_not_mem_costProfileClass_iff_lt_rank
    {language : Set (Word α)}
    (hTarget :
      language ∈
        StartRootedCorrectedConcreteTargetClass
          (v := z)
          α
          (↥U → M)
          (selectedObservationProduct obsFamily U)
          f)
    (costBudget : Nat) :
    language ∉
        CorrectedConcreteObservationSelectionCostProfileClass
          (z := z)
          α
          ι
          M
          obsFamily
          f
          selectionCost
          U
          costBudget ↔
      costBudget <
        ambientTargetObservationSelectionCostRank
          (z := z)
          obsFamily
          f
          selectionCost
          U
          hTarget := by

  let hSelection :=
    hasCorrectedConcreteObservationSelectionCost_of_fullProductTarget
      (obsFamily := obsFamily)
      (f := f)
      selectionCost
      hTarget

  simpa [
    ambientTargetObservationSelectionCostRank,
    ambientTargetObservationSelectionMinimumCost,
    hSelection
  ] using
    observationSelection_not_mem_costProfileClass_iff_lt_minimum
      (z := z)
      hSelection
      costBudget

end AmbientObservationSelectionCostRank


section CertifiedObservationSelectionRank

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

/-- A full-product target has an exact observation-selection cost rank, an
actual minimum-cost selected subset at that rank, and a certified learner for
the selected product. -/
theorem ambientTarget_observationSelectionCostRank_certified_package
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
      (rank : Nat)
      (S : Finset ι)
      (hSelected :
        language ∈
          StartRootedCorrectedConcreteTargetClass
            (v := z)
            α
            (↥S → M)
            (selectedObservationProduct obsFamily S)
            f),
      rank =
          ambientTargetObservationSelectionCostRank
            (z := z)
            obsFamily
            f
            selectionCost
            U
            hTarget ∧
        selectionCost S = rank ∧
        language ∈
          CorrectedConcreteObservationSelectionExactCostRankClass
            (z := z)
            α
            ι
            M
            obsFamily
            f
            selectionCost
            U
            rank ∧
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

  let hSelection :=
    hasCorrectedConcreteObservationSelectionCost_of_fullProductTarget
      (obsFamily := obsFamily)
      (f := f)
      selectionCost
      hTarget

  let result :=
    correctedConcreteObservationMinimumCostSelectionResult
      (z := z)
      obsFamily
      f
      selectionCost
      U
      language
      hSelection

  have hCertified :=
    correctedConcreteObservationMinimumCostSelectionResult_certified_package
      (z := z)
      hα
      obsFamily
      f
      selectionCost
      U
      language
      hSelection
      result

  let rank :=
    correctedConcreteObservationSelectionMinimumCost
      selectionCost
      hSelection

  have hRankClass :
      language ∈
        CorrectedConcreteObservationSelectionExactCostRankClass
          (z := z)
          α
          ι
          M
          obsFamily
          f
          selectionCost
          U
          rank :=
    observationSelection_mem_exactMinimumCostRankClass
      (z := z)
      hSelection

  have hRankEq :
      rank =
        ambientTargetObservationSelectionCostRank
          (z := z)
          obsFamily
          f
          selectionCost
          U
          hTarget := by

    simp [
      rank,
      ambientTargetObservationSelectionCostRank,
      ambientTargetObservationSelectionMinimumCost,
      hSelection
    ]

  exact
    ⟨rank,
      result.selected,
      result.selected_target,
      hRankEq,
      by
        simpa [rank] using
          result.selected_cost_eq_minimum,
      hRankClass,
      hCertified.1,
      hCertified.2.2⟩

end CertifiedObservationSelectionRank


section PositiveAdditiveObservationSelectionRank

variable {α : Type u}
variable {ι : Type v}
variable {M : Type w}
variable [Monoid M]
variable (obsFamily : ι → α → M)
variable (f : Nat)
variable (coordinateWeight : ι → Nat)
variable (U : Finset ι)

/-- Positive-additive observation-selection cumulative profile. -/
def CorrectedConcretePositiveAdditiveObservationSelectionProfileClass
    (costBudget : Nat) :
    Set (Set (Word α)) :=
  CorrectedConcreteObservationSelectionCostProfileClass
    (z := z)
    α
    ι
    M
    obsFamily
    f
    (correctedConcreteObservationSelectionPositiveAdditiveCost
      coordinateWeight)
    U
    costBudget

/-- Positive-additive exact observation-selection rank shell. -/
def CorrectedConcretePositiveAdditiveObservationSelectionExactRankClass
    (rank : Nat) :
    Set (Set (Word α)) :=
  CorrectedConcreteObservationSelectionExactCostRankClass
    (z := z)
    α
    ι
    M
    obsFamily
    f
    (correctedConcreteObservationSelectionPositiveAdditiveCost
      coordinateWeight)
    U
    rank

/-- Positive-additive profiles are monotone. -/
theorem positiveAdditiveObservationSelectionProfileClass_mono
    {costBudget costBudget' : Nat}
    (hBudget :
      costBudget <= costBudget') :
    CorrectedConcretePositiveAdditiveObservationSelectionProfileClass
        (z := z)
        obsFamily
        f
        coordinateWeight
        U
        costBudget ⊆
      CorrectedConcretePositiveAdditiveObservationSelectionProfileClass
        (z := z)
        obsFamily
        f
        coordinateWeight
        U
        costBudget' := by

  exact
    observationSelectionCostProfileClass_mono
      (z := z)
      hBudget

/-- Distinct positive-additive exact-rank shells are disjoint. -/
theorem positiveAdditiveObservationSelectionExactRankClasses_disjoint
    {rank rank' : Nat}
    (hNe :
      rank ≠ rank') :
    Set.Disjoint
      (CorrectedConcretePositiveAdditiveObservationSelectionExactRankClass
        (z := z)
        obsFamily
        f
        coordinateWeight
        U
        rank)
      (CorrectedConcretePositiveAdditiveObservationSelectionExactRankClass
        (z := z)
        obsFamily
        f
        coordinateWeight
        U
        rank') := by

  exact
    observationSelectionExactCostRankClasses_disjoint
      (z := z)
      hNe

/-- The full ambient-product target class decomposes into positive-additive
exact-rank shells. -/
theorem
    fullProductTargetClass_eq_exists_positiveAdditiveObservationSelectionRank :
    StartRootedCorrectedConcreteTargetClass
        (v := z)
        α
        (↥U → M)
        (selectedObservationProduct obsFamily U)
        f =
      {language : Set (Word α) |
        ∃ rank : Nat,
          language ∈
            CorrectedConcretePositiveAdditiveObservationSelectionExactRankClass
              (z := z)
              obsFamily
              f
              coordinateWeight
              U
              rank} := by

  exact
    fullProductTargetClass_eq_exists_exactObservationSelectionCostRank
      (z := z)

end PositiveAdditiveObservationSelectionRank


section ObservationSelectionRankFinalPackage

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

/-- Final cumulative profile, exact shell, obstruction, decomposition, and
certified minimum-rank selection package. -/
theorem
    correctedConcreteCertifiedWorkingGrammar_observationSelectionRank_package :
    (∀ costBudget costBudget' : Nat,
      costBudget <= costBudget' →
      CorrectedConcreteObservationSelectionCostProfileClass
          (z := z)
          α
          ι
          M
          obsFamily
          f
          selectionCost
          U
          costBudget ⊆
        CorrectedConcreteObservationSelectionCostProfileClass
          (z := z)
          α
          ι
          M
          obsFamily
          f
          selectionCost
          U
          costBudget') ∧
      (StartRootedCorrectedConcreteTargetClass
          (v := z)
          α
          (↥U → M)
          (selectedObservationProduct obsFamily U)
          f =
        {language : Set (Word α) |
          ∃ rank : Nat,
            language ∈
              CorrectedConcreteObservationSelectionExactCostRankClass
                (z := z)
                α
                ι
                M
                obsFamily
                f
                selectionCost
                U
                rank}) ∧
      (∀ rank rank' : Nat,
        rank ≠ rank' →
        Set.Disjoint
          (CorrectedConcreteObservationSelectionExactCostRankClass
            (z := z)
            α
            ι
            M
            obsFamily
            f
            selectionCost
            U
            rank)
          (CorrectedConcreteObservationSelectionExactCostRankClass
            (z := z)
            α
            ι
            M
            obsFamily
            f
            selectionCost
            U
            rank')) ∧
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
        ∀ costBudget : Nat,
          (language ∉
              CorrectedConcreteObservationSelectionCostProfileClass
                (z := z)
                α
                ι
                M
                obsFamily
                f
                selectionCost
                U
                costBudget ↔
            costBudget <
              ambientTargetObservationSelectionCostRank
                (z := z)
                obsFamily
                f
                selectionCost
                U
                hTarget)) ∧
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
          (rank : Nat)
          (S : Finset ι)
          (hSelected :
            language ∈
              StartRootedCorrectedConcreteTargetClass
                (v := z)
                α
                (↥S → M)
                (selectedObservationProduct obsFamily S)
                f),
          rank =
              ambientTargetObservationSelectionCostRank
                (z := z)
                obsFamily
                f
                selectionCost
                U
                hTarget ∧
            selectionCost S = rank ∧
            language ∈
              CorrectedConcreteObservationSelectionExactCostRankClass
                (z := z)
                α
                ι
                M
                obsFamily
                f
                selectionCost
                U
                rank ∧
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
                    f) := by

  refine
    ⟨?_,
      fullProductTargetClass_eq_exists_exactObservationSelectionCostRank
        (z := z),
      ?_,
      ?_,
      ?_⟩

  · intro costBudget costBudget' hBudget

    exact
      observationSelectionCostProfileClass_mono
        (z := z)
        hBudget

  · intro rank rank' hNe

    exact
      observationSelectionExactCostRankClasses_disjoint
        (z := z)
        hNe

  · intro language hTarget costBudget

    exact
      ambientTarget_not_mem_costProfileClass_iff_lt_rank
        (z := z)
        obsFamily
        f
        selectionCost
        U
        hTarget
        costBudget

  · intro language hTarget

    exact
      ambientTarget_observationSelectionCostRank_certified_package
        (z := z)
        hα
        obsFamily
        f
        selectionCost
        U
        hTarget

end ObservationSelectionRankFinalPackage

end MCFG
