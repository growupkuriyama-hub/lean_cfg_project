/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG.ConcreteCanonicalLearnerWorkingGrammarObservationProduct

/-!
# ConcreteCanonicalLearnerWorkingGrammarObservationSelection.lean

The preceding file constructs a binary product observation and separates its
factor targets from genuinely joint synergy targets.

This file turns a finite family of candidate observations into a monotone
selection system.

## Selected finite product

Let

```lean
obsFamily : ι → α → M
```

be a family of observations into one fixed finite monoid.  For a finite
selection

```lean
S : Finset ι
```

define

```lean
selectedObservationProduct obsFamily S : α → (↥S → M)
```

by collecting exactly the coordinates indexed by `S`.

Every selected coordinate refines to the selected product by evaluation at that
coordinate.  If `S ⊆ T`, the `T`-product refines the `S`-product by coordinate
restriction.

Consequently

```text
S ⊆ T
⇒ Target(S) ⊆ Target(T)
⇒ Failure(T) ⊆ Failure(S).
```

The target class added by extending `S` to `T` is exactly the existing strict
observation-gain class for this restriction refinement.  The extension is
redundant exactly when the two selected-product target classes are equal.

## Family synergy

The factor-union class at `S` consists of languages represented by at least one
selected coordinate.  The selected-product synergy class consists of languages
represented by the whole selected product but by no individual selected
coordinate.

We prove the exact decomposition

```text
Target(Product S)
  =
FactorUnion(S) ∪ Synergy(S),
```

with disjoint union.

Thus

```text
Synergy(S) = ∅
```

exactly when the selected product contributes no language beyond the union of
its individual coordinates.

## Minimum observation-selection cardinality

Fix a finite ambient candidate set

```lean
U : Finset ι.
```

A target language is selectable at cardinality budget `k` when some
`S ⊆ U` with `S.card ≤ k` represents the language under its selected product.

The least such budget is

```lean
correctedConcreteObservationSelectionCardinality.
```

It is defined by `Nat.find`, is attained by an actual finite selection, and has
the exact threshold property

```text
selection possible at budget k
  ↔
minimum selection cardinality ≤ k.
```

For every language represented by the full ambient product, the minimum is at
most `U.card`.

## Certified learner for a minimum selection

When the terminal alphabet and monoid are finite and decidable, an attained
minimum selection `S` supplies its own certified learner.  That learner

* identifies the target language;
* gives the target a minimum certified-description rank relative to the
  selected product; and
* returns one exact checked output satisfying the bit and finite-search budgets
  at that description rank.

This is a semantic minimum-cardinality observation-selection theorem.  It does
not yet give an algorithm for computing the minimum selection from an unknown
language, nor a complexity classification of the finite optimization problem.

No target grammar is supplied to any learner.
No `sorry`, `admit`, or `axiom` is used.
-/

namespace MCFG

universe u v w z


section SelectedObservationProductDefinition

variable {α : Type u}
variable {ι : Type v}
variable {M : Type w}
variable [Monoid M]

/-- Product of exactly the observation coordinates selected by `S`. -/
def selectedObservationProduct
    (obsFamily : ι → α → M)
    (S : Finset ι) :
    α → (↥S → M) :=
  fun terminal selectedIndex =>
    obsFamily selectedIndex.1 terminal

@[simp] theorem selectedObservationProduct_apply
    (obsFamily : ι → α → M)
    (S : Finset ι)
    (terminal : α)
    (selectedIndex : ↥S) :
    selectedObservationProduct obsFamily S terminal selectedIndex =
      obsFamily selectedIndex.1 terminal := by

  rfl

namespace Refines

/-- One selected factor refines to the complete selected product. -/
def factorToSelectedObservationProduct
    (obsFamily : ι → α → M)
    (S : Finset ι)
    {index : ι}
    (hindex : index ∈ S) :
    Refines
      (obsFamily index)
      (selectedObservationProduct obsFamily S) where

  map :=
    fun value =>
      value ⟨index, hindex⟩

  map_one := by
    rfl

  map_mul := by
    intro left right
    rfl

  comm := by
    intro terminal
    rfl

/-- Inclusion of selected coordinate sets induces observation refinement from
the smaller selected product to the larger selected product. -/
def selectedObservationProductOfSubset
    (obsFamily : ι → α → M)
    {S T : Finset ι}
    (hST : S ⊆ T) :
    Refines
      (selectedObservationProduct obsFamily S)
      (selectedObservationProduct obsFamily T) where

  map :=
    fun value selectedIndex =>
      value
        ⟨selectedIndex.1,
          hST selectedIndex.2⟩

  map_one := by
    rfl

  map_mul := by
    intro left right
    rfl

  comm := by
    intro terminal
    funext selectedIndex
    rfl

end Refines

end SelectedObservationProductDefinition


section SelectedObservationMonotonicity

variable {α : Type u}
variable {ι : Type v}
variable {M : Type w}
variable [Monoid M]
variable (obsFamily : ι → α → M)
variable (f : Nat)

/-- Enlarging a selected observation set enlarges the semantic target class. -/
theorem selectedObservationProductTargetClass_mono
    {S T : Finset ι}
    (hST : S ⊆ T) :
    StartRootedCorrectedConcreteTargetClass
        (v := z)
        α
        (↥S → M)
        (selectedObservationProduct obsFamily S)
        f ⊆
      StartRootedCorrectedConcreteTargetClass
        (v := z)
        α
        (↥T → M)
        (selectedObservationProduct obsFamily T)
        f := by

  exact
    startRootedCorrectedConcreteTargetClass_subset_of_refines
      (z := z)
      (Refines.selectedObservationProductOfSubset
        obsFamily hST)

/-- Enlarging a selected observation set shrinks the observation-failure
class. -/
theorem selectedObservationProductFailureClass_antitone
    {S T : Finset ι}
    (hST : S ⊆ T) :
    StartRootedCorrectedConcreteObservationFailureClass
        (z := z)
        α
        (↥T → M)
        (selectedObservationProduct obsFamily T)
        f ⊆
      StartRootedCorrectedConcreteObservationFailureClass
        (z := z)
        α
        (↥S → M)
        (selectedObservationProduct obsFamily S)
        f := by

  exact
    observationFailureClass_subset_of_refines
      (z := z)
      (Refines.selectedObservationProductOfSubset
        obsFamily hST)

/-- Every individually selected factor target belongs to the selected-product
target class. -/
theorem selectedObservationFactorTarget_subset_productTarget
    (S : Finset ι)
    {index : ι}
    (hindex : index ∈ S) :
    StartRootedCorrectedConcreteTargetClass
        (v := z)
        α M
        (obsFamily index)
        f ⊆
      StartRootedCorrectedConcreteTargetClass
        (v := z)
        α
        (↥S → M)
        (selectedObservationProduct obsFamily S)
        f := by

  exact
    startRootedCorrectedConcreteTargetClass_subset_of_refines
      (z := z)
      (Refines.factorToSelectedObservationProduct
        obsFamily S hindex)

end SelectedObservationMonotonicity


section SelectedObservationExtensionGain

variable {α : Type u}
variable {ι : Type v}
variable {M : Type w}
variable [Monoid M]
variable (obsFamily : ι → α → M)
variable (f : Nat)

/-- Languages added by enlarging the selected coordinate set from `S` to `T`. -/
def StartRootedCorrectedConcreteSelectedObservationExtensionGainClass
    (S T : Finset ι) :
    Set (Set (Word α)) :=
  StartRootedCorrectedConcreteObservationGainClass
    (z := z)
    α
    (↥S → M)
    (↥T → M)
    (selectedObservationProduct obsFamily S)
    (selectedObservationProduct obsFamily T)
    f

/-- Under `S ⊆ T`, the `T` target class is exactly the `S` target class
together with the strict extension-gain class. -/
theorem
    selectedObservationProductTargetClass_eq_smaller_union_extensionGain
    {S T : Finset ι}
    (hST : S ⊆ T) :
    StartRootedCorrectedConcreteTargetClass
        (v := z)
        α
        (↥T → M)
        (selectedObservationProduct obsFamily T)
        f =
      StartRootedCorrectedConcreteTargetClass
          (v := z)
          α
          (↥S → M)
          (selectedObservationProduct obsFamily S)
          f ∪
        StartRootedCorrectedConcreteSelectedObservationExtensionGainClass
          (z := z)
          obsFamily f S T := by

  exact
    finerTargetClass_eq_coarser_union_observationGainClass
      (z := z)
      (Refines.selectedObservationProductOfSubset
        obsFamily hST)

/-- The extension is redundant exactly when the two selected-product target
classes coincide. -/
theorem
    selectedObservationExtension_redundant_iff_targetClass_eq
    {S T : Finset ι}
    (hST : S ⊆ T) :
    CorrectedConcreteObservationRefinementRedundant
        (z := z)
        α
        (↥S → M)
        (↥T → M)
        (selectedObservationProduct obsFamily S)
        (selectedObservationProduct obsFamily T)
        f ↔
      StartRootedCorrectedConcreteTargetClass
          (v := z)
          α
          (↥S → M)
          (selectedObservationProduct obsFamily S)
          f =
        StartRootedCorrectedConcreteTargetClass
          (v := z)
          α
          (↥T → M)
          (selectedObservationProduct obsFamily T)
          f := by

  exact
    observationRefinementRedundant_iff_targetClass_eq
      (z := z)
      f
      (Refines.selectedObservationProductOfSubset
        obsFamily hST)

/-- The extension is essential exactly when its target class grows strictly. -/
theorem
    selectedObservationExtension_essential_iff_targetClass_ne
    {S T : Finset ι}
    (hST : S ⊆ T) :
    CorrectedConcreteObservationRefinementEssential
        (z := z)
        α
        (↥S → M)
        (↥T → M)
        (selectedObservationProduct obsFamily S)
        (selectedObservationProduct obsFamily T)
        f ↔
      StartRootedCorrectedConcreteTargetClass
          (v := z)
          α
          (↥S → M)
          (selectedObservationProduct obsFamily S)
          f ≠
        StartRootedCorrectedConcreteTargetClass
          (v := z)
          α
          (↥T → M)
          (selectedObservationProduct obsFamily T)
          f := by

  exact
    observationRefinementEssential_iff_targetClass_ne
      (z := z)
      f
      (Refines.selectedObservationProductOfSubset
        obsFamily hST)

end SelectedObservationExtensionGain


section SelectedObservationFactorUnionAndSynergy

variable (α : Type u)
variable (ι : Type v)
variable (M : Type w)
variable [Monoid M]
variable (obsFamily : ι → α → M)
variable (f : Nat)

/-- Languages represented by at least one individually selected observation. -/
def StartRootedCorrectedConcreteSelectedObservationFactorUnionClass
    (S : Finset ι) :
    Set (Set (Word α)) :=
  {language |
    ∃ selectedIndex : ↥S,
      language ∈
        StartRootedCorrectedConcreteTargetClass
          (v := z)
          α M
          (obsFamily selectedIndex.1)
          f}

/-- Languages represented by the complete selected product but by no
individual selected coordinate. -/
def StartRootedCorrectedConcreteSelectedObservationSynergyClass
    (S : Finset ι) :
    Set (Set (Word α)) :=
  {language |
    language ∈
        StartRootedCorrectedConcreteTargetClass
          (v := z)
          α
          (↥S → M)
          (selectedObservationProduct obsFamily S)
          f ∧
      ∀ selectedIndex : ↥S,
        language ∉
          StartRootedCorrectedConcreteTargetClass
            (v := z)
            α M
            (obsFamily selectedIndex.1)
            f}

variable {α ι M obsFamily f}

/-- The union of individually selected factor targets embeds into the selected
product target class. -/
theorem selectedObservationFactorUnion_subset_productTarget
    (S : Finset ι) :
    StartRootedCorrectedConcreteSelectedObservationFactorUnionClass
        (z := z)
        α ι M obsFamily f S ⊆
      StartRootedCorrectedConcreteTargetClass
        (v := z)
        α
        (↥S → M)
        (selectedObservationProduct obsFamily S)
        f := by

  intro language hLanguage

  rcases hLanguage with
    ⟨selectedIndex, hFactor⟩

  exact
    selectedObservationFactorTarget_subset_productTarget
      (z := z)
      obsFamily f
      S
      selectedIndex.2
      hFactor

/-- The selected-product synergy class is disjoint from the factor-union
class. -/
theorem selectedObservationSynergy_disjoint_factorUnion
    (S : Finset ι) :
    Set.Disjoint
      (StartRootedCorrectedConcreteSelectedObservationSynergyClass
        (z := z)
        α ι M obsFamily f S)
      (StartRootedCorrectedConcreteSelectedObservationFactorUnionClass
        (z := z)
        α ι M obsFamily f S) := by

  rw [Set.disjoint_left]

  intro language hSynergy hFactor

  rcases hFactor with
    ⟨selectedIndex, hSelected⟩

  exact
    hSynergy.2 selectedIndex hSelected

/-- Exact decomposition of the selected-product target class into individual
factor targets and genuinely joint synergy targets. -/
theorem
    selectedObservationProductTargetClass_eq_factorUnion_union_synergy
    (S : Finset ι) :
    StartRootedCorrectedConcreteTargetClass
        (v := z)
        α
        (↥S → M)
        (selectedObservationProduct obsFamily S)
        f =
      StartRootedCorrectedConcreteSelectedObservationFactorUnionClass
          (z := z)
          α ι M obsFamily f S ∪
        StartRootedCorrectedConcreteSelectedObservationSynergyClass
          (z := z)
          α ι M obsFamily f S := by

  classical

  ext language

  constructor

  · intro hProduct

    by_cases hFactor :
        ∃ selectedIndex : ↥S,
          language ∈
            StartRootedCorrectedConcreteTargetClass
              (v := z)
              α M
              (obsFamily selectedIndex.1)
              f

    · exact
        Or.inl hFactor

    · exact
        Or.inr
          ⟨hProduct,
            by
              intro selectedIndex hSelected
              exact
                hFactor
                  ⟨selectedIndex, hSelected⟩⟩

  · intro hDecomposition

    rcases hDecomposition with
      hFactor | hSynergy

    · exact
        selectedObservationFactorUnion_subset_productTarget
          (z := z)
          S hFactor

    · exact
        hSynergy.1

/-- The selected product contributes no genuinely joint target exactly when its
target class is already the factor-union class. -/
theorem
    selectedObservationSynergy_eq_empty_iff_productTarget_eq_factorUnion
    (S : Finset ι) :
    StartRootedCorrectedConcreteSelectedObservationSynergyClass
          (z := z)
          α ι M obsFamily f S =
        ∅ ↔
      StartRootedCorrectedConcreteTargetClass
          (v := z)
          α
          (↥S → M)
          (selectedObservationProduct obsFamily S)
          f =
        StartRootedCorrectedConcreteSelectedObservationFactorUnionClass
          (z := z)
          α ι M obsFamily f S := by

  constructor

  · intro hEmpty

    rw [
      selectedObservationProductTargetClass_eq_factorUnion_union_synergy
        (z := z)
        S,
      hEmpty,
      Set.union_empty
    ]

  · intro hClasses

    ext language

    constructor

    · intro hSynergy

      have hProduct :
          language ∈
            StartRootedCorrectedConcreteTargetClass
              (v := z)
              α
              (↥S → M)
              (selectedObservationProduct obsFamily S)
              f :=
        hSynergy.1

      rw [hClasses] at hProduct

      rcases hProduct with
        ⟨selectedIndex, hSelected⟩

      exact
        False.elim
          (hSynergy.2 selectedIndex hSelected)

    · intro hEmpty

      simp at hEmpty

end SelectedObservationFactorUnionAndSynergy


section GenericObservationSelectionCardinality

variable {α : Type u}
variable {ι : Type v}
variable {M : Type w}
variable [Monoid M]
variable {obsFamily : ι → α → M}
variable {f : Nat}

/-- A target language is realizable from an ambient candidate set `U` using at
most `cardinalityBudget` selected observation coordinates. -/
def CorrectedConcreteObservationSelectionAtCardinality
    (U : Finset ι)
    (language : Set (Word α))
    (cardinalityBudget : Nat) :
    Prop :=
  ∃ S : Finset ι,
    S ⊆ U ∧
      S.card <= cardinalityBudget ∧
      language ∈
        StartRootedCorrectedConcreteTargetClass
          (v := z)
          α
          (↥S → M)
          (selectedObservationProduct obsFamily S)
          f

/-- Existence of some finite observation selection from `U` representing the
language. -/
def HasCorrectedConcreteObservationSelection
    (U : Finset ι)
    (language : Set (Word α)) :
    Prop :=
  ∃ cardinalityBudget : Nat,
    CorrectedConcreteObservationSelectionAtCardinality
      (obsFamily := obsFamily)
      (f := f)
      U language cardinalityBudget

/-- Observation-selection feasibility is upward closed in the cardinality
budget. -/
theorem correctedConcreteObservationSelectionAtCardinality_mono
    {U : Finset ι}
    {language : Set (Word α)}
    {budget budget' : Nat}
    (hbudget : budget <= budget')
    (hselection :
      CorrectedConcreteObservationSelectionAtCardinality
        (obsFamily := obsFamily)
        (f := f)
        U language budget) :
    CorrectedConcreteObservationSelectionAtCardinality
      (obsFamily := obsFamily)
      (f := f)
      U language budget' := by

  rcases hselection with
    ⟨S, hSU, hcard, hTarget⟩

  exact
    ⟨S,
      hSU,
      hcard.trans hbudget,
      hTarget⟩

/-- Full-product target membership supplies some finite selection from the
ambient candidate set. -/
theorem hasCorrectedConcreteObservationSelection_of_fullProductTarget
    {U : Finset ι}
    {language : Set (Word α)}
    (hTarget :
      language ∈
        StartRootedCorrectedConcreteTargetClass
          (v := z)
          α
          (↥U → M)
          (selectedObservationProduct obsFamily U)
          f) :
    HasCorrectedConcreteObservationSelection
      (obsFamily := obsFamily)
      (f := f)
      U language := by

  exact
    ⟨U.card,
      U,
      by
        intro index hindex
        exact hindex,
      Nat.le_refl _,
      hTarget⟩

/-- Least number of selected observation coordinates needed to represent the
language from the ambient candidate set. -/
noncomputable def correctedConcreteObservationSelectionCardinality
    {U : Finset ι}
    {language : Set (Word α)}
    (hSelection :
      HasCorrectedConcreteObservationSelection
        (obsFamily := obsFamily)
        (f := f)
        U language) :
    Nat :=
  Nat.find hSelection

namespace HasCorrectedConcreteObservationSelection

variable {U : Finset ι}
variable {language : Set (Word α)}

/-- The minimum selection-cardinality budget is attained. -/
theorem cardinality_spec
    (hSelection :
      HasCorrectedConcreteObservationSelection
        (obsFamily := obsFamily)
        (f := f)
        U language) :
    CorrectedConcreteObservationSelectionAtCardinality
      (obsFamily := obsFamily)
      (f := f)
      U language
      (correctedConcreteObservationSelectionCardinality
        hSelection) := by

  exact
    Nat.find_spec hSelection

/-- Minimality of the observation-selection cardinality. -/
theorem cardinality_le_of_selection
    (hSelection :
      HasCorrectedConcreteObservationSelection
        (obsFamily := obsFamily)
        (f := f)
        U language)
    {budget : Nat}
    (hbudget :
      CorrectedConcreteObservationSelectionAtCardinality
        (obsFamily := obsFamily)
        (f := f)
        U language budget) :
    correctedConcreteObservationSelectionCardinality
        hSelection <=
      budget := by

  exact
    Nat.find_min' hSelection hbudget

/-- Exact threshold theorem for observation-selection cardinality. -/
theorem selectionAtCardinality_iff_minimum_le
    (hSelection :
      HasCorrectedConcreteObservationSelection
        (obsFamily := obsFamily)
        (f := f)
        U language)
    (budget : Nat) :
    CorrectedConcreteObservationSelectionAtCardinality
        (obsFamily := obsFamily)
        (f := f)
        U language budget ↔
      correctedConcreteObservationSelectionCardinality
          hSelection <=
        budget := by

  constructor

  · exact
      hSelection.cardinality_le_of_selection

  · intro hminimum

    exact
      correctedConcreteObservationSelectionAtCardinality_mono
        hminimum
        hSelection.cardinality_spec

/-- The minimum is attained by an actual selected subset whose cardinality is
exactly the minimum value. -/
theorem exists_selection_exact_cardinality
    (hSelection :
      HasCorrectedConcreteObservationSelection
        (obsFamily := obsFamily)
        (f := f)
        U language) :
    ∃ S : Finset ι,
      S ⊆ U ∧
        S.card =
          correctedConcreteObservationSelectionCardinality
            hSelection ∧
        language ∈
          StartRootedCorrectedConcreteTargetClass
            (v := z)
            α
            (↥S → M)
            (selectedObservationProduct obsFamily S)
            f := by

  rcases hSelection.cardinality_spec with
    ⟨S, hSU, hcard, hTarget⟩

  have hminimum :
      correctedConcreteObservationSelectionCardinality
          hSelection <=
        S.card := by

    apply hSelection.cardinality_le_of_selection

    exact
      ⟨S,
        hSU,
        Nat.le_refl _,
        hTarget⟩

  exact
    ⟨S,
      hSU,
      Nat.le_antisymm
        hcard
        hminimum,
      hTarget⟩

end HasCorrectedConcreteObservationSelection

end GenericObservationSelectionCardinality


section AmbientObservationSelection

variable {α : Type u}
variable {ι : Type v}
variable {M : Type w}
variable [Monoid M]
variable (obsFamily : ι → α → M)
variable (f : Nat)
variable (U : Finset ι)

/-- Minimum selection cardinality for a target represented by the full ambient
product. -/
noncomputable def ambientTargetObservationSelectionCardinality
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
  correctedConcreteObservationSelectionCardinality
    (hasCorrectedConcreteObservationSelection_of_fullProductTarget
      (obsFamily := obsFamily)
      (f := f)
      hTarget)

/-- The minimum number of selected coordinates is at most the ambient candidate
count. -/
theorem ambientTargetObservationSelectionCardinality_le
    {language : Set (Word α)}
    (hTarget :
      language ∈
        StartRootedCorrectedConcreteTargetClass
          (v := z)
          α
          (↥U → M)
          (selectedObservationProduct obsFamily U)
          f) :
    ambientTargetObservationSelectionCardinality
        (z := z)
        obsFamily f U hTarget <=
      U.card := by

  unfold
    ambientTargetObservationSelectionCardinality

  apply
    (hasCorrectedConcreteObservationSelection_of_fullProductTarget
      (obsFamily := obsFamily)
      (f := f)
      hTarget).cardinality_le_of_selection

  exact
    ⟨U,
      by
        intro index hindex
        exact hindex,
      Nat.le_refl _,
      hTarget⟩

/-- An ambient-product target has an actual minimum-cardinality selected subset. -/
theorem ambientTarget_exists_minimumObservationSelection
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
      S ⊆ U ∧
        S.card =
          ambientTargetObservationSelectionCardinality
            (z := z)
            obsFamily f U hTarget ∧
        language ∈
          StartRootedCorrectedConcreteTargetClass
            (v := z)
            α
            (↥S → M)
            (selectedObservationProduct obsFamily S)
            f := by

  exact
    (hasCorrectedConcreteObservationSelection_of_fullProductTarget
      (obsFamily := obsFamily)
      (f := f)
      hTarget).exists_selection_exact_cardinality

end AmbientObservationSelection


section MinimumSelectionCertifiedLearner

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
variable (U : Finset ι)

/-- Every selected-product certified learner identifies its own semantic target
class. -/
theorem selectedProductCertifiedLearner_identifies_targetClass
    (S : Finset ι) :
    IdentifiesClassFromPositiveData
      (correctedConcreteCertifiedWorkingGrammarHypLanguage
        (selectedObservationProduct obsFamily S)
        f)
      (correctedConcreteCertifiedWorkingGrammarLearner
        hα
        (selectedObservationProduct obsFamily S)
        f)
      (StartRootedCorrectedConcreteTargetClass
        (v := z)
        α
        (↥S → M)
        (selectedObservationProduct obsFamily S)
        f) := by

  exact
    correctedConcreteCertifiedWorkingGrammarLearner_identifies_startRootedTargetClass
      (v := z)
      hα
      (selectedObservationProduct obsFamily S)
      f

/-- If `S ⊆ T`, the `T`-product certified learner identifies every target
already represented by the `S` product. -/
theorem largerSelectionCertifiedLearner_identifies_smallerTargetClass
    {S T : Finset ι}
    (hST : S ⊆ T) :
    IdentifiesClassFromPositiveData
      (correctedConcreteCertifiedWorkingGrammarHypLanguage
        (selectedObservationProduct obsFamily T)
        f)
      (correctedConcreteCertifiedWorkingGrammarLearner
        hα
        (selectedObservationProduct obsFamily T)
        f)
      (StartRootedCorrectedConcreteTargetClass
        (v := z)
        α
        (↥S → M)
        (selectedObservationProduct obsFamily S)
        f) := by

  exact
    refinedCertifiedLearner_identifies_coarserTargetClass
      (z := z)
      hα
      (selectedObservationProduct obsFamily S)
      (selectedObservationProduct obsFamily T)
      f
      (Refines.selectedObservationProductOfSubset
        obsFamily hST)

/-- If `S ⊆ T`, the `T`-product certified learner identifies the strict
extension-gain class. -/
theorem largerSelectionCertifiedLearner_identifies_extensionGainClass
    {S T : Finset ι}
    (hST : S ⊆ T) :
    IdentifiesClassFromPositiveData
      (correctedConcreteCertifiedWorkingGrammarHypLanguage
        (selectedObservationProduct obsFamily T)
        f)
      (correctedConcreteCertifiedWorkingGrammarLearner
        hα
        (selectedObservationProduct obsFamily T)
        f)
      (StartRootedCorrectedConcreteSelectedObservationExtensionGainClass
        (z := z)
        obsFamily f S T) := by

  exact
    refinedCertifiedLearner_identifies_observationGainClass
      (z := z)
      hα
      (selectedObservationProduct obsFamily S)
      (selectedObservationProduct obsFamily T)
      f
      (Refines.selectedObservationProductOfSubset
        obsFamily hST)

/-- An ambient-product target admits a minimum-cardinality selected product,
and that selected product has its own certified learner and minimum-rank checked
description. -/
theorem ambientTarget_exists_minimumCertifiedObservationSelection
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
      (hSU : S ⊆ U)
      (hSelected :
        language ∈
          StartRootedCorrectedConcreteTargetClass
            (v := z)
            α
            (↥S → M)
            (selectedObservationProduct obsFamily S)
            f),
      S.card =
          ambientTargetObservationSelectionCardinality
            (z := z)
            obsFamily f U hTarget ∧
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
              hSelected) ∧
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
      ambientTarget_exists_minimumObservationSelection
        (z := z)
        obsFamily f U hTarget with
    ⟨S, hSU, hcard, hSelected⟩

  exact
    ⟨S,
      hSU,
      hSelected,
      hcard,
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

end MinimumSelectionCertifiedLearner


section ObservationSelectionFinalPackage

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
variable (U : Finset ι)

/-- Final monotonicity, synergy, minimum-cardinality selection, and certified
learning package for a finite family of candidate observations. -/
theorem
    correctedConcreteCertifiedWorkingGrammar_observationSelection_package :
    (∀ S T : Finset ι,
      S ⊆ T →
      StartRootedCorrectedConcreteTargetClass
          (v := z)
          α
          (↥S → M)
          (selectedObservationProduct obsFamily S)
          f ⊆
        StartRootedCorrectedConcreteTargetClass
          (v := z)
          α
          (↥T → M)
          (selectedObservationProduct obsFamily T)
          f) ∧
      (∀ S T : Finset ι,
        S ⊆ T →
        StartRootedCorrectedConcreteObservationFailureClass
            (z := z)
            α
            (↥T → M)
            (selectedObservationProduct obsFamily T)
            f ⊆
          StartRootedCorrectedConcreteObservationFailureClass
            (z := z)
            α
            (↥S → M)
            (selectedObservationProduct obsFamily S)
            f) ∧
      (∀ S : Finset ι,
        StartRootedCorrectedConcreteTargetClass
            (v := z)
            α
            (↥S → M)
            (selectedObservationProduct obsFamily S)
            f =
          StartRootedCorrectedConcreteSelectedObservationFactorUnionClass
              (z := z)
              α ι M obsFamily f S ∪
            StartRootedCorrectedConcreteSelectedObservationSynergyClass
              (z := z)
              α ι M obsFamily f S) ∧
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
        ambientTargetObservationSelectionCardinality
            (z := z)
            obsFamily f U hTarget <=
          U.card) ∧
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
          (hSU : S ⊆ U)
          (hSelected :
            language ∈
              StartRootedCorrectedConcreteTargetClass
                (v := z)
                α
                (↥S → M)
                (selectedObservationProduct obsFamily S)
                f),
          S.card =
              ambientTargetObservationSelectionCardinality
                (z := z)
                obsFamily f U hTarget ∧
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

  exact
    ⟨fun S T hST =>
        selectedObservationProductTargetClass_mono
          (z := z)
          obsFamily f hST,
      fun S T hST =>
        selectedObservationProductFailureClass_antitone
          (z := z)
          obsFamily f hST,
      fun S =>
        selectedObservationProductTargetClass_eq_factorUnion_union_synergy
          (z := z)
          S,
      fun language hTarget =>
        ambientTargetObservationSelectionCardinality_le
          (z := z)
          obsFamily f U hTarget,
      fun language hTarget => by
        rcases
            ambientTarget_exists_minimumCertifiedObservationSelection
              (z := z)
              hα obsFamily f U hTarget with
          ⟨S,
            hSU,
            hSelected,
            hcard,
            hIdentifies,
            hProfile,
            C,
            hLanguage,
            hBits,
            hSearch⟩

        exact
          ⟨S,
            hSU,
            hSelected,
            hcard,
            hIdentifies,
            C,
            hLanguage,
            hBits,
            hSearch⟩⟩

end ObservationSelectionFinalPackage

end MCFG
