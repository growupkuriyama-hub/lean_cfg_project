/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG2.ConcreteCanonicalLearnerWorkingGrammarObservationAblation

/-!
# ConcreteCanonicalLearnerWorkingGrammarObservationProduct.lean

The preceding files develop the order theory of fixed finite observations:

* refinement transports semantic target witnesses;
* target classes grow under refinement;
* failure classes shrink;
* strict gain classes record newly representable languages;
* mutual refinement gives semantic equivalence; and
* an interface is redundant exactly when its strict gain class is empty.

This file constructs the binary product of two observations and analyzes the
extra semantic power obtained by using both interfaces simultaneously.

## Paired observation

For

```lean
obs₀ : α → M₀
obs₁ : α → M₁
```

define

```lean
pairedObservation obs₀ obs₁ : α → M₀ × M₁
```

by letterwise pairing.

The paired observation refines both factors through the coordinate
projections.  Consequently each factor target class embeds into the paired
target class, and the paired failure class is contained in each factor failure
class.

The paired observation is semantically commutative and associative: swapping
coordinates or reassociating nested products gives mutually refining
observations and hence exactly the same semantic target and failure classes.

## Synergy class

The strict paired-observation synergy class consists of languages that

```text
are targets under the paired observation,
are not targets under obs₀,
and are not targets under obs₁.
```

This is the genuinely joint information gain.  It is exactly the intersection
of the two strict gain classes

```text
Gain(obs₀, pair(obs₀,obs₁))
∩
Gain(obs₁, pair(obs₀,obs₁)).
```

The paired target class decomposes exactly as

```text
Target(pair(obs₀,obs₁))
  =
(Target(obs₀) ∪ Target(obs₁))
  ∪ Synergy(obs₀,obs₁).
```

The synergy class is disjoint from the union of the two factor target classes.
Therefore

```text
Synergy = ∅
```

is equivalent to saying that the product creates no target beyond the union of
the two factor classes.

If the synergy class is inhabited, then both coordinate refinements are
essential.  The converse is not asserted: the two refinements may each add
languages already supplied by the other factor without producing a genuinely
joint target.

## Certified learner for the paired observation

When both factor monoids are finite and decidable, the certified learner built
from the paired observation identifies

* the complete paired target class;
* each factor target class;
* the union of the factor target classes;
* each coordinate strict gain class; and
* the synergy class.

Every synergy target has

* a minimum paired-observation certified-description rank;
* exact membership in the paired profile at that minimum rank;
* a paired characteristic-rank upper bound; and
* one exact certified output meeting both minimum-rank bit and search budgets,

while remaining outside both factor target classes.

## Boundary

This file constructs the product interface and the exact semantic decomposition,
but it does not prove that a particular pair has nonempty synergy.  A concrete
strict-synergy witness remains a substantive separation theorem.

No target grammar is supplied to any learner.
No `sorry`, `admit`, or `axiom` is used.
-/

namespace MCFG

universe u v w x z


section PairedObservationDefinition

variable {α : Type u}
variable {M₀ : Type v}
variable {M₁ : Type w}
variable [Monoid M₀]
variable [Monoid M₁]

/-- Letterwise product of two finite-monoid observations. -/
def pairedObservation
    (obs₀ : α → M₀)
    (obs₁ : α → M₁) :
    α → M₀ × M₁ :=
  fun terminal =>
    (obs₀ terminal, obs₁ terminal)

@[simp] theorem pairedObservation_fst
    (obs₀ : α → M₀)
    (obs₁ : α → M₁)
    (terminal : α) :
    (pairedObservation obs₀ obs₁ terminal).1 =
      obs₀ terminal := by

  rfl

@[simp] theorem pairedObservation_snd
    (obs₀ : α → M₀)
    (obs₁ : α → M₁)
    (terminal : α) :
    (pairedObservation obs₀ obs₁ terminal).2 =
      obs₁ terminal := by

  rfl

namespace Refines

/-- The paired observation refines its left coordinate observation. -/
def leftToPairedObservation
    (obs₀ : α → M₀)
    (obs₁ : α → M₁) :
    Refines
      obs₀
      (pairedObservation obs₀ obs₁) where

  map :=
    fun value =>
      value.1

  map_one := by
    rfl

  map_mul := by
    intro left right
    rfl

  comm := by
    intro terminal
    rfl

/-- The paired observation refines its right coordinate observation. -/
def rightToPairedObservation
    (obs₀ : α → M₀)
    (obs₁ : α → M₁) :
    Refines
      obs₁
      (pairedObservation obs₀ obs₁) where

  map :=
    fun value =>
      value.2

  map_one := by
    rfl

  map_mul := by
    intro left right
    rfl

  comm := by
    intro terminal
    rfl

end Refines

/-- Swapping the two coordinates gives an observation equivalent product. -/
def pairedObservation_swapEquivalent
    (obs₀ : α → M₀)
    (obs₁ : α → M₁) :
    ObservationEquivalent
      (pairedObservation obs₀ obs₁)
      (pairedObservation obs₁ obs₀) where

  toRefines :=
    { map :=
        fun value =>
          (value.2, value.1)

      map_one := by
        rfl

      map_mul := by
        intro left right
        rfl

      comm := by
        intro terminal
        rfl }

  fromRefines :=
    { map :=
        fun value =>
          (value.2, value.1)

      map_one := by
        rfl

      map_mul := by
        intro left right
        rfl

      comm := by
        intro terminal
        rfl }

end PairedObservationDefinition


section PairedObservationAssociativity

variable {α : Type u}
variable {M₀ : Type v}
variable {M₁ : Type w}
variable {M₂ : Type x}
variable [Monoid M₀]
variable [Monoid M₁]
variable [Monoid M₂]

/-- Reassociation of a three-coordinate product gives mutually refining
observations. -/
def pairedObservation_associativeEquivalent
    (obs₀ : α → M₀)
    (obs₁ : α → M₁)
    (obs₂ : α → M₂) :
    ObservationEquivalent
      (pairedObservation
        (pairedObservation obs₀ obs₁)
        obs₂)
      (pairedObservation
        obs₀
        (pairedObservation obs₁ obs₂)) where

  toRefines :=
    { map :=
        fun value =>
          ((value.1, value.2.1), value.2.2)

      map_one := by
        rfl

      map_mul := by
        intro left right
        rfl

      comm := by
        intro terminal
        rfl }

  fromRefines :=
    { map :=
        fun value =>
          (value.1.1, (value.1.2, value.2))

      map_one := by
        rfl

      map_mul := by
        intro left right
        rfl

      comm := by
        intro terminal
        rfl }

end PairedObservationAssociativity


section PairedObservationTargetAndFailureClasses

variable {α : Type u}
variable {M₀ : Type v}
variable {M₁ : Type w}
variable [Monoid M₀]
variable [Monoid M₁]
variable (obs₀ : α → M₀)
variable (obs₁ : α → M₁)
variable (f : Nat)

/-- Every left-factor target remains a target under the paired observation. -/
theorem leftTargetClass_subset_pairedTargetClass :
    StartRootedCorrectedConcreteTargetClass
        (v := z) α M₀ obs₀ f ⊆
      StartRootedCorrectedConcreteTargetClass
        (v := z)
        α
        (M₀ × M₁)
        (pairedObservation obs₀ obs₁)
        f := by

  exact
    startRootedCorrectedConcreteTargetClass_subset_of_refines
      (z := z)
      (Refines.leftToPairedObservation
        obs₀ obs₁)

/-- Every right-factor target remains a target under the paired observation. -/
theorem rightTargetClass_subset_pairedTargetClass :
    StartRootedCorrectedConcreteTargetClass
        (v := z) α M₁ obs₁ f ⊆
      StartRootedCorrectedConcreteTargetClass
        (v := z)
        α
        (M₀ × M₁)
        (pairedObservation obs₀ obs₁)
        f := by

  exact
    startRootedCorrectedConcreteTargetClass_subset_of_refines
      (z := z)
      (Refines.rightToPairedObservation
        obs₀ obs₁)

/-- The union of both factor target classes embeds into the paired target
class. -/
theorem factorTargetClassUnion_subset_pairedTargetClass :
    StartRootedCorrectedConcreteTargetClass
          (v := z) α M₀ obs₀ f ∪
        StartRootedCorrectedConcreteTargetClass
          (v := z) α M₁ obs₁ f ⊆
      StartRootedCorrectedConcreteTargetClass
        (v := z)
        α
        (M₀ × M₁)
        (pairedObservation obs₀ obs₁)
        f := by

  intro language hLanguage

  rcases hLanguage with
    hLeft | hRight

  · exact
      leftTargetClass_subset_pairedTargetClass
        (z := z)
        obs₀ obs₁ f hLeft

  · exact
      rightTargetClass_subset_pairedTargetClass
        (z := z)
        obs₀ obs₁ f hRight

/-- Failure under the paired observation implies failure under the left
factor. -/
theorem pairedFailureClass_subset_leftFailureClass :
    StartRootedCorrectedConcreteObservationFailureClass
        (z := z)
        α
        (M₀ × M₁)
        (pairedObservation obs₀ obs₁)
        f ⊆
      StartRootedCorrectedConcreteObservationFailureClass
        (z := z) α M₀ obs₀ f := by

  exact
    observationFailureClass_subset_of_refines
      (z := z)
      (Refines.leftToPairedObservation
        obs₀ obs₁)

/-- Failure under the paired observation implies failure under the right
factor. -/
theorem pairedFailureClass_subset_rightFailureClass :
    StartRootedCorrectedConcreteObservationFailureClass
        (z := z)
        α
        (M₀ × M₁)
        (pairedObservation obs₀ obs₁)
        f ⊆
      StartRootedCorrectedConcreteObservationFailureClass
        (z := z) α M₁ obs₁ f := by

  exact
    observationFailureClass_subset_of_refines
      (z := z)
      (Refines.rightToPairedObservation
        obs₀ obs₁)

/-- Paired-observation failure implies simultaneous failure of both factors. -/
theorem pairedFailureClass_subset_factorFailureIntersection :
    StartRootedCorrectedConcreteObservationFailureClass
        (z := z)
        α
        (M₀ × M₁)
        (pairedObservation obs₀ obs₁)
        f ⊆
      {language : Set (Word α) |
        language ∈
            StartRootedCorrectedConcreteObservationFailureClass
              (z := z) α M₀ obs₀ f ∧
          language ∈
            StartRootedCorrectedConcreteObservationFailureClass
              (z := z) α M₁ obs₁ f} := by

  intro language hFailure

  exact
    ⟨pairedFailureClass_subset_leftFailureClass
        (z := z)
        obs₀ obs₁ f hFailure,
      pairedFailureClass_subset_rightFailureClass
        (z := z)
        obs₀ obs₁ f hFailure⟩

end PairedObservationTargetAndFailureClasses


section PairedObservationSemanticCommutativity

variable {α : Type u}
variable {M₀ : Type v}
variable {M₁ : Type w}
variable [Monoid M₀]
variable [Monoid M₁]
variable (obs₀ : α → M₀)
variable (obs₁ : α → M₁)
variable (f : Nat)

/-- Product target classes are invariant under swapping coordinates. -/
theorem pairedObservation_targetClass_swap_eq :
    StartRootedCorrectedConcreteTargetClass
        (v := z)
        α
        (M₀ × M₁)
        (pairedObservation obs₀ obs₁)
        f =
      StartRootedCorrectedConcreteTargetClass
        (v := z)
        α
        (M₁ × M₀)
        (pairedObservation obs₁ obs₀)
        f := by

  exact
    observationEquivalent_targetClass_eq
      (z := z)
      f
      (pairedObservation_swapEquivalent
        obs₀ obs₁)

/-- Product failure classes are invariant under swapping coordinates. -/
theorem pairedObservation_failureClass_swap_eq :
    StartRootedCorrectedConcreteObservationFailureClass
        (z := z)
        α
        (M₀ × M₁)
        (pairedObservation obs₀ obs₁)
        f =
      StartRootedCorrectedConcreteObservationFailureClass
        (z := z)
        α
        (M₁ × M₀)
        (pairedObservation obs₁ obs₀)
        f := by

  exact
    observationEquivalent_failureClass_eq
      (z := z)
      f
      (pairedObservation_swapEquivalent
        obs₀ obs₁)

end PairedObservationSemanticCommutativity


section PairedObservationSemanticAssociativity

variable {α : Type u}
variable {M₀ : Type v}
variable {M₁ : Type w}
variable {M₂ : Type x}
variable [Monoid M₀]
variable [Monoid M₁]
variable [Monoid M₂]
variable (obs₀ : α → M₀)
variable (obs₁ : α → M₁)
variable (obs₂ : α → M₂)
variable (f : Nat)

/-- Nested product target classes are invariant under reassociation. -/
theorem pairedObservation_targetClass_associative_eq :
    StartRootedCorrectedConcreteTargetClass
        (v := z)
        α
        ((M₀ × M₁) × M₂)
        (pairedObservation
          (pairedObservation obs₀ obs₁)
          obs₂)
        f =
      StartRootedCorrectedConcreteTargetClass
        (v := z)
        α
        (M₀ × (M₁ × M₂))
        (pairedObservation
          obs₀
          (pairedObservation obs₁ obs₂))
        f := by

  exact
    observationEquivalent_targetClass_eq
      (z := z)
      f
      (pairedObservation_associativeEquivalent
        obs₀ obs₁ obs₂)

/-- Nested product failure classes are invariant under reassociation. -/
theorem pairedObservation_failureClass_associative_eq :
    StartRootedCorrectedConcreteObservationFailureClass
        (z := z)
        α
        ((M₀ × M₁) × M₂)
        (pairedObservation
          (pairedObservation obs₀ obs₁)
          obs₂)
        f =
      StartRootedCorrectedConcreteObservationFailureClass
        (z := z)
        α
        (M₀ × (M₁ × M₂))
        (pairedObservation
          obs₀
          (pairedObservation obs₁ obs₂))
        f := by

  exact
    observationEquivalent_failureClass_eq
      (z := z)
      f
      (pairedObservation_associativeEquivalent
        obs₀ obs₁ obs₂)

end PairedObservationSemanticAssociativity


section PairedObservationSynergyClass

variable (α : Type u)
variable (M₀ : Type v)
variable (M₁ : Type w)
variable [Monoid M₀]
variable [Monoid M₁]
variable (obs₀ : α → M₀)
variable (obs₁ : α → M₁)
variable (f : Nat)

/-- Languages representable only by using the two observation coordinates
jointly, not by either factor alone. -/
def StartRootedCorrectedConcretePairedObservationSynergyClass :
    Set (Set (Word α)) :=
  {language |
    language ∈
        StartRootedCorrectedConcreteTargetClass
          (v := z)
          α
          (M₀ × M₁)
          (pairedObservation obs₀ obs₁)
          f ∧
      language ∉
          StartRootedCorrectedConcreteTargetClass
            (v := z) α M₀ obs₀ f ∧
      language ∉
          StartRootedCorrectedConcreteTargetClass
            (v := z) α M₁ obs₁ f}

variable {α M₀ M₁ obs₀ obs₁ f}

/-- Every synergy language is a paired-observation target. -/
theorem pairedObservationSynergyClass_subset_pairedTargetClass :
    StartRootedCorrectedConcretePairedObservationSynergyClass
        (z := z) α M₀ M₁ obs₀ obs₁ f ⊆
      StartRootedCorrectedConcreteTargetClass
        (v := z)
        α
        (M₀ × M₁)
        (pairedObservation obs₀ obs₁)
        f := by

  intro language hLanguage

  exact hLanguage.1

/-- The synergy class is disjoint from the left factor target class. -/
theorem pairedObservationSynergyClass_disjoint_leftTargetClass :
    Set.Disjoint
      (StartRootedCorrectedConcretePairedObservationSynergyClass
        (z := z) α M₀ M₁ obs₀ obs₁ f)
      (StartRootedCorrectedConcreteTargetClass
        (v := z) α M₀ obs₀ f) := by

  rw [Set.disjoint_left]

  intro language hSynergy hLeft

  exact
    hSynergy.2.1 hLeft

/-- The synergy class is disjoint from the right factor target class. -/
theorem pairedObservationSynergyClass_disjoint_rightTargetClass :
    Set.Disjoint
      (StartRootedCorrectedConcretePairedObservationSynergyClass
        (z := z) α M₀ M₁ obs₀ obs₁ f)
      (StartRootedCorrectedConcreteTargetClass
        (v := z) α M₁ obs₁ f) := by

  rw [Set.disjoint_left]

  intro language hSynergy hRight

  exact
    hSynergy.2.2 hRight

/-- The synergy class is disjoint from the union of both factor target
classes. -/
theorem pairedObservationSynergyClass_disjoint_factorTargetUnion :
    Set.Disjoint
      (StartRootedCorrectedConcretePairedObservationSynergyClass
        (z := z) α M₀ M₁ obs₀ obs₁ f)
      (StartRootedCorrectedConcreteTargetClass
          (v := z) α M₀ obs₀ f ∪
        StartRootedCorrectedConcreteTargetClass
          (v := z) α M₁ obs₁ f) := by

  rw [Set.disjoint_left]

  intro language hSynergy hFactor

  rcases hFactor with
    hLeft | hRight

  · exact
      hSynergy.2.1 hLeft

  · exact
      hSynergy.2.2 hRight

/-- Synergy is exactly the intersection of the two coordinate strict-gain
classes. -/
theorem pairedObservationSynergyClass_eq_gainIntersection :
    StartRootedCorrectedConcretePairedObservationSynergyClass
        (z := z) α M₀ M₁ obs₀ obs₁ f =
      {language : Set (Word α) |
        language ∈
            StartRootedCorrectedConcreteObservationGainClass
              (z := z)
              α
              M₀
              (M₀ × M₁)
              obs₀
              (pairedObservation obs₀ obs₁)
              f ∧
          language ∈
            StartRootedCorrectedConcreteObservationGainClass
              (z := z)
              α
              M₁
              (M₀ × M₁)
              obs₁
              (pairedObservation obs₀ obs₁)
              f} := by

  ext language

  constructor

  · intro hSynergy

    exact
      ⟨⟨hSynergy.1,
          hSynergy.2.1⟩,
        ⟨hSynergy.1,
          hSynergy.2.2⟩⟩

  · intro hIntersection

    exact
      ⟨hIntersection.1.1,
        hIntersection.1.2,
        hIntersection.2.2⟩

/-- The paired target class is the union of factor targets and genuinely joint
synergy targets. -/
theorem pairedTargetClass_eq_factorUnion_union_synergy :
    StartRootedCorrectedConcreteTargetClass
        (v := z)
        α
        (M₀ × M₁)
        (pairedObservation obs₀ obs₁)
        f =
      (StartRootedCorrectedConcreteTargetClass
          (v := z) α M₀ obs₀ f ∪
        StartRootedCorrectedConcreteTargetClass
          (v := z) α M₁ obs₁ f) ∪
        StartRootedCorrectedConcretePairedObservationSynergyClass
          (z := z) α M₀ M₁ obs₀ obs₁ f := by

  ext language

  constructor

  · intro hPaired

    by_cases hLeft :
        language ∈
          StartRootedCorrectedConcreteTargetClass
            (v := z) α M₀ obs₀ f

    · exact
        Or.inl
          (Or.inl hLeft)

    · by_cases hRight :
          language ∈
            StartRootedCorrectedConcreteTargetClass
              (v := z) α M₁ obs₁ f

      · exact
          Or.inl
            (Or.inr hRight)

      · exact
          Or.inr
            ⟨hPaired,
              hLeft,
              hRight⟩

  · intro hDecomposition

    rcases hDecomposition with
      hFactor | hSynergy

    · exact
        factorTargetClassUnion_subset_pairedTargetClass
          (z := z)
          obs₀ obs₁ f hFactor

    · exact
        hSynergy.1

/-- The product adds no genuinely joint target exactly when its target class is
already the union of the two factor target classes. -/
theorem
    pairedObservationSynergyClass_eq_empty_iff_targetClass_eq_factorUnion :
    StartRootedCorrectedConcretePairedObservationSynergyClass
          (z := z) α M₀ M₁ obs₀ obs₁ f =
        ∅ ↔
      StartRootedCorrectedConcreteTargetClass
          (v := z)
          α
          (M₀ × M₁)
          (pairedObservation obs₀ obs₁)
          f =
        StartRootedCorrectedConcreteTargetClass
            (v := z) α M₀ obs₀ f ∪
          StartRootedCorrectedConcreteTargetClass
            (v := z) α M₁ obs₁ f := by

  constructor

  · intro hEmpty

    rw [
      pairedTargetClass_eq_factorUnion_union_synergy
        (z := z),
      hEmpty,
      Set.union_empty
    ]

  · intro hClasses

    ext language

    constructor

    · intro hSynergy

      have hPaired :
          language ∈
            StartRootedCorrectedConcreteTargetClass
              (v := z)
              α
              (M₀ × M₁)
              (pairedObservation obs₀ obs₁)
              f :=
        hSynergy.1

      rw [hClasses] at hPaired

      rcases hPaired with
        hLeft | hRight

      · exact
          False.elim
            (hSynergy.2.1 hLeft)

      · exact
          False.elim
            (hSynergy.2.2 hRight)

    · intro hEmpty

      simp at hEmpty

/-- Any synergy witness makes both coordinate refinements essential. -/
theorem pairedObservationSynergy_nonempty_implies_both_refinementsEssential
    (hSynergy :
      ∃ language : Set (Word α),
        language ∈
          StartRootedCorrectedConcretePairedObservationSynergyClass
            (z := z) α M₀ M₁ obs₀ obs₁ f) :
    CorrectedConcreteObservationRefinementEssential
        (z := z)
        α
        M₀
        (M₀ × M₁)
        obs₀
        (pairedObservation obs₀ obs₁)
        f ∧
      CorrectedConcreteObservationRefinementEssential
        (z := z)
        α
        M₁
        (M₀ × M₁)
        obs₁
        (pairedObservation obs₀ obs₁)
        f := by

  rcases hSynergy with
    ⟨language, hLanguage⟩

  exact
    ⟨⟨language,
        hLanguage.1,
        hLanguage.2.1⟩,
      ⟨language,
        hLanguage.1,
        hLanguage.2.2⟩⟩

/-- If both coordinate refinements are redundant, then the two factor target
classes and the product target class are all equal. -/
theorem pairedObservation_both_redundant_targetClasses_eq
    (hLeft :
      CorrectedConcreteObservationRefinementRedundant
        (z := z)
        α
        M₀
        (M₀ × M₁)
        obs₀
        (pairedObservation obs₀ obs₁)
        f)
    (hRight :
      CorrectedConcreteObservationRefinementRedundant
        (z := z)
        α
        M₁
        (M₀ × M₁)
        obs₁
        (pairedObservation obs₀ obs₁)
        f) :
    StartRootedCorrectedConcreteTargetClass
        (v := z) α M₀ obs₀ f =
      StartRootedCorrectedConcreteTargetClass
        (v := z) α M₁ obs₁ f ∧
      StartRootedCorrectedConcreteTargetClass
          (v := z) α M₀ obs₀ f =
        StartRootedCorrectedConcreteTargetClass
          (v := z)
          α
          (M₀ × M₁)
          (pairedObservation obs₀ obs₁)
          f := by

  have hLeftEq :
      StartRootedCorrectedConcreteTargetClass
          (v := z) α M₀ obs₀ f =
        StartRootedCorrectedConcreteTargetClass
          (v := z)
          α
          (M₀ × M₁)
          (pairedObservation obs₀ obs₁)
          f :=
    (observationRefinementRedundant_iff_targetClass_eq
      (z := z)
      f
      (Refines.leftToPairedObservation
        obs₀ obs₁)).mp
      hLeft

  have hRightEq :
      StartRootedCorrectedConcreteTargetClass
          (v := z) α M₁ obs₁ f =
        StartRootedCorrectedConcreteTargetClass
          (v := z)
          α
          (M₀ × M₁)
          (pairedObservation obs₀ obs₁)
          f :=
    (observationRefinementRedundant_iff_targetClass_eq
      (z := z)
      f
      (Refines.rightToPairedObservation
        obs₀ obs₁)).mp
      hRight

  exact
    ⟨hLeftEq.trans hRightEq.symm,
      hLeftEq⟩

/-- Compact semantic product decomposition package. -/
theorem pairedObservation_semanticDecomposition_package :
    (StartRootedCorrectedConcreteTargetClass
          (v := z) α M₀ obs₀ f ∪
        StartRootedCorrectedConcreteTargetClass
          (v := z) α M₁ obs₁ f ⊆
      StartRootedCorrectedConcreteTargetClass
        (v := z)
        α
        (M₀ × M₁)
        (pairedObservation obs₀ obs₁)
        f) ∧
      (StartRootedCorrectedConcreteTargetClass
          (v := z)
          α
          (M₀ × M₁)
          (pairedObservation obs₀ obs₁)
          f =
        (StartRootedCorrectedConcreteTargetClass
            (v := z) α M₀ obs₀ f ∪
          StartRootedCorrectedConcreteTargetClass
            (v := z) α M₁ obs₁ f) ∪
          StartRootedCorrectedConcretePairedObservationSynergyClass
            (z := z) α M₀ M₁ obs₀ obs₁ f) ∧
      Set.Disjoint
        (StartRootedCorrectedConcretePairedObservationSynergyClass
          (z := z) α M₀ M₁ obs₀ obs₁ f)
        (StartRootedCorrectedConcreteTargetClass
            (v := z) α M₀ obs₀ f ∪
          StartRootedCorrectedConcreteTargetClass
            (v := z) α M₁ obs₁ f) ∧
      (StartRootedCorrectedConcretePairedObservationSynergyClass
          (z := z) α M₀ M₁ obs₀ obs₁ f =
        {language : Set (Word α) |
          language ∈
              StartRootedCorrectedConcreteObservationGainClass
                (z := z)
                α
                M₀
                (M₀ × M₁)
                obs₀
                (pairedObservation obs₀ obs₁)
                f ∧
            language ∈
              StartRootedCorrectedConcreteObservationGainClass
                (z := z)
                α
                M₁
                (M₀ × M₁)
                obs₁
                (pairedObservation obs₀ obs₁)
                f}) := by

  exact
    ⟨factorTargetClassUnion_subset_pairedTargetClass
        (z := z)
        obs₀ obs₁ f,
      pairedTargetClass_eq_factorUnion_union_synergy
        (z := z),
      pairedObservationSynergyClass_disjoint_factorTargetUnion
        (z := z),
      pairedObservationSynergyClass_eq_gainIntersection
        (z := z)⟩

end PairedObservationSynergyClass


section PairedObservationCertifiedLearner

variable {α : Type u}
variable {M₀ : Type v}
variable {M₁ : Type w}
variable [Fintype M₀]
variable [Fintype M₁]
variable [DecidableEq α]
variable [DecidableEq M₀]
variable [DecidableEq M₁]
variable [Monoid M₀]
variable [Monoid M₁]
variable (hα : Nonempty α)
variable (obs₀ : α → M₀)
variable (obs₁ : α → M₁)
variable (f : Nat)

/-- The paired-observation certified learner identifies the complete paired
target class. -/
theorem pairedCertifiedLearner_identifies_pairedTargetClass :
    IdentifiesClassFromPositiveData
      (correctedConcreteCertifiedWorkingGrammarHypLanguage
        (pairedObservation obs₀ obs₁)
        f)
      (correctedConcreteCertifiedWorkingGrammarLearner
        hα
        (pairedObservation obs₀ obs₁)
        f)
      (StartRootedCorrectedConcreteTargetClass
        (v := z)
        α
        (M₀ × M₁)
        (pairedObservation obs₀ obs₁)
        f) := by

  exact
    correctedConcreteCertifiedWorkingGrammarLearner_identifies_startRootedTargetClass
      (v := z)
      hα
      (pairedObservation obs₀ obs₁)
      f

/-- The paired-observation certified learner identifies every left-factor
target. -/
theorem pairedCertifiedLearner_identifies_leftTargetClass :
    IdentifiesClassFromPositiveData
      (correctedConcreteCertifiedWorkingGrammarHypLanguage
        (pairedObservation obs₀ obs₁)
        f)
      (correctedConcreteCertifiedWorkingGrammarLearner
        hα
        (pairedObservation obs₀ obs₁)
        f)
      (StartRootedCorrectedConcreteTargetClass
        (v := z) α M₀ obs₀ f) := by

  exact
    refinedCertifiedLearner_identifies_coarserTargetClass
      (z := z)
      hα
      obs₀
      (pairedObservation obs₀ obs₁)
      f
      (Refines.leftToPairedObservation
        obs₀ obs₁)

/-- The paired-observation certified learner identifies every right-factor
target. -/
theorem pairedCertifiedLearner_identifies_rightTargetClass :
    IdentifiesClassFromPositiveData
      (correctedConcreteCertifiedWorkingGrammarHypLanguage
        (pairedObservation obs₀ obs₁)
        f)
      (correctedConcreteCertifiedWorkingGrammarLearner
        hα
        (pairedObservation obs₀ obs₁)
        f)
      (StartRootedCorrectedConcreteTargetClass
        (v := z) α M₁ obs₁ f) := by

  exact
    refinedCertifiedLearner_identifies_coarserTargetClass
      (z := z)
      hα
      obs₁
      (pairedObservation obs₀ obs₁)
      f
      (Refines.rightToPairedObservation
        obs₀ obs₁)

/-- The paired-observation certified learner identifies the union of both
factor target classes. -/
theorem pairedCertifiedLearner_identifies_factorTargetUnion :
    IdentifiesClassFromPositiveData
      (correctedConcreteCertifiedWorkingGrammarHypLanguage
        (pairedObservation obs₀ obs₁)
        f)
      (correctedConcreteCertifiedWorkingGrammarLearner
        hα
        (pairedObservation obs₀ obs₁)
        f)
      (StartRootedCorrectedConcreteTargetClass
          (v := z) α M₀ obs₀ f ∪
        StartRootedCorrectedConcreteTargetClass
          (v := z) α M₁ obs₁ f) := by

  intro language hLanguage

  rcases hLanguage with
    hLeft | hRight

  · exact
      pairedCertifiedLearner_identifies_leftTargetClass
        (z := z)
        hα obs₀ obs₁ f
        language hLeft

  · exact
      pairedCertifiedLearner_identifies_rightTargetClass
        (z := z)
        hα obs₀ obs₁ f
        language hRight

/-- The paired-observation certified learner identifies the strict gain class
over the left factor. -/
theorem pairedCertifiedLearner_identifies_leftGainClass :
    IdentifiesClassFromPositiveData
      (correctedConcreteCertifiedWorkingGrammarHypLanguage
        (pairedObservation obs₀ obs₁)
        f)
      (correctedConcreteCertifiedWorkingGrammarLearner
        hα
        (pairedObservation obs₀ obs₁)
        f)
      (StartRootedCorrectedConcreteObservationGainClass
        (z := z)
        α
        M₀
        (M₀ × M₁)
        obs₀
        (pairedObservation obs₀ obs₁)
        f) := by

  exact
    refinedCertifiedLearner_identifies_observationGainClass
      (z := z)
      hα
      obs₀
      (pairedObservation obs₀ obs₁)
      f
      (Refines.leftToPairedObservation
        obs₀ obs₁)

/-- The paired-observation certified learner identifies the strict gain class
over the right factor. -/
theorem pairedCertifiedLearner_identifies_rightGainClass :
    IdentifiesClassFromPositiveData
      (correctedConcreteCertifiedWorkingGrammarHypLanguage
        (pairedObservation obs₀ obs₁)
        f)
      (correctedConcreteCertifiedWorkingGrammarLearner
        hα
        (pairedObservation obs₀ obs₁)
        f)
      (StartRootedCorrectedConcreteObservationGainClass
        (z := z)
        α
        M₁
        (M₀ × M₁)
        obs₁
        (pairedObservation obs₀ obs₁)
        f) := by

  exact
    refinedCertifiedLearner_identifies_observationGainClass
      (z := z)
      hα
      obs₁
      (pairedObservation obs₀ obs₁)
      f
      (Refines.rightToPairedObservation
        obs₀ obs₁)

/-- The paired-observation certified learner identifies every genuinely joint
synergy target. -/
theorem pairedCertifiedLearner_identifies_synergyClass :
    IdentifiesClassFromPositiveData
      (correctedConcreteCertifiedWorkingGrammarHypLanguage
        (pairedObservation obs₀ obs₁)
        f)
      (correctedConcreteCertifiedWorkingGrammarLearner
        hα
        (pairedObservation obs₀ obs₁)
        f)
      (StartRootedCorrectedConcretePairedObservationSynergyClass
        (z := z) α M₀ M₁ obs₀ obs₁ f) := by

  intro language hSynergy

  exact
    pairedCertifiedLearner_identifies_pairedTargetClass
      (z := z)
      hα obs₀ obs₁ f
      language hSynergy.1

/-- Every synergy target has an exact minimum-rank certified description under
the paired observation while remaining outside both factor target classes. -/
theorem pairedObservationSynergy_target_descriptionRank_package
    {language : Set (Word α)}
    (hSynergy :
      language ∈
        StartRootedCorrectedConcretePairedObservationSynergyClass
          (z := z) α M₀ M₁ obs₀ obs₁ f) :
    language ∉
        StartRootedCorrectedConcreteTargetClass
          (v := z) α M₀ obs₀ f ∧
      language ∉
        StartRootedCorrectedConcreteTargetClass
          (v := z) α M₁ obs₁ f ∧
      IdentifiesLanguageFromPositiveData
        (correctedConcreteCertifiedWorkingGrammarHypLanguage
          (pairedObservation obs₀ obs₁)
          f)
        (correctedConcreteCertifiedWorkingGrammarLearner
          hα
          (pairedObservation obs₀ obs₁)
          f)
        language ∧
      language ∈
        CorrectedConcreteCertifiedRankProfileClass
          (α := α)
          (M := M₀ × M₁)
          (pairedObservation obs₀ obs₁)
          f
          (startRootedTargetCertifiedDescriptionRank
            (v := z)
            hα
            (pairedObservation obs₀ obs₁)
            f
            hSynergy.1) ∧
      startRootedTargetCertifiedDescriptionRank
          (v := z)
          hα
          (pairedObservation obs₀ obs₁)
          f
          hSynergy.1 <=
        startRootedTargetCharacteristicRank
          (v := z)
          hα
          (pairedObservation obs₀ obs₁)
          f
          hSynergy.1 ∧
      ∃
        C :
          CorrectedConcreteCertifiedWorkingGrammarHypothesis
            α
            (M₀ × M₁)
            (pairedObservation obs₀ obs₁)
            f,
        C.output.grammar.StringLanguage =
            language ∧
          C.bits.length <=
            correctedConcreteCertifiedRankBitBudget
              (startRootedTargetCertifiedDescriptionRank
                (v := z)
                hα
                (pairedObservation obs₀ obs₁)
                f
                hSynergy.1)
              f ∧
          C.canonicalSearch.length <=
            correctedConcreteCertifiedRankSearchBudget
              (startRootedTargetCertifiedDescriptionRank
                (v := z)
                hα
                (pairedObservation obs₀ obs₁)
                f
                hSynergy.1)
              f := by

  exact
    ⟨hSynergy.2.1,
      hSynergy.2.2,
      pairedCertifiedLearner_identifies_synergyClass
        (z := z)
        hα obs₀ obs₁ f
        language hSynergy,
      startRootedTarget_mem_minimumCertifiedDescriptionRankProfile
        (v := z)
        hα
        (pairedObservation obs₀ obs₁)
        f
        hSynergy.1,
      startRootedTargetCertifiedDescriptionRank_le_characteristicRank
        (v := z)
        hα
        (pairedObservation obs₀ obs₁)
        f
        hSynergy.1,
      startRootedTarget_exists_output_at_minimumCertifiedDescriptionRank
        (v := z)
        hα
        (pairedObservation obs₀ obs₁)
        f
        hSynergy.1⟩

/-- Every synergy language lies in some finite certified profile level for the
paired observation. -/
theorem
    pairedObservationSynergyClass_subset_exists_certifiedRankProfile :
    StartRootedCorrectedConcretePairedObservationSynergyClass
        (z := z) α M₀ M₁ obs₀ obs₁ f ⊆
      {language : Set (Word α) |
        ∃ rank : Nat,
          language ∈
            CorrectedConcreteCertifiedRankProfileClass
              (α := α)
              (M := M₀ × M₁)
              (pairedObservation obs₀ obs₁)
              f
              rank} := by

  intro language hSynergy

  exact
    ⟨startRootedTargetCertifiedDescriptionRank
        (v := z)
        hα
        (pairedObservation obs₀ obs₁)
        f
        hSynergy.1,
      startRootedTarget_mem_minimumCertifiedDescriptionRankProfile
        (v := z)
        hα
        (pairedObservation obs₀ obs₁)
        f
        hSynergy.1⟩

/-- Compact certified-learning package for the paired observation. -/
theorem pairedCertifiedLearner_identification_package :
    IdentifiesClassFromPositiveData
        (correctedConcreteCertifiedWorkingGrammarHypLanguage
          (pairedObservation obs₀ obs₁)
          f)
        (correctedConcreteCertifiedWorkingGrammarLearner
          hα
          (pairedObservation obs₀ obs₁)
          f)
        (StartRootedCorrectedConcreteTargetClass
          (v := z)
          α
          (M₀ × M₁)
          (pairedObservation obs₀ obs₁)
          f) ∧
      IdentifiesClassFromPositiveData
        (correctedConcreteCertifiedWorkingGrammarHypLanguage
          (pairedObservation obs₀ obs₁)
          f)
        (correctedConcreteCertifiedWorkingGrammarLearner
          hα
          (pairedObservation obs₀ obs₁)
          f)
        (StartRootedCorrectedConcreteTargetClass
          (v := z) α M₀ obs₀ f) ∧
      IdentifiesClassFromPositiveData
        (correctedConcreteCertifiedWorkingGrammarHypLanguage
          (pairedObservation obs₀ obs₁)
          f)
        (correctedConcreteCertifiedWorkingGrammarLearner
          hα
          (pairedObservation obs₀ obs₁)
          f)
        (StartRootedCorrectedConcreteTargetClass
          (v := z) α M₁ obs₁ f) ∧
      IdentifiesClassFromPositiveData
        (correctedConcreteCertifiedWorkingGrammarHypLanguage
          (pairedObservation obs₀ obs₁)
          f)
        (correctedConcreteCertifiedWorkingGrammarLearner
          hα
          (pairedObservation obs₀ obs₁)
          f)
        (StartRootedCorrectedConcretePairedObservationSynergyClass
          (z := z) α M₀ M₁ obs₀ obs₁ f) ∧
      (StartRootedCorrectedConcretePairedObservationSynergyClass
          (z := z) α M₀ M₁ obs₀ obs₁ f ⊆
        {language : Set (Word α) |
          ∃ rank : Nat,
            language ∈
              CorrectedConcreteCertifiedRankProfileClass
                (α := α)
                (M := M₀ × M₁)
                (pairedObservation obs₀ obs₁)
                f
                rank}) := by

  exact
    ⟨pairedCertifiedLearner_identifies_pairedTargetClass
        (z := z)
        hα obs₀ obs₁ f,
      pairedCertifiedLearner_identifies_leftTargetClass
        (z := z)
        hα obs₀ obs₁ f,
      pairedCertifiedLearner_identifies_rightTargetClass
        (z := z)
        hα obs₀ obs₁ f,
      pairedCertifiedLearner_identifies_synergyClass
        (z := z)
        hα obs₀ obs₁ f,
      pairedObservationSynergyClass_subset_exists_certifiedRankProfile
        (z := z)
        hα obs₀ obs₁ f⟩

end PairedObservationCertifiedLearner


section PairedObservationAblationConsequences

variable {α : Type u}
variable {M₀ : Type v}
variable {M₁ : Type w}
variable [Monoid M₀]
variable [Monoid M₁]
variable (obs₀ : α → M₀)
variable (obs₁ : α → M₁)
variable (f : Nat)

/-- Redundancy of the left coordinate refinement is exactly equality between
the left target class and the paired target class. -/
theorem leftToPaired_redundant_iff_targetClass_eq :
    CorrectedConcreteObservationRefinementRedundant
        (z := z)
        α
        M₀
        (M₀ × M₁)
        obs₀
        (pairedObservation obs₀ obs₁)
        f ↔
      StartRootedCorrectedConcreteTargetClass
          (v := z) α M₀ obs₀ f =
        StartRootedCorrectedConcreteTargetClass
          (v := z)
          α
          (M₀ × M₁)
          (pairedObservation obs₀ obs₁)
          f := by

  exact
    observationRefinementRedundant_iff_targetClass_eq
      (z := z)
      f
      (Refines.leftToPairedObservation
        obs₀ obs₁)

/-- Redundancy of the right coordinate refinement is exactly equality between
the right target class and the paired target class. -/
theorem rightToPaired_redundant_iff_targetClass_eq :
    CorrectedConcreteObservationRefinementRedundant
        (z := z)
        α
        M₁
        (M₀ × M₁)
        obs₁
        (pairedObservation obs₀ obs₁)
        f ↔
      StartRootedCorrectedConcreteTargetClass
          (v := z) α M₁ obs₁ f =
        StartRootedCorrectedConcreteTargetClass
          (v := z)
          α
          (M₀ × M₁)
          (pairedObservation obs₀ obs₁)
          f := by

  exact
    observationRefinementRedundant_iff_targetClass_eq
      (z := z)
      f
      (Refines.rightToPairedObservation
        obs₀ obs₁)

/-- A nonempty synergy class forces strict target-class growth over each
factor. -/
theorem pairedObservationSynergy_nonempty_implies_strict_growth_over_both
    (hSynergy :
      ∃ language : Set (Word α),
        language ∈
          StartRootedCorrectedConcretePairedObservationSynergyClass
            (z := z) α M₀ M₁ obs₀ obs₁ f) :
    (StartRootedCorrectedConcreteTargetClass
        (v := z) α M₀ obs₀ f ⊆
      StartRootedCorrectedConcreteTargetClass
        (v := z)
        α
        (M₀ × M₁)
        (pairedObservation obs₀ obs₁)
        f) ∧
      (StartRootedCorrectedConcreteTargetClass
        (v := z) α M₀ obs₀ f ≠
      StartRootedCorrectedConcreteTargetClass
        (v := z)
        α
        (M₀ × M₁)
        (pairedObservation obs₀ obs₁)
        f) ∧
      (StartRootedCorrectedConcreteTargetClass
        (v := z) α M₁ obs₁ f ⊆
      StartRootedCorrectedConcreteTargetClass
        (v := z)
        α
        (M₀ × M₁)
        (pairedObservation obs₀ obs₁)
        f) ∧
      (StartRootedCorrectedConcreteTargetClass
        (v := z) α M₁ obs₁ f ≠
      StartRootedCorrectedConcreteTargetClass
        (v := z)
        α
        (M₀ × M₁)
        (pairedObservation obs₀ obs₁)
        f) := by

  have hEssential :=
    pairedObservationSynergy_nonempty_implies_both_refinementsEssential
      (z := z)
      hSynergy

  rcases
      (observationRefinementEssential_iff_strict_targetClass_growth
        (z := z)
        f
        (Refines.leftToPairedObservation
          obs₀ obs₁)).mp
        hEssential.1 with
    ⟨hLeftSubset, hLeftNe⟩

  rcases
      (observationRefinementEssential_iff_strict_targetClass_growth
        (z := z)
        f
        (Refines.rightToPairedObservation
          obs₀ obs₁)).mp
        hEssential.2 with
    ⟨hRightSubset, hRightNe⟩

  exact
    ⟨hLeftSubset,
      hLeftNe,
      hRightSubset,
      hRightNe⟩

/-- Compact product-interface ablation package. -/
theorem pairedObservation_ablation_package :
    (CorrectedConcreteObservationRefinementRedundant
          (z := z)
          α
          M₀
          (M₀ × M₁)
          obs₀
          (pairedObservation obs₀ obs₁)
          f ↔
        StartRootedCorrectedConcreteTargetClass
            (v := z) α M₀ obs₀ f =
          StartRootedCorrectedConcreteTargetClass
            (v := z)
            α
            (M₀ × M₁)
            (pairedObservation obs₀ obs₁)
            f) ∧
      (CorrectedConcreteObservationRefinementRedundant
          (z := z)
          α
          M₁
          (M₀ × M₁)
          obs₁
          (pairedObservation obs₀ obs₁)
          f ↔
        StartRootedCorrectedConcreteTargetClass
            (v := z) α M₁ obs₁ f =
          StartRootedCorrectedConcreteTargetClass
            (v := z)
            α
            (M₀ × M₁)
            (pairedObservation obs₀ obs₁)
            f) ∧
      (StartRootedCorrectedConcretePairedObservationSynergyClass
            (z := z) α M₀ M₁ obs₀ obs₁ f =
          ∅ ↔
        StartRootedCorrectedConcreteTargetClass
            (v := z)
            α
            (M₀ × M₁)
            (pairedObservation obs₀ obs₁)
            f =
          StartRootedCorrectedConcreteTargetClass
              (v := z) α M₀ obs₀ f ∪
            StartRootedCorrectedConcreteTargetClass
              (v := z) α M₁ obs₁ f) ∧
      ((∃ language : Set (Word α),
          language ∈
            StartRootedCorrectedConcretePairedObservationSynergyClass
              (z := z) α M₀ M₁ obs₀ obs₁ f) →
        CorrectedConcreteObservationRefinementEssential
            (z := z)
            α
            M₀
            (M₀ × M₁)
            obs₀
            (pairedObservation obs₀ obs₁)
            f ∧
          CorrectedConcreteObservationRefinementEssential
            (z := z)
            α
            M₁
            (M₀ × M₁)
            obs₁
            (pairedObservation obs₀ obs₁)
            f) := by

  exact
    ⟨leftToPaired_redundant_iff_targetClass_eq
        (z := z)
        obs₀ obs₁ f,
      rightToPaired_redundant_iff_targetClass_eq
        (z := z)
        obs₀ obs₁ f,
      pairedObservationSynergyClass_eq_empty_iff_targetClass_eq_factorUnion
        (z := z),
      pairedObservationSynergy_nonempty_implies_both_refinementsEssential
        (z := z)⟩

end PairedObservationAblationConsequences


section ObservationProductFinalPackage

variable {α : Type u}
variable {M₀ : Type v}
variable {M₁ : Type w}
variable [Fintype M₀]
variable [Fintype M₁]
variable [DecidableEq α]
variable [DecidableEq M₀]
variable [DecidableEq M₁]
variable [Monoid M₀]
variable [Monoid M₁]
variable (hα : Nonempty α)
variable (obs₀ : α → M₀)
variable (obs₁ : α → M₁)
variable (f : Nat)

/-- Final semantic, ablation, and certified-learning theorem for a binary
observation product. -/
theorem
    correctedConcreteCertifiedWorkingGrammar_observationProduct_package :
    (StartRootedCorrectedConcreteTargetClass
          (v := z) α M₀ obs₀ f ∪
        StartRootedCorrectedConcreteTargetClass
          (v := z) α M₁ obs₁ f ⊆
      StartRootedCorrectedConcreteTargetClass
        (v := z)
        α
        (M₀ × M₁)
        (pairedObservation obs₀ obs₁)
        f) ∧
      (StartRootedCorrectedConcreteTargetClass
          (v := z)
          α
          (M₀ × M₁)
          (pairedObservation obs₀ obs₁)
          f =
        (StartRootedCorrectedConcreteTargetClass
            (v := z) α M₀ obs₀ f ∪
          StartRootedCorrectedConcreteTargetClass
            (v := z) α M₁ obs₁ f) ∪
          StartRootedCorrectedConcretePairedObservationSynergyClass
            (z := z) α M₀ M₁ obs₀ obs₁ f) ∧
      Set.Disjoint
        (StartRootedCorrectedConcretePairedObservationSynergyClass
          (z := z) α M₀ M₁ obs₀ obs₁ f)
        (StartRootedCorrectedConcreteTargetClass
            (v := z) α M₀ obs₀ f ∪
          StartRootedCorrectedConcreteTargetClass
            (v := z) α M₁ obs₁ f) ∧
      (StartRootedCorrectedConcreteObservationFailureClass
          (z := z)
          α
          (M₀ × M₁)
          (pairedObservation obs₀ obs₁)
          f ⊆
        {language : Set (Word α) |
          language ∈
              StartRootedCorrectedConcreteObservationFailureClass
                (z := z) α M₀ obs₀ f ∧
            language ∈
              StartRootedCorrectedConcreteObservationFailureClass
                (z := z) α M₁ obs₁ f}) ∧
      IdentifiesClassFromPositiveData
        (correctedConcreteCertifiedWorkingGrammarHypLanguage
          (pairedObservation obs₀ obs₁)
          f)
        (correctedConcreteCertifiedWorkingGrammarLearner
          hα
          (pairedObservation obs₀ obs₁)
          f)
        (StartRootedCorrectedConcreteTargetClass
          (v := z)
          α
          (M₀ × M₁)
          (pairedObservation obs₀ obs₁)
          f) ∧
      IdentifiesClassFromPositiveData
        (correctedConcreteCertifiedWorkingGrammarHypLanguage
          (pairedObservation obs₀ obs₁)
          f)
        (correctedConcreteCertifiedWorkingGrammarLearner
          hα
          (pairedObservation obs₀ obs₁)
          f)
        (StartRootedCorrectedConcretePairedObservationSynergyClass
          (z := z) α M₀ M₁ obs₀ obs₁ f) ∧
      (StartRootedCorrectedConcretePairedObservationSynergyClass
          (z := z) α M₀ M₁ obs₀ obs₁ f ⊆
        {language : Set (Word α) |
          ∃ rank : Nat,
            language ∈
              CorrectedConcreteCertifiedRankProfileClass
                (α := α)
                (M := M₀ × M₁)
                (pairedObservation obs₀ obs₁)
                f
                rank}) := by

  exact
    ⟨factorTargetClassUnion_subset_pairedTargetClass
        (z := z)
        obs₀ obs₁ f,
      pairedTargetClass_eq_factorUnion_union_synergy
        (z := z),
      pairedObservationSynergyClass_disjoint_factorTargetUnion
        (z := z),
      pairedFailureClass_subset_factorFailureIntersection
        (z := z)
        obs₀ obs₁ f,
      pairedCertifiedLearner_identifies_pairedTargetClass
        (z := z)
        hα obs₀ obs₁ f,
      pairedCertifiedLearner_identifies_synergyClass
        (z := z)
        hα obs₀ obs₁ f,
      pairedObservationSynergyClass_subset_exists_certifiedRankProfile
        (z := z)
        hα obs₀ obs₁ f⟩

end ObservationProductFinalPackage

end MCFG
