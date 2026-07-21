/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG.ConcreteCanonicalLearnerWorkingGrammarObservationRefinementFailure

/-!
# ConcreteCanonicalLearnerWorkingGrammarObservationEquivalenceChain.lean

The preceding file proves semantic target-class monotonicity under observation
refinement and defines strict observation-gain and observation-loss classes.

This file closes the algebra of observation comparison.

## Refinement identity and composition

For every observation map `obs` there is an identity refinement

```lean
Refines.identity obs.
```

If

```text
obs₁ refines obs₀
and
obs₂ refines obs₁,
```

their multiplication-preserving maps compose to a refinement of `obs₀` by
`obs₂`:

```lean
Refines.compose.
```

The induced target-class inclusions and failure-class reverse inclusions
therefore compose.

## Observation equivalence

Two observations are semantically equivalent for the present theory when each
refines the other:

```lean
ObservationEquivalent obs obs'.
```

Observation equivalence is reflexive, symmetric, and transitive.

Mutually refining observations have

```text
equal semantic target classes,
equal observation-failure classes,
empty gain class in either direction,
and empty loss class in either direction.
```

Their certified output types and numerical description ranks need not be
definitionally identical, because those types depend on the observation monoid.
Nevertheless, when both monoids are finite and decidable, each certified
learner identifies the common semantic target class.

## Three-stage refinement chains

Suppose

```text
obs₀ ← obs₁ ← obs₂
```

where each arrow is the multiplication-preserving map from the finer
observation to the coarser observation.

Write

```text
G₀₁ = targets(obs₁) \ targets(obs₀),
G₁₂ = targets(obs₂) \ targets(obs₁),
G₀₂ = targets(obs₂) \ targets(obs₀).
```

Then

```text
G₀₂ = G₀₁ ∪ G₁₂.
```

The two incremental gain classes are disjoint.  Equivalently,

```text
targets(obs₂)
  =
(targets(obs₀) ∪ G₀₁) ∪ G₁₂.
```

Thus refinement gains are path-independent at the semantic class level and
decompose into the disjoint gains introduced at each stage.

Failure behaves in the opposite direction:

```text
failure(obs₂) ⊆ failure(obs₁) ⊆ failure(obs₀).
```

No language is lost along either refinement step or along their composite.

## Certified learning along a chain

When all three observation monoids are finite and decidable, the certified
learner for the finest observation `obs₂` identifies

* the coarsest target class;
* the intermediate target class;
* the first incremental gain class;
* the second incremental gain class; and
* the direct gain class from `obs₀` to `obs₂`.

Every direct-gain language therefore has a finest-observation minimum certified
description rank and an exact finite checked output, while remaining outside
the coarsest semantic target class.

No strict-gain language is asserted to exist.  Existence requires a concrete
separation example for the chosen observations.

No target grammar is supplied to any learner.
No `sorry`, `admit`, or `axiom` is used.
-/

namespace MCFG

universe u v w x z


section RefinementIdentityAndComposition

variable {α : Type u}
variable {M₀ : Type v}
variable {M₁ : Type w}
variable {M₂ : Type x}
variable [Monoid M₀]
variable [Monoid M₁]
variable [Monoid M₂]
variable {obs₀ : α → M₀}
variable {obs₁ : α → M₁}
variable {obs₂ : α → M₂}

namespace Refines

/-- Every observation refines itself through the identity monoid morphism. -/
def identity
    (obs : α → M₀) :
    Refines obs obs where

  map :=
    fun value => value

  map_one :=
    rfl

  map_mul :=
    by
      intro left right
      rfl

  comm :=
    by
      intro terminal
      rfl

/-- Composition of observation refinements.

If `obs₁` refines `obs₀` and `obs₂` refines `obs₁`, then `obs₂` refines
`obs₀`. -/
def compose
    (r₀₁ : Refines obs₀ obs₁)
    (r₁₂ : Refines obs₁ obs₂) :
    Refines obs₀ obs₂ where

  map :=
    fun value =>
      r₀₁.map
        (r₁₂.map value)

  map_one := by
    rw [
      r₁₂.map_one,
      r₀₁.map_one
    ]

  map_mul := by
    intro left right

    rw [
      r₁₂.map_mul,
      r₀₁.map_mul
    ]

  comm := by
    intro terminal

    rw [
      r₁₂.comm terminal,
      r₀₁.comm terminal
    ]

/-- The composite refinement map is pointwise the composite of the two maps. -/
@[simp] theorem compose_map
    (r₀₁ : Refines obs₀ obs₁)
    (r₁₂ : Refines obs₁ obs₂)
    (value : M₂) :
    (r₀₁.compose r₁₂).map value =
      r₀₁.map (r₁₂.map value) := by

  rfl

/-- Refinement composition preserves word-observation commutation. -/
theorem evalObs_compose
    (r₀₁ : Refines obs₀ obs₁)
    (r₁₂ : Refines obs₁ obs₂)
    (word : Word α) :
    (r₀₁.compose r₁₂).map
        (evalObs obs₂ word) =
      evalObs obs₀ word := by

  exact
    evalObs_refines
      (r₀₁.compose r₁₂)
      word

end Refines

/-- Target-class inclusion along a two-step refinement chain. -/
theorem
    startRootedCorrectedConcreteTargetClass_subset_of_refines_compose
    (r₀₁ : Refines obs₀ obs₁)
    (r₁₂ : Refines obs₁ obs₂)
    (f : Nat) :
    StartRootedCorrectedConcreteTargetClass
        (v := z) α M₀ obs₀ f ⊆
      StartRootedCorrectedConcreteTargetClass
        (v := z) α M₂ obs₂ f := by

  exact
    startRootedCorrectedConcreteTargetClass_subset_of_refines
      (z := z)
      (r₀₁.compose r₁₂)

/-- Failure-class inclusion along a two-step refinement chain. -/
theorem
    observationFailureClass_subset_of_refines_compose
    (r₀₁ : Refines obs₀ obs₁)
    (r₁₂ : Refines obs₁ obs₂)
    (f : Nat) :
    StartRootedCorrectedConcreteObservationFailureClass
        (z := z) α M₂ obs₂ f ⊆
      StartRootedCorrectedConcreteObservationFailureClass
        (z := z) α M₀ obs₀ f := by

  exact
    observationFailureClass_subset_of_refines
      (z := z)
      (r₀₁.compose r₁₂)

end RefinementIdentityAndComposition


section ObservationEquivalenceDefinition

variable {α : Type u}
variable {M : Type v}
variable {M' : Type w}
variable {M'' : Type x}
variable [Monoid M]
variable [Monoid M']
variable [Monoid M'']
variable {obs : α → M}
variable {obs' : α → M'}
variable {obs'' : α → M''}

/-- Mutual observation refinement.  This is the semantic equivalence notion
needed for the fixed-observation target theory. -/
structure ObservationEquivalent
    (obs : α → M)
    (obs' : α → M') :
    Prop where

  toRefines :
    Refines obs obs'

  fromRefines :
    Refines obs' obs

namespace ObservationEquivalent

/-- Observation equivalence is reflexive. -/
def reflexive
    (obs : α → M) :
    ObservationEquivalent obs obs where

  toRefines :=
    Refines.identity obs

  fromRefines :=
    Refines.identity obs

/-- Observation equivalence is symmetric. -/
def symmetric
    (equivalent :
      ObservationEquivalent obs obs') :
    ObservationEquivalent obs' obs where

  toRefines :=
    equivalent.fromRefines

  fromRefines :=
    equivalent.toRefines

/-- Observation equivalence is transitive. -/
def transitive
    (equivalent₀₁ :
      ObservationEquivalent obs obs')
    (equivalent₁₂ :
      ObservationEquivalent obs' obs'') :
    ObservationEquivalent obs obs'' where

  toRefines :=
    equivalent₀₁.toRefines.compose
      equivalent₁₂.toRefines

  fromRefines :=
    equivalent₁₂.fromRefines.compose
      equivalent₀₁.fromRefines

end ObservationEquivalent

end ObservationEquivalenceDefinition


section ObservationEquivalenceSemanticClasses

variable {α : Type u}
variable {M : Type v}
variable {M' : Type w}
variable [Monoid M]
variable [Monoid M']
variable {obs : α → M}
variable {obs' : α → M'}
variable (f : Nat)

/-- Mutually refining observations have exactly the same semantic target
class. -/
theorem observationEquivalent_targetClass_eq
    (equivalent :
      ObservationEquivalent obs obs') :
    StartRootedCorrectedConcreteTargetClass
        (v := z) α M obs f =
      StartRootedCorrectedConcreteTargetClass
        (v := z) α M' obs' f := by

  apply Set.Subset.antisymm

  · exact
      startRootedCorrectedConcreteTargetClass_subset_of_refines
        (z := z)
        equivalent.toRefines

  · exact
      startRootedCorrectedConcreteTargetClass_subset_of_refines
        (z := z)
        equivalent.fromRefines

/-- Mutually refining observations have exactly the same failure class. -/
theorem observationEquivalent_failureClass_eq
    (equivalent :
      ObservationEquivalent obs obs') :
    StartRootedCorrectedConcreteObservationFailureClass
        (z := z) α M obs f =
      StartRootedCorrectedConcreteObservationFailureClass
        (z := z) α M' obs' f := by

  apply Set.Subset.antisymm

  · exact
      observationFailureClass_subset_of_refines
        (z := z)
        equivalent.fromRefines

  · exact
      observationFailureClass_subset_of_refines
        (z := z)
        equivalent.toRefines

/-- Mutual refinement leaves no strict gain from `obs` to `obs'`. -/
theorem observationEquivalent_gainClass_eq_empty
    (equivalent :
      ObservationEquivalent obs obs') :
    StartRootedCorrectedConcreteObservationGainClass
        (z := z) α M M' obs obs' f =
      ∅ := by

  ext language

  constructor

  · intro hGain

    exact
      False.elim
        (hGain.2
          (startRootedCorrectedConcreteTarget_mem_of_refines
            (z := z)
            equivalent.fromRefines
            hGain.1))

  · intro hEmpty

    simp at hEmpty

/-- Mutual refinement leaves no strict gain in the reverse direction either. -/
theorem observationEquivalent_reverseGainClass_eq_empty
    (equivalent :
      ObservationEquivalent obs obs') :
    StartRootedCorrectedConcreteObservationGainClass
        (z := z) α M' M obs' obs f =
      ∅ := by

  exact
    observationEquivalent_gainClass_eq_empty
      (z := z)
      f
      equivalent.symmetric

/-- Mutual refinement leaves no loss from `obs` to `obs'`. -/
theorem observationEquivalent_lossClass_eq_empty
    (equivalent :
      ObservationEquivalent obs obs') :
    StartRootedCorrectedConcreteObservationLossClass
        (z := z) α M M' obs obs' f =
      ∅ := by

  exact
    observationLossClass_eq_empty_of_refines
      (z := z)
      equivalent.toRefines

/-- Target success and observation failure are pointwise invariant under mutual
refinement. -/
theorem observationEquivalent_target_failure_iff_package
    (equivalent :
      ObservationEquivalent obs obs')
    (language : Set (Word α)) :
    (language ∈
        StartRootedCorrectedConcreteTargetClass
          (v := z) α M obs f ↔
      language ∈
        StartRootedCorrectedConcreteTargetClass
          (v := z) α M' obs' f) ∧
      (language ∈
          StartRootedCorrectedConcreteObservationFailureClass
            (z := z) α M obs f ↔
        language ∈
          StartRootedCorrectedConcreteObservationFailureClass
            (z := z) α M' obs' f) := by

  constructor

  · rw [
      observationEquivalent_targetClass_eq
        (z := z) f equivalent
    ]

  · rw [
      observationEquivalent_failureClass_eq
        (z := z) f equivalent
    ]

/-- Compact semantic observation-equivalence package. -/
theorem observationEquivalent_semanticClass_package
    (equivalent :
      ObservationEquivalent obs obs') :
    (StartRootedCorrectedConcreteTargetClass
        (v := z) α M obs f =
      StartRootedCorrectedConcreteTargetClass
        (v := z) α M' obs' f) ∧
      (StartRootedCorrectedConcreteObservationFailureClass
          (z := z) α M obs f =
        StartRootedCorrectedConcreteObservationFailureClass
          (z := z) α M' obs' f) ∧
      (StartRootedCorrectedConcreteObservationGainClass
          (z := z) α M M' obs obs' f =
        ∅) ∧
      (StartRootedCorrectedConcreteObservationGainClass
          (z := z) α M' M obs' obs f =
        ∅) ∧
      (StartRootedCorrectedConcreteObservationLossClass
          (z := z) α M M' obs obs' f =
        ∅) := by

  exact
    ⟨observationEquivalent_targetClass_eq
        (z := z) f equivalent,
      observationEquivalent_failureClass_eq
        (z := z) f equivalent,
      observationEquivalent_gainClass_eq_empty
        (z := z) f equivalent,
      observationEquivalent_reverseGainClass_eq_empty
        (z := z) f equivalent,
      observationEquivalent_lossClass_eq_empty
        (z := z) f equivalent⟩

end ObservationEquivalenceSemanticClasses


section ObservationEquivalentCertifiedLearners

variable {α : Type u}
variable {M : Type v}
variable {M' : Type w}
variable [Fintype M]
variable [Fintype M']
variable [DecidableEq α]
variable [DecidableEq M]
variable [DecidableEq M']
variable [Monoid M]
variable [Monoid M']
variable (hα : Nonempty α)
variable (obs : α → M)
variable (obs' : α → M')
variable (f : Nat)
variable (equivalent :
  ObservationEquivalent obs obs')

/-- The certified learner built from `obs'` identifies the target class
originally presented under `obs`. -/
theorem
    observationEquivalent_refinedLearner_identifies_originalTargetClass :
    IdentifiesClassFromPositiveData
      (correctedConcreteCertifiedWorkingGrammarHypLanguage
        obs' f)
      (correctedConcreteCertifiedWorkingGrammarLearner
        hα obs' f)
      (StartRootedCorrectedConcreteTargetClass
        (v := z) α M obs f) := by

  exact
    refinedCertifiedLearner_identifies_coarserTargetClass
      (z := z)
      hα obs obs' f
      equivalent.toRefines

/-- The certified learner built from `obs` identifies the target class
originally presented under `obs'`. -/
theorem
    observationEquivalent_originalLearner_identifies_refinedTargetClass :
    IdentifiesClassFromPositiveData
      (correctedConcreteCertifiedWorkingGrammarHypLanguage
        obs f)
      (correctedConcreteCertifiedWorkingGrammarLearner
        hα obs f)
      (StartRootedCorrectedConcreteTargetClass
        (v := z) α M' obs' f) := by

  exact
    refinedCertifiedLearner_identifies_coarserTargetClass
      (z := z)
      hα obs' obs f
      equivalent.fromRefines

/-- Both certified learners identify the same semantic target class, although
their certified output types remain observation-dependent. -/
theorem observationEquivalent_bothCertifiedLearners_package :
    IdentifiesClassFromPositiveData
        (correctedConcreteCertifiedWorkingGrammarHypLanguage
          obs f)
        (correctedConcreteCertifiedWorkingGrammarLearner
          hα obs f)
        (StartRootedCorrectedConcreteTargetClass
          (v := z) α M obs f) ∧
      IdentifiesClassFromPositiveData
        (correctedConcreteCertifiedWorkingGrammarHypLanguage
          obs' f)
        (correctedConcreteCertifiedWorkingGrammarLearner
          hα obs' f)
        (StartRootedCorrectedConcreteTargetClass
          (v := z) α M obs f) ∧
      IdentifiesClassFromPositiveData
        (correctedConcreteCertifiedWorkingGrammarHypLanguage
          obs f)
        (correctedConcreteCertifiedWorkingGrammarLearner
          hα obs f)
        (StartRootedCorrectedConcreteTargetClass
          (v := z) α M' obs' f) ∧
      IdentifiesClassFromPositiveData
        (correctedConcreteCertifiedWorkingGrammarHypLanguage
          obs' f)
        (correctedConcreteCertifiedWorkingGrammarLearner
          hα obs' f)
        (StartRootedCorrectedConcreteTargetClass
          (v := z) α M' obs' f) := by

  exact
    ⟨correctedConcreteCertifiedWorkingGrammarLearner_identifies_startRootedTargetClass
        (v := z) hα obs f,
      observationEquivalent_refinedLearner_identifies_originalTargetClass
        (z := z) hα obs obs' f equivalent,
      observationEquivalent_originalLearner_identifies_refinedTargetClass
        (z := z) hα obs obs' f equivalent,
      correctedConcreteCertifiedWorkingGrammarLearner_identifies_startRootedTargetClass
        (v := z) hα obs' f⟩

end ObservationEquivalentCertifiedLearners


section ThreeStageObservationRefinementChain

variable {α : Type u}
variable {M₀ : Type v}
variable {M₁ : Type w}
variable {M₂ : Type x}
variable [Monoid M₀]
variable [Monoid M₁]
variable [Monoid M₂]
variable {obs₀ : α → M₀}
variable {obs₁ : α → M₁}
variable {obs₂ : α → M₂}
variable (f : Nat)
variable (r₀₁ : Refines obs₀ obs₁)
variable (r₁₂ : Refines obs₁ obs₂)

/-- The direct strict gain from `obs₀` to `obs₂` is exactly the union of the
two incremental gain classes. -/
theorem observationGainClass_compose_eq_union :
    StartRootedCorrectedConcreteObservationGainClass
        (z := z) α M₀ M₂ obs₀ obs₂ f =
      StartRootedCorrectedConcreteObservationGainClass
          (z := z) α M₀ M₁ obs₀ obs₁ f ∪
        StartRootedCorrectedConcreteObservationGainClass
          (z := z) α M₁ M₂ obs₁ obs₂ f := by

  ext language

  constructor

  · intro hDirect

    by_cases hIntermediate :
        language ∈
          StartRootedCorrectedConcreteTargetClass
            (v := z) α M₁ obs₁ f

    · exact
        Or.inl
          ⟨hIntermediate,
            hDirect.2⟩

    · exact
        Or.inr
          ⟨hDirect.1,
            hIntermediate⟩

  · intro hIncremental

    rcases hIncremental with
      hFirst | hSecond

    · exact
        ⟨startRootedCorrectedConcreteTarget_mem_of_refines
            (z := z)
            r₁₂
            hFirst.1,
          hFirst.2⟩

    · refine
        ⟨hSecond.1,
          ?_⟩

      intro hCoarse

      exact
        hSecond.2
          (startRootedCorrectedConcreteTarget_mem_of_refines
            (z := z)
            r₀₁
            hCoarse)

/-- The two incremental gain classes in a refinement chain are disjoint. -/
theorem observationGainClasses_incremental_disjoint :
    Set.Disjoint
      (StartRootedCorrectedConcreteObservationGainClass
        (z := z) α M₀ M₁ obs₀ obs₁ f)
      (StartRootedCorrectedConcreteObservationGainClass
        (z := z) α M₁ M₂ obs₁ obs₂ f) := by

  rw [Set.disjoint_left]

  intro language hFirst hSecond

  exact
    hSecond.2
      hFirst.1

/-- The finest target class decomposes into the coarsest targets, first-stage
gains, and second-stage gains. -/
theorem finestTargetClass_eq_coarsest_union_incrementalGains :
    StartRootedCorrectedConcreteTargetClass
        (v := z) α M₂ obs₂ f =
      (StartRootedCorrectedConcreteTargetClass
          (v := z) α M₀ obs₀ f ∪
        StartRootedCorrectedConcreteObservationGainClass
          (z := z) α M₀ M₁ obs₀ obs₁ f) ∪
        StartRootedCorrectedConcreteObservationGainClass
          (z := z) α M₁ M₂ obs₁ obs₂ f := by

  calc
    StartRootedCorrectedConcreteTargetClass
        (v := z) α M₂ obs₂ f =
      StartRootedCorrectedConcreteTargetClass
          (v := z) α M₁ obs₁ f ∪
        StartRootedCorrectedConcreteObservationGainClass
          (z := z) α M₁ M₂ obs₁ obs₂ f :=
      finerTargetClass_eq_coarser_union_observationGainClass
        (z := z)
        r₁₂
    _ =
      (StartRootedCorrectedConcreteTargetClass
          (v := z) α M₀ obs₀ f ∪
        StartRootedCorrectedConcreteObservationGainClass
          (z := z) α M₀ M₁ obs₀ obs₁ f) ∪
        StartRootedCorrectedConcreteObservationGainClass
          (z := z) α M₁ M₂ obs₁ obs₂ f := by

      rw [
        finerTargetClass_eq_coarser_union_observationGainClass
          (z := z)
          r₀₁
      ]

/-- Failure classes form the reverse inclusion chain. -/
theorem observationFailureClasses_chain :
    StartRootedCorrectedConcreteObservationFailureClass
        (z := z) α M₂ obs₂ f ⊆
      StartRootedCorrectedConcreteObservationFailureClass
        (z := z) α M₁ obs₁ f ∧
      StartRootedCorrectedConcreteObservationFailureClass
        (z := z) α M₁ obs₁ f ⊆
      StartRootedCorrectedConcreteObservationFailureClass
        (z := z) α M₀ obs₀ f ∧
      StartRootedCorrectedConcreteObservationFailureClass
        (z := z) α M₂ obs₂ f ⊆
      StartRootedCorrectedConcreteObservationFailureClass
        (z := z) α M₀ obs₀ f := by

  exact
    ⟨observationFailureClass_subset_of_refines
        (z := z)
        r₁₂,
      observationFailureClass_subset_of_refines
        (z := z)
        r₀₁,
      observationFailureClass_subset_of_refines
        (z := z)
        (r₀₁.compose r₁₂)⟩

/-- No language is lost at either stage or along the composed refinement. -/
theorem observationLossClasses_chain_eq_empty :
    StartRootedCorrectedConcreteObservationLossClass
        (z := z) α M₀ M₁ obs₀ obs₁ f =
      ∅ ∧
      StartRootedCorrectedConcreteObservationLossClass
          (z := z) α M₁ M₂ obs₁ obs₂ f =
        ∅ ∧
      StartRootedCorrectedConcreteObservationLossClass
          (z := z) α M₀ M₂ obs₀ obs₂ f =
        ∅ := by

  exact
    ⟨observationLossClass_eq_empty_of_refines
        (z := z)
        r₀₁,
      observationLossClass_eq_empty_of_refines
        (z := z)
        r₁₂,
      observationLossClass_eq_empty_of_refines
        (z := z)
        (r₀₁.compose r₁₂)⟩

/-- Compact path-independent semantic gain decomposition package. -/
theorem observationRefinementChain_semanticGain_package :
    (StartRootedCorrectedConcreteTargetClass
        (v := z) α M₀ obs₀ f ⊆
      StartRootedCorrectedConcreteTargetClass
        (v := z) α M₁ obs₁ f) ∧
      (StartRootedCorrectedConcreteTargetClass
          (v := z) α M₁ obs₁ f ⊆
        StartRootedCorrectedConcreteTargetClass
          (v := z) α M₂ obs₂ f) ∧
      (StartRootedCorrectedConcreteObservationGainClass
          (z := z) α M₀ M₂ obs₀ obs₂ f =
        StartRootedCorrectedConcreteObservationGainClass
            (z := z) α M₀ M₁ obs₀ obs₁ f ∪
          StartRootedCorrectedConcreteObservationGainClass
            (z := z) α M₁ M₂ obs₁ obs₂ f) ∧
      Set.Disjoint
        (StartRootedCorrectedConcreteObservationGainClass
          (z := z) α M₀ M₁ obs₀ obs₁ f)
        (StartRootedCorrectedConcreteObservationGainClass
          (z := z) α M₁ M₂ obs₁ obs₂ f) ∧
      (StartRootedCorrectedConcreteTargetClass
          (v := z) α M₂ obs₂ f =
        (StartRootedCorrectedConcreteTargetClass
            (v := z) α M₀ obs₀ f ∪
          StartRootedCorrectedConcreteObservationGainClass
            (z := z) α M₀ M₁ obs₀ obs₁ f) ∪
          StartRootedCorrectedConcreteObservationGainClass
            (z := z) α M₁ M₂ obs₁ obs₂ f) := by

  exact
    ⟨startRootedCorrectedConcreteTargetClass_subset_of_refines
        (z := z)
        r₀₁,
      startRootedCorrectedConcreteTargetClass_subset_of_refines
        (z := z)
        r₁₂,
      observationGainClass_compose_eq_union
        (z := z)
        f r₀₁ r₁₂,
      observationGainClasses_incremental_disjoint
        (z := z)
        f r₀₁ r₁₂,
      finestTargetClass_eq_coarsest_union_incrementalGains
        (z := z)
        f r₀₁ r₁₂⟩

end ThreeStageObservationRefinementChain


section FinestCertifiedLearnerAlongRefinementChain

variable {α : Type u}
variable {M₀ : Type v}
variable {M₁ : Type w}
variable {M₂ : Type x}
variable [Fintype M₀]
variable [Fintype M₁]
variable [Fintype M₂]
variable [DecidableEq α]
variable [DecidableEq M₀]
variable [DecidableEq M₁]
variable [DecidableEq M₂]
variable [Monoid M₀]
variable [Monoid M₁]
variable [Monoid M₂]
variable (hα : Nonempty α)
variable (obs₀ : α → M₀)
variable (obs₁ : α → M₁)
variable (obs₂ : α → M₂)
variable (f : Nat)
variable (r₀₁ : Refines obs₀ obs₁)
variable (r₁₂ : Refines obs₁ obs₂)

/-- The finest certified learner identifies the coarsest target class. -/
theorem
    finestCertifiedLearner_identifies_coarsestTargetClass :
    IdentifiesClassFromPositiveData
      (correctedConcreteCertifiedWorkingGrammarHypLanguage
        obs₂ f)
      (correctedConcreteCertifiedWorkingGrammarLearner
        hα obs₂ f)
      (StartRootedCorrectedConcreteTargetClass
        (v := z) α M₀ obs₀ f) := by

  exact
    refinedCertifiedLearner_identifies_coarserTargetClass
      (z := z)
      hα obs₀ obs₂ f
      (r₀₁.compose r₁₂)

/-- The finest certified learner identifies the intermediate target class. -/
theorem
    finestCertifiedLearner_identifies_intermediateTargetClass :
    IdentifiesClassFromPositiveData
      (correctedConcreteCertifiedWorkingGrammarHypLanguage
        obs₂ f)
      (correctedConcreteCertifiedWorkingGrammarLearner
        hα obs₂ f)
      (StartRootedCorrectedConcreteTargetClass
        (v := z) α M₁ obs₁ f) := by

  exact
    refinedCertifiedLearner_identifies_coarserTargetClass
      (z := z)
      hα obs₁ obs₂ f
      r₁₂

/-- The finest certified learner identifies the first incremental gain class. -/
theorem
    finestCertifiedLearner_identifies_firstObservationGainClass :
    IdentifiesClassFromPositiveData
      (correctedConcreteCertifiedWorkingGrammarHypLanguage
        obs₂ f)
      (correctedConcreteCertifiedWorkingGrammarLearner
        hα obs₂ f)
      (StartRootedCorrectedConcreteObservationGainClass
        (z := z) α M₀ M₁ obs₀ obs₁ f) := by

  intro language hGain

  exact
    correctedConcreteCertifiedWorkingGrammarLearner_identifies_startRootedTargetClass
      (v := z)
      hα obs₂ f
      language
      (startRootedCorrectedConcreteTarget_mem_of_refines
        (z := z)
        r₁₂
        hGain.1)

/-- The finest certified learner identifies the second incremental gain class. -/
theorem
    finestCertifiedLearner_identifies_secondObservationGainClass :
    IdentifiesClassFromPositiveData
      (correctedConcreteCertifiedWorkingGrammarHypLanguage
        obs₂ f)
      (correctedConcreteCertifiedWorkingGrammarLearner
        hα obs₂ f)
      (StartRootedCorrectedConcreteObservationGainClass
        (z := z) α M₁ M₂ obs₁ obs₂ f) := by

  exact
    refinedCertifiedLearner_identifies_observationGainClass
      (z := z)
      hα obs₁ obs₂ f
      r₁₂

/-- The finest certified learner identifies the direct gain class from the
coarsest to the finest observation. -/
theorem
    finestCertifiedLearner_identifies_directObservationGainClass :
    IdentifiesClassFromPositiveData
      (correctedConcreteCertifiedWorkingGrammarHypLanguage
        obs₂ f)
      (correctedConcreteCertifiedWorkingGrammarLearner
        hα obs₂ f)
      (StartRootedCorrectedConcreteObservationGainClass
        (z := z) α M₀ M₂ obs₀ obs₂ f) := by

  exact
    refinedCertifiedLearner_identifies_observationGainClass
      (z := z)
      hα obs₀ obs₂ f
      (r₀₁.compose r₁₂)

/-- A direct-gain language has a finest-observation minimum certified
description rank and exact finite checked output, while remaining outside the
coarsest target class. -/
theorem
    directObservationGain_target_finestDescriptionRank_package
    {L : Set (Word α)}
    (hGain :
      L ∈
        StartRootedCorrectedConcreteObservationGainClass
          (z := z) α M₀ M₂ obs₀ obs₂ f) :
    L ∉
        StartRootedCorrectedConcreteTargetClass
          (v := z) α M₀ obs₀ f ∧
      L ∈
        CorrectedConcreteCertifiedRankProfileClass
          (α := α)
          (M := M₂)
          obs₂ f
          (startRootedTargetCertifiedDescriptionRank
            (v := z) hα obs₂ f hGain.1) ∧
      startRootedTargetCertifiedDescriptionRank
          (v := z) hα obs₂ f hGain.1 <=
        startRootedTargetCharacteristicRank
          (v := z) hα obs₂ f hGain.1 ∧
      ∃
        C :
          CorrectedConcreteCertifiedWorkingGrammarHypothesis
            α M₂ obs₂ f,
        C.output.grammar.StringLanguage = L ∧
          C.bits.length <=
            correctedConcreteCertifiedRankBitBudget
              (startRootedTargetCertifiedDescriptionRank
                (v := z) hα obs₂ f hGain.1)
              f ∧
          C.canonicalSearch.length <=
            correctedConcreteCertifiedRankSearchBudget
              (startRootedTargetCertifiedDescriptionRank
                (v := z) hα obs₂ f hGain.1)
              f := by

  exact
    observationGain_target_refinedDescriptionRank_package
      (z := z)
      hα obs₀ obs₂ f
      (r₀₁.compose r₁₂)
      hGain

/-- Compact certified-learning package for a three-stage observation chain. -/
theorem finestCertifiedLearner_refinementChain_package :
    IdentifiesClassFromPositiveData
        (correctedConcreteCertifiedWorkingGrammarHypLanguage
          obs₂ f)
        (correctedConcreteCertifiedWorkingGrammarLearner
          hα obs₂ f)
        (StartRootedCorrectedConcreteTargetClass
          (v := z) α M₀ obs₀ f) ∧
      IdentifiesClassFromPositiveData
        (correctedConcreteCertifiedWorkingGrammarHypLanguage
          obs₂ f)
        (correctedConcreteCertifiedWorkingGrammarLearner
          hα obs₂ f)
        (StartRootedCorrectedConcreteTargetClass
          (v := z) α M₁ obs₁ f) ∧
      IdentifiesClassFromPositiveData
        (correctedConcreteCertifiedWorkingGrammarHypLanguage
          obs₂ f)
        (correctedConcreteCertifiedWorkingGrammarLearner
          hα obs₂ f)
        (StartRootedCorrectedConcreteObservationGainClass
          (z := z) α M₀ M₁ obs₀ obs₁ f) ∧
      IdentifiesClassFromPositiveData
        (correctedConcreteCertifiedWorkingGrammarHypLanguage
          obs₂ f)
        (correctedConcreteCertifiedWorkingGrammarLearner
          hα obs₂ f)
        (StartRootedCorrectedConcreteObservationGainClass
          (z := z) α M₁ M₂ obs₁ obs₂ f) ∧
      IdentifiesClassFromPositiveData
        (correctedConcreteCertifiedWorkingGrammarHypLanguage
          obs₂ f)
        (correctedConcreteCertifiedWorkingGrammarLearner
          hα obs₂ f)
        (StartRootedCorrectedConcreteObservationGainClass
          (z := z) α M₀ M₂ obs₀ obs₂ f) := by

  exact
    ⟨finestCertifiedLearner_identifies_coarsestTargetClass
        (z := z)
        hα obs₀ obs₁ obs₂ f r₀₁ r₁₂,
      finestCertifiedLearner_identifies_intermediateTargetClass
        (z := z)
        hα obs₀ obs₁ obs₂ f r₀₁ r₁₂,
      finestCertifiedLearner_identifies_firstObservationGainClass
        (z := z)
        hα obs₀ obs₁ obs₂ f r₀₁ r₁₂,
      finestCertifiedLearner_identifies_secondObservationGainClass
        (z := z)
        hα obs₀ obs₁ obs₂ f r₀₁ r₁₂,
      finestCertifiedLearner_identifies_directObservationGainClass
        (z := z)
        hα obs₀ obs₁ obs₂ f r₀₁ r₁₂⟩

end FinestCertifiedLearnerAlongRefinementChain


section ObservationEquivalenceChainFinalPackages

variable {α : Type u}
variable {M₀ : Type v}
variable {M₁ : Type w}
variable {M₂ : Type x}
variable [Fintype M₀]
variable [Fintype M₁]
variable [Fintype M₂]
variable [DecidableEq α]
variable [DecidableEq M₀]
variable [DecidableEq M₁]
variable [DecidableEq M₂]
variable [Monoid M₀]
variable [Monoid M₁]
variable [Monoid M₂]
variable (hα : Nonempty α)
variable (obs₀ : α → M₀)
variable (obs₁ : α → M₁)
variable (obs₂ : α → M₂)
variable (f : Nat)
variable (r₀₁ : Refines obs₀ obs₁)
variable (r₁₂ : Refines obs₁ obs₂)

/-- Final semantic and certified-learning package for a composed observation
refinement chain. -/
theorem
    correctedConcreteCertifiedWorkingGrammar_observationRefinementChain_package :
    (StartRootedCorrectedConcreteTargetClass
        (v := z) α M₀ obs₀ f ⊆
      StartRootedCorrectedConcreteTargetClass
        (v := z) α M₁ obs₁ f) ∧
      (StartRootedCorrectedConcreteTargetClass
          (v := z) α M₁ obs₁ f ⊆
        StartRootedCorrectedConcreteTargetClass
          (v := z) α M₂ obs₂ f) ∧
      (StartRootedCorrectedConcreteObservationGainClass
          (z := z) α M₀ M₂ obs₀ obs₂ f =
        StartRootedCorrectedConcreteObservationGainClass
            (z := z) α M₀ M₁ obs₀ obs₁ f ∪
          StartRootedCorrectedConcreteObservationGainClass
            (z := z) α M₁ M₂ obs₁ obs₂ f) ∧
      Set.Disjoint
        (StartRootedCorrectedConcreteObservationGainClass
          (z := z) α M₀ M₁ obs₀ obs₁ f)
        (StartRootedCorrectedConcreteObservationGainClass
          (z := z) α M₁ M₂ obs₁ obs₂ f) ∧
      (StartRootedCorrectedConcreteObservationFailureClass
          (z := z) α M₂ obs₂ f ⊆
        StartRootedCorrectedConcreteObservationFailureClass
          (z := z) α M₀ obs₀ f) ∧
      IdentifiesClassFromPositiveData
        (correctedConcreteCertifiedWorkingGrammarHypLanguage
          obs₂ f)
        (correctedConcreteCertifiedWorkingGrammarLearner
          hα obs₂ f)
        (StartRootedCorrectedConcreteTargetClass
          (v := z) α M₀ obs₀ f) ∧
      IdentifiesClassFromPositiveData
        (correctedConcreteCertifiedWorkingGrammarHypLanguage
          obs₂ f)
        (correctedConcreteCertifiedWorkingGrammarLearner
          hα obs₂ f)
        (StartRootedCorrectedConcreteObservationGainClass
          (z := z) α M₀ M₂ obs₀ obs₂ f) := by

  exact
    ⟨startRootedCorrectedConcreteTargetClass_subset_of_refines
        (z := z)
        r₀₁,
      startRootedCorrectedConcreteTargetClass_subset_of_refines
        (z := z)
        r₁₂,
      observationGainClass_compose_eq_union
        (z := z)
        f r₀₁ r₁₂,
      observationGainClasses_incremental_disjoint
        (z := z)
        f r₀₁ r₁₂,
      observationFailureClass_subset_of_refines
        (z := z)
        (r₀₁.compose r₁₂),
      finestCertifiedLearner_identifies_coarsestTargetClass
        (z := z)
        hα obs₀ obs₁ obs₂ f r₀₁ r₁₂,
      finestCertifiedLearner_identifies_directObservationGainClass
        (z := z)
        hα obs₀ obs₁ obs₂ f r₀₁ r₁₂⟩

end ObservationEquivalenceChainFinalPackages

end MCFG
