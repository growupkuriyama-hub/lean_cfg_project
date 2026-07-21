/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG.ConcreteCanonicalLearnerWorkingGrammarObservationEquivalenceChain

/-!
# ConcreteCanonicalLearnerWorkingGrammarObservationAblation.lean

The preceding files prove that observation refinement enlarges the semantic
target class, shrinks the observation-failure class, and decomposes a
multi-stage refinement into disjoint strict gain classes.

This file gives the exact interface-ablation criterion.

Let

```lean
r : Refines obs obs'
```

mean that `obs'` is finer than `obs`.

## Redundant and essential refinement

The refinement step is **redundant** when its strict gain class is empty:

```lean
CorrectedConcreteObservationRefinementRedundant.
```

It is **essential** when some language belongs to the strict gain class:

```lean
CorrectedConcreteObservationRefinementEssential.
```

Under refinement, the following are equivalent:

```text
the step is redundant;
the strict gain class is empty;
the coarse and fine semantic target classes are equal;
the coarse and fine observation-failure classes are equal.
```

Likewise, the following are equivalent:

```text
the step is essential;
the strict gain class is inhabited;
the target class grows strictly;
the failure class shrinks strictly.
```

Thus ablating the finer observation back to the coarser one changes the
semantic theory exactly when the gain class is nonempty.

## Certified-learning consequence

An essential refinement supplies an actual semantic language `L` such that

```text
L is not a coarse-observation target,
L is a fine-observation target,
the fine certified learner identifies L,
and L has a fine-observation minimum certified-description rank
with one exact bounded certified output.
```

A redundant refinement supplies no new semantic targets.  Both certified
learners identify the same semantic target class, although their output and
presentation types remain observation-dependent.

## Refinement chains

For a chain

```text
obs₀ ← obs₁ ← obs₂,
```

the direct refinement is essential exactly when at least one incremental step
is essential.  It is redundant exactly when both incremental steps are
redundant.

Equivalently,

```text
targets(obs₀) = targets(obs₂)
```

exactly when

```text
targets(obs₀) = targets(obs₁)
and
targets(obs₁) = targets(obs₂).
```

The already proved disjoint gain decomposition records which incremental step
contributes each newly representable language.

## Boundary

No theorem here asserts that a particular refinement is essential.  That
requires one concrete strict-gain witness.  The present file proves that such a
witness is exactly the missing interface-ablation input and packages all of its
learning and complexity consequences.

No target grammar is supplied to any learner.
No `sorry`, `admit`, or `axiom` is used.
-/

namespace MCFG

universe u v w x z


section ObservationAblationDefinitions

variable (α : Type u)
variable (M : Type v)
variable (M' : Type w)
variable [Monoid M]
variable [Monoid M']
variable (obs : α → M)
variable (obs' : α → M')
variable (f : Nat)

/-- A refinement step is semantically redundant when it creates no strict
observation-gain language. -/
def CorrectedConcreteObservationRefinementRedundant :
    Prop :=
  StartRootedCorrectedConcreteObservationGainClass
      (z := z) α M M' obs obs' f =
    ∅

/-- A refinement step is semantically essential when it creates at least one
strict observation-gain language. -/
def CorrectedConcreteObservationRefinementEssential :
    Prop :=
  ∃ language : Set (Word α),
    language ∈
      StartRootedCorrectedConcreteObservationGainClass
        (z := z) α M M' obs obs' f

end ObservationAblationDefinitions


section RedundancyAndEssentialityLogic

variable {α : Type u}
variable {M : Type v}
variable {M' : Type w}
variable [Monoid M]
variable [Monoid M']
variable {obs : α → M}
variable {obs' : α → M'}
variable {f : Nat}

/-- Redundancy is exactly the negation of essentiality. -/
theorem observationRefinementRedundant_iff_not_essential :
    CorrectedConcreteObservationRefinementRedundant
        (z := z) α M M' obs obs' f ↔
      ¬
        CorrectedConcreteObservationRefinementEssential
          (z := z) α M M' obs obs' f := by

  constructor

  · intro hRedundant hEssential

    rcases hEssential with
      ⟨language, hGain⟩

    rw [hRedundant] at hGain
    simp at hGain

  · intro hNotEssential

    unfold
      CorrectedConcreteObservationRefinementRedundant

    ext language

    constructor

    · intro hGain

      exact
        False.elim
          (hNotEssential
            ⟨language, hGain⟩)

    · intro hEmpty

      simp at hEmpty

/-- Essentiality is exactly the negation of redundancy. -/
theorem observationRefinementEssential_iff_not_redundant :
    CorrectedConcreteObservationRefinementEssential
        (z := z) α M M' obs obs' f ↔
      ¬
        CorrectedConcreteObservationRefinementRedundant
          (z := z) α M M' obs obs' f := by

  constructor

  · intro hEssential hRedundant

    exact
      (observationRefinementRedundant_iff_not_essential
        (z := z)
        (α := α)
        (M := M)
        (M' := M')
        (obs := obs)
        (obs' := obs')
        (f := f)).mp
        hRedundant
        hEssential

  · intro hNotRedundant

    by_contra hNotEssential

    exact
      hNotRedundant
        ((observationRefinementRedundant_iff_not_essential
          (z := z)
          (α := α)
          (M := M)
          (M' := M')
          (obs := obs)
          (obs' := obs')
          (f := f)).mpr
          hNotEssential)

/-- A refinement step cannot be both redundant and essential. -/
theorem observationRefinementRedundant_not_essential
    (hRedundant :
      CorrectedConcreteObservationRefinementRedundant
        (z := z) α M M' obs obs' f) :
    ¬
      CorrectedConcreteObservationRefinementEssential
        (z := z) α M M' obs obs' f := by

  exact
    (observationRefinementRedundant_iff_not_essential
      (z := z)
      (α := α)
      (M := M)
      (M' := M')
      (obs := obs)
      (obs' := obs')
      (f := f)).mp
      hRedundant

/-- Every nonredundant refinement step has an explicit strict-gain language. -/
theorem exists_observationGain_of_not_redundant
    (hNotRedundant :
      ¬
        CorrectedConcreteObservationRefinementRedundant
          (z := z) α M M' obs obs' f) :
    ∃ language : Set (Word α),
      language ∈
        StartRootedCorrectedConcreteObservationGainClass
          (z := z) α M M' obs obs' f := by

  exact
    (observationRefinementEssential_iff_not_redundant
      (z := z)
      (α := α)
      (M := M)
      (M' := M')
      (obs := obs)
      (obs' := obs')
      (f := f)).mpr
      hNotRedundant

end RedundancyAndEssentialityLogic


section RefinementAblationCriteria

variable {α : Type u}
variable {M : Type v}
variable {M' : Type w}
variable [Monoid M]
variable [Monoid M']
variable {obs : α → M}
variable {obs' : α → M'}
variable (f : Nat)
variable (r : Refines obs obs')

/-- A refinement is redundant exactly when coarse and fine semantic target
classes are equal. -/
theorem observationRefinementRedundant_iff_targetClass_eq :
    CorrectedConcreteObservationRefinementRedundant
        (z := z) α M M' obs obs' f ↔
      StartRootedCorrectedConcreteTargetClass
          (v := z) α M obs f =
        StartRootedCorrectedConcreteTargetClass
          (v := z) α M' obs' f := by

  constructor

  · intro hRedundant

    have hDecomposition :
        StartRootedCorrectedConcreteTargetClass
            (v := z) α M' obs' f =
          StartRootedCorrectedConcreteTargetClass
              (v := z) α M obs f ∪
            StartRootedCorrectedConcreteObservationGainClass
              (z := z) α M M' obs obs' f :=
      finerTargetClass_eq_coarser_union_observationGainClass
        (z := z)
        r

    rw [
      hRedundant,
      Set.union_empty
    ] at hDecomposition

    exact
      hDecomposition.symm

  · intro hClasses

    unfold
      CorrectedConcreteObservationRefinementRedundant

    ext language

    constructor

    · intro hGain

      exact
        False.elim
          (hGain.2
            (by
              rw [hClasses]
              exact hGain.1))

    · intro hEmpty

      simp at hEmpty

/-- A refinement is redundant exactly when its failure class is unchanged. -/
theorem observationRefinementRedundant_iff_failureClass_eq :
    CorrectedConcreteObservationRefinementRedundant
        (z := z) α M M' obs obs' f ↔
      StartRootedCorrectedConcreteObservationFailureClass
          (z := z) α M obs f =
        StartRootedCorrectedConcreteObservationFailureClass
          (z := z) α M' obs' f := by

  constructor

  · intro hRedundant

    have hTargetClasses :
        StartRootedCorrectedConcreteTargetClass
            (v := z) α M obs f =
          StartRootedCorrectedConcreteTargetClass
            (v := z) α M' obs' f :=
      (observationRefinementRedundant_iff_targetClass_eq
        (z := z)
        f r).mp
        hRedundant

    unfold
      StartRootedCorrectedConcreteObservationFailureClass

    rw [hTargetClasses]

  · intro hFailureClasses

    apply
      (observationRefinementRedundant_iff_targetClass_eq
        (z := z)
        f r).mpr

    apply Set.Subset.antisymm

    · exact
        startRootedCorrectedConcreteTargetClass_subset_of_refines
          (z := z)
          r

    · intro language hFine

      by_contra hNotCoarse

      have hCoarseFailure :
          language ∈
            StartRootedCorrectedConcreteObservationFailureClass
              (z := z) α M obs f :=
        hNotCoarse

      rw [hFailureClasses] at hCoarseFailure

      exact
        hCoarseFailure hFine

/-- A refinement is essential exactly when its semantic target class changes. -/
theorem observationRefinementEssential_iff_targetClass_ne :
    CorrectedConcreteObservationRefinementEssential
        (z := z) α M M' obs obs' f ↔
      StartRootedCorrectedConcreteTargetClass
          (v := z) α M obs f ≠
        StartRootedCorrectedConcreteTargetClass
          (v := z) α M' obs' f := by

  constructor

  · intro hEssential hClasses

    rcases hEssential with
      ⟨language, hGain⟩

    exact
      hGain.2
        (by
          rw [hClasses]
          exact hGain.1)

  · intro hClasses

    apply
      (observationRefinementEssential_iff_not_redundant
        (z := z)
        (α := α)
        (M := M)
        (M' := M')
        (obs := obs)
        (obs' := obs')
        (f := f)).mpr

    intro hRedundant

    exact
      hClasses
        ((observationRefinementRedundant_iff_targetClass_eq
          (z := z)
          f r).mp
          hRedundant)

/-- A refinement is essential exactly when its failure class changes. -/
theorem observationRefinementEssential_iff_failureClass_ne :
    CorrectedConcreteObservationRefinementEssential
        (z := z) α M M' obs obs' f ↔
      StartRootedCorrectedConcreteObservationFailureClass
          (z := z) α M obs f ≠
        StartRootedCorrectedConcreteObservationFailureClass
          (z := z) α M' obs' f := by

  constructor

  · intro hEssential hFailureClasses

    have hRedundant :
        CorrectedConcreteObservationRefinementRedundant
          (z := z) α M M' obs obs' f :=
      (observationRefinementRedundant_iff_failureClass_eq
        (z := z)
        f r).mpr
        hFailureClasses

    exact
      (observationRefinementRedundant_not_essential
        (z := z)
        hRedundant)
        hEssential

  · intro hFailureClasses

    apply
      (observationRefinementEssential_iff_not_redundant
        (z := z)
        (α := α)
        (M := M)
        (M' := M')
        (obs := obs)
        (obs' := obs')
        (f := f)).mpr

    intro hRedundant

    exact
      hFailureClasses
        ((observationRefinementRedundant_iff_failureClass_eq
          (z := z)
          f r).mp
          hRedundant)

/-- Essentiality is equivalent to strict target-class growth, expressed without
depending on a particular strict-subset notation. -/
theorem observationRefinementEssential_iff_strict_targetClass_growth :
    CorrectedConcreteObservationRefinementEssential
        (z := z) α M M' obs obs' f ↔
      (StartRootedCorrectedConcreteTargetClass
          (v := z) α M obs f ⊆
        StartRootedCorrectedConcreteTargetClass
          (v := z) α M' obs' f) ∧
      (StartRootedCorrectedConcreteTargetClass
          (v := z) α M obs f ≠
        StartRootedCorrectedConcreteTargetClass
          (v := z) α M' obs' f) := by

  constructor

  · intro hEssential

    exact
      ⟨startRootedCorrectedConcreteTargetClass_subset_of_refines
          (z := z)
          r,
        (observationRefinementEssential_iff_targetClass_ne
          (z := z)
          f r).mp
          hEssential⟩

  · intro hStrict

    exact
      (observationRefinementEssential_iff_targetClass_ne
        (z := z)
        f r).mpr
        hStrict.2

/-- Essentiality is equivalent to strict failure-class shrinkage. -/
theorem observationRefinementEssential_iff_strict_failureClass_shrinkage :
    CorrectedConcreteObservationRefinementEssential
        (z := z) α M M' obs obs' f ↔
      (StartRootedCorrectedConcreteObservationFailureClass
          (z := z) α M' obs' f ⊆
        StartRootedCorrectedConcreteObservationFailureClass
          (z := z) α M obs f) ∧
      (StartRootedCorrectedConcreteObservationFailureClass
          (z := z) α M' obs' f ≠
        StartRootedCorrectedConcreteObservationFailureClass
          (z := z) α M obs f) := by

  constructor

  · intro hEssential

    have hNeCoarseFine :
        StartRootedCorrectedConcreteObservationFailureClass
            (z := z) α M obs f ≠
          StartRootedCorrectedConcreteObservationFailureClass
            (z := z) α M' obs' f :=
      (observationRefinementEssential_iff_failureClass_ne
        (z := z)
        f r).mp
        hEssential

    exact
      ⟨observationFailureClass_subset_of_refines
          (z := z)
          r,
        by
          intro hFineCoarse

          exact
            hNeCoarseFine
              hFineCoarse.symm⟩

  · intro hStrict

    apply
      (observationRefinementEssential_iff_failureClass_ne
        (z := z)
        f r).mpr

    intro hCoarseFine

    exact
      hStrict.2
        hCoarseFine.symm

/-- Complete semantic interface-ablation criterion. -/
theorem observationRefinement_ablationCriterion_package :
    (CorrectedConcreteObservationRefinementRedundant
          (z := z) α M M' obs obs' f ↔
        StartRootedCorrectedConcreteTargetClass
            (v := z) α M obs f =
          StartRootedCorrectedConcreteTargetClass
            (v := z) α M' obs' f) ∧
      (CorrectedConcreteObservationRefinementRedundant
          (z := z) α M M' obs obs' f ↔
        StartRootedCorrectedConcreteObservationFailureClass
            (z := z) α M obs f =
          StartRootedCorrectedConcreteObservationFailureClass
            (z := z) α M' obs' f) ∧
      (CorrectedConcreteObservationRefinementEssential
          (z := z) α M M' obs obs' f ↔
        StartRootedCorrectedConcreteTargetClass
            (v := z) α M obs f ≠
          StartRootedCorrectedConcreteTargetClass
            (v := z) α M' obs' f) ∧
      (CorrectedConcreteObservationRefinementEssential
          (z := z) α M M' obs obs' f ↔
        StartRootedCorrectedConcreteObservationFailureClass
            (z := z) α M obs f ≠
          StartRootedCorrectedConcreteObservationFailureClass
            (z := z) α M' obs' f) := by

  exact
    ⟨observationRefinementRedundant_iff_targetClass_eq
        (z := z)
        f r,
      observationRefinementRedundant_iff_failureClass_eq
        (z := z)
        f r,
      observationRefinementEssential_iff_targetClass_ne
        (z := z)
        f r,
      observationRefinementEssential_iff_failureClass_ne
        (z := z)
        f r⟩

end RefinementAblationCriteria


section EssentialRefinementCertifiedWitness

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
variable (r : Refines obs obs')

/-- An essential refinement supplies one genuinely new fine-observation target
that is identified by the refined certified learner and has an exact
minimum-rank certified description. -/
theorem essentialObservationRefinement_exists_newCertifiedTarget
    (hEssential :
      CorrectedConcreteObservationRefinementEssential
        (z := z) α M M' obs obs' f) :
    ∃
      (language : Set (Word α))
      (hFine :
        language ∈
          StartRootedCorrectedConcreteTargetClass
            (v := z) α M' obs' f),
      language ∉
          StartRootedCorrectedConcreteTargetClass
            (v := z) α M obs f ∧
        IdentifiesLanguageFromPositiveData
          (correctedConcreteCertifiedWorkingGrammarHypLanguage
            obs' f)
          (correctedConcreteCertifiedWorkingGrammarLearner
            hα obs' f)
          language ∧
        language ∈
          CorrectedConcreteCertifiedRankProfileClass
            (α := α)
            (M := M')
            obs' f
            (startRootedTargetCertifiedDescriptionRank
              (v := z) hα obs' f hFine) ∧
        ∃
          C :
            CorrectedConcreteCertifiedWorkingGrammarHypothesis
              α M' obs' f,
          C.output.grammar.StringLanguage =
              language ∧
            C.bits.length <=
              correctedConcreteCertifiedRankBitBudget
                (startRootedTargetCertifiedDescriptionRank
                  (v := z) hα obs' f hFine)
                f ∧
            C.canonicalSearch.length <=
              correctedConcreteCertifiedRankSearchBudget
                (startRootedTargetCertifiedDescriptionRank
                  (v := z) hα obs' f hFine)
                f := by

  rcases hEssential with
    ⟨language, hGain⟩

  exact
    ⟨language,
      hGain.1,
      hGain.2,
      correctedConcreteCertifiedWorkingGrammarLearner_identifies_startRootedTargetClass
        (v := z)
        hα obs' f
        language hGain.1,
      startRootedTarget_mem_minimumCertifiedDescriptionRankProfile
        (v := z)
        hα obs' f hGain.1,
      startRootedTarget_exists_output_at_minimumCertifiedDescriptionRank
        (v := z)
        hα obs' f hGain.1⟩

/-- Under a redundant refinement, both certified learners identify one and the
same semantic target class and no strict gain language exists. -/
theorem redundantObservationRefinement_certifiedLearning_package
    (hRedundant :
      CorrectedConcreteObservationRefinementRedundant
        (z := z) α M M' obs obs' f) :
    (StartRootedCorrectedConcreteTargetClass
        (v := z) α M obs f =
      StartRootedCorrectedConcreteTargetClass
        (v := z) α M' obs' f) ∧
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
      (StartRootedCorrectedConcreteObservationGainClass
          (z := z) α M M' obs obs' f =
        ∅) := by

  exact
    ⟨(observationRefinementRedundant_iff_targetClass_eq
        (z := z)
        f r).mp
        hRedundant,
      correctedConcreteCertifiedWorkingGrammarLearner_identifies_startRootedTargetClass
        (v := z)
        hα obs f,
      refinedCertifiedLearner_identifies_coarserTargetClass
        (z := z)
        hα obs obs' f r,
      hRedundant⟩

/-- Certified-learning dichotomy for one refinement step. -/
theorem observationRefinement_certifiedAblationDichotomy :
    (CorrectedConcreteObservationRefinementRedundant
        (z := z) α M M' obs obs' f →
      StartRootedCorrectedConcreteTargetClass
          (v := z) α M obs f =
        StartRootedCorrectedConcreteTargetClass
          (v := z) α M' obs' f) ∧
      (CorrectedConcreteObservationRefinementEssential
        (z := z) α M M' obs obs' f →
      ∃
        (language : Set (Word α))
        (hFine :
          language ∈
            StartRootedCorrectedConcreteTargetClass
              (v := z) α M' obs' f),
        language ∉
            StartRootedCorrectedConcreteTargetClass
              (v := z) α M obs f ∧
          IdentifiesLanguageFromPositiveData
            (correctedConcreteCertifiedWorkingGrammarHypLanguage
              obs' f)
            (correctedConcreteCertifiedWorkingGrammarLearner
              hα obs' f)
            language) := by

  constructor

  · intro hRedundant

    exact
      (observationRefinementRedundant_iff_targetClass_eq
        (z := z)
        f r).mp
        hRedundant

  · intro hEssential

    rcases
        essentialObservationRefinement_exists_newCertifiedTarget
          (z := z)
          hα obs obs' f r hEssential with
      ⟨language,
        hFine,
        hNotCoarse,
        hIdentifies,
        hProfile,
        C,
        hLanguage,
        hBits,
        hSearch⟩

    exact
      ⟨language,
        hFine,
        hNotCoarse,
        hIdentifies⟩

end EssentialRefinementCertifiedWitness


section RefinementChainAblation

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

/-- The direct refinement is essential exactly when at least one incremental
refinement step is essential. -/
theorem observationRefinementChain_directEssential_iff_incremental :
    CorrectedConcreteObservationRefinementEssential
        (z := z) α M₀ M₂ obs₀ obs₂ f ↔
      CorrectedConcreteObservationRefinementEssential
          (z := z) α M₀ M₁ obs₀ obs₁ f ∨
        CorrectedConcreteObservationRefinementEssential
          (z := z) α M₁ M₂ obs₁ obs₂ f := by

  constructor

  · intro hDirect

    rcases hDirect with
      ⟨language, hGain⟩

    have hIncremental :
        language ∈
          StartRootedCorrectedConcreteObservationGainClass
              (z := z) α M₀ M₁ obs₀ obs₁ f ∪
            StartRootedCorrectedConcreteObservationGainClass
              (z := z) α M₁ M₂ obs₁ obs₂ f := by

      rw [
        ← observationGainClass_compose_eq_union
          (z := z)
          f r₀₁ r₁₂
      ]

      exact hGain

    rcases hIncremental with
      hFirst | hSecond

    · exact
        Or.inl
          ⟨language, hFirst⟩

    · exact
        Or.inr
          ⟨language, hSecond⟩

  · intro hIncremental

    rcases hIncremental with
      hFirst | hSecond

    · rcases hFirst with
        ⟨language, hGain⟩

      refine
        ⟨language,
          ?_⟩

      rw [
        observationGainClass_compose_eq_union
          (z := z)
          f r₀₁ r₁₂
      ]

      exact
        Or.inl hGain

    · rcases hSecond with
        ⟨language, hGain⟩

      refine
        ⟨language,
          ?_⟩

      rw [
        observationGainClass_compose_eq_union
          (z := z)
          f r₀₁ r₁₂
      ]

      exact
        Or.inr hGain

/-- The direct refinement is redundant exactly when both incremental steps are
redundant. -/
theorem observationRefinementChain_directRedundant_iff_incremental :
    CorrectedConcreteObservationRefinementRedundant
        (z := z) α M₀ M₂ obs₀ obs₂ f ↔
      CorrectedConcreteObservationRefinementRedundant
          (z := z) α M₀ M₁ obs₀ obs₁ f ∧
        CorrectedConcreteObservationRefinementRedundant
          (z := z) α M₁ M₂ obs₁ obs₂ f := by

  constructor

  · intro hDirect

    have hNoDirect :
        ¬
          CorrectedConcreteObservationRefinementEssential
            (z := z) α M₀ M₂ obs₀ obs₂ f :=
      (observationRefinementRedundant_iff_not_essential
        (z := z)
        (α := α)
        (M := M₀)
        (M' := M₂)
        (obs := obs₀)
        (obs' := obs₂)
        (f := f)).mp
        hDirect

    have hNoFirst :
        ¬
          CorrectedConcreteObservationRefinementEssential
            (z := z) α M₀ M₁ obs₀ obs₁ f := by

      intro hFirst

      exact
        hNoDirect
          ((observationRefinementChain_directEssential_iff_incremental
            (z := z)
            f r₀₁ r₁₂).mpr
            (Or.inl hFirst))

    have hNoSecond :
        ¬
          CorrectedConcreteObservationRefinementEssential
            (z := z) α M₁ M₂ obs₁ obs₂ f := by

      intro hSecond

      exact
        hNoDirect
          ((observationRefinementChain_directEssential_iff_incremental
            (z := z)
            f r₀₁ r₁₂).mpr
            (Or.inr hSecond))

    exact
      ⟨(observationRefinementRedundant_iff_not_essential
          (z := z)
          (α := α)
          (M := M₀)
          (M' := M₁)
          (obs := obs₀)
          (obs' := obs₁)
          (f := f)).mpr
          hNoFirst,
        (observationRefinementRedundant_iff_not_essential
          (z := z)
          (α := α)
          (M := M₁)
          (M' := M₂)
          (obs := obs₁)
          (obs' := obs₂)
          (f := f)).mpr
          hNoSecond⟩

  · intro hIncremental

    apply
      (observationRefinementRedundant_iff_not_essential
        (z := z)
        (α := α)
        (M := M₀)
        (M' := M₂)
        (obs := obs₀)
        (obs' := obs₂)
        (f := f)).mpr

    intro hDirect

    rcases
        (observationRefinementChain_directEssential_iff_incremental
          (z := z)
          f r₀₁ r₁₂).mp
          hDirect with
      hFirst | hSecond

    · exact
        ((observationRefinementRedundant_iff_not_essential
          (z := z)
          (α := α)
          (M := M₀)
          (M' := M₁)
          (obs := obs₀)
          (obs' := obs₁)
          (f := f)).mp
          hIncremental.1)
          hFirst

    · exact
        ((observationRefinementRedundant_iff_not_essential
          (z := z)
          (α := α)
          (M := M₁)
          (M' := M₂)
          (obs := obs₁)
          (obs' := obs₂)
          (f := f)).mp
          hIncremental.2)
          hSecond

/-- Equality of the coarsest and finest target classes is equivalent to equality
at both incremental steps. -/
theorem observationRefinementChain_endpointTargetClass_eq_iff_incremental :
    (StartRootedCorrectedConcreteTargetClass
        (v := z) α M₀ obs₀ f =
      StartRootedCorrectedConcreteTargetClass
        (v := z) α M₂ obs₂ f) ↔
      (StartRootedCorrectedConcreteTargetClass
          (v := z) α M₀ obs₀ f =
        StartRootedCorrectedConcreteTargetClass
          (v := z) α M₁ obs₁ f) ∧
      (StartRootedCorrectedConcreteTargetClass
          (v := z) α M₁ obs₁ f =
        StartRootedCorrectedConcreteTargetClass
          (v := z) α M₂ obs₂ f) := by

  constructor

  · intro hEndpoints

    have hDirectRedundant :
        CorrectedConcreteObservationRefinementRedundant
          (z := z) α M₀ M₂ obs₀ obs₂ f :=
      (observationRefinementRedundant_iff_targetClass_eq
        (z := z)
        f
        (r₀₁.compose r₁₂)).mpr
        hEndpoints

    have hIncremental :
        CorrectedConcreteObservationRefinementRedundant
              (z := z) α M₀ M₁ obs₀ obs₁ f ∧
          CorrectedConcreteObservationRefinementRedundant
              (z := z) α M₁ M₂ obs₁ obs₂ f :=
      (observationRefinementChain_directRedundant_iff_incremental
        (z := z)
        f r₀₁ r₁₂).mp
        hDirectRedundant

    exact
      ⟨(observationRefinementRedundant_iff_targetClass_eq
          (z := z)
          f r₀₁).mp
          hIncremental.1,
        (observationRefinementRedundant_iff_targetClass_eq
          (z := z)
          f r₁₂).mp
          hIncremental.2⟩

  · intro hIncrementalClasses

    have hIncrementalRedundant :
        CorrectedConcreteObservationRefinementRedundant
              (z := z) α M₀ M₁ obs₀ obs₁ f ∧
          CorrectedConcreteObservationRefinementRedundant
              (z := z) α M₁ M₂ obs₁ obs₂ f :=
      ⟨(observationRefinementRedundant_iff_targetClass_eq
          (z := z)
          f r₀₁).mpr
          hIncrementalClasses.1,
        (observationRefinementRedundant_iff_targetClass_eq
          (z := z)
          f r₁₂).mpr
          hIncrementalClasses.2⟩

    exact
      (observationRefinementRedundant_iff_targetClass_eq
        (z := z)
        f
        (r₀₁.compose r₁₂)).mp
        ((observationRefinementChain_directRedundant_iff_incremental
          (z := z)
          f r₀₁ r₁₂).mpr
          hIncrementalRedundant)

/-- A direct endpoint change occurs exactly when at least one incremental step
changes its target class. -/
theorem observationRefinementChain_endpointTargetClass_ne_iff_incremental :
    (StartRootedCorrectedConcreteTargetClass
        (v := z) α M₀ obs₀ f ≠
      StartRootedCorrectedConcreteTargetClass
        (v := z) α M₂ obs₂ f) ↔
      (StartRootedCorrectedConcreteTargetClass
          (v := z) α M₀ obs₀ f ≠
        StartRootedCorrectedConcreteTargetClass
          (v := z) α M₁ obs₁ f) ∨
      (StartRootedCorrectedConcreteTargetClass
          (v := z) α M₁ obs₁ f ≠
        StartRootedCorrectedConcreteTargetClass
          (v := z) α M₂ obs₂ f) := by

  constructor

  · intro hEndpoints

    have hDirectEssential :
        CorrectedConcreteObservationRefinementEssential
          (z := z) α M₀ M₂ obs₀ obs₂ f :=
      (observationRefinementEssential_iff_targetClass_ne
        (z := z)
        f
        (r₀₁.compose r₁₂)).mpr
        hEndpoints

    rcases
        (observationRefinementChain_directEssential_iff_incremental
          (z := z)
          f r₀₁ r₁₂).mp
          hDirectEssential with
      hFirst | hSecond

    · exact
        Or.inl
          ((observationRefinementEssential_iff_targetClass_ne
            (z := z)
            f r₀₁).mp
            hFirst)

    · exact
        Or.inr
          ((observationRefinementEssential_iff_targetClass_ne
            (z := z)
            f r₁₂).mp
            hSecond)

  · intro hIncremental

    apply
      (observationRefinementEssential_iff_targetClass_ne
        (z := z)
        f
        (r₀₁.compose r₁₂)).mp

    apply
      (observationRefinementChain_directEssential_iff_incremental
        (z := z)
        f r₀₁ r₁₂).mpr

    rcases hIncremental with
      hFirst | hSecond

    · exact
        Or.inl
          ((observationRefinementEssential_iff_targetClass_ne
            (z := z)
            f r₀₁).mpr
            hFirst)

    · exact
        Or.inr
          ((observationRefinementEssential_iff_targetClass_ne
            (z := z)
            f r₁₂).mpr
            hSecond)

/-- Compact three-stage interface-ablation package. -/
theorem observationRefinementChain_ablation_package :
    (CorrectedConcreteObservationRefinementEssential
          (z := z) α M₀ M₂ obs₀ obs₂ f ↔
        CorrectedConcreteObservationRefinementEssential
            (z := z) α M₀ M₁ obs₀ obs₁ f ∨
          CorrectedConcreteObservationRefinementEssential
            (z := z) α M₁ M₂ obs₁ obs₂ f) ∧
      (CorrectedConcreteObservationRefinementRedundant
          (z := z) α M₀ M₂ obs₀ obs₂ f ↔
        CorrectedConcreteObservationRefinementRedundant
            (z := z) α M₀ M₁ obs₀ obs₁ f ∧
          CorrectedConcreteObservationRefinementRedundant
            (z := z) α M₁ M₂ obs₁ obs₂ f) ∧
      ((StartRootedCorrectedConcreteTargetClass
          (v := z) α M₀ obs₀ f =
        StartRootedCorrectedConcreteTargetClass
          (v := z) α M₂ obs₂ f) ↔
        (StartRootedCorrectedConcreteTargetClass
            (v := z) α M₀ obs₀ f =
          StartRootedCorrectedConcreteTargetClass
            (v := z) α M₁ obs₁ f) ∧
        (StartRootedCorrectedConcreteTargetClass
            (v := z) α M₁ obs₁ f =
          StartRootedCorrectedConcreteTargetClass
            (v := z) α M₂ obs₂ f)) ∧
      Set.Disjoint
        (StartRootedCorrectedConcreteObservationGainClass
          (z := z) α M₀ M₁ obs₀ obs₁ f)
        (StartRootedCorrectedConcreteObservationGainClass
          (z := z) α M₁ M₂ obs₁ obs₂ f) := by

  exact
    ⟨observationRefinementChain_directEssential_iff_incremental
        (z := z)
        f r₀₁ r₁₂,
      observationRefinementChain_directRedundant_iff_incremental
        (z := z)
        f r₀₁ r₁₂,
      observationRefinementChain_endpointTargetClass_eq_iff_incremental
        (z := z)
        f r₀₁ r₁₂,
      observationGainClasses_incremental_disjoint
        (z := z)
        f r₀₁ r₁₂⟩

end RefinementChainAblation


section ObservationAblationFinalPackage

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
variable (r : Refines obs obs')

/-- Final semantic and certified-learning interface-ablation theorem. -/
theorem
    correctedConcreteCertifiedWorkingGrammar_observationAblation_package :
    (CorrectedConcreteObservationRefinementRedundant
          (z := z) α M M' obs obs' f ↔
        StartRootedCorrectedConcreteTargetClass
            (v := z) α M obs f =
          StartRootedCorrectedConcreteTargetClass
            (v := z) α M' obs' f) ∧
      (CorrectedConcreteObservationRefinementEssential
          (z := z) α M M' obs obs' f ↔
        (StartRootedCorrectedConcreteTargetClass
            (v := z) α M obs f ⊆
          StartRootedCorrectedConcreteTargetClass
            (v := z) α M' obs' f) ∧
        (StartRootedCorrectedConcreteTargetClass
            (v := z) α M obs f ≠
          StartRootedCorrectedConcreteTargetClass
            (v := z) α M' obs' f)) ∧
      (CorrectedConcreteObservationRefinementEssential
          (z := z) α M M' obs obs' f ↔
        (StartRootedCorrectedConcreteObservationFailureClass
            (z := z) α M' obs' f ⊆
          StartRootedCorrectedConcreteObservationFailureClass
            (z := z) α M obs f) ∧
        (StartRootedCorrectedConcreteObservationFailureClass
            (z := z) α M' obs' f ≠
          StartRootedCorrectedConcreteObservationFailureClass
            (z := z) α M obs f)) ∧
      (CorrectedConcreteObservationRefinementEssential
          (z := z) α M M' obs obs' f →
        ∃
          (language : Set (Word α))
          (hFine :
            language ∈
              StartRootedCorrectedConcreteTargetClass
                (v := z) α M' obs' f),
          language ∉
              StartRootedCorrectedConcreteTargetClass
                (v := z) α M obs f ∧
            IdentifiesLanguageFromPositiveData
              (correctedConcreteCertifiedWorkingGrammarHypLanguage
                obs' f)
              (correctedConcreteCertifiedWorkingGrammarLearner
                hα obs' f)
              language ∧
            ∃
              C :
                CorrectedConcreteCertifiedWorkingGrammarHypothesis
                  α M' obs' f,
              C.output.grammar.StringLanguage =
                  language ∧
                C.bits.length <=
                  correctedConcreteCertifiedRankBitBudget
                    (startRootedTargetCertifiedDescriptionRank
                      (v := z) hα obs' f hFine)
                    f ∧
                C.canonicalSearch.length <=
                  correctedConcreteCertifiedRankSearchBudget
                    (startRootedTargetCertifiedDescriptionRank
                      (v := z) hα obs' f hFine)
                    f) := by

  refine
    ⟨observationRefinementRedundant_iff_targetClass_eq
        (z := z)
        f r,
      observationRefinementEssential_iff_strict_targetClass_growth
        (z := z)
        f r,
      observationRefinementEssential_iff_strict_failureClass_shrinkage
        (z := z)
        f r,
      ?_⟩

  intro hEssential

  rcases
      essentialObservationRefinement_exists_newCertifiedTarget
        (z := z)
        hα obs obs' f r hEssential with
    ⟨language,
      hFine,
      hNotCoarse,
      hIdentifies,
      hProfile,
      C,
      hLanguage,
      hBits,
      hSearch⟩

  exact
    ⟨language,
      hFine,
      hNotCoarse,
      hIdentifies,
      C,
      hLanguage,
      hBits,
      hSearch⟩

end ObservationAblationFinalPackage

end MCFG
