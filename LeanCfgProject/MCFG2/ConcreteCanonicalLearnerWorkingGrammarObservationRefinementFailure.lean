/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG2.ConcreteCanonicalLearnerWorkingGrammarCertifiedDescriptionRankObstructions

/-!
# ConcreteCanonicalLearnerWorkingGrammarObservationRefinementFailure.lean

The preceding files develop certified finite descriptions, minimum simultaneous
description ranks, and profile obstructions for one fixed finite observation
map.

This file varies the observation map.

Let

```lean
r : Refines obs obs'
```

mean that `obs'` is finer than `obs`: a multiplication-preserving map from the
finer monoid to the coarser monoid commutes with all letter observations.

The fixed-observation substitutability condition is monotone in this direction.
Therefore every target witness for the coarser observation is also a target
witness for the finer observation.

## Target-class monotonicity

We define an explicit witness transport

```lean
StartRootedCorrectedConcreteTargetWitness.refineObservation.
```

It keeps

* the same finite nonterminal type;
* the same actual working grammar;
* the same exact-working proof;
* the same semantic start-rooted-normal proof;
* the same fan-out proof; and
* the same target-language equality.

Only the fixed-observation substitutability proof is transported along `r`.

Consequently

```text
coarse target class ⊆ fine target class.
```

## Observation failure and gain

The observation-failure class is the complement of the corresponding semantic
target class.

Refinement has the contravariant failure law

```text
failure under the finer observation
  ⊆
failure under the coarser observation.
```

Equivalently, refinement can create target languages but cannot destroy them.

The strict observation-gain class consists of languages that

```text
belong to the finer target class
and
do not belong to the coarser target class.
```

Under refinement, the finer target class decomposes exactly as

```text
finer target class
  =
coarser target class ∪ strict gain class.
```

The corresponding observation-loss class is empty.

## Certified learning

When both observation monoids are finite and decidable, the certified learner
for the finer observation identifies

* the entire finer target class;
* the entire coarser target class; and
* the strict gain class.

For every strict-gain target, the finer observation supplies

* a minimum simultaneous certified-description rank;
* exact membership in the finer rank profile at that minimum rank;
* a characteristic-rank upper bound; and
* one exact certified output meeting the minimum-rank bit/search budgets.

At the same time the language is formally outside the coarser semantic target
class.  This is the precise observation-failure statement available without
postulating an explicit strict-gain example.

## Important boundary

The certified output types, presentation types, decoders, and canonical
searches depend on the observation monoid.  Hence this file does not claim a
direct inclusion between the two certified profile classes at equal numerical
rank.  What transports canonically is the semantic target witness and target
class.  Certified descriptions are then reconstructed by the learner belonging
to the chosen observation.

No target grammar is supplied to either learner.
No `sorry`, `admit`, or `axiom` is used.
-/

namespace MCFG

universe u v w z


section StartRootedTargetWitnessObservationRefinement

variable {α : Type u}
variable {M : Type v}
variable {M' : Type w}
variable [Monoid M]
variable [Monoid M']
variable {obs : α → M}
variable {obs' : α → M'}
variable {f : Nat}
variable {L : Set (Word α)}

/-- Transport a semantic start-rooted target witness from a coarser observation
to a finer observation while retaining the same actual grammar. -/
def StartRootedCorrectedConcreteTargetWitness.refineObservation
    (r : Refines obs obs')
    (W :
      StartRootedCorrectedConcreteTargetWitness
        (v := z) α M obs f L) :
    StartRootedCorrectedConcreteTargetWitness
      (v := z) α M' obs' f L where

  nonterminal :=
    W.nonterminal

  fintypeNonterminal :=
    W.fintypeNonterminal

  grammar :=
    W.grammar

  exactWorking :=
    W.exactWorking

  startRooted :=
    W.startRooted

  fanout :=
    W.fanout

  substitutable :=
    fixedNamedTupleSubstitutable_of_refines
      r W.substitutable

  language_eq :=
    W.language_eq

/-- Observation refinement preserves the underlying actual working grammar. -/
@[simp] theorem
    StartRootedCorrectedConcreteTargetWitness.refineObservation_grammar
    (r : Refines obs obs')
    (W :
      StartRootedCorrectedConcreteTargetWitness
        (v := z) α M obs f L) :
    (W.refineObservation r).grammar =
      W.grammar := by

  rfl

/-- Observation refinement preserves the exact target-language equation. -/
@[simp] theorem
    StartRootedCorrectedConcreteTargetWitness.refineObservation_language_eq
    (r : Refines obs obs')
    (W :
      StartRootedCorrectedConcreteTargetWitness
        (v := z) α M obs f L) :
    (W.refineObservation r).grammar.StringLanguage =
      L := by

  exact
    W.language_eq

/-- Every language represented under the coarser observation remains represented
under the finer observation. -/
theorem
    startRootedCorrectedConcreteTargetClass_subset_of_refines
    (r : Refines obs obs') :
    StartRootedCorrectedConcreteTargetClass
        (v := z) α M obs f ⊆
      StartRootedCorrectedConcreteTargetClass
        (v := z) α M' obs' f := by

  intro language hlanguage

  rcases hlanguage with
    ⟨W⟩

  exact
    ⟨W.refineObservation r⟩

/-- Pointwise success transfer from a coarser observation to a finer one. -/
theorem
    startRootedCorrectedConcreteTarget_mem_of_refines
    (r : Refines obs obs')
    (hL :
      L ∈
        StartRootedCorrectedConcreteTargetClass
          (v := z) α M obs f) :
    L ∈
      StartRootedCorrectedConcreteTargetClass
        (v := z) α M' obs' f := by

  exact
    startRootedCorrectedConcreteTargetClass_subset_of_refines
      r hL

end StartRootedTargetWitnessObservationRefinement


section ObservationFailureAndGainClasses

variable (α : Type u)
variable (M : Type v)
variable (M' : Type w)
variable [Monoid M]
variable [Monoid M']
variable (obs : α → M)
variable (obs' : α → M')
variable (f : Nat)

/-- Languages not represented by the semantic target class under one fixed
observation. -/
def StartRootedCorrectedConcreteObservationFailureClass :
    Set (Set (Word α)) :=
  {L |
    L ∉
      StartRootedCorrectedConcreteTargetClass
        (v := z) α M obs f}

/-- Languages gained by replacing `obs` with `obs'`: represented under `obs'`
but not under `obs`. -/
def StartRootedCorrectedConcreteObservationGainClass :
    Set (Set (Word α)) :=
  {L |
    L ∈
        StartRootedCorrectedConcreteTargetClass
          (v := z) α M' obs' f ∧
      L ∉
        StartRootedCorrectedConcreteTargetClass
          (v := z) α M obs f}

/-- Languages lost by replacing `obs` with `obs'`: represented under `obs` but
not under `obs'`.  Under an actual refinement this class is empty. -/
def StartRootedCorrectedConcreteObservationLossClass :
    Set (Set (Word α)) :=
  {L |
    L ∈
        StartRootedCorrectedConcreteTargetClass
          (v := z) α M obs f ∧
      L ∉
        StartRootedCorrectedConcreteTargetClass
          (v := z) α M' obs' f}

variable {α M M' obs obs' f}

/-- Failure under a finer observation implies failure under the coarser
observation. -/
theorem
    observationFailure_of_finer_implies_failure_of_coarser
    (r : Refines obs obs')
    {L : Set (Word α)}
    (hfailure :
      L ∈
        StartRootedCorrectedConcreteObservationFailureClass
          (z := z) α M' obs' f) :
    L ∈
      StartRootedCorrectedConcreteObservationFailureClass
        (z := z) α M obs f := by

  intro hcoarse

  exact
    hfailure
      (startRootedCorrectedConcreteTarget_mem_of_refines
        (z := z) r hcoarse)

/-- Observation-failure classes are contravariantly monotone under
refinement. -/
theorem
    observationFailureClass_subset_of_refines
    (r : Refines obs obs') :
    StartRootedCorrectedConcreteObservationFailureClass
        (z := z) α M' obs' f ⊆
      StartRootedCorrectedConcreteObservationFailureClass
        (z := z) α M obs f := by

  intro L hL

  exact
    observationFailure_of_finer_implies_failure_of_coarser
      (z := z) r hL

/-- Strict observation gains are always represented under the finer
observation. -/
theorem
    observationGainClass_subset_finerTargetClass :
    StartRootedCorrectedConcreteObservationGainClass
        (z := z) α M M' obs obs' f ⊆
      StartRootedCorrectedConcreteTargetClass
        (v := z) α M' obs' f := by

  intro L hL

  exact hL.1

/-- Strict observation gains are disjoint from the coarser target class. -/
theorem
    observationGainClass_disjoint_coarserTargetClass :
    Set.Disjoint
      (StartRootedCorrectedConcreteObservationGainClass
        (z := z) α M M' obs obs' f)
      (StartRootedCorrectedConcreteTargetClass
        (v := z) α M obs f) := by

  rw [Set.disjoint_left]

  intro L hgain hcoarse

  exact
    hgain.2 hcoarse

/-- Under refinement, no language is lost. -/
theorem
    observationLossClass_eq_empty_of_refines
    (r : Refines obs obs') :
    StartRootedCorrectedConcreteObservationLossClass
        (z := z) α M M' obs obs' f =
      ∅ := by

  ext L

  constructor

  · intro hLoss

    rcases hLoss with
      ⟨hcoarse, hnotFine⟩

    exact
      False.elim
        (hnotFine
          (startRootedCorrectedConcreteTarget_mem_of_refines
            (z := z) r hcoarse))

  · intro hEmpty

    simp at hEmpty

/-- Under refinement, the finer target class is exactly the union of the
coarser target class and the strict observation-gain class. -/
theorem
    finerTargetClass_eq_coarser_union_observationGainClass
    (r : Refines obs obs') :
    StartRootedCorrectedConcreteTargetClass
        (v := z) α M' obs' f =
      StartRootedCorrectedConcreteTargetClass
          (v := z) α M obs f ∪
        StartRootedCorrectedConcreteObservationGainClass
          (z := z) α M M' obs obs' f := by

  ext L

  constructor

  · intro hFine

    by_cases hCoarse :
        L ∈
          StartRootedCorrectedConcreteTargetClass
            (v := z) α M obs f

    · exact
        Or.inl hCoarse

    · exact
        Or.inr
          ⟨hFine,
            hCoarse⟩

  · intro hUnion

    rcases hUnion with
      hCoarse | hGain

    · exact
        startRootedCorrectedConcreteTarget_mem_of_refines
          (z := z) r hCoarse

    · exact
        hGain.1

/-- The finer target class consists of old targets and genuinely new targets,
with no overlap between the two parts. -/
theorem
    finerTargetClass_observationGain_decomposition_package
    (r : Refines obs obs') :
    StartRootedCorrectedConcreteTargetClass
        (v := z) α M obs f ⊆
      StartRootedCorrectedConcreteTargetClass
        (v := z) α M' obs' f ∧
      Set.Disjoint
        (StartRootedCorrectedConcreteObservationGainClass
          (z := z) α M M' obs obs' f)
        (StartRootedCorrectedConcreteTargetClass
          (v := z) α M obs f) ∧
      StartRootedCorrectedConcreteTargetClass
          (v := z) α M' obs' f =
        StartRootedCorrectedConcreteTargetClass
            (v := z) α M obs f ∪
          StartRootedCorrectedConcreteObservationGainClass
            (z := z) α M M' obs obs' f ∧
      StartRootedCorrectedConcreteObservationLossClass
          (z := z) α M M' obs obs' f =
        ∅ := by

  exact
    ⟨startRootedCorrectedConcreteTargetClass_subset_of_refines
        (z := z) r,
      observationGainClass_disjoint_coarserTargetClass
        (z := z),
      finerTargetClass_eq_coarser_union_observationGainClass
        (z := z) r,
      observationLossClass_eq_empty_of_refines
        (z := z) r⟩

end ObservationFailureAndGainClasses


section CertifiedLearnerObservationRefinement

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

/-- The certified learner built from the finer observation identifies every
language already represented under the coarser observation. -/
theorem
    refinedCertifiedLearner_identifies_coarserTargetClass :
    IdentifiesClassFromPositiveData
      (correctedConcreteCertifiedWorkingGrammarHypLanguage
        obs' f)
      (correctedConcreteCertifiedWorkingGrammarLearner
        hα obs' f)
      (StartRootedCorrectedConcreteTargetClass
        (v := z) α M obs f) := by

  intro L hCoarse

  exact
    correctedConcreteCertifiedWorkingGrammarLearner_identifies_startRootedTargetClass
      (v := z) hα obs' f
      L
      (startRootedCorrectedConcreteTarget_mem_of_refines
        (z := z) r hCoarse)

/-- The certified learner built from the finer observation identifies every
strict observation-gain language. -/
theorem
    refinedCertifiedLearner_identifies_observationGainClass :
    IdentifiesClassFromPositiveData
      (correctedConcreteCertifiedWorkingGrammarHypLanguage
        obs' f)
      (correctedConcreteCertifiedWorkingGrammarLearner
        hα obs' f)
      (StartRootedCorrectedConcreteObservationGainClass
        (z := z) α M M' obs obs' f) := by

  intro L hGain

  exact
    correctedConcreteCertifiedWorkingGrammarLearner_identifies_startRootedTargetClass
      (v := z) hα obs' f
      L hGain.1

/-- Every coarser target is identified by both the coarse and the refined
certified learners. -/
theorem
    coarserTarget_identified_by_both_certifiedLearners
    {L : Set (Word α)}
    (hL :
      L ∈
        StartRootedCorrectedConcreteTargetClass
          (v := z) α M obs f) :
    IdentifiesLanguageFromPositiveData
        (correctedConcreteCertifiedWorkingGrammarHypLanguage
          obs f)
        (correctedConcreteCertifiedWorkingGrammarLearner
          hα obs f)
        L ∧
      IdentifiesLanguageFromPositiveData
        (correctedConcreteCertifiedWorkingGrammarHypLanguage
          obs' f)
        (correctedConcreteCertifiedWorkingGrammarLearner
          hα obs' f)
        L := by

  exact
    ⟨correctedConcreteCertifiedWorkingGrammarLearner_identifies_startRootedTargetClass
        (v := z) hα obs f L hL,
      correctedConcreteCertifiedWorkingGrammarLearner_identifies_startRootedTargetClass
        (v := z) hα obs' f L
        (startRootedCorrectedConcreteTarget_mem_of_refines
          (z := z) r hL)⟩

/-- A strict-gain language has a refined-observation minimum certified
description rank, while remaining outside the coarser semantic target class. -/
theorem observationGain_target_refinedDescriptionRank_package
    {L : Set (Word α)}
    (hGain :
      L ∈
        StartRootedCorrectedConcreteObservationGainClass
          (z := z) α M M' obs obs' f) :
    L ∉
        StartRootedCorrectedConcreteTargetClass
          (v := z) α M obs f ∧
      L ∈
        CorrectedConcreteCertifiedRankProfileClass
          (α := α)
          (M := M')
          obs' f
          (startRootedTargetCertifiedDescriptionRank
            (v := z) hα obs' f hGain.1) ∧
      startRootedTargetCertifiedDescriptionRank
          (v := z) hα obs' f hGain.1 <=
        startRootedTargetCharacteristicRank
          (v := z) hα obs' f hGain.1 ∧
      ∃
        C :
          CorrectedConcreteCertifiedWorkingGrammarHypothesis
            α M' obs' f,
        C.output.grammar.StringLanguage = L ∧
          C.bits.length <=
            correctedConcreteCertifiedRankBitBudget
              (startRootedTargetCertifiedDescriptionRank
                (v := z) hα obs' f hGain.1)
              f ∧
          C.canonicalSearch.length <=
            correctedConcreteCertifiedRankSearchBudget
              (startRootedTargetCertifiedDescriptionRank
                (v := z) hα obs' f hGain.1)
              f := by

  exact
    ⟨hGain.2,
      startRootedTarget_mem_minimumCertifiedDescriptionRankProfile
        (v := z) hα obs' f hGain.1,
      startRootedTargetCertifiedDescriptionRank_le_characteristicRank
        (v := z) hα obs' f hGain.1,
      startRootedTarget_exists_output_at_minimumCertifiedDescriptionRank
        (v := z) hα obs' f hGain.1⟩

/-- Every strict observation-gain language belongs to some finite certified
rank profile for the refined observation. -/
theorem
    observationGainClass_subset_exists_refinedCertifiedRankProfile :
    StartRootedCorrectedConcreteObservationGainClass
        (z := z) α M M' obs obs' f ⊆
      {L : Set (Word α) |
        ∃ rank : Nat,
          L ∈
            CorrectedConcreteCertifiedRankProfileClass
              (α := α)
              (M := M')
              obs' f rank} := by

  intro L hGain

  exact
    ⟨startRootedTargetCertifiedDescriptionRank
        (v := z) hα obs' f hGain.1,
      startRootedTarget_mem_minimumCertifiedDescriptionRankProfile
        (v := z) hα obs' f hGain.1⟩

end CertifiedLearnerObservationRefinement


section ObservationRefinementFailurePackages

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

/-- Final observation-refinement, failure, strict-gain, and certified-learning
package. -/
theorem
    correctedConcreteCertifiedWorkingGrammar_observationRefinementFailure_package :
    (StartRootedCorrectedConcreteTargetClass
        (v := z) α M obs f ⊆
      StartRootedCorrectedConcreteTargetClass
        (v := z) α M' obs' f) ∧
      (StartRootedCorrectedConcreteObservationFailureClass
          (z := z) α M' obs' f ⊆
        StartRootedCorrectedConcreteObservationFailureClass
          (z := z) α M obs f) ∧
      (StartRootedCorrectedConcreteObservationLossClass
          (z := z) α M M' obs obs' f =
        ∅) ∧
      (StartRootedCorrectedConcreteTargetClass
          (v := z) α M' obs' f =
        StartRootedCorrectedConcreteTargetClass
            (v := z) α M obs f ∪
          StartRootedCorrectedConcreteObservationGainClass
            (z := z) α M M' obs obs' f) ∧
      IdentifiesClassFromPositiveData
        (correctedConcreteCertifiedWorkingGrammarHypLanguage
          obs' f)
        (correctedConcreteCertifiedWorkingGrammarLearner
          hα obs' f)
        (StartRootedCorrectedConcreteTargetClass
          (v := z) α M obs f) ∧
      IdentifiesClassFromPositiveData
        (correctedConcreteCertifiedWorkingGrammarHypLanguage
          obs' f)
        (correctedConcreteCertifiedWorkingGrammarLearner
          hα obs' f)
        (StartRootedCorrectedConcreteObservationGainClass
          (z := z) α M M' obs obs' f) ∧
      (StartRootedCorrectedConcreteObservationGainClass
          (z := z) α M M' obs obs' f ⊆
        {L : Set (Word α) |
          ∃ rank : Nat,
            L ∈
              CorrectedConcreteCertifiedRankProfileClass
                (α := α)
                (M := M')
                obs' f rank}) := by

  exact
    ⟨startRootedCorrectedConcreteTargetClass_subset_of_refines
        (z := z) r,
      observationFailureClass_subset_of_refines
        (z := z) r,
      observationLossClass_eq_empty_of_refines
        (z := z) r,
      finerTargetClass_eq_coarser_union_observationGainClass
        (z := z) r,
      refinedCertifiedLearner_identifies_coarserTargetClass
        (z := z) hα obs obs' f r,
      refinedCertifiedLearner_identifies_observationGainClass
        (z := z) hα obs obs' f r,
      observationGainClass_subset_exists_refinedCertifiedRankProfile
        (z := z) hα obs obs' f r⟩

end ObservationRefinementFailurePackages

end MCFG
