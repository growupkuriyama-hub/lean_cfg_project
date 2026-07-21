/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG.CharacteristicSampleGlobalPaperWitnessTheorem

/-!
# CharacteristicSampleBoundedGlobalPaperTheorem.lean

Ninety-fourth clean Lean experiment for the fixed-observation MCFG project.

`CharacteristicSampleGlobalPaperWitnessTheorem.lean` hid both the trimmed
output-type presentation and its pre-core datum, but the fanout bound

```lean
f : Nat
```

was still an external parameter.

This file hides the fanout bound inside the witness package.  The paper-facing
statement now has the shape:

```text
BoundedGlobalPaperMainWitness
⇒ identification in the limit for the witness's bound.
```

This is close to the informal theorem form:

> if some finite fanout bound and its trimmed semantic witness are available,
> then the corresponding reachable learner identifies the target language from
> positive data.

No new mathematical principle is introduced here.

No theorem here uses `sorry`.
-/

namespace MCFG

universe u v w

section BoundedGlobalPaperWitnesses

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}

/-- Bounded global paper witness for the preferred common-context route.

This package hides the fanout bound as well as the trimmed presentation and
pre-core witness data. -/
structure TrimmedPresentationBoundedGlobalPaperMainWitness where
  fanoutBound : Nat
  witness :
    TrimmedPresentationGlobalPaperMainWitness
      (G := G) (obs := obs) (f := fanoutBound)

/-- Bounded global paper witness for the direct exposing route. -/
structure TrimmedPresentationBoundedGlobalPaperExposingWitness where
  fanoutBound : Nat
  witness :
    TrimmedPresentationGlobalPaperExposingWitness
      (G := G) (obs := obs) (f := fanoutBound)

/-- Bounded global paper witness for the stronger same-context route. -/
structure TrimmedPresentationBoundedGlobalPaperSameContextWitness where
  fanoutBound : Nat
  witness :
    TrimmedPresentationGlobalPaperSameContextWitness
      (G := G) (obs := obs) (f := fanoutBound)

namespace TrimmedPresentationBoundedGlobalPaperMainWitness

/-- The finite sample extracted from a bounded global main witness. -/
def sample
    (W : TrimmedPresentationBoundedGlobalPaperMainWitness
      (G := G) (obs := obs)) :
    Finset (Word α) :=
  W.witness.sample

/-- The extracted sample is positive. -/
theorem sample_positive
    (W : TrimmedPresentationBoundedGlobalPaperMainWitness
      (G := G) (obs := obs)) :
    (W.sample : Set (Word α)) ⊆ G.StringLanguage :=
  W.witness.sample_positive

/-- The extracted sample is characteristic for the reachable learner at the
witness's bound. -/
theorem characteristic_sample
    (W : TrimmedPresentationBoundedGlobalPaperMainWitness
      (G := G) (obs := obs)) :
    CharacteristicSample
      (reachableHypLanguage obs W.fanoutBound)
      (reachableSampleLearner (α := α))
      W.sample
      G.StringLanguage :=
  W.witness.characteristic_sample

/-- Existence form for a finite positive characteristic sample at the witness's
bound. -/
theorem exists_positive_characteristic_sample
    (W : TrimmedPresentationBoundedGlobalPaperMainWitness
      (G := G) (obs := obs)) :
    ∃ S : Finset (Word α),
      (S : Set (Word α)) ⊆ G.StringLanguage ∧
      CharacteristicSample
        (reachableHypLanguage obs W.fanoutBound)
        (reachableSampleLearner (α := α))
        S
        G.StringLanguage :=
  W.witness.exists_positive_characteristic_sample

/-- Existential form hiding the fanout bound as well as the sample. -/
theorem exists_bound_and_positive_characteristic_sample
    (W : TrimmedPresentationBoundedGlobalPaperMainWitness
      (G := G) (obs := obs)) :
    ∃ f : Nat, ∃ S : Finset (Word α),
      (S : Set (Word α)) ⊆ G.StringLanguage ∧
      CharacteristicSample
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        S
        G.StringLanguage :=
  ⟨W.fanoutBound, W.sample, W.sample_positive, W.characteristic_sample⟩

/-- Exact reconstruction from every positive finite superset of the extracted
sample. -/
theorem exact_for_positive_superset
    (W : TrimmedPresentationBoundedGlobalPaperMainWitness
      (G := G) (obs := obs))
    {K : Finset (Word α)}
    (hWK : (W.sample : Set (Word α)) ⊆ (K : Set (Word α)))
    (hKpos : (K : Set (Word α)) ⊆ G.StringLanguage) :
    ReachableSampleStringLanguage K obs W.fanoutBound = G.StringLanguage :=
  W.witness.exact_for_positive_superset hWK hKpos

/-- Eventual prefix-exact reconstruction on every positive text. -/
theorem prefix_exact_eventually
    (W : TrimmedPresentationBoundedGlobalPaperMainWitness
      (G := G) (obs := obs)) :
    ∀ Ttxt : TextFor G.StringLanguage,
      ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
        ReachableSampleStringLanguage
          (Ttxt.prefixSample n) obs W.fanoutBound =
          G.StringLanguage :=
  W.witness.prefix_exact_eventually

/-- Gold-style identification in the limit from every positive text at the
witness's bound. -/
theorem identifies_from_positive_text
    (W : TrimmedPresentationBoundedGlobalPaperMainWitness
      (G := G) (obs := obs)) :
    ∀ Ttxt : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs W.fanoutBound)
        (reachableSampleLearner (α := α))
        Ttxt :=
  W.witness.identifies_from_positive_text

/-- Pointwise eventual correctness on one positive text. -/
theorem eventually_correct_on_text
    (W : TrimmedPresentationBoundedGlobalPaperMainWitness
      (G := G) (obs := obs))
    (Ttxt : TextFor G.StringLanguage) :
    EventuallyCorrectOnText
      (reachableHypLanguage obs W.fanoutBound)
      (reachableSampleLearner (α := α))
      Ttxt :=
  W.identifies_from_positive_text Ttxt

end TrimmedPresentationBoundedGlobalPaperMainWitness


namespace TrimmedPresentationBoundedGlobalPaperExposingWitness

/-- The finite sample extracted from a bounded global exposing witness. -/
def sample
    (W : TrimmedPresentationBoundedGlobalPaperExposingWitness
      (G := G) (obs := obs)) :
    Finset (Word α) :=
  W.witness.sample

/-- The extracted sample is positive. -/
theorem sample_positive
    (W : TrimmedPresentationBoundedGlobalPaperExposingWitness
      (G := G) (obs := obs)) :
    (W.sample : Set (Word α)) ⊆ G.StringLanguage :=
  W.witness.sample_positive

/-- The extracted sample is characteristic at the witness's bound. -/
theorem characteristic_sample
    (W : TrimmedPresentationBoundedGlobalPaperExposingWitness
      (G := G) (obs := obs)) :
    CharacteristicSample
      (reachableHypLanguage obs W.fanoutBound)
      (reachableSampleLearner (α := α))
      W.sample
      G.StringLanguage :=
  W.witness.characteristic_sample

/-- Existence form for a finite positive characteristic sample. -/
theorem exists_positive_characteristic_sample
    (W : TrimmedPresentationBoundedGlobalPaperExposingWitness
      (G := G) (obs := obs)) :
    ∃ S : Finset (Word α),
      (S : Set (Word α)) ⊆ G.StringLanguage ∧
      CharacteristicSample
        (reachableHypLanguage obs W.fanoutBound)
        (reachableSampleLearner (α := α))
        S
        G.StringLanguage :=
  W.witness.exists_positive_characteristic_sample

/-- Existential form hiding the fanout bound as well as the sample. -/
theorem exists_bound_and_positive_characteristic_sample
    (W : TrimmedPresentationBoundedGlobalPaperExposingWitness
      (G := G) (obs := obs)) :
    ∃ f : Nat, ∃ S : Finset (Word α),
      (S : Set (Word α)) ⊆ G.StringLanguage ∧
      CharacteristicSample
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        S
        G.StringLanguage :=
  ⟨W.fanoutBound, W.sample, W.sample_positive, W.characteristic_sample⟩

/-- Eventual prefix-exact reconstruction on every positive text. -/
theorem prefix_exact_eventually
    (W : TrimmedPresentationBoundedGlobalPaperExposingWitness
      (G := G) (obs := obs)) :
    ∀ Ttxt : TextFor G.StringLanguage,
      ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
        ReachableSampleStringLanguage
          (Ttxt.prefixSample n) obs W.fanoutBound =
          G.StringLanguage :=
  W.witness.prefix_exact_eventually

/-- Gold-style identification in the limit from every positive text. -/
theorem identifies_from_positive_text
    (W : TrimmedPresentationBoundedGlobalPaperExposingWitness
      (G := G) (obs := obs)) :
    ∀ Ttxt : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs W.fanoutBound)
        (reachableSampleLearner (α := α))
        Ttxt :=
  W.witness.identifies_from_positive_text

end TrimmedPresentationBoundedGlobalPaperExposingWitness


namespace TrimmedPresentationBoundedGlobalPaperSameContextWitness

/-- The finite sample extracted from a bounded global same-context witness. -/
def sample
    (W : TrimmedPresentationBoundedGlobalPaperSameContextWitness
      (G := G) (obs := obs)) :
    Finset (Word α) :=
  W.witness.sample

/-- The extracted sample is positive. -/
theorem sample_positive
    (W : TrimmedPresentationBoundedGlobalPaperSameContextWitness
      (G := G) (obs := obs)) :
    (W.sample : Set (Word α)) ⊆ G.StringLanguage :=
  W.witness.sample_positive

/-- The extracted sample is characteristic at the witness's bound. -/
theorem characteristic_sample
    (W : TrimmedPresentationBoundedGlobalPaperSameContextWitness
      (G := G) (obs := obs)) :
    CharacteristicSample
      (reachableHypLanguage obs W.fanoutBound)
      (reachableSampleLearner (α := α))
      W.sample
      G.StringLanguage :=
  W.witness.characteristic_sample

/-- Existence form for a finite positive characteristic sample. -/
theorem exists_positive_characteristic_sample
    (W : TrimmedPresentationBoundedGlobalPaperSameContextWitness
      (G := G) (obs := obs)) :
    ∃ S : Finset (Word α),
      (S : Set (Word α)) ⊆ G.StringLanguage ∧
      CharacteristicSample
        (reachableHypLanguage obs W.fanoutBound)
        (reachableSampleLearner (α := α))
        S
        G.StringLanguage :=
  W.witness.exists_positive_characteristic_sample

/-- Existential form hiding the fanout bound as well as the sample. -/
theorem exists_bound_and_positive_characteristic_sample
    (W : TrimmedPresentationBoundedGlobalPaperSameContextWitness
      (G := G) (obs := obs)) :
    ∃ f : Nat, ∃ S : Finset (Word α),
      (S : Set (Word α)) ⊆ G.StringLanguage ∧
      CharacteristicSample
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        S
        G.StringLanguage :=
  ⟨W.fanoutBound, W.sample, W.sample_positive, W.characteristic_sample⟩

/-- Convert a bounded same-context witness to a bounded exposing witness. -/
def toExposingWitness
    (W : TrimmedPresentationBoundedGlobalPaperSameContextWitness
      (G := G) (obs := obs)) :
    TrimmedPresentationBoundedGlobalPaperExposingWitness
      (G := G) (obs := obs) where
  fanoutBound := W.fanoutBound
  witness := W.witness.toExposingWitness

/-- Eventual prefix-exact reconstruction on every positive text. -/
theorem prefix_exact_eventually
    (W : TrimmedPresentationBoundedGlobalPaperSameContextWitness
      (G := G) (obs := obs)) :
    ∀ Ttxt : TextFor G.StringLanguage,
      ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
        ReachableSampleStringLanguage
          (Ttxt.prefixSample n) obs W.fanoutBound =
          G.StringLanguage :=
  W.witness.prefix_exact_eventually

/-- Gold-style identification in the limit from every positive text. -/
theorem identifies_from_positive_text
    (W : TrimmedPresentationBoundedGlobalPaperSameContextWitness
      (G := G) (obs := obs)) :
    ∀ Ttxt : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs W.fanoutBound)
        (reachableSampleLearner (α := α))
        Ttxt :=
  W.witness.identifies_from_positive_text

/-- Gold-style identification through the exposing witness conversion. -/
theorem identifies_from_positive_text_via_exposing
    (W : TrimmedPresentationBoundedGlobalPaperSameContextWitness
      (G := G) (obs := obs)) :
    ∀ Ttxt : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs W.fanoutBound)
        (reachableSampleLearner (α := α))
        Ttxt :=
  W.toExposingWitness.identifies_from_positive_text

end TrimmedPresentationBoundedGlobalPaperSameContextWitness

end BoundedGlobalPaperWitnesses


section BoundedGlobalPaperTheorems

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}

/-- Bounded global paper theorem: a bounded main witness gives a finite positive
characteristic sample at its hidden bound. -/
theorem trimmed_bounded_global_paper_exists_positive_characteristic_sample
    (W : TrimmedPresentationBoundedGlobalPaperMainWitness
      (G := G) (obs := obs)) :
    ∃ S : Finset (Word α),
      (S : Set (Word α)) ⊆ G.StringLanguage ∧
      CharacteristicSample
        (reachableHypLanguage obs W.fanoutBound)
        (reachableSampleLearner (α := α))
        S
        G.StringLanguage :=
  W.exists_positive_characteristic_sample

/-- Bounded global paper theorem: hiding both the bound and the sample. -/
theorem trimmed_bounded_global_paper_exists_bound_and_characteristic_sample
    (W : TrimmedPresentationBoundedGlobalPaperMainWitness
      (G := G) (obs := obs)) :
    ∃ f : Nat, ∃ S : Finset (Word α),
      (S : Set (Word α)) ⊆ G.StringLanguage ∧
      CharacteristicSample
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        S
        G.StringLanguage :=
  W.exists_bound_and_positive_characteristic_sample

/-- Bounded global paper theorem: eventual prefix exactness at the hidden bound. -/
theorem trimmed_bounded_global_paper_prefix_exact_eventually
    (W : TrimmedPresentationBoundedGlobalPaperMainWitness
      (G := G) (obs := obs)) :
    ∀ Ttxt : TextFor G.StringLanguage,
      ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
        ReachableSampleStringLanguage
          (Ttxt.prefixSample n) obs W.fanoutBound =
          G.StringLanguage :=
  W.prefix_exact_eventually

/-- Bounded global paper theorem: Gold-style identification at the hidden
bound. -/
theorem trimmed_bounded_global_paper_main_theorem
    (W : TrimmedPresentationBoundedGlobalPaperMainWitness
      (G := G) (obs := obs)) :
    ∀ Ttxt : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs W.fanoutBound)
        (reachableSampleLearner (α := α))
        Ttxt :=
  W.identifies_from_positive_text

/-- Bounded global exposing-witness theorem. -/
theorem trimmed_bounded_global_paper_exposing_main_theorem
    (W : TrimmedPresentationBoundedGlobalPaperExposingWitness
      (G := G) (obs := obs)) :
    ∀ Ttxt : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs W.fanoutBound)
        (reachableSampleLearner (α := α))
        Ttxt :=
  W.identifies_from_positive_text

/-- Bounded global same-context-witness theorem. -/
theorem trimmed_bounded_global_paper_same_context_main_theorem
    (W : TrimmedPresentationBoundedGlobalPaperSameContextWitness
      (G := G) (obs := obs)) :
    ∀ Ttxt : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs W.fanoutBound)
        (reachableSampleLearner (α := α))
        Ttxt :=
  W.identifies_from_positive_text

/-- Bounded global same-context-witness theorem through exposing conversion. -/
theorem trimmed_bounded_global_paper_same_context_via_exposing_theorem
    (W : TrimmedPresentationBoundedGlobalPaperSameContextWitness
      (G := G) (obs := obs)) :
    ∀ Ttxt : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs W.fanoutBound)
        (reachableSampleLearner (α := α))
        Ttxt :=
  W.identifies_from_positive_text_via_exposing

end BoundedGlobalPaperTheorems

end MCFG
