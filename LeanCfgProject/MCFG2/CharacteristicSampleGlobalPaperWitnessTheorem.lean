/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG2.CharacteristicSamplePaperWitnessTheorem

/-!
# CharacteristicSampleGlobalPaperWitnessTheorem.lean

Ninety-third clean Lean experiment for the fixed-observation MCFG project.

`CharacteristicSamplePaperWitnessTheorem.lean` hid the dependent pre-core datum

```lean
D : TrimmedPresentationPreCoreData T f
```

inside a paper witness package.

This file hides the trimmed output-type presentation itself:

```lean
T : TrimmedOutputTypePresentation G obs.
```

Thus the main theorem can now be stated from a single global witness package:

```text
GlobalPaperMainWitness ⇒ identification in the limit.
```

This is closer to the final paper-level sentence:

> If the trimmed finite-observation presentation and its semantic transport
> witnesses are constructible, then the reachable learner identifies the target
> language from positive data.

No new mathematical principle is introduced here.

No theorem here uses `sorry`.
-/

namespace MCFG

universe u v w

section GlobalPaperWitnesses

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}
variable {f : Nat}

/-- Global paper witness for the preferred common-context route.

This package hides both:

* the trimmed output-type presentation `T`;
* the pre-core datum `D` living over `T`. -/
structure TrimmedPresentationGlobalPaperMainWitness where
  presentation : TrimmedOutputTypePresentation G obs
  witness :
    TrimmedPresentationPaperMainWitness
      (G := G) (obs := obs) (f := f) presentation

/-- Global paper witness for the direct exposing route. -/
structure TrimmedPresentationGlobalPaperExposingWitness where
  presentation : TrimmedOutputTypePresentation G obs
  witness :
    TrimmedPresentationPaperExposingWitness
      (G := G) (obs := obs) (f := f) presentation

/-- Global paper witness for the stronger same-context route. -/
structure TrimmedPresentationGlobalPaperSameContextWitness where
  presentation : TrimmedOutputTypePresentation G obs
  witness :
    TrimmedPresentationPaperSameContextWitness
      (G := G) (obs := obs) (f := f) presentation

namespace TrimmedPresentationGlobalPaperMainWitness

/-- The finite sample extracted from a global main witness. -/
def sample
    (W : TrimmedPresentationGlobalPaperMainWitness
      (G := G) (obs := obs) (f := f)) :
    Finset (Word α) :=
  W.witness.sample

/-- The extracted sample is positive. -/
theorem sample_positive
    (W : TrimmedPresentationGlobalPaperMainWitness
      (G := G) (obs := obs) (f := f)) :
    (W.sample : Set (Word α)) ⊆ G.StringLanguage :=
  W.witness.sample_positive

/-- The extracted sample is characteristic for the reachable learner. -/
theorem characteristic_sample
    (W : TrimmedPresentationGlobalPaperMainWitness
      (G := G) (obs := obs) (f := f)) :
    CharacteristicSample
      (reachableHypLanguage obs f)
      (reachableSampleLearner (α := α))
      W.sample
      G.StringLanguage :=
  W.witness.characteristic_sample

/-- Existence form for a finite positive characteristic sample. -/
theorem exists_positive_characteristic_sample
    (W : TrimmedPresentationGlobalPaperMainWitness
      (G := G) (obs := obs) (f := f)) :
    ∃ S : Finset (Word α),
      (S : Set (Word α)) ⊆ G.StringLanguage ∧
      CharacteristicSample
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        S
        G.StringLanguage :=
  W.witness.exists_positive_characteristic_sample

/-- Exact reconstruction from every positive finite superset of the extracted
sample. -/
theorem exact_for_positive_superset
    (W : TrimmedPresentationGlobalPaperMainWitness
      (G := G) (obs := obs) (f := f))
    {K : Finset (Word α)}
    (hWK : (W.sample : Set (Word α)) ⊆ (K : Set (Word α)))
    (hKpos : (K : Set (Word α)) ⊆ G.StringLanguage) :
    ReachableSampleStringLanguage K obs f = G.StringLanguage :=
  W.witness.exact_for_positive_superset hWK hKpos

/-- Eventual prefix-exact reconstruction on every positive text. -/
theorem prefix_exact_eventually
    (W : TrimmedPresentationGlobalPaperMainWitness
      (G := G) (obs := obs) (f := f)) :
    ∀ Ttxt : TextFor G.StringLanguage,
      ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
        ReachableSampleStringLanguage (Ttxt.prefixSample n) obs f =
          G.StringLanguage :=
  W.witness.prefix_exact_eventually

/-- Gold-style identification in the limit from every positive text. -/
theorem identifies_from_positive_text
    (W : TrimmedPresentationGlobalPaperMainWitness
      (G := G) (obs := obs) (f := f)) :
    ∀ Ttxt : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        Ttxt :=
  W.witness.identifies_from_positive_text

/-- Pointwise eventual correctness on one positive text. -/
theorem eventually_correct_on_text
    (W : TrimmedPresentationGlobalPaperMainWitness
      (G := G) (obs := obs) (f := f))
    (Ttxt : TextFor G.StringLanguage) :
    EventuallyCorrectOnText
      (reachableHypLanguage obs f)
      (reachableSampleLearner (α := α))
      Ttxt :=
  W.identifies_from_positive_text Ttxt

end TrimmedPresentationGlobalPaperMainWitness


namespace TrimmedPresentationGlobalPaperExposingWitness

/-- The finite sample extracted from a global exposing witness. -/
def sample
    (W : TrimmedPresentationGlobalPaperExposingWitness
      (G := G) (obs := obs) (f := f)) :
    Finset (Word α) :=
  W.witness.sample

/-- The extracted sample is positive. -/
theorem sample_positive
    (W : TrimmedPresentationGlobalPaperExposingWitness
      (G := G) (obs := obs) (f := f)) :
    (W.sample : Set (Word α)) ⊆ G.StringLanguage :=
  W.witness.sample_positive

/-- The extracted sample is characteristic for the reachable learner. -/
theorem characteristic_sample
    (W : TrimmedPresentationGlobalPaperExposingWitness
      (G := G) (obs := obs) (f := f)) :
    CharacteristicSample
      (reachableHypLanguage obs f)
      (reachableSampleLearner (α := α))
      W.sample
      G.StringLanguage :=
  W.witness.characteristic_sample

/-- Existence form for a finite positive characteristic sample. -/
theorem exists_positive_characteristic_sample
    (W : TrimmedPresentationGlobalPaperExposingWitness
      (G := G) (obs := obs) (f := f)) :
    ∃ S : Finset (Word α),
      (S : Set (Word α)) ⊆ G.StringLanguage ∧
      CharacteristicSample
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        S
        G.StringLanguage :=
  W.witness.exists_positive_characteristic_sample

/-- Eventual prefix-exact reconstruction on every positive text. -/
theorem prefix_exact_eventually
    (W : TrimmedPresentationGlobalPaperExposingWitness
      (G := G) (obs := obs) (f := f)) :
    ∀ Ttxt : TextFor G.StringLanguage,
      ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
        ReachableSampleStringLanguage (Ttxt.prefixSample n) obs f =
          G.StringLanguage :=
  W.witness.prefix_exact_eventually

/-- Gold-style identification in the limit from every positive text. -/
theorem identifies_from_positive_text
    (W : TrimmedPresentationGlobalPaperExposingWitness
      (G := G) (obs := obs) (f := f)) :
    ∀ Ttxt : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        Ttxt :=
  W.witness.identifies_from_positive_text

end TrimmedPresentationGlobalPaperExposingWitness


namespace TrimmedPresentationGlobalPaperSameContextWitness

/-- The finite sample extracted from a global same-context witness. -/
def sample
    (W : TrimmedPresentationGlobalPaperSameContextWitness
      (G := G) (obs := obs) (f := f)) :
    Finset (Word α) :=
  W.witness.sample

/-- The extracted sample is positive. -/
theorem sample_positive
    (W : TrimmedPresentationGlobalPaperSameContextWitness
      (G := G) (obs := obs) (f := f)) :
    (W.sample : Set (Word α)) ⊆ G.StringLanguage :=
  W.witness.sample_positive

/-- The extracted sample is characteristic for the reachable learner. -/
theorem characteristic_sample
    (W : TrimmedPresentationGlobalPaperSameContextWitness
      (G := G) (obs := obs) (f := f)) :
    CharacteristicSample
      (reachableHypLanguage obs f)
      (reachableSampleLearner (α := α))
      W.sample
      G.StringLanguage :=
  W.witness.characteristic_sample

/-- Existence form for a finite positive characteristic sample. -/
theorem exists_positive_characteristic_sample
    (W : TrimmedPresentationGlobalPaperSameContextWitness
      (G := G) (obs := obs) (f := f)) :
    ∃ S : Finset (Word α),
      (S : Set (Word α)) ⊆ G.StringLanguage ∧
      CharacteristicSample
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        S
        G.StringLanguage :=
  W.witness.exists_positive_characteristic_sample

/-- Convert a global same-context witness to a global exposing witness. -/
def toExposingWitness
    (W : TrimmedPresentationGlobalPaperSameContextWitness
      (G := G) (obs := obs) (f := f)) :
    TrimmedPresentationGlobalPaperExposingWitness
      (G := G) (obs := obs) (f := f) where
  presentation := W.presentation
  witness := W.witness.toExposingWitness

/-- Eventual prefix-exact reconstruction on every positive text. -/
theorem prefix_exact_eventually
    (W : TrimmedPresentationGlobalPaperSameContextWitness
      (G := G) (obs := obs) (f := f)) :
    ∀ Ttxt : TextFor G.StringLanguage,
      ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
        ReachableSampleStringLanguage (Ttxt.prefixSample n) obs f =
          G.StringLanguage :=
  W.witness.prefix_exact_eventually

/-- Gold-style identification in the limit from every positive text. -/
theorem identifies_from_positive_text
    (W : TrimmedPresentationGlobalPaperSameContextWitness
      (G := G) (obs := obs) (f := f)) :
    ∀ Ttxt : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        Ttxt :=
  W.witness.identifies_from_positive_text

/-- Gold-style identification through the exposing witness conversion. -/
theorem identifies_from_positive_text_via_exposing
    (W : TrimmedPresentationGlobalPaperSameContextWitness
      (G := G) (obs := obs) (f := f)) :
    ∀ Ttxt : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        Ttxt :=
  W.toExposingWitness.identifies_from_positive_text

end TrimmedPresentationGlobalPaperSameContextWitness

end GlobalPaperWitnesses


section GlobalPaperWitnessTheorems

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}
variable {f : Nat}

/-- Global paper-witness theorem: a global main witness gives a finite positive
characteristic sample. -/
theorem trimmed_global_paper_witness_exists_positive_characteristic_sample
    (W : TrimmedPresentationGlobalPaperMainWitness
      (G := G) (obs := obs) (f := f)) :
    ∃ S : Finset (Word α),
      (S : Set (Word α)) ⊆ G.StringLanguage ∧
      CharacteristicSample
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        S
        G.StringLanguage :=
  W.exists_positive_characteristic_sample

/-- Global paper-witness theorem: a global main witness gives eventual prefix
exactness. -/
theorem trimmed_global_paper_witness_prefix_exact_eventually
    (W : TrimmedPresentationGlobalPaperMainWitness
      (G := G) (obs := obs) (f := f)) :
    ∀ Ttxt : TextFor G.StringLanguage,
      ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
        ReachableSampleStringLanguage (Ttxt.prefixSample n) obs f =
          G.StringLanguage :=
  W.prefix_exact_eventually

/-- Global paper-witness theorem: a global main witness gives Gold-style
identification. -/
theorem trimmed_global_paper_witness_main_theorem
    (W : TrimmedPresentationGlobalPaperMainWitness
      (G := G) (obs := obs) (f := f)) :
    ∀ Ttxt : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        Ttxt :=
  W.identifies_from_positive_text

/-- Global exposing-witness theorem. -/
theorem trimmed_global_paper_exposing_witness_main_theorem
    (W : TrimmedPresentationGlobalPaperExposingWitness
      (G := G) (obs := obs) (f := f)) :
    ∀ Ttxt : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        Ttxt :=
  W.identifies_from_positive_text

/-- Global same-context-witness theorem. -/
theorem trimmed_global_paper_same_context_witness_main_theorem
    (W : TrimmedPresentationGlobalPaperSameContextWitness
      (G := G) (obs := obs) (f := f)) :
    ∀ Ttxt : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        Ttxt :=
  W.identifies_from_positive_text

/-- Global same-context-witness theorem through exposing conversion. -/
theorem trimmed_global_paper_same_context_witness_via_exposing_theorem
    (W : TrimmedPresentationGlobalPaperSameContextWitness
      (G := G) (obs := obs) (f := f)) :
    ∀ Ttxt : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        Ttxt :=
  W.identifies_from_positive_text_via_exposing

end GlobalPaperWitnessTheorems

end MCFG
