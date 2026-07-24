/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG2.CharacteristicSamplePaperAssumptionDiagram

/-!
# CharacteristicSamplePaperWitnessTheorem.lean

Ninety-second clean Lean experiment for the fixed-observation MCFG project.

The previous files introduced paper-facing assumption packages, but those
packages were still indexed by a concrete pre-core datum

```lean
D : TrimmedPresentationPreCoreData T f.
```

This file hides that dependent index in a witness package.  This is closer to
the paper-level formulation:

```text
if a trimmed presentation witness exists,
then the reachable learner identifies the target language.
```

We provide witness packages for the three paper-facing routes:

* preferred anchor common-context route;
* direct exposing route;
* stronger same-context route.

No new mathematical principle is introduced here.

No theorem here uses `sorry`.
-/

namespace MCFG

universe u v w

section PaperWitnesses

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}
variable {f : Nat}
variable (T : TrimmedOutputTypePresentation G obs)

/-- Paper-facing witness package for the preferred common-context route.

The concrete `D : TrimmedPresentationPreCoreData T f` is hidden inside the
package. -/
structure TrimmedPresentationPaperMainWitness where
  data : TrimmedPresentationPreCoreData T f
  assumptions : TrimmedPresentationPaperMainAssumptions data

/-- Paper-facing witness package for the direct exposing route. -/
structure TrimmedPresentationPaperExposingWitness where
  data : TrimmedPresentationPreCoreData T f
  assumptions : TrimmedPresentationPaperExposingAssumptions data

/-- Paper-facing witness package for the stronger same-context route. -/
structure TrimmedPresentationPaperSameContextWitness where
  data : TrimmedPresentationPreCoreData T f
  assumptions : TrimmedPresentationPaperSameContextAssumptions data

namespace TrimmedPresentationPaperMainWitness

variable {T}

/-- The finite sample extracted from a main paper witness. -/
noncomputable def sample
    (W : TrimmedPresentationPaperMainWitness (G := G) (obs := obs) (f := f) T) :
    Finset (Word α) :=
  W.assumptions.sample

/-- The extracted sample is positive. -/
theorem sample_positive
    (W : TrimmedPresentationPaperMainWitness (G := G) (obs := obs) (f := f) T) :
    (W.sample : Set (Word α)) ⊆ G.StringLanguage :=
  W.assumptions.sample_positive

/-- The extracted sample contains the witness words for the hidden pre-core
datum. -/
theorem contains_witnesses
    (W : TrimmedPresentationPaperMainWitness (G := G) (obs := obs) (f := f) T) :
    TrimmedPresentationWitnessWordSet W.data ⊆
      (W.sample : Set (Word α)) :=
  W.assumptions.contains_witnesses

/-- The extracted sample is characteristic for the reachable learner. -/
theorem characteristic_sample
    (W : TrimmedPresentationPaperMainWitness (G := G) (obs := obs) (f := f) T) :
    CharacteristicSample
      (reachableHypLanguage obs f)
      (reachableSampleLearner (α := α))
      W.sample
      G.StringLanguage :=
  W.assumptions.characteristic_sample

/-- Existence form for the finite positive characteristic sample. -/
theorem exists_positive_characteristic_sample
    (W : TrimmedPresentationPaperMainWitness (G := G) (obs := obs) (f := f) T) :
    ∃ S : Finset (Word α),
      (S : Set (Word α)) ⊆ G.StringLanguage ∧
      CharacteristicSample
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        S
        G.StringLanguage :=
  W.assumptions.exists_positive_characteristic_sample

/-- Exact reconstruction from every positive finite superset of the extracted
sample. -/
theorem exact_for_positive_superset
    (W : TrimmedPresentationPaperMainWitness (G := G) (obs := obs) (f := f) T)
    {K : Finset (Word α)}
    (hWK : (W.sample : Set (Word α)) ⊆ (K : Set (Word α)))
    (hKpos : (K : Set (Word α)) ⊆ G.StringLanguage) :
    ReachableSampleStringLanguage K obs f = G.StringLanguage :=
  W.assumptions.exact_for_positive_superset hWK hKpos

/-- Eventual prefix-exact reconstruction on every positive text. -/
theorem prefix_exact_eventually
    (W : TrimmedPresentationPaperMainWitness (G := G) (obs := obs) (f := f) T) :
    ∀ Ttxt : TextFor G.StringLanguage,
      ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
        ReachableSampleStringLanguage (Ttxt.prefixSample n) obs f =
          G.StringLanguage :=
  W.assumptions.prefix_exact_eventually

/-- Gold-style identification in the limit from every positive text. -/
theorem identifies_from_positive_text
    (W : TrimmedPresentationPaperMainWitness (G := G) (obs := obs) (f := f) T) :
    ∀ Ttxt : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        Ttxt :=
  W.assumptions.identifies_from_positive_text

end TrimmedPresentationPaperMainWitness


namespace TrimmedPresentationPaperExposingWitness

variable {T}

/-- The finite sample extracted from an exposing paper witness. -/
noncomputable def sample
    (W : TrimmedPresentationPaperExposingWitness (G := G) (obs := obs) (f := f) T) :
    Finset (Word α) :=
  W.assumptions.sample

/-- The extracted sample is positive. -/
theorem sample_positive
    (W : TrimmedPresentationPaperExposingWitness (G := G) (obs := obs) (f := f) T) :
    (W.sample : Set (Word α)) ⊆ G.StringLanguage :=
  W.assumptions.sample_positive

/-- The extracted sample is characteristic for the reachable learner. -/
theorem characteristic_sample
    (W : TrimmedPresentationPaperExposingWitness (G := G) (obs := obs) (f := f) T) :
    CharacteristicSample
      (reachableHypLanguage obs f)
      (reachableSampleLearner (α := α))
      W.sample
      G.StringLanguage :=
  W.assumptions.characteristic_sample

/-- Existence form for the finite positive characteristic sample. -/
theorem exists_positive_characteristic_sample
    (W : TrimmedPresentationPaperExposingWitness (G := G) (obs := obs) (f := f) T) :
    ∃ S : Finset (Word α),
      (S : Set (Word α)) ⊆ G.StringLanguage ∧
      CharacteristicSample
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        S
        G.StringLanguage :=
  W.assumptions.exists_positive_characteristic_sample

/-- Eventual prefix-exact reconstruction on every positive text. -/
theorem prefix_exact_eventually
    (W : TrimmedPresentationPaperExposingWitness (G := G) (obs := obs) (f := f) T) :
    ∀ Ttxt : TextFor G.StringLanguage,
      ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
        ReachableSampleStringLanguage (Ttxt.prefixSample n) obs f =
          G.StringLanguage :=
  W.assumptions.prefix_exact_eventually

/-- Gold-style identification in the limit from every positive text. -/
theorem identifies_from_positive_text
    (W : TrimmedPresentationPaperExposingWitness (G := G) (obs := obs) (f := f) T) :
    ∀ Ttxt : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        Ttxt :=
  W.assumptions.identifies_from_positive_text

end TrimmedPresentationPaperExposingWitness


namespace TrimmedPresentationPaperSameContextWitness

variable {T}

/-- The finite sample extracted from a same-context paper witness. -/
noncomputable def sample
    (W : TrimmedPresentationPaperSameContextWitness (G := G) (obs := obs) (f := f) T) :
    Finset (Word α) :=
  W.assumptions.sample

/-- The extracted sample is positive. -/
theorem sample_positive
    (W : TrimmedPresentationPaperSameContextWitness (G := G) (obs := obs) (f := f) T) :
    (W.sample : Set (Word α)) ⊆ G.StringLanguage :=
  W.assumptions.sample_positive

/-- The extracted sample is characteristic for the reachable learner. -/
theorem characteristic_sample
    (W : TrimmedPresentationPaperSameContextWitness (G := G) (obs := obs) (f := f) T) :
    CharacteristicSample
      (reachableHypLanguage obs f)
      (reachableSampleLearner (α := α))
      W.sample
      G.StringLanguage :=
  W.assumptions.characteristic_sample

/-- Existence form for the finite positive characteristic sample. -/
theorem exists_positive_characteristic_sample
    (W : TrimmedPresentationPaperSameContextWitness (G := G) (obs := obs) (f := f) T) :
    ∃ S : Finset (Word α),
      (S : Set (Word α)) ⊆ G.StringLanguage ∧
      CharacteristicSample
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        S
        G.StringLanguage :=
  W.assumptions.exists_positive_characteristic_sample

/-- Same-context witness converted to an exposing witness. -/
def toExposingWitness
    (W : TrimmedPresentationPaperSameContextWitness (G := G) (obs := obs) (f := f) T) :
    TrimmedPresentationPaperExposingWitness (G := G) (obs := obs) (f := f) T where
  data := W.data
  assumptions := W.assumptions.toPaperExposingAssumptions

/-- Eventual prefix-exact reconstruction on every positive text. -/
theorem prefix_exact_eventually
    (W : TrimmedPresentationPaperSameContextWitness (G := G) (obs := obs) (f := f) T) :
    ∀ Ttxt : TextFor G.StringLanguage,
      ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
        ReachableSampleStringLanguage (Ttxt.prefixSample n) obs f =
          G.StringLanguage :=
  W.assumptions.prefix_exact_eventually

/-- Gold-style identification in the limit from every positive text. -/
theorem identifies_from_positive_text
    (W : TrimmedPresentationPaperSameContextWitness (G := G) (obs := obs) (f := f) T) :
    ∀ Ttxt : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        Ttxt :=
  W.assumptions.identifies_from_positive_text

/-- Gold-style identification through the exposing witness. -/
theorem identifies_from_positive_text_via_exposing
    (W : TrimmedPresentationPaperSameContextWitness (G := G) (obs := obs) (f := f) T) :
    ∀ Ttxt : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        Ttxt :=
  W.toExposingWitness.identifies_from_positive_text

end TrimmedPresentationPaperSameContextWitness

end PaperWitnesses


section PaperWitnessTheorems

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}
variable {f : Nat}
variable {T : TrimmedOutputTypePresentation G obs}

/-- Paper-witness theorem: a main witness gives a finite positive characteristic
sample. -/
theorem trimmed_paper_witness_exists_positive_characteristic_sample
    (W : TrimmedPresentationPaperMainWitness (G := G) (obs := obs) (f := f) T) :
    ∃ S : Finset (Word α),
      (S : Set (Word α)) ⊆ G.StringLanguage ∧
      CharacteristicSample
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        S
        G.StringLanguage :=
  W.exists_positive_characteristic_sample

/-- Paper-witness theorem: a main witness gives eventual prefix exactness. -/
theorem trimmed_paper_witness_prefix_exact_eventually
    (W : TrimmedPresentationPaperMainWitness (G := G) (obs := obs) (f := f) T) :
    ∀ Ttxt : TextFor G.StringLanguage,
      ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
        ReachableSampleStringLanguage (Ttxt.prefixSample n) obs f =
          G.StringLanguage :=
  W.prefix_exact_eventually

/-- Paper-witness theorem: a main witness gives Gold-style identification. -/
theorem trimmed_paper_witness_main_theorem
    (W : TrimmedPresentationPaperMainWitness (G := G) (obs := obs) (f := f) T) :
    ∀ Ttxt : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        Ttxt :=
  W.identifies_from_positive_text

/-- Exposing paper-witness theorem. -/
theorem trimmed_paper_exposing_witness_main_theorem
    (W : TrimmedPresentationPaperExposingWitness (G := G) (obs := obs) (f := f) T) :
    ∀ Ttxt : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        Ttxt :=
  W.identifies_from_positive_text

/-- Same-context paper-witness theorem. -/
theorem trimmed_paper_same_context_witness_main_theorem
    (W : TrimmedPresentationPaperSameContextWitness (G := G) (obs := obs) (f := f) T) :
    ∀ Ttxt : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        Ttxt :=
  W.identifies_from_positive_text

/-- Same-context paper-witness theorem through exposing conversion. -/
theorem trimmed_paper_same_context_witness_via_exposing_theorem
    (W : TrimmedPresentationPaperSameContextWitness (G := G) (obs := obs) (f := f) T) :
    ∀ Ttxt : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        Ttxt :=
  W.identifies_from_positive_text_via_exposing

end PaperWitnessTheorems

end MCFG
