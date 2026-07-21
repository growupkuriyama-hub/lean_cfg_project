/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG2.CharacteristicSampleBoundedGlobalPaperTheorem

/-!
# CharacteristicSampleExistentialPaperTheorem.lean

Ninety-fifth clean Lean experiment for the fixed-observation MCFG project.

`CharacteristicSampleBoundedGlobalPaperTheorem.lean` hid the fanout bound inside
a bounded global witness package.  This file takes one more paper-facing step:
it states the final conclusions from a mere `Nonempty` witness.

The central theorem shape is:

```text
Nonempty BoundedGlobalPaperMainWitness
⇒ ∃ f, identification in the limit for the reachable learner at f.
```

We also expose the corresponding existence of a finite positive characteristic
sample:

```text
Nonempty BoundedGlobalPaperMainWitness
⇒ ∃ f S, S is positive and characteristic for f.
```

No new mathematical principle is introduced here.

No theorem here uses `sorry`.
-/

namespace MCFG

universe u v w

section ExistentialStatements

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]

/-- There is a finite positive characteristic sample for some finite fanout
bound. -/
def ExistsBoundedPositiveCharacteristicSample
    (G : WorkingMCFG N α) (obs : α → M) : Prop :=
  ∃ f : Nat, ∃ S : Finset (Word α),
    (S : Set (Word α)) ⊆ G.StringLanguage ∧
    CharacteristicSample
      (reachableHypLanguage obs f)
      (reachableSampleLearner (α := α))
      S
      G.StringLanguage

/-- The reachable learner identifies the target language from every positive
text for some finite fanout bound. -/
def ExistsBoundedReachableIdentification
    (G : WorkingMCFG N α) (obs : α → M) : Prop :=
  ∃ f : Nat,
    ∀ Ttxt : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        Ttxt

/-- The reachable learner is eventually prefix-exact on every positive text for
some finite fanout bound. -/
def ExistsBoundedPrefixExactIdentification
    (G : WorkingMCFG N α) (obs : α → M) : Prop :=
  ∃ f : Nat,
    ∀ Ttxt : TextFor G.StringLanguage,
      ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
        ReachableSampleStringLanguage (Ttxt.prefixSample n) obs f =
          G.StringLanguage

end ExistentialStatements


section BoundedWitnessToExistentialStatements

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}

namespace TrimmedPresentationBoundedGlobalPaperMainWitness

/-- A bounded global main witness gives the existential characteristic-sample
statement. -/
theorem exists_bounded_positive_characteristic_sample
    (W : TrimmedPresentationBoundedGlobalPaperMainWitness
      (G := G) (obs := obs)) :
    ExistsBoundedPositiveCharacteristicSample G obs :=
  W.exists_bound_and_positive_characteristic_sample

/-- A bounded global main witness gives the existential identification statement. -/
theorem exists_bounded_reachable_identification
    (W : TrimmedPresentationBoundedGlobalPaperMainWitness
      (G := G) (obs := obs)) :
    ExistsBoundedReachableIdentification G obs :=
  ⟨W.fanoutBound, W.identifies_from_positive_text⟩

/-- A bounded global main witness gives the existential prefix-exact statement. -/
theorem exists_bounded_prefix_exact_identification
    (W : TrimmedPresentationBoundedGlobalPaperMainWitness
      (G := G) (obs := obs)) :
    ExistsBoundedPrefixExactIdentification G obs :=
  ⟨W.fanoutBound, W.prefix_exact_eventually⟩

end TrimmedPresentationBoundedGlobalPaperMainWitness


namespace TrimmedPresentationBoundedGlobalPaperExposingWitness

/-- A bounded global exposing witness gives the existential characteristic-sample
statement. -/
theorem exists_bounded_positive_characteristic_sample
    (W : TrimmedPresentationBoundedGlobalPaperExposingWitness
      (G := G) (obs := obs)) :
    ExistsBoundedPositiveCharacteristicSample G obs :=
  W.exists_bound_and_positive_characteristic_sample

/-- A bounded global exposing witness gives the existential identification
statement. -/
theorem exists_bounded_reachable_identification
    (W : TrimmedPresentationBoundedGlobalPaperExposingWitness
      (G := G) (obs := obs)) :
    ExistsBoundedReachableIdentification G obs :=
  ⟨W.fanoutBound, W.identifies_from_positive_text⟩

/-- A bounded global exposing witness gives the existential prefix-exact
statement. -/
theorem exists_bounded_prefix_exact_identification
    (W : TrimmedPresentationBoundedGlobalPaperExposingWitness
      (G := G) (obs := obs)) :
    ExistsBoundedPrefixExactIdentification G obs :=
  ⟨W.fanoutBound, W.prefix_exact_eventually⟩

end TrimmedPresentationBoundedGlobalPaperExposingWitness


namespace TrimmedPresentationBoundedGlobalPaperSameContextWitness

/-- A bounded global same-context witness gives the existential
characteristic-sample statement. -/
theorem exists_bounded_positive_characteristic_sample
    (W : TrimmedPresentationBoundedGlobalPaperSameContextWitness
      (G := G) (obs := obs)) :
    ExistsBoundedPositiveCharacteristicSample G obs :=
  W.exists_bound_and_positive_characteristic_sample

/-- A bounded global same-context witness gives the existential identification
statement. -/
theorem exists_bounded_reachable_identification
    (W : TrimmedPresentationBoundedGlobalPaperSameContextWitness
      (G := G) (obs := obs)) :
    ExistsBoundedReachableIdentification G obs :=
  ⟨W.fanoutBound, W.identifies_from_positive_text⟩

/-- A bounded global same-context witness gives the existential prefix-exact
statement. -/
theorem exists_bounded_prefix_exact_identification
    (W : TrimmedPresentationBoundedGlobalPaperSameContextWitness
      (G := G) (obs := obs)) :
    ExistsBoundedPrefixExactIdentification G obs :=
  ⟨W.fanoutBound, W.prefix_exact_eventually⟩

/-- Same-context witnesses also give existential identification through the
exposing conversion. -/
theorem exists_bounded_reachable_identification_via_exposing
    (W : TrimmedPresentationBoundedGlobalPaperSameContextWitness
      (G := G) (obs := obs)) :
    ExistsBoundedReachableIdentification G obs :=
  ⟨W.fanoutBound, W.identifies_from_positive_text_via_exposing⟩

end TrimmedPresentationBoundedGlobalPaperSameContextWitness

end BoundedWitnessToExistentialStatements


section NonemptyWitnessTheorems

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}

/-- If a bounded global main witness exists, then there is a finite positive
characteristic sample for some finite fanout bound. -/
theorem trimmed_existential_paper_exists_characteristic_sample
    (h :
      Nonempty
        (TrimmedPresentationBoundedGlobalPaperMainWitness
          (G := G) (obs := obs))) :
    ExistsBoundedPositiveCharacteristicSample G obs :=
  match h with
  | ⟨W⟩ => W.exists_bounded_positive_characteristic_sample

/-- If a bounded global main witness exists, then the reachable learner
identifies the target language from every positive text for some bound. -/
theorem trimmed_existential_paper_main_theorem
    (h :
      Nonempty
        (TrimmedPresentationBoundedGlobalPaperMainWitness
          (G := G) (obs := obs))) :
    ExistsBoundedReachableIdentification G obs :=
  match h with
  | ⟨W⟩ => W.exists_bounded_reachable_identification

/-- If a bounded global main witness exists, then the reachable learner is
eventually prefix-exact for some bound. -/
theorem trimmed_existential_paper_prefix_exact_theorem
    (h :
      Nonempty
        (TrimmedPresentationBoundedGlobalPaperMainWitness
          (G := G) (obs := obs))) :
    ExistsBoundedPrefixExactIdentification G obs :=
  match h with
  | ⟨W⟩ => W.exists_bounded_prefix_exact_identification

/-- Exposing-variant existential theorem. -/
theorem trimmed_existential_paper_exposing_main_theorem
    (h :
      Nonempty
        (TrimmedPresentationBoundedGlobalPaperExposingWitness
          (G := G) (obs := obs))) :
    ExistsBoundedReachableIdentification G obs :=
  match h with
  | ⟨W⟩ => W.exists_bounded_reachable_identification

/-- Same-context-variant existential theorem. -/
theorem trimmed_existential_paper_same_context_main_theorem
    (h :
      Nonempty
        (TrimmedPresentationBoundedGlobalPaperSameContextWitness
          (G := G) (obs := obs))) :
    ExistsBoundedReachableIdentification G obs :=
  match h with
  | ⟨W⟩ => W.exists_bounded_reachable_identification

/-- Same-context-variant existential theorem through exposing conversion. -/
theorem trimmed_existential_paper_same_context_via_exposing_theorem
    (h :
      Nonempty
        (TrimmedPresentationBoundedGlobalPaperSameContextWitness
          (G := G) (obs := obs))) :
    ExistsBoundedReachableIdentification G obs :=
  match h with
  | ⟨W⟩ => W.exists_bounded_reachable_identification_via_exposing

end NonemptyWitnessTheorems

end MCFG
