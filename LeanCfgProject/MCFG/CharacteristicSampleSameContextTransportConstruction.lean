/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG.CharacteristicSampleAnchorCommonTransportConstruction

/-!
# CharacteristicSampleSameContextTransportConstruction.lean

Ninety-eighth clean Lean experiment for the fixed-observation MCFG project.

The previous construction-facing files introduced direct exposing-context
construction data and the preferred anchor-common-context construction data.

This file introduces the stronger same-context construction package.  This is
mostly a debugging and comparison route:

```text
SameContextTransport
⇒ ExposingContextTransport
⇒ reachable identification.
```

The package

```lean
TrimmedPresentationSameContextTransportConstructionData
```

spells out the concrete data needed for the same-context route and converts it
to both:

* `TrimmedPresentationBoundedGlobalPaperSameContextWitness`;
* `TrimmedPresentationExposingTransportConstructionData`.

No new mathematical principle is introduced here.

No theorem here uses `sorry`.
-/

namespace MCFG

universe u v w

section SameContextTransportConstruction

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}

/-- Construction-facing package for the stronger same-context route. -/
structure TrimmedPresentationSameContextTransportConstructionData where
  fanoutBound : Nat
  presentation : TrimmedOutputTypePresentation G obs
  data : TrimmedPresentationPreCoreData presentation fanoutBound
  builder : TrimmedPresentationGrammarRuleBuilder data
  sameContextTransport : TrimmedPresentationSameContextTransport data
  splicingConstructor : NamedContextSplicingConstructor α
  fanout : G.FanoutAtMost fanoutBound
  promise : FixedNamedTupleSubstitutable fanoutBound obs G.StringLanguage

namespace TrimmedPresentationSameContextTransportConstructionData

/-- The exposing-context transport obtained from same-context transport. -/
def exposingTransport
    (C : TrimmedPresentationSameContextTransportConstructionData
      (G := G) (obs := obs)) :
    TrimmedPresentationExposingContextTransport C.data :=
  TrimmedPresentationExposingContextTransport.ofSameContextTransport
    C.sameContextTransport

/-- Convert construction-facing same-context data to the paper-facing
same-context assumptions. -/
def toPaperSameContextAssumptions
    (C : TrimmedPresentationSameContextTransportConstructionData
      (G := G) (obs := obs)) :
    TrimmedPresentationPaperSameContextAssumptions C.data where
  builder := C.builder
  sameContextTransport := C.sameContextTransport
  splicingConstructor := C.splicingConstructor
  fanout := C.fanout
  promise := C.promise

/-- Convert construction-facing same-context data to a paper same-context
witness. -/
def toPaperSameContextWitness
    (C : TrimmedPresentationSameContextTransportConstructionData
      (G := G) (obs := obs)) :
    TrimmedPresentationPaperSameContextWitness
      (G := G) (obs := obs) (f := C.fanoutBound) C.presentation where
  data := C.data
  assumptions := C.toPaperSameContextAssumptions

/-- Convert construction-facing same-context data to a global paper same-context
witness. -/
def toGlobalPaperSameContextWitness
    (C : TrimmedPresentationSameContextTransportConstructionData
      (G := G) (obs := obs)) :
    TrimmedPresentationGlobalPaperSameContextWitness
      (G := G) (obs := obs) (f := C.fanoutBound) where
  presentation := C.presentation
  witness := C.toPaperSameContextWitness

/-- Convert construction-facing same-context data to a bounded global paper
same-context witness. -/
def toBoundedGlobalPaperSameContextWitness
    (C : TrimmedPresentationSameContextTransportConstructionData
      (G := G) (obs := obs)) :
    TrimmedPresentationBoundedGlobalPaperSameContextWitness
      (G := G) (obs := obs) where
  fanoutBound := C.fanoutBound
  witness := C.toGlobalPaperSameContextWitness

/-- Convert same-context construction data to direct exposing construction data. -/
def toExposingTransportConstructionData
    (C : TrimmedPresentationSameContextTransportConstructionData
      (G := G) (obs := obs)) :
    TrimmedPresentationExposingTransportConstructionData
      (G := G) (obs := obs) where
  fanoutBound := C.fanoutBound
  presentation := C.presentation
  data := C.data
  builder := C.builder
  exposingTransport := C.exposingTransport
  splicingConstructor := C.splicingConstructor
  fanout := C.fanout
  promise := C.promise

/-- The finite sample extracted from same-context construction data. -/
def sample
    (C : TrimmedPresentationSameContextTransportConstructionData
      (G := G) (obs := obs)) :
    Finset (Word α) :=
  C.toBoundedGlobalPaperSameContextWitness.sample

/-- The extracted sample is positive. -/
theorem sample_positive
    (C : TrimmedPresentationSameContextTransportConstructionData
      (G := G) (obs := obs)) :
    (C.sample : Set (Word α)) ⊆ G.StringLanguage :=
  C.toBoundedGlobalPaperSameContextWitness.sample_positive

/-- The extracted sample is characteristic at the constructed bound. -/
theorem characteristic_sample
    (C : TrimmedPresentationSameContextTransportConstructionData
      (G := G) (obs := obs)) :
    CharacteristicSample
      (reachableHypLanguage obs C.fanoutBound)
      (reachableSampleLearner (α := α))
      C.sample
      G.StringLanguage :=
  C.toBoundedGlobalPaperSameContextWitness.characteristic_sample

/-- Existence of a finite positive characteristic sample at the constructed
bound. -/
theorem exists_positive_characteristic_sample
    (C : TrimmedPresentationSameContextTransportConstructionData
      (G := G) (obs := obs)) :
    ∃ S : Finset (Word α),
      (S : Set (Word α)) ⊆ G.StringLanguage ∧
      CharacteristicSample
        (reachableHypLanguage obs C.fanoutBound)
        (reachableSampleLearner (α := α))
        S
        G.StringLanguage :=
  C.toBoundedGlobalPaperSameContextWitness.exists_positive_characteristic_sample

/-- Existence of a bound and a finite positive characteristic sample. -/
theorem exists_bound_and_positive_characteristic_sample
    (C : TrimmedPresentationSameContextTransportConstructionData
      (G := G) (obs := obs)) :
    ExistsBoundedPositiveCharacteristicSample G obs :=
  C.toBoundedGlobalPaperSameContextWitness
    .exists_bounded_positive_characteristic_sample

/-- Eventual prefix-exact reconstruction at the constructed bound. -/
theorem prefix_exact_eventually
    (C : TrimmedPresentationSameContextTransportConstructionData
      (G := G) (obs := obs)) :
    ∀ Ttxt : TextFor G.StringLanguage,
      ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
        ReachableSampleStringLanguage
          (Ttxt.prefixSample n) obs C.fanoutBound =
          G.StringLanguage :=
  C.toBoundedGlobalPaperSameContextWitness.prefix_exact_eventually

/-- Existential prefix-exact reconstruction. -/
theorem exists_bounded_prefix_exact_identification
    (C : TrimmedPresentationSameContextTransportConstructionData
      (G := G) (obs := obs)) :
    ExistsBoundedPrefixExactIdentification G obs :=
  C.toBoundedGlobalPaperSameContextWitness
    .exists_bounded_prefix_exact_identification

/-- Gold-style identification at the constructed bound. -/
theorem identifies_from_positive_text
    (C : TrimmedPresentationSameContextTransportConstructionData
      (G := G) (obs := obs)) :
    ∀ Ttxt : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs C.fanoutBound)
        (reachableSampleLearner (α := α))
        Ttxt :=
  C.toBoundedGlobalPaperSameContextWitness.identifies_from_positive_text

/-- Existential Gold-style identification. -/
theorem exists_bounded_reachable_identification
    (C : TrimmedPresentationSameContextTransportConstructionData
      (G := G) (obs := obs)) :
    ExistsBoundedReachableIdentification G obs :=
  C.toBoundedGlobalPaperSameContextWitness
    .exists_bounded_reachable_identification

/-- Gold-style identification through the exposing-construction route. -/
theorem exists_bounded_reachable_identification_via_exposing
    (C : TrimmedPresentationSameContextTransportConstructionData
      (G := G) (obs := obs)) :
    ExistsBoundedReachableIdentification G obs :=
  C.toExposingTransportConstructionData
    .exists_bounded_reachable_identification

/-- Pointwise eventual correctness on one positive text. -/
theorem eventually_correct_on_text
    (C : TrimmedPresentationSameContextTransportConstructionData
      (G := G) (obs := obs))
    (Ttxt : TextFor G.StringLanguage) :
    EventuallyCorrectOnText
      (reachableHypLanguage obs C.fanoutBound)
      (reachableSampleLearner (α := α))
      Ttxt :=
  C.identifies_from_positive_text Ttxt

end TrimmedPresentationSameContextTransportConstructionData

end SameContextTransportConstruction


section SameContextTransportConstructionTheorems

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}

/-- Construction-facing theorem: same-context construction data gives a finite
positive characteristic sample for some bound. -/
theorem trimmed_same_context_transport_construction_exists_characteristic_sample
    (C : TrimmedPresentationSameContextTransportConstructionData
      (G := G) (obs := obs)) :
    ExistsBoundedPositiveCharacteristicSample G obs :=
  C.exists_bound_and_positive_characteristic_sample

/-- Construction-facing theorem: same-context construction data gives eventual
prefix exactness for some bound. -/
theorem trimmed_same_context_transport_construction_prefix_exact_theorem
    (C : TrimmedPresentationSameContextTransportConstructionData
      (G := G) (obs := obs)) :
    ExistsBoundedPrefixExactIdentification G obs :=
  C.exists_bounded_prefix_exact_identification

/-- Construction-facing theorem: same-context construction data gives Gold-style
identification for some bound. -/
theorem trimmed_same_context_transport_construction_main_theorem
    (C : TrimmedPresentationSameContextTransportConstructionData
      (G := G) (obs := obs)) :
    ExistsBoundedReachableIdentification G obs :=
  C.exists_bounded_reachable_identification

/-- Construction-facing theorem: same-context construction data gives Gold-style
identification through the exposing-construction route. -/
theorem trimmed_same_context_transport_construction_main_theorem_via_exposing
    (C : TrimmedPresentationSameContextTransportConstructionData
      (G := G) (obs := obs)) :
    ExistsBoundedReachableIdentification G obs :=
  C.exists_bounded_reachable_identification_via_exposing

/-- Nonempty version of the same-context construction theorem. -/
theorem trimmed_same_context_transport_construction_main_theorem_of_nonempty
    (h :
      Nonempty
        (TrimmedPresentationSameContextTransportConstructionData
          (G := G) (obs := obs))) :
    ExistsBoundedReachableIdentification G obs :=
  match h with
  | ⟨C⟩ => C.exists_bounded_reachable_identification

/-- Nonempty version of the same-context construction characteristic-sample
theorem. -/
theorem trimmed_same_context_transport_construction_characteristic_sample_of_nonempty
    (h :
      Nonempty
        (TrimmedPresentationSameContextTransportConstructionData
          (G := G) (obs := obs))) :
    ExistsBoundedPositiveCharacteristicSample G obs :=
  match h with
  | ⟨C⟩ => C.exists_bound_and_positive_characteristic_sample

end SameContextTransportConstructionTheorems

end MCFG
