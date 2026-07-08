/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG.CharacteristicSampleExistentialPaperTheorem

/-!
# CharacteristicSampleExposingTransportConstruction.lean

Ninety-sixth clean Lean experiment for the fixed-observation MCFG project.

The previous files built theorem-facing facades up to the existential paper
statement.  This file starts the next phase: isolate an actual construction
target for one remaining semantic obligation.

The target of this file is the direct exposing-context route.  The package

```lean
TrimmedPresentationExposingTransportConstructionData
```

contains the concrete objects that a future construction should provide:

* a fanout bound;
* a trimmed output-type presentation;
* a pre-core datum over that presentation;
* a grammar-rule builder;
* an exposing-context transport witness;
* a named-context splicing constructor;
* fanout and fixed-observation substitutability assumptions.

From this construction data we build the bounded global exposing witness and
therefore obtain the current existential paper theorem.

No new mathematical principle is introduced here.  This file is the first
construction-facing entry point after the paper-facing packaging layer.

No theorem here uses `sorry`.
-/

namespace MCFG

universe u v w

section ExposingTransportConstruction

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}

/-- Construction-facing package for the direct exposing-context route.

Unlike the previous paper-facing witness packages, this record spells out the
concrete pieces that have to be constructed. -/
structure TrimmedPresentationExposingTransportConstructionData where
  fanoutBound : Nat
  presentation : TrimmedOutputTypePresentation G obs
  data : TrimmedPresentationPreCoreData presentation fanoutBound
  builder : TrimmedPresentationGrammarRuleBuilder data
  exposingTransport : TrimmedPresentationExposingContextTransport data
  splicingConstructor : NamedContextSplicingConstructor α
  fanout : G.FanoutAtMost fanoutBound
  promise : FixedNamedTupleSubstitutable fanoutBound obs G.StringLanguage

namespace TrimmedPresentationExposingTransportConstructionData

/-- Convert construction-facing data to the paper-facing exposing assumptions. -/
def toPaperExposingAssumptions
    (C : TrimmedPresentationExposingTransportConstructionData
      (G := G) (obs := obs)) :
    TrimmedPresentationPaperExposingAssumptions C.data where
  builder := C.builder
  exposingTransport := C.exposingTransport
  splicingConstructor := C.splicingConstructor
  fanout := C.fanout
  promise := C.promise

/-- Convert construction-facing data to a paper exposing witness. -/
def toPaperExposingWitness
    (C : TrimmedPresentationExposingTransportConstructionData
      (G := G) (obs := obs)) :
    TrimmedPresentationPaperExposingWitness
      (G := G) (obs := obs) (f := C.fanoutBound) C.presentation where
  data := C.data
  assumptions := C.toPaperExposingAssumptions

/-- Convert construction-facing data to a global paper exposing witness. -/
def toGlobalPaperExposingWitness
    (C : TrimmedPresentationExposingTransportConstructionData
      (G := G) (obs := obs)) :
    TrimmedPresentationGlobalPaperExposingWitness
      (G := G) (obs := obs) (f := C.fanoutBound) where
  presentation := C.presentation
  witness := C.toPaperExposingWitness

/-- Convert construction-facing data to a bounded global paper exposing witness. -/
def toBoundedGlobalPaperExposingWitness
    (C : TrimmedPresentationExposingTransportConstructionData
      (G := G) (obs := obs)) :
    TrimmedPresentationBoundedGlobalPaperExposingWitness
      (G := G) (obs := obs) where
  fanoutBound := C.fanoutBound
  witness := C.toGlobalPaperExposingWitness

/-- The finite sample extracted from exposing construction data. -/
def sample
    (C : TrimmedPresentationExposingTransportConstructionData
      (G := G) (obs := obs)) :
    Finset (Word α) :=
  C.toBoundedGlobalPaperExposingWitness.sample

/-- The extracted sample is positive. -/
theorem sample_positive
    (C : TrimmedPresentationExposingTransportConstructionData
      (G := G) (obs := obs)) :
    (C.sample : Set (Word α)) ⊆ G.StringLanguage :=
  C.toBoundedGlobalPaperExposingWitness.sample_positive

/-- The extracted sample is characteristic at the constructed bound. -/
theorem characteristic_sample
    (C : TrimmedPresentationExposingTransportConstructionData
      (G := G) (obs := obs)) :
    CharacteristicSample
      (reachableHypLanguage obs C.fanoutBound)
      (reachableSampleLearner (α := α))
      C.sample
      G.StringLanguage :=
  C.toBoundedGlobalPaperExposingWitness.characteristic_sample

/-- Existence of a finite positive characteristic sample at the constructed
bound. -/
theorem exists_positive_characteristic_sample
    (C : TrimmedPresentationExposingTransportConstructionData
      (G := G) (obs := obs)) :
    ∃ S : Finset (Word α),
      (S : Set (Word α)) ⊆ G.StringLanguage ∧
      CharacteristicSample
        (reachableHypLanguage obs C.fanoutBound)
        (reachableSampleLearner (α := α))
        S
        G.StringLanguage :=
  C.toBoundedGlobalPaperExposingWitness.exists_positive_characteristic_sample

/-- Existence of a bound and a finite positive characteristic sample. -/
theorem exists_bound_and_positive_characteristic_sample
    (C : TrimmedPresentationExposingTransportConstructionData
      (G := G) (obs := obs)) :
    ExistsBoundedPositiveCharacteristicSample G obs :=
  C.toBoundedGlobalPaperExposingWitness
    .exists_bounded_positive_characteristic_sample

/-- Eventual prefix-exact reconstruction at the constructed bound. -/
theorem prefix_exact_eventually
    (C : TrimmedPresentationExposingTransportConstructionData
      (G := G) (obs := obs)) :
    ∀ Ttxt : TextFor G.StringLanguage,
      ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
        ReachableSampleStringLanguage
          (Ttxt.prefixSample n) obs C.fanoutBound =
          G.StringLanguage :=
  C.toBoundedGlobalPaperExposingWitness.prefix_exact_eventually

/-- Existential prefix-exact reconstruction. -/
theorem exists_bounded_prefix_exact_identification
    (C : TrimmedPresentationExposingTransportConstructionData
      (G := G) (obs := obs)) :
    ExistsBoundedPrefixExactIdentification G obs :=
  C.toBoundedGlobalPaperExposingWitness
    .exists_bounded_prefix_exact_identification

/-- Gold-style identification at the constructed bound. -/
theorem identifies_from_positive_text
    (C : TrimmedPresentationExposingTransportConstructionData
      (G := G) (obs := obs)) :
    ∀ Ttxt : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs C.fanoutBound)
        (reachableSampleLearner (α := α))
        Ttxt :=
  C.toBoundedGlobalPaperExposingWitness.identifies_from_positive_text

/-- Existential Gold-style identification. -/
theorem exists_bounded_reachable_identification
    (C : TrimmedPresentationExposingTransportConstructionData
      (G := G) (obs := obs)) :
    ExistsBoundedReachableIdentification G obs :=
  C.toBoundedGlobalPaperExposingWitness
    .exists_bounded_reachable_identification

/-- Pointwise eventual correctness on one positive text. -/
theorem eventually_correct_on_text
    (C : TrimmedPresentationExposingTransportConstructionData
      (G := G) (obs := obs))
    (Ttxt : TextFor G.StringLanguage) :
    EventuallyCorrectOnText
      (reachableHypLanguage obs C.fanoutBound)
      (reachableSampleLearner (α := α))
      Ttxt :=
  C.identifies_from_positive_text Ttxt

end TrimmedPresentationExposingTransportConstructionData

end ExposingTransportConstruction


section ExposingTransportConstructionTheorems

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}

/-- Construction-facing theorem: direct exposing construction data gives a
finite positive characteristic sample at its constructed bound. -/
theorem trimmed_exposing_transport_construction_exists_characteristic_sample
    (C : TrimmedPresentationExposingTransportConstructionData
      (G := G) (obs := obs)) :
    ExistsBoundedPositiveCharacteristicSample G obs :=
  C.exists_bound_and_positive_characteristic_sample

/-- Construction-facing theorem: direct exposing construction data gives
eventual prefix exactness for some bound. -/
theorem trimmed_exposing_transport_construction_prefix_exact_theorem
    (C : TrimmedPresentationExposingTransportConstructionData
      (G := G) (obs := obs)) :
    ExistsBoundedPrefixExactIdentification G obs :=
  C.exists_bounded_prefix_exact_identification

/-- Construction-facing theorem: direct exposing construction data gives
Gold-style identification for some bound. -/
theorem trimmed_exposing_transport_construction_main_theorem
    (C : TrimmedPresentationExposingTransportConstructionData
      (G := G) (obs := obs)) :
    ExistsBoundedReachableIdentification G obs :=
  C.exists_bounded_reachable_identification

/-- Nonempty version of the exposing construction theorem. -/
theorem trimmed_exposing_transport_construction_main_theorem_of_nonempty
    (h :
      Nonempty
        (TrimmedPresentationExposingTransportConstructionData
          (G := G) (obs := obs))) :
    ExistsBoundedReachableIdentification G obs :=
  match h with
  | ⟨C⟩ => C.exists_bounded_reachable_identification

/-- Nonempty version of the exposing construction characteristic-sample theorem. -/
theorem trimmed_exposing_transport_construction_characteristic_sample_of_nonempty
    (h :
      Nonempty
        (TrimmedPresentationExposingTransportConstructionData
          (G := G) (obs := obs))) :
    ExistsBoundedPositiveCharacteristicSample G obs :=
  match h with
  | ⟨C⟩ => C.exists_bound_and_positive_characteristic_sample

end ExposingTransportConstructionTheorems

end MCFG
