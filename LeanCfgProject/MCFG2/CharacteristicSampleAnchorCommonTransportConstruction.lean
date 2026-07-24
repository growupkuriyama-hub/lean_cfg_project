/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG2.CharacteristicSampleExposingTransportConstruction

/-!
# CharacteristicSampleAnchorCommonTransportConstruction.lean

Ninety-seventh clean Lean experiment for the fixed-observation MCFG project.

`CharacteristicSampleExposingTransportConstruction.lean` introduced a
construction-facing package for the direct exposing-context route.

This file introduces the construction-facing package for the preferred
paper route:

```text
AnchorCommonContextTransport.
```

The package

```lean
TrimmedPresentationAnchorCommonTransportConstructionData
```

spells out the concrete pieces needed for the main paper-facing theorem:

* a fanout bound;
* a trimmed output-type presentation;
* a pre-core datum over that presentation;
* a grammar-rule builder;
* an anchor common-context transport witness;
* a named-context splicing constructor;
* fanout and fixed-observation substitutability assumptions.

It then converts this data both to:

* `TrimmedPresentationBoundedGlobalPaperMainWitness`;
* `TrimmedPresentationExposingTransportConstructionData`.

Thus this file records, at the construction-facing level, that the preferred
common-context construction also supplies the exposing-construction route.

No new mathematical principle is introduced here.

No theorem here uses `sorry`.
-/

namespace MCFG

universe u v w

section AnchorCommonTransportConstruction

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}

/-- Construction-facing package for the preferred anchor common-context route. -/
structure TrimmedPresentationAnchorCommonTransportConstructionData where
  fanoutBound : Nat
  presentation : TrimmedOutputTypePresentation G obs
  data : TrimmedPresentationPreCoreData presentation fanoutBound
  builder : TrimmedPresentationGrammarRuleBuilder data
  commonTransport : TrimmedPresentationAnchorCommonContextTransport data
  splicingConstructor : NamedContextSplicingConstructor α
  fanout : G.FanoutAtMost fanoutBound
  promise : FixedNamedTupleSubstitutable fanoutBound obs G.StringLanguage

namespace TrimmedPresentationAnchorCommonTransportConstructionData

/-- The exposing-context transport obtained from anchor common-context transport. -/
def exposingTransport
    (C : TrimmedPresentationAnchorCommonTransportConstructionData
      (G := G) (obs := obs)) :
    TrimmedPresentationExposingContextTransport C.data :=
  C.commonTransport.toExposingContextTransport C.fanout C.promise

/-- Convert construction-facing data to the paper-facing main assumptions. -/
def toPaperMainAssumptions
    (C : TrimmedPresentationAnchorCommonTransportConstructionData
      (G := G) (obs := obs)) :
    TrimmedPresentationPaperMainAssumptions C.data where
  builder := C.builder
  commonTransport := C.commonTransport
  splicingConstructor := C.splicingConstructor
  fanout := C.fanout
  promise := C.promise

/-- Convert construction-facing data to a paper main witness. -/
def toPaperMainWitness
    (C : TrimmedPresentationAnchorCommonTransportConstructionData
      (G := G) (obs := obs)) :
    TrimmedPresentationPaperMainWitness
      (G := G) (obs := obs) (f := C.fanoutBound) C.presentation where
  data := C.data
  assumptions := C.toPaperMainAssumptions

/-- Convert construction-facing data to a global paper main witness. -/
def toGlobalPaperMainWitness
    (C : TrimmedPresentationAnchorCommonTransportConstructionData
      (G := G) (obs := obs)) :
    TrimmedPresentationGlobalPaperMainWitness
      (G := G) (obs := obs) (f := C.fanoutBound) where
  presentation := C.presentation
  witness := C.toPaperMainWitness

/-- Convert construction-facing data to a bounded global paper main witness. -/
def toBoundedGlobalPaperMainWitness
    (C : TrimmedPresentationAnchorCommonTransportConstructionData
      (G := G) (obs := obs)) :
    TrimmedPresentationBoundedGlobalPaperMainWitness
      (G := G) (obs := obs) where
  fanoutBound := C.fanoutBound
  witness := C.toGlobalPaperMainWitness

/-- Convert preferred common-context construction data to direct exposing
construction data. -/
def toExposingTransportConstructionData
    (C : TrimmedPresentationAnchorCommonTransportConstructionData
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

/-- The finite sample extracted from common-context construction data. -/
noncomputable def sample
    (C : TrimmedPresentationAnchorCommonTransportConstructionData
      (G := G) (obs := obs)) :
    Finset (Word α) :=
  C.toBoundedGlobalPaperMainWitness.sample

/-- The extracted sample is positive. -/
theorem sample_positive
    (C : TrimmedPresentationAnchorCommonTransportConstructionData
      (G := G) (obs := obs)) :
    (C.sample : Set (Word α)) ⊆ G.StringLanguage :=
  C.toBoundedGlobalPaperMainWitness.sample_positive

/-- The extracted sample is characteristic at the constructed bound. -/
theorem characteristic_sample
    (C : TrimmedPresentationAnchorCommonTransportConstructionData
      (G := G) (obs := obs)) :
    CharacteristicSample
      (reachableHypLanguage obs C.fanoutBound)
      (reachableSampleLearner (α := α))
      C.sample
      G.StringLanguage :=
  C.toBoundedGlobalPaperMainWitness.characteristic_sample

/-- Existence of a finite positive characteristic sample at the constructed
bound. -/
theorem exists_positive_characteristic_sample
    (C : TrimmedPresentationAnchorCommonTransportConstructionData
      (G := G) (obs := obs)) :
    ∃ S : Finset (Word α),
      (S : Set (Word α)) ⊆ G.StringLanguage ∧
      CharacteristicSample
        (reachableHypLanguage obs C.fanoutBound)
        (reachableSampleLearner (α := α))
        S
        G.StringLanguage :=
  C.toBoundedGlobalPaperMainWitness.exists_positive_characteristic_sample

/-- Existence of a bound and a finite positive characteristic sample. -/
theorem exists_bound_and_positive_characteristic_sample
    (C : TrimmedPresentationAnchorCommonTransportConstructionData
      (G := G) (obs := obs)) :
    ExistsBoundedPositiveCharacteristicSample G obs :=
  C.toBoundedGlobalPaperMainWitness.exists_bounded_positive_characteristic_sample

/-- Eventual prefix-exact reconstruction at the constructed bound. -/
theorem prefix_exact_eventually
    (C : TrimmedPresentationAnchorCommonTransportConstructionData
      (G := G) (obs := obs)) :
    ∀ Ttxt : TextFor G.StringLanguage,
      ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
        ReachableSampleStringLanguage
          (Ttxt.prefixSample n) obs C.fanoutBound =
          G.StringLanguage :=
  C.toBoundedGlobalPaperMainWitness.prefix_exact_eventually

/-- Existential prefix-exact reconstruction. -/
theorem exists_bounded_prefix_exact_identification
    (C : TrimmedPresentationAnchorCommonTransportConstructionData
      (G := G) (obs := obs)) :
    ExistsBoundedPrefixExactIdentification G obs :=
  C.toBoundedGlobalPaperMainWitness.exists_bounded_prefix_exact_identification

/-- Gold-style identification at the constructed bound. -/
theorem identifies_from_positive_text
    (C : TrimmedPresentationAnchorCommonTransportConstructionData
      (G := G) (obs := obs)) :
    ∀ Ttxt : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs C.fanoutBound)
        (reachableSampleLearner (α := α))
        Ttxt :=
  C.toBoundedGlobalPaperMainWitness.identifies_from_positive_text

/-- Existential Gold-style identification. -/
theorem exists_bounded_reachable_identification
    (C : TrimmedPresentationAnchorCommonTransportConstructionData
      (G := G) (obs := obs)) :
    ExistsBoundedReachableIdentification G obs :=
  C.toBoundedGlobalPaperMainWitness.exists_bounded_reachable_identification

/-- Gold-style identification through the exposing-construction route. -/
theorem exists_bounded_reachable_identification_via_exposing
    (C : TrimmedPresentationAnchorCommonTransportConstructionData
      (G := G) (obs := obs)) :
    ExistsBoundedReachableIdentification G obs :=
  C.toExposingTransportConstructionData.exists_bounded_reachable_identification

/-- Pointwise eventual correctness on one positive text. -/
theorem eventually_correct_on_text
    (C : TrimmedPresentationAnchorCommonTransportConstructionData
      (G := G) (obs := obs))
    (Ttxt : TextFor G.StringLanguage) :
    EventuallyCorrectOnText
      (reachableHypLanguage obs C.fanoutBound)
      (reachableSampleLearner (α := α))
      Ttxt :=
  C.identifies_from_positive_text Ttxt

end TrimmedPresentationAnchorCommonTransportConstructionData

end AnchorCommonTransportConstruction


section AnchorCommonTransportConstructionTheorems

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}

/-- Construction-facing theorem: common-context construction data gives a
finite positive characteristic sample for some bound. -/
theorem trimmed_anchor_common_transport_construction_exists_characteristic_sample
    (C : TrimmedPresentationAnchorCommonTransportConstructionData
      (G := G) (obs := obs)) :
    ExistsBoundedPositiveCharacteristicSample G obs :=
  C.exists_bound_and_positive_characteristic_sample

/-- Construction-facing theorem: common-context construction data gives
eventual prefix exactness for some bound. -/
theorem trimmed_anchor_common_transport_construction_prefix_exact_theorem
    (C : TrimmedPresentationAnchorCommonTransportConstructionData
      (G := G) (obs := obs)) :
    ExistsBoundedPrefixExactIdentification G obs :=
  C.exists_bounded_prefix_exact_identification

/-- Construction-facing theorem: common-context construction data gives
Gold-style identification for some bound. -/
theorem trimmed_anchor_common_transport_construction_main_theorem
    (C : TrimmedPresentationAnchorCommonTransportConstructionData
      (G := G) (obs := obs)) :
    ExistsBoundedReachableIdentification G obs :=
  C.exists_bounded_reachable_identification

/-- Construction-facing theorem: common-context construction data gives
Gold-style identification through the exposing-construction route. -/
theorem trimmed_anchor_common_transport_construction_main_theorem_via_exposing
    (C : TrimmedPresentationAnchorCommonTransportConstructionData
      (G := G) (obs := obs)) :
    ExistsBoundedReachableIdentification G obs :=
  C.exists_bounded_reachable_identification_via_exposing

/-- Nonempty version of the common-context construction theorem. -/
theorem trimmed_anchor_common_transport_construction_main_theorem_of_nonempty
    (h :
      Nonempty
        (TrimmedPresentationAnchorCommonTransportConstructionData
          (G := G) (obs := obs))) :
    ExistsBoundedReachableIdentification G obs :=
  match h with
  | ⟨C⟩ => C.exists_bounded_reachable_identification

/-- Nonempty version of the common-context construction characteristic-sample
theorem. -/
theorem trimmed_anchor_common_transport_construction_characteristic_sample_of_nonempty
    (h :
      Nonempty
        (TrimmedPresentationAnchorCommonTransportConstructionData
          (G := G) (obs := obs))) :
    ExistsBoundedPositiveCharacteristicSample G obs :=
  match h with
  | ⟨C⟩ => C.exists_bound_and_positive_characteristic_sample

end AnchorCommonTransportConstructionTheorems

end MCFG
