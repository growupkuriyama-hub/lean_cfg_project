/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG.CharacteristicSampleBaseConstructionLayers

/-!
# CharacteristicSampleCoreConstructionLayers.lean

One-hundred-fourth clean Lean experiment for the fixed-observation MCFG project.

`CharacteristicSampleBaseConstructionLayers.lean` split the construction problem
into:

```text
CoreConstructionData
+
GlobalConstructionAssumptions
+
TransportWitnessChoice.
```

This file splits the core construction data itself into three layers:

1. presentation layer:
   a fanout bound and a trimmed output-type presentation;
2. pre-core layer:
   a `TrimmedPresentationPreCoreData` over that presentation;
3. grammar-rule-builder layer:
   a `TrimmedPresentationGrammarRuleBuilder` over the pre-core datum.

This prepares the next phase where the actual construction of

```text
T : TrimmedOutputTypePresentation G obs
D : TrimmedPresentationPreCoreData T f
builder : TrimmedPresentationGrammarRuleBuilder D
```

can be attacked separately.

No new mathematical principle is introduced here.

No theorem here uses `sorry`.
-/

namespace MCFG

universe u v w

section CoreLayerRecords

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}

/-- First core layer: a fanout bound and a trimmed output-type presentation. -/
structure TrimmedPresentationPresentationConstructionData where
  fanoutBound : Nat
  presentation : TrimmedOutputTypePresentation G obs

/-- Second core layer: pre-core data over a presentation construction layer. -/
structure TrimmedPresentationPreCoreConstructionData where
  presentationLayer :
    TrimmedPresentationPresentationConstructionData
      (G := G) (obs := obs)
  data :
    TrimmedPresentationPreCoreData
      presentationLayer.presentation
      presentationLayer.fanoutBound

/-- Third core layer: grammar-rule builder data over a pre-core layer. -/
structure TrimmedPresentationRuleBuilderConstructionData where
  preCoreLayer :
    TrimmedPresentationPreCoreConstructionData
      (G := G) (obs := obs)
  builder :
    TrimmedPresentationGrammarRuleBuilder preCoreLayer.data

namespace TrimmedPresentationPresentationConstructionData

/-- The presentation layer is the first component of a pre-core layer. -/
def withPreCoreData
    (P : TrimmedPresentationPresentationConstructionData
      (G := G) (obs := obs))
    (D : TrimmedPresentationPreCoreData
      P.presentation P.fanoutBound) :
    TrimmedPresentationPreCoreConstructionData
      (G := G) (obs := obs) where
  presentationLayer := P
  data := D

end TrimmedPresentationPresentationConstructionData


namespace TrimmedPresentationPreCoreConstructionData

/-- Add a grammar-rule builder to a pre-core layer. -/
def withGrammarRuleBuilder
    (D : TrimmedPresentationPreCoreConstructionData
      (G := G) (obs := obs))
    (builder : TrimmedPresentationGrammarRuleBuilder D.data) :
    TrimmedPresentationRuleBuilderConstructionData
      (G := G) (obs := obs) where
  preCoreLayer := D
  builder := builder

/-- The fanout bound inherited from the presentation layer. -/
def fanoutBound
    (D : TrimmedPresentationPreCoreConstructionData
      (G := G) (obs := obs)) : Nat :=
  D.presentationLayer.fanoutBound

/-- The trimmed output-type presentation inherited from the presentation layer. -/
def presentation
    (D : TrimmedPresentationPreCoreConstructionData
      (G := G) (obs := obs)) :
    TrimmedOutputTypePresentation G obs :=
  D.presentationLayer.presentation

end TrimmedPresentationPreCoreConstructionData


namespace TrimmedPresentationRuleBuilderConstructionData

/-- The fanout bound inherited from the lower layers. -/
def fanoutBound
    (R : TrimmedPresentationRuleBuilderConstructionData
      (G := G) (obs := obs)) : Nat :=
  R.preCoreLayer.presentationLayer.fanoutBound

/-- The trimmed output-type presentation inherited from the lower layers. -/
def presentation
    (R : TrimmedPresentationRuleBuilderConstructionData
      (G := G) (obs := obs)) :
    TrimmedOutputTypePresentation G obs :=
  R.preCoreLayer.presentationLayer.presentation

/-- The pre-core datum inherited from the lower layer. -/
def data
    (R : TrimmedPresentationRuleBuilderConstructionData
      (G := G) (obs := obs)) :
    TrimmedPresentationPreCoreData R.presentation R.fanoutBound :=
  R.preCoreLayer.data

/-- Convert the three core layers back to the previous core-construction
package. -/
def toCoreConstructionData
    (R : TrimmedPresentationRuleBuilderConstructionData
      (G := G) (obs := obs)) :
    TrimmedPresentationCoreConstructionData
      (G := G) (obs := obs) where
  fanoutBound := R.fanoutBound
  presentation := R.presentation
  data := R.data
  builder := R.builder

/-- Add global assumptions to the reconstructed core package. -/
def toBaseConstructionData
    (R : TrimmedPresentationRuleBuilderConstructionData
      (G := G) (obs := obs))
    (A :
      TrimmedPresentationGlobalConstructionAssumptions
        R.toCoreConstructionData) :
    TrimmedPresentationBaseConstructionData
      (G := G) (obs := obs) :=
  R.toCoreConstructionData.toBaseConstructionData A

/-- Add global assumptions and direct exposing-context transport. -/
def toExposingTransportConstructionData
    (R : TrimmedPresentationRuleBuilderConstructionData
      (G := G) (obs := obs))
    (A :
      TrimmedPresentationGlobalConstructionAssumptions
        R.toCoreConstructionData)
    (E :
      TrimmedPresentationExposingContextTransport
        R.toCoreConstructionData.data) :
    TrimmedPresentationExposingTransportConstructionData
      (G := G) (obs := obs) :=
  R.toCoreConstructionData.toExposingTransportConstructionData A E

/-- Add global assumptions and anchor common-context transport. -/
def toAnchorCommonTransportConstructionData
    (R : TrimmedPresentationRuleBuilderConstructionData
      (G := G) (obs := obs))
    (A :
      TrimmedPresentationGlobalConstructionAssumptions
        R.toCoreConstructionData)
    (C :
      TrimmedPresentationAnchorCommonContextTransport
        R.toCoreConstructionData.data) :
    TrimmedPresentationAnchorCommonTransportConstructionData
      (G := G) (obs := obs) :=
  R.toCoreConstructionData.toAnchorCommonTransportConstructionData A C

/-- Add global assumptions and same-context transport. -/
def toSameContextTransportConstructionData
    (R : TrimmedPresentationRuleBuilderConstructionData
      (G := G) (obs := obs))
    (A :
      TrimmedPresentationGlobalConstructionAssumptions
        R.toCoreConstructionData)
    (S :
      TrimmedPresentationSameContextTransport
        R.toCoreConstructionData.data) :
    TrimmedPresentationSameContextTransportConstructionData
      (G := G) (obs := obs) :=
  R.toCoreConstructionData.toSameContextTransportConstructionData A S

end TrimmedPresentationRuleBuilderConstructionData

end CoreLayerRecords


section LayeredCoreConstruction

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}

/-- Fully layered construction data using the split core layers. -/
structure TrimmedPresentationFullyLayeredConstructionData where
  ruleBuilderLayer :
    TrimmedPresentationRuleBuilderConstructionData
      (G := G) (obs := obs)
  global :
    TrimmedPresentationGlobalConstructionAssumptions
      ruleBuilderLayer.toCoreConstructionData
  transport :
    TrimmedPresentationTransportWitnessChoice
      (ruleBuilderLayer.toBaseConstructionData global)

namespace TrimmedPresentationFullyLayeredConstructionData

/-- Reconstruct the previous core construction data. -/
def core
    (L : TrimmedPresentationFullyLayeredConstructionData
      (G := G) (obs := obs)) :
    TrimmedPresentationCoreConstructionData
      (G := G) (obs := obs) :=
  L.ruleBuilderLayer.toCoreConstructionData

/-- Reconstruct the previous base construction data. -/
def base
    (L : TrimmedPresentationFullyLayeredConstructionData
      (G := G) (obs := obs)) :
    TrimmedPresentationBaseConstructionData
      (G := G) (obs := obs) :=
  L.ruleBuilderLayer.toBaseConstructionData L.global

/-- Reconstruct the previous layered transport construction data. -/
def toLayeredTransportConstructionData
    (L : TrimmedPresentationFullyLayeredConstructionData
      (G := G) (obs := obs)) :
    TrimmedPresentationLayeredTransportConstructionData
      (G := G) (obs := obs) where
  core := L.core
  global := L.global
  transport := L.transport

/-- Reconstruct the previous structured transport construction data. -/
def toStructuredTransportConstructionData
    (L : TrimmedPresentationFullyLayeredConstructionData
      (G := G) (obs := obs)) :
    TrimmedPresentationStructuredTransportConstructionData
      (G := G) (obs := obs) :=
  L.toLayeredTransportConstructionData
    .toStructuredTransportConstructionData

/-- A fully layered construction datum gives a positive characteristic sample
for some finite fanout bound. -/
theorem exists_bounded_positive_characteristic_sample
    (L : TrimmedPresentationFullyLayeredConstructionData
      (G := G) (obs := obs)) :
    ExistsBoundedPositiveCharacteristicSample G obs :=
  L.toLayeredTransportConstructionData
    .exists_bounded_positive_characteristic_sample

/-- A fully layered construction datum gives prefix exactness for some finite
fanout bound. -/
theorem exists_bounded_prefix_exact_identification
    (L : TrimmedPresentationFullyLayeredConstructionData
      (G := G) (obs := obs)) :
    ExistsBoundedPrefixExactIdentification G obs :=
  L.toLayeredTransportConstructionData
    .exists_bounded_prefix_exact_identification

/-- A fully layered construction datum gives Gold-style identification for some
finite fanout bound. -/
theorem exists_bounded_reachable_identification
    (L : TrimmedPresentationFullyLayeredConstructionData
      (G := G) (obs := obs)) :
    ExistsBoundedReachableIdentification G obs :=
  L.toLayeredTransportConstructionData
    .exists_bounded_reachable_identification

end TrimmedPresentationFullyLayeredConstructionData

end LayeredCoreConstruction


section ExistentialCoreLayers

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}

/-- There exists a fully layered construction datum. -/
def ExistsFullyLayeredTransportConstruction
    (G : WorkingMCFG N α) (obs : α → M) : Prop :=
  Nonempty
    (TrimmedPresentationFullyLayeredConstructionData
      (G := G) (obs := obs))

/-- A fully layered construction gives the previous layered construction
existential interface. -/
theorem existsLayeredTransportConstruction_of_fullyLayered
    (h : ExistsFullyLayeredTransportConstruction G obs) :
    ExistsLayeredTransportConstruction G obs :=
  match h with
  | ⟨L⟩ =>
      ⟨L.core, L.global, ⟨L.transport⟩⟩

/-- A fully layered construction gives the previous base-plus-transport
existential interface. -/
theorem existsBaseWithTransportWitnessChoice_of_fullyLayered
    (h : ExistsFullyLayeredTransportConstruction G obs) :
    ExistsBaseWithTransportWitnessChoice G obs :=
  existsBaseWithTransportWitnessChoice_of_layered
    (existsLayeredTransportConstruction_of_fullyLayered h)

/-- Main theorem from a fully layered construction. -/
theorem existsFullyLayeredTransportConstruction_main_theorem
    (h : ExistsFullyLayeredTransportConstruction G obs) :
    ExistsBoundedReachableIdentification G obs :=
  trimmed_exists_layered_transport_construction_main_theorem
    (existsLayeredTransportConstruction_of_fullyLayered h)

/-- Prefix-exact theorem from a fully layered construction. -/
theorem existsFullyLayeredTransportConstruction_prefix_exact
    (h : ExistsFullyLayeredTransportConstruction G obs) :
    ExistsBoundedPrefixExactIdentification G obs :=
  trimmed_exists_base_transport_choice_prefix_exact_theorem
    (existsBaseWithTransportWitnessChoice_of_fullyLayered h)

/-- Characteristic-sample theorem from a fully layered construction. -/
theorem existsFullyLayeredTransportConstruction_characteristic_sample
    (h : ExistsFullyLayeredTransportConstruction G obs) :
    ExistsBoundedPositiveCharacteristicSample G obs :=
  trimmed_exists_base_transport_choice_characteristic_sample
    (existsBaseWithTransportWitnessChoice_of_fullyLayered h)

end ExistentialCoreLayers


section CoreLayerTopLevelTheorems

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}

/-- Top-level theorem: fully layered construction data gives Gold-style
identification for some finite bound. -/
theorem trimmed_fully_layered_transport_construction_main_theorem
    (L : TrimmedPresentationFullyLayeredConstructionData
      (G := G) (obs := obs)) :
    ExistsBoundedReachableIdentification G obs :=
  L.exists_bounded_reachable_identification

/-- Top-level theorem: existence of fully layered construction data gives
Gold-style identification for some finite bound. -/
theorem trimmed_exists_fully_layered_transport_construction_main_theorem
    (h : ExistsFullyLayeredTransportConstruction G obs) :
    ExistsBoundedReachableIdentification G obs :=
  existsFullyLayeredTransportConstruction_main_theorem h

/-- Top-level prefix-exact theorem from fully layered construction data. -/
theorem trimmed_exists_fully_layered_transport_construction_prefix_exact
    (h : ExistsFullyLayeredTransportConstruction G obs) :
    ExistsBoundedPrefixExactIdentification G obs :=
  existsFullyLayeredTransportConstruction_prefix_exact h

/-- Top-level characteristic-sample theorem from fully layered construction data. -/
theorem trimmed_exists_fully_layered_transport_construction_characteristic_sample
    (h : ExistsFullyLayeredTransportConstruction G obs) :
    ExistsBoundedPositiveCharacteristicSample G obs :=
  existsFullyLayeredTransportConstruction_characteristic_sample h

end CoreLayerTopLevelTheorems

end MCFG
