/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG2.CharacteristicSampleTransportConstructionExistential

/-!
# CharacteristicSampleBaseConstructionLayers.lean

One-hundred-third clean Lean experiment for the fixed-observation MCFG project.

`CharacteristicSampleTransportConstructionBase.lean` introduced

```lean
TrimmedPresentationBaseConstructionData
```

which still bundled two different kinds of information:

1. construction core:
   `fanoutBound`, `presentation`, `pre-core data`, and `grammar-rule builder`;
2. global semantic assumptions:
   `NamedContextSplicingConstructor`, `fanout`, and fixed-observation promise.

This file splits those layers:

```lean
TrimmedPresentationCoreConstructionData
TrimmedPresentationGlobalConstructionAssumptions
```

and proves that a core plus global assumptions plus a transport witness choice
reconstructs the previous base/structured construction interfaces.

No new mathematical principle is introduced here.  This is a bookkeeping split
preparing the later construction of the actual trimmed presentation data.

No theorem here uses `sorry`.
-/

namespace MCFG

universe u v w

section CoreConstructionData

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}

/-- The construction core before adding splicing/fanout/promise assumptions.

This is the part that should eventually be constructed from the concrete
trimmed output-type presentation. -/
structure TrimmedPresentationCoreConstructionData where
  fanoutBound : Nat
  presentation : TrimmedOutputTypePresentation G obs
  data : TrimmedPresentationPreCoreData presentation fanoutBound
  builder : TrimmedPresentationGrammarRuleBuilder data

/-- The global assumptions added on top of a fixed construction core. -/
structure TrimmedPresentationGlobalConstructionAssumptions
    (K : TrimmedPresentationCoreConstructionData
      (G := G) (obs := obs)) where
  splicingConstructor : NamedContextSplicingConstructor α
  fanout : G.FanoutAtMost K.fanoutBound
  promise : FixedNamedTupleSubstitutable
    K.fanoutBound obs G.StringLanguage

namespace TrimmedPresentationCoreConstructionData

/-- Add global assumptions to core construction data, obtaining the previous
base construction package. -/
def toBaseConstructionData
    (K : TrimmedPresentationCoreConstructionData
      (G := G) (obs := obs))
    (A : TrimmedPresentationGlobalConstructionAssumptions K) :
    TrimmedPresentationBaseConstructionData
      (G := G) (obs := obs) where
  fanoutBound := K.fanoutBound
  presentation := K.presentation
  data := K.data
  builder := K.builder
  splicingConstructor := A.splicingConstructor
  fanout := A.fanout
  promise := A.promise

/-- Add global assumptions and direct exposing-context transport. -/
def toExposingTransportConstructionData
    (K : TrimmedPresentationCoreConstructionData
      (G := G) (obs := obs))
    (A : TrimmedPresentationGlobalConstructionAssumptions K)
    (E : TrimmedPresentationExposingContextTransport K.data) :
    TrimmedPresentationExposingTransportConstructionData
      (G := G) (obs := obs) :=
  (K.toBaseConstructionData A).withExposingTransport E

/-- Add global assumptions and anchor common-context transport. -/
def toAnchorCommonTransportConstructionData
    (K : TrimmedPresentationCoreConstructionData
      (G := G) (obs := obs))
    (A : TrimmedPresentationGlobalConstructionAssumptions K)
    (C : TrimmedPresentationAnchorCommonContextTransport K.data) :
    TrimmedPresentationAnchorCommonTransportConstructionData
      (G := G) (obs := obs) :=
  (K.toBaseConstructionData A).withAnchorCommonTransport C

/-- Add global assumptions and same-context transport. -/
def toSameContextTransportConstructionData
    (K : TrimmedPresentationCoreConstructionData
      (G := G) (obs := obs))
    (A : TrimmedPresentationGlobalConstructionAssumptions K)
    (S : TrimmedPresentationSameContextTransport K.data) :
    TrimmedPresentationSameContextTransportConstructionData
      (G := G) (obs := obs) :=
  (K.toBaseConstructionData A).withSameContextTransport S

end TrimmedPresentationCoreConstructionData

end CoreConstructionData


section LayeredConstructionData

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}

/-- Layered construction data: a construction core, global assumptions over that
core, and one transport witness choice over the resulting base. -/
structure TrimmedPresentationLayeredTransportConstructionData where
  core : TrimmedPresentationCoreConstructionData
    (G := G) (obs := obs)
  global : TrimmedPresentationGlobalConstructionAssumptions core
  transport :
    TrimmedPresentationTransportWitnessChoice
      (core.toBaseConstructionData global)

namespace TrimmedPresentationLayeredTransportConstructionData

/-- Recover the previous base construction data. -/
def base
    (L : TrimmedPresentationLayeredTransportConstructionData
      (G := G) (obs := obs)) :
    TrimmedPresentationBaseConstructionData
      (G := G) (obs := obs) :=
  L.core.toBaseConstructionData L.global

/-- Recover the previous structured transport construction data. -/
def toStructuredTransportConstructionData
    (L : TrimmedPresentationLayeredTransportConstructionData
      (G := G) (obs := obs)) :
    TrimmedPresentationStructuredTransportConstructionData
      (G := G) (obs := obs) where
  base := L.base
  transport := L.transport

/-- Convert layered construction data to a transport-construction choice. -/
def toTransportConstructionChoice
    (L : TrimmedPresentationLayeredTransportConstructionData
      (G := G) (obs := obs)) :
    TrimmedPresentationTransportConstructionChoice
      (G := G) (obs := obs) :=
  L.toStructuredTransportConstructionData.toTransportConstructionChoice

/-- A layered construction datum gives a finite positive characteristic sample
for some finite fanout bound. -/
theorem exists_bounded_positive_characteristic_sample
    (L : TrimmedPresentationLayeredTransportConstructionData
      (G := G) (obs := obs)) :
    ExistsBoundedPositiveCharacteristicSample G obs :=
  L.toStructuredTransportConstructionData
    .exists_bounded_positive_characteristic_sample

/-- A layered construction datum gives eventual prefix exactness for some finite
fanout bound. -/
theorem exists_bounded_prefix_exact_identification
    (L : TrimmedPresentationLayeredTransportConstructionData
      (G := G) (obs := obs)) :
    ExistsBoundedPrefixExactIdentification G obs :=
  L.toStructuredTransportConstructionData
    .exists_bounded_prefix_exact_identification

/-- A layered construction datum gives Gold-style identification for some finite
fanout bound. -/
theorem exists_bounded_reachable_identification
    (L : TrimmedPresentationLayeredTransportConstructionData
      (G := G) (obs := obs)) :
    ExistsBoundedReachableIdentification G obs :=
  L.toStructuredTransportConstructionData
    .exists_bounded_reachable_identification

/-- A layered construction datum gives Gold-style identification through the
exposing route. -/
theorem exists_bounded_reachable_identification_via_exposing
    (L : TrimmedPresentationLayeredTransportConstructionData
      (G := G) (obs := obs)) :
    ExistsBoundedReachableIdentification G obs :=
  L.toStructuredTransportConstructionData
    .exists_bounded_reachable_identification_via_exposing

end TrimmedPresentationLayeredTransportConstructionData

end LayeredConstructionData


section ExistentialLayeredConstruction

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}

/-- There exists a construction core, global assumptions over it, and one
transport witness choice over the resulting base. -/
def ExistsLayeredTransportConstruction
    (G : WorkingMCFG N α) (obs : α → M) : Prop :=
  ∃ K : TrimmedPresentationCoreConstructionData
      (G := G) (obs := obs),
    ∃ A : TrimmedPresentationGlobalConstructionAssumptions K,
      Nonempty
        (TrimmedPresentationTransportWitnessChoice
          (K.toBaseConstructionData A))

/-- There exists a construction core, global assumptions, and direct
exposing-context transport. -/
def ExistsLayeredExposingTransportConstruction
    (G : WorkingMCFG N α) (obs : α → M) : Prop :=
  ∃ K : TrimmedPresentationCoreConstructionData
      (G := G) (obs := obs),
    ∃ A : TrimmedPresentationGlobalConstructionAssumptions K,
      Nonempty (TrimmedPresentationExposingContextTransport K.data)

/-- There exists a construction core, global assumptions, and anchor
common-context transport. -/
def ExistsLayeredAnchorCommonTransportConstruction
    (G : WorkingMCFG N α) (obs : α → M) : Prop :=
  ∃ K : TrimmedPresentationCoreConstructionData
      (G := G) (obs := obs),
    ∃ A : TrimmedPresentationGlobalConstructionAssumptions K,
      Nonempty (TrimmedPresentationAnchorCommonContextTransport K.data)

/-- There exists a construction core, global assumptions, and same-context
transport. -/
def ExistsLayeredSameContextTransportConstruction
    (G : WorkingMCFG N α) (obs : α → M) : Prop :=
  ∃ K : TrimmedPresentationCoreConstructionData
      (G := G) (obs := obs),
    ∃ A : TrimmedPresentationGlobalConstructionAssumptions K,
      Nonempty (TrimmedPresentationSameContextTransport K.data)

/-- Layered exposing construction gives layered transport construction. -/
theorem existsLayeredTransportConstruction_of_exposing
    (h : ExistsLayeredExposingTransportConstruction G obs) :
    ExistsLayeredTransportConstruction G obs :=
  match h with
  | ⟨K, A, hE⟩ =>
      match hE with
      | ⟨E⟩ =>
          ⟨K, A,
            ⟨TrimmedPresentationTransportWitnessChoice.exposing E⟩⟩

/-- Layered anchor-common construction gives layered transport construction. -/
theorem existsLayeredTransportConstruction_of_anchorCommon
    (h : ExistsLayeredAnchorCommonTransportConstruction G obs) :
    ExistsLayeredTransportConstruction G obs :=
  match h with
  | ⟨K, A, hC⟩ =>
      match hC with
      | ⟨C⟩ =>
          ⟨K, A,
            ⟨TrimmedPresentationTransportWitnessChoice.anchorCommon C⟩⟩

/-- Layered same-context construction gives layered transport construction. -/
theorem existsLayeredTransportConstruction_of_sameContext
    (h : ExistsLayeredSameContextTransportConstruction G obs) :
    ExistsLayeredTransportConstruction G obs :=
  match h with
  | ⟨K, A, hS⟩ =>
      match hS with
      | ⟨S⟩ =>
          ⟨K, A,
            ⟨TrimmedPresentationTransportWitnessChoice.sameContext S⟩⟩

/-- A layered existential construction gives the previous base-plus-transport
existential interface. -/
theorem existsBaseWithTransportWitnessChoice_of_layered
    (h : ExistsLayeredTransportConstruction G obs) :
    ExistsBaseWithTransportWitnessChoice G obs :=
  match h with
  | ⟨K, A, hW⟩ =>
      ⟨K.toBaseConstructionData A, hW⟩

/-- Main theorem from the layered transport construction interface. -/
theorem existsLayeredTransportConstruction_main_theorem
    (h : ExistsLayeredTransportConstruction G obs) :
    ExistsBoundedReachableIdentification G obs :=
  trimmed_exists_base_transport_choice_main_theorem
    (existsBaseWithTransportWitnessChoice_of_layered h)

/-- Prefix-exact theorem from the layered transport construction interface. -/
theorem existsLayeredTransportConstruction_prefix_exact
    (h : ExistsLayeredTransportConstruction G obs) :
    ExistsBoundedPrefixExactIdentification G obs :=
  trimmed_exists_base_transport_choice_prefix_exact_theorem
    (existsBaseWithTransportWitnessChoice_of_layered h)

/-- Characteristic-sample theorem from the layered transport construction
interface. -/
theorem existsLayeredTransportConstruction_characteristic_sample
    (h : ExistsLayeredTransportConstruction G obs) :
    ExistsBoundedPositiveCharacteristicSample G obs :=
  trimmed_exists_base_transport_choice_characteristic_sample
    (existsBaseWithTransportWitnessChoice_of_layered h)

/-- Main theorem from layered exposing construction. -/
theorem existsLayeredExposingTransportConstruction_main_theorem
    (h : ExistsLayeredExposingTransportConstruction G obs) :
    ExistsBoundedReachableIdentification G obs :=
  existsLayeredTransportConstruction_main_theorem
    (existsLayeredTransportConstruction_of_exposing h)

/-- Main theorem from layered anchor-common construction. -/
theorem existsLayeredAnchorCommonTransportConstruction_main_theorem
    (h : ExistsLayeredAnchorCommonTransportConstruction G obs) :
    ExistsBoundedReachableIdentification G obs :=
  existsLayeredTransportConstruction_main_theorem
    (existsLayeredTransportConstruction_of_anchorCommon h)

/-- Main theorem from layered same-context construction. -/
theorem existsLayeredSameContextTransportConstruction_main_theorem
    (h : ExistsLayeredSameContextTransportConstruction G obs) :
    ExistsBoundedReachableIdentification G obs :=
  existsLayeredTransportConstruction_main_theorem
    (existsLayeredTransportConstruction_of_sameContext h)

end ExistentialLayeredConstruction


section LayeredConstructionTopLevel

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}

/-- Top-level theorem: layered construction data gives Gold-style identification
for some finite bound. -/
theorem trimmed_layered_transport_construction_main_theorem
    (L : TrimmedPresentationLayeredTransportConstructionData
      (G := G) (obs := obs)) :
    ExistsBoundedReachableIdentification G obs :=
  L.exists_bounded_reachable_identification

/-- Top-level theorem: if a layered transport construction exists, then the
reachable learner identifies the target for some finite bound. -/
theorem trimmed_exists_layered_transport_construction_main_theorem
    (h : ExistsLayeredTransportConstruction G obs) :
    ExistsBoundedReachableIdentification G obs :=
  existsLayeredTransportConstruction_main_theorem h

/-- Top-level theorem for layered exposing construction. -/
theorem trimmed_exists_layered_exposing_transport_construction_main_theorem
    (h : ExistsLayeredExposingTransportConstruction G obs) :
    ExistsBoundedReachableIdentification G obs :=
  existsLayeredExposingTransportConstruction_main_theorem h

/-- Top-level theorem for layered anchor-common construction. -/
theorem trimmed_exists_layered_anchor_common_transport_construction_main_theorem
    (h : ExistsLayeredAnchorCommonTransportConstruction G obs) :
    ExistsBoundedReachableIdentification G obs :=
  existsLayeredAnchorCommonTransportConstruction_main_theorem h

/-- Top-level theorem for layered same-context construction. -/
theorem trimmed_exists_layered_same_context_transport_construction_main_theorem
    (h : ExistsLayeredSameContextTransportConstruction G obs) :
    ExistsBoundedReachableIdentification G obs :=
  existsLayeredSameContextTransportConstruction_main_theorem h

end LayeredConstructionTopLevel

end MCFG
