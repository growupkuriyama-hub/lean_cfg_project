/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG2.CharacteristicSampleCoreConstructionLayers

/-!
# CharacteristicSampleCoreConstructionExistential.lean

One-hundred-fifth clean Lean experiment for the fixed-observation MCFG project.

`CharacteristicSampleCoreConstructionLayers.lean` split the core construction
into presentation, pre-core, and grammar-rule-builder layers.  This file gives
an even more construction-facing, unpacked facade.

The new package

```lean
TrimmedPresentationSplitCoreConstructionData
```

spells out the three core objects directly:

```text
f : Nat
T : TrimmedOutputTypePresentation G obs
D : TrimmedPresentationPreCoreData T f
builder : TrimmedPresentationGrammarRuleBuilder D
```

and then reconnects this split core to the previous fully layered construction
interface.

This is useful because future construction work can now target the individual
fields `presentation`, `data`, and `builder` directly, while still inheriting
the already verified existential paper theorem.

No new mathematical principle is introduced here.

No theorem here uses `sorry`.
-/

namespace MCFG

universe u v w

section SplitCoreConstruction

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}

/-- Unpacked core construction data.

This is definitionally close to `TrimmedPresentationCoreConstructionData`, but
its purpose is to make the future concrete construction targets visibly
separate. -/
structure TrimmedPresentationSplitCoreConstructionData where
  fanoutBound : Nat
  presentation : TrimmedOutputTypePresentation G obs
  data : TrimmedPresentationPreCoreData presentation fanoutBound
  builder : TrimmedPresentationGrammarRuleBuilder data

namespace TrimmedPresentationSplitCoreConstructionData

/-- Convert split core data to the presentation layer. -/
def toPresentationConstructionData
    (C : TrimmedPresentationSplitCoreConstructionData
      (G := G) (obs := obs)) :
    TrimmedPresentationPresentationConstructionData
      (G := G) (obs := obs) where
  fanoutBound := C.fanoutBound
  presentation := C.presentation

/-- Convert split core data to the pre-core layer. -/
def toPreCoreConstructionData
    (C : TrimmedPresentationSplitCoreConstructionData
      (G := G) (obs := obs)) :
    TrimmedPresentationPreCoreConstructionData
      (G := G) (obs := obs) where
  presentationLayer := C.toPresentationConstructionData
  data := C.data

/-- Convert split core data to the grammar-rule-builder layer. -/
def toRuleBuilderConstructionData
    (C : TrimmedPresentationSplitCoreConstructionData
      (G := G) (obs := obs)) :
    TrimmedPresentationRuleBuilderConstructionData
      (G := G) (obs := obs) where
  preCoreLayer := C.toPreCoreConstructionData
  builder := C.builder

/-- Convert split core data to the previous core-construction package. -/
def toCoreConstructionData
    (C : TrimmedPresentationSplitCoreConstructionData
      (G := G) (obs := obs)) :
    TrimmedPresentationCoreConstructionData
      (G := G) (obs := obs) :=
  C.toRuleBuilderConstructionData.toCoreConstructionData

/-- Add global assumptions to split core data. -/
def toBaseConstructionData
    (C : TrimmedPresentationSplitCoreConstructionData
      (G := G) (obs := obs))
    (A :
      TrimmedPresentationGlobalConstructionAssumptions
        C.toCoreConstructionData) :
    TrimmedPresentationBaseConstructionData
      (G := G) (obs := obs) :=
  C.toCoreConstructionData.toBaseConstructionData A

/-- Add global assumptions and a transport witness choice. -/
def withGlobalAndTransport
    (C : TrimmedPresentationSplitCoreConstructionData
      (G := G) (obs := obs))
    (A :
      TrimmedPresentationGlobalConstructionAssumptions
        C.toCoreConstructionData)
    (W :
      TrimmedPresentationTransportWitnessChoice
        (C.toBaseConstructionData A)) :
    TrimmedPresentationFullyLayeredConstructionData
      (G := G) (obs := obs) where
  ruleBuilderLayer := C.toRuleBuilderConstructionData
  global := A
  transport := W

end TrimmedPresentationSplitCoreConstructionData

end SplitCoreConstruction


section SplitLayeredConstruction

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}

/-- Fully layered construction data using an unpacked split core. -/
structure TrimmedPresentationSplitLayeredTransportConstructionData where
  splitCore : TrimmedPresentationSplitCoreConstructionData
    (G := G) (obs := obs)
  global :
    TrimmedPresentationGlobalConstructionAssumptions
      splitCore.toCoreConstructionData
  transport :
    TrimmedPresentationTransportWitnessChoice
      (splitCore.toBaseConstructionData global)

namespace TrimmedPresentationSplitLayeredTransportConstructionData

/-- Convert split layered construction data to the previous fully layered
package. -/
def toFullyLayeredTransportConstructionData
    (L : TrimmedPresentationSplitLayeredTransportConstructionData
      (G := G) (obs := obs)) :
    TrimmedPresentationFullyLayeredConstructionData
      (G := G) (obs := obs) :=
  L.splitCore.withGlobalAndTransport L.global L.transport

/-- Convert split layered construction data to the previous layered package. -/
def toLayeredTransportConstructionData
    (L : TrimmedPresentationSplitLayeredTransportConstructionData
      (G := G) (obs := obs)) :
    TrimmedPresentationLayeredTransportConstructionData
      (G := G) (obs := obs) :=
  L.toFullyLayeredTransportConstructionData
    .toLayeredTransportConstructionData

/-- Convert split layered construction data to a transport-construction choice. -/
def toTransportConstructionChoice
    (L : TrimmedPresentationSplitLayeredTransportConstructionData
      (G := G) (obs := obs)) :
    TrimmedPresentationTransportConstructionChoice
      (G := G) (obs := obs) :=
  L.toLayeredTransportConstructionData.toTransportConstructionChoice

/-- A split layered construction gives a positive characteristic sample for some
finite fanout bound. -/
theorem exists_bounded_positive_characteristic_sample
    (L : TrimmedPresentationSplitLayeredTransportConstructionData
      (G := G) (obs := obs)) :
    ExistsBoundedPositiveCharacteristicSample G obs :=
  L.toFullyLayeredTransportConstructionData
    .exists_bounded_positive_characteristic_sample

/-- A split layered construction gives prefix exactness for some finite fanout
bound. -/
theorem exists_bounded_prefix_exact_identification
    (L : TrimmedPresentationSplitLayeredTransportConstructionData
      (G := G) (obs := obs)) :
    ExistsBoundedPrefixExactIdentification G obs :=
  L.toFullyLayeredTransportConstructionData
    .exists_bounded_prefix_exact_identification

/-- A split layered construction gives Gold-style identification for some finite
fanout bound. -/
theorem exists_bounded_reachable_identification
    (L : TrimmedPresentationSplitLayeredTransportConstructionData
      (G := G) (obs := obs)) :
    ExistsBoundedReachableIdentification G obs :=
  L.toFullyLayeredTransportConstructionData
    .exists_bounded_reachable_identification

end TrimmedPresentationSplitLayeredTransportConstructionData

end SplitLayeredConstruction


section SplitLayeredRouteVariants

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}

/-- Split layered construction data with direct exposing-context transport. -/
structure TrimmedPresentationSplitLayeredExposingConstructionData where
  splitCore : TrimmedPresentationSplitCoreConstructionData
    (G := G) (obs := obs)
  global :
    TrimmedPresentationGlobalConstructionAssumptions
      splitCore.toCoreConstructionData
  exposingTransport :
    TrimmedPresentationExposingContextTransport
      splitCore.toCoreConstructionData.data

/-- Split layered construction data with anchor common-context transport. -/
structure TrimmedPresentationSplitLayeredAnchorCommonConstructionData where
  splitCore : TrimmedPresentationSplitCoreConstructionData
    (G := G) (obs := obs)
  global :
    TrimmedPresentationGlobalConstructionAssumptions
      splitCore.toCoreConstructionData
  commonTransport :
    TrimmedPresentationAnchorCommonContextTransport
      splitCore.toCoreConstructionData.data

/-- Split layered construction data with same-context transport. -/
structure TrimmedPresentationSplitLayeredSameContextConstructionData where
  splitCore : TrimmedPresentationSplitCoreConstructionData
    (G := G) (obs := obs)
  global :
    TrimmedPresentationGlobalConstructionAssumptions
      splitCore.toCoreConstructionData
  sameContextTransport :
    TrimmedPresentationSameContextTransport
      splitCore.toCoreConstructionData.data

namespace TrimmedPresentationSplitLayeredExposingConstructionData

/-- Convert direct exposing split-layered data to generic split-layered data. -/
def toSplitLayeredTransportConstructionData
    (L : TrimmedPresentationSplitLayeredExposingConstructionData
      (G := G) (obs := obs)) :
    TrimmedPresentationSplitLayeredTransportConstructionData
      (G := G) (obs := obs) where
  splitCore := L.splitCore
  global := L.global
  transport := TrimmedPresentationTransportWitnessChoice.exposing
    L.exposingTransport

/-- Main theorem for direct exposing split-layered data. -/
theorem exists_bounded_reachable_identification
    (L : TrimmedPresentationSplitLayeredExposingConstructionData
      (G := G) (obs := obs)) :
    ExistsBoundedReachableIdentification G obs :=
  L.toSplitLayeredTransportConstructionData
    .exists_bounded_reachable_identification

end TrimmedPresentationSplitLayeredExposingConstructionData


namespace TrimmedPresentationSplitLayeredAnchorCommonConstructionData

/-- Convert anchor-common split-layered data to generic split-layered data. -/
def toSplitLayeredTransportConstructionData
    (L : TrimmedPresentationSplitLayeredAnchorCommonConstructionData
      (G := G) (obs := obs)) :
    TrimmedPresentationSplitLayeredTransportConstructionData
      (G := G) (obs := obs) where
  splitCore := L.splitCore
  global := L.global
  transport := TrimmedPresentationTransportWitnessChoice.anchorCommon
    L.commonTransport

/-- Main theorem for anchor-common split-layered data. -/
theorem exists_bounded_reachable_identification
    (L : TrimmedPresentationSplitLayeredAnchorCommonConstructionData
      (G := G) (obs := obs)) :
    ExistsBoundedReachableIdentification G obs :=
  L.toSplitLayeredTransportConstructionData
    .exists_bounded_reachable_identification

end TrimmedPresentationSplitLayeredAnchorCommonConstructionData


namespace TrimmedPresentationSplitLayeredSameContextConstructionData

/-- Convert same-context split-layered data to generic split-layered data. -/
def toSplitLayeredTransportConstructionData
    (L : TrimmedPresentationSplitLayeredSameContextConstructionData
      (G := G) (obs := obs)) :
    TrimmedPresentationSplitLayeredTransportConstructionData
      (G := G) (obs := obs) where
  splitCore := L.splitCore
  global := L.global
  transport := TrimmedPresentationTransportWitnessChoice.sameContext
    L.sameContextTransport

/-- Main theorem for same-context split-layered data. -/
theorem exists_bounded_reachable_identification
    (L : TrimmedPresentationSplitLayeredSameContextConstructionData
      (G := G) (obs := obs)) :
    ExistsBoundedReachableIdentification G obs :=
  L.toSplitLayeredTransportConstructionData
    .exists_bounded_reachable_identification

end TrimmedPresentationSplitLayeredSameContextConstructionData

end SplitLayeredRouteVariants


section SplitCoreExistentialTheorems

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}

/-- Existence of split layered construction data. -/
def ExistsSplitLayeredTransportConstruction
    (G : WorkingMCFG N α) (obs : α → M) : Prop :=
  Nonempty
    (TrimmedPresentationSplitLayeredTransportConstructionData
      (G := G) (obs := obs))

/-- Existence of split layered direct exposing construction data. -/
def ExistsSplitLayeredExposingConstruction
    (G : WorkingMCFG N α) (obs : α → M) : Prop :=
  Nonempty
    (TrimmedPresentationSplitLayeredExposingConstructionData
      (G := G) (obs := obs))

/-- Existence of split layered anchor-common construction data. -/
def ExistsSplitLayeredAnchorCommonConstruction
    (G : WorkingMCFG N α) (obs : α → M) : Prop :=
  Nonempty
    (TrimmedPresentationSplitLayeredAnchorCommonConstructionData
      (G := G) (obs := obs))

/-- Existence of split layered same-context construction data. -/
def ExistsSplitLayeredSameContextConstruction
    (G : WorkingMCFG N α) (obs : α → M) : Prop :=
  Nonempty
    (TrimmedPresentationSplitLayeredSameContextConstructionData
      (G := G) (obs := obs))

/-- Split layered construction gives the previous fully layered existence
interface. -/
theorem existsFullyLayeredTransportConstruction_of_splitLayered
    (h : ExistsSplitLayeredTransportConstruction G obs) :
    ExistsFullyLayeredTransportConstruction G obs :=
  match h with
  | ⟨L⟩ =>
      ⟨L.toFullyLayeredTransportConstructionData⟩

/-- Split layered exposing construction gives split layered transport
construction. -/
theorem existsSplitLayeredTransportConstruction_of_exposing
    (h : ExistsSplitLayeredExposingConstruction G obs) :
    ExistsSplitLayeredTransportConstruction G obs :=
  match h with
  | ⟨L⟩ =>
      ⟨L.toSplitLayeredTransportConstructionData⟩

/-- Split layered anchor-common construction gives split layered transport
construction. -/
theorem existsSplitLayeredTransportConstruction_of_anchorCommon
    (h : ExistsSplitLayeredAnchorCommonConstruction G obs) :
    ExistsSplitLayeredTransportConstruction G obs :=
  match h with
  | ⟨L⟩ =>
      ⟨L.toSplitLayeredTransportConstructionData⟩

/-- Split layered same-context construction gives split layered transport
construction. -/
theorem existsSplitLayeredTransportConstruction_of_sameContext
    (h : ExistsSplitLayeredSameContextConstruction G obs) :
    ExistsSplitLayeredTransportConstruction G obs :=
  match h with
  | ⟨L⟩ =>
      ⟨L.toSplitLayeredTransportConstructionData⟩

/-- Main theorem from split layered construction. -/
theorem existsSplitLayeredTransportConstruction_main_theorem
    (h : ExistsSplitLayeredTransportConstruction G obs) :
    ExistsBoundedReachableIdentification G obs :=
  trimmed_exists_fully_layered_transport_construction_main_theorem
    (existsFullyLayeredTransportConstruction_of_splitLayered h)

/-- Main theorem from split layered exposing construction. -/
theorem existsSplitLayeredExposingConstruction_main_theorem
    (h : ExistsSplitLayeredExposingConstruction G obs) :
    ExistsBoundedReachableIdentification G obs :=
  existsSplitLayeredTransportConstruction_main_theorem
    (existsSplitLayeredTransportConstruction_of_exposing h)

/-- Main theorem from split layered anchor-common construction. -/
theorem existsSplitLayeredAnchorCommonConstruction_main_theorem
    (h : ExistsSplitLayeredAnchorCommonConstruction G obs) :
    ExistsBoundedReachableIdentification G obs :=
  existsSplitLayeredTransportConstruction_main_theorem
    (existsSplitLayeredTransportConstruction_of_anchorCommon h)

/-- Main theorem from split layered same-context construction. -/
theorem existsSplitLayeredSameContextConstruction_main_theorem
    (h : ExistsSplitLayeredSameContextConstruction G obs) :
    ExistsBoundedReachableIdentification G obs :=
  existsSplitLayeredTransportConstruction_main_theorem
    (existsSplitLayeredTransportConstruction_of_sameContext h)

end SplitCoreExistentialTheorems


section SplitCoreTopLevelTheorems

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}

/-- Top-level theorem: split layered construction gives Gold-style identification
for some finite bound. -/
theorem trimmed_split_layered_transport_construction_main_theorem
    (h : ExistsSplitLayeredTransportConstruction G obs) :
    ExistsBoundedReachableIdentification G obs :=
  existsSplitLayeredTransportConstruction_main_theorem h

/-- Top-level theorem: split layered exposing construction gives Gold-style
identification for some finite bound. -/
theorem trimmed_split_layered_exposing_construction_main_theorem
    (h : ExistsSplitLayeredExposingConstruction G obs) :
    ExistsBoundedReachableIdentification G obs :=
  existsSplitLayeredExposingConstruction_main_theorem h

/-- Top-level theorem: split layered anchor-common construction gives Gold-style
identification for some finite bound. -/
theorem trimmed_split_layered_anchor_common_construction_main_theorem
    (h : ExistsSplitLayeredAnchorCommonConstruction G obs) :
    ExistsBoundedReachableIdentification G obs :=
  existsSplitLayeredAnchorCommonConstruction_main_theorem h

/-- Top-level theorem: split layered same-context construction gives Gold-style
identification for some finite bound. -/
theorem trimmed_split_layered_same_context_construction_main_theorem
    (h : ExistsSplitLayeredSameContextConstruction G obs) :
    ExistsBoundedReachableIdentification G obs :=
  existsSplitLayeredSameContextConstruction_main_theorem h

end SplitCoreTopLevelTheorems

end MCFG
