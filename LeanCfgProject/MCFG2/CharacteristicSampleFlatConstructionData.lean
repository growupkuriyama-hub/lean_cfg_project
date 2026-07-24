/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG2.CharacteristicSampleTargetAssumptionLayers

/-!
# CharacteristicSampleFlatConstructionData.lean

One-hundred-ninth clean Lean experiment for the fixed-observation MCFG project.

The previous files decomposed the construction interface into many layers:

```text
split core
+
splicing constructor
+
fanout assumption
+
substitutability promise
+
transport witness.
```

This file provides a flat, user-facing construction interface where all fields
are visible at the top level.

The route-specific flat records are:

* `TrimmedPresentationFlatExposingConstructionData`;
* `TrimmedPresentationFlatAnchorCommonConstructionData`;
* `TrimmedPresentationFlatSameContextConstructionData`.

Each flat record repackages into the already verified fully split/global
interfaces and therefore inherits the main identification theorem.

No new mathematical principle is introduced here.

No theorem here uses `sorry`.
-/

namespace MCFG

universe u v w

section FlatConstructionData

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}

/-- Flat construction data for the direct exposing-context route. -/
structure TrimmedPresentationFlatExposingConstructionData where
  fanoutBound : Nat
  presentation : TrimmedOutputTypePresentation G obs
  data : TrimmedPresentationPreCoreData presentation fanoutBound
  builder : TrimmedPresentationGrammarRuleBuilder data
  splicingConstructor : NamedContextSplicingConstructor α
  fanout : G.FanoutAtMost fanoutBound
  promise : FixedNamedTupleSubstitutable fanoutBound obs G.StringLanguage
  exposingTransport : TrimmedPresentationExposingContextTransport data

/-- Flat construction data for the preferred anchor common-context route. -/
structure TrimmedPresentationFlatAnchorCommonConstructionData where
  fanoutBound : Nat
  presentation : TrimmedOutputTypePresentation G obs
  data : TrimmedPresentationPreCoreData presentation fanoutBound
  builder : TrimmedPresentationGrammarRuleBuilder data
  splicingConstructor : NamedContextSplicingConstructor α
  fanout : G.FanoutAtMost fanoutBound
  promise : FixedNamedTupleSubstitutable fanoutBound obs G.StringLanguage
  commonTransport : TrimmedPresentationAnchorCommonContextTransport data

/-- Flat construction data for the stronger same-context route. -/
structure TrimmedPresentationFlatSameContextConstructionData where
  fanoutBound : Nat
  presentation : TrimmedOutputTypePresentation G obs
  data : TrimmedPresentationPreCoreData presentation fanoutBound
  builder : TrimmedPresentationGrammarRuleBuilder data
  splicingConstructor : NamedContextSplicingConstructor α
  fanout : G.FanoutAtMost fanoutBound
  promise : FixedNamedTupleSubstitutable fanoutBound obs G.StringLanguage
  sameContextTransport : TrimmedPresentationSameContextTransport data

namespace TrimmedPresentationFlatExposingConstructionData

/-- Extract the split core from flat exposing construction data. -/
def splitCore
    (C : TrimmedPresentationFlatExposingConstructionData
      (G := G) (obs := obs)) :
    TrimmedPresentationSplitCoreConstructionData
      (G := G) (obs := obs) where
  fanoutBound := C.fanoutBound
  presentation := C.presentation
  data := C.data
  builder := C.builder

/-- Extract the fully split global assumptions from flat exposing construction
data. -/
def fullySplitGlobal
    (C : TrimmedPresentationFlatExposingConstructionData
      (G := G) (obs := obs)) :
    TrimmedPresentationFullySplitGlobalConstructionAssumptions
      C.splitCore.toCoreConstructionData where
  splicing := {
    splicingConstructor := C.splicingConstructor
  }
  fanoutAssumption := {
    fanout := C.fanout
  }
  substitutabilityAssumption := {
    promise := C.promise
  }

/-- Convert flat exposing construction data to the split-core/fully-split-global
layer. -/
def toSplitCoreWithFullySplitGlobalAssumptions
    (C : TrimmedPresentationFlatExposingConstructionData
      (G := G) (obs := obs)) :
    TrimmedPresentationSplitCoreWithFullySplitGlobalAssumptions
      (G := G) (obs := obs) where
  splitCore := C.splitCore
  fullySplitGlobal := C.fullySplitGlobal

/-- Convert flat exposing construction data to split-layered exposing
construction data. -/
def toSplitLayeredExposingConstructionData
    (C : TrimmedPresentationFlatExposingConstructionData
      (G := G) (obs := obs)) :
    TrimmedPresentationSplitLayeredExposingConstructionData
      (G := G) (obs := obs) :=
  C.toSplitCoreWithFullySplitGlobalAssumptions.withExposingTransport C.exposingTransport

/-- Flat exposing construction data gives Gold-style identification for some
finite bound. -/
theorem exists_bounded_reachable_identification
    (C : TrimmedPresentationFlatExposingConstructionData
      (G := G) (obs := obs)) :
    ExistsBoundedReachableIdentification G obs :=
  C.toSplitLayeredExposingConstructionData.exists_bounded_reachable_identification

end TrimmedPresentationFlatExposingConstructionData


namespace TrimmedPresentationFlatAnchorCommonConstructionData

/-- Extract the split core from flat anchor-common construction data. -/
def splitCore
    (C : TrimmedPresentationFlatAnchorCommonConstructionData
      (G := G) (obs := obs)) :
    TrimmedPresentationSplitCoreConstructionData
      (G := G) (obs := obs) where
  fanoutBound := C.fanoutBound
  presentation := C.presentation
  data := C.data
  builder := C.builder

/-- Extract the fully split global assumptions from flat anchor-common
construction data. -/
def fullySplitGlobal
    (C : TrimmedPresentationFlatAnchorCommonConstructionData
      (G := G) (obs := obs)) :
    TrimmedPresentationFullySplitGlobalConstructionAssumptions
      C.splitCore.toCoreConstructionData where
  splicing := {
    splicingConstructor := C.splicingConstructor
  }
  fanoutAssumption := {
    fanout := C.fanout
  }
  substitutabilityAssumption := {
    promise := C.promise
  }

/-- Convert flat anchor-common construction data to the
split-core/fully-split-global layer. -/
def toSplitCoreWithFullySplitGlobalAssumptions
    (C : TrimmedPresentationFlatAnchorCommonConstructionData
      (G := G) (obs := obs)) :
    TrimmedPresentationSplitCoreWithFullySplitGlobalAssumptions
      (G := G) (obs := obs) where
  splitCore := C.splitCore
  fullySplitGlobal := C.fullySplitGlobal

/-- Convert flat anchor-common construction data to split-layered anchor-common
construction data. -/
def toSplitLayeredAnchorCommonConstructionData
    (C : TrimmedPresentationFlatAnchorCommonConstructionData
      (G := G) (obs := obs)) :
    TrimmedPresentationSplitLayeredAnchorCommonConstructionData
      (G := G) (obs := obs) :=
  C.toSplitCoreWithFullySplitGlobalAssumptions.withAnchorCommonTransport C.commonTransport

/-- Flat anchor-common construction data gives Gold-style identification for
some finite bound. -/
theorem exists_bounded_reachable_identification
    (C : TrimmedPresentationFlatAnchorCommonConstructionData
      (G := G) (obs := obs)) :
    ExistsBoundedReachableIdentification G obs :=
  C.toSplitLayeredAnchorCommonConstructionData.exists_bounded_reachable_identification

end TrimmedPresentationFlatAnchorCommonConstructionData


namespace TrimmedPresentationFlatSameContextConstructionData

/-- Extract the split core from flat same-context construction data. -/
def splitCore
    (C : TrimmedPresentationFlatSameContextConstructionData
      (G := G) (obs := obs)) :
    TrimmedPresentationSplitCoreConstructionData
      (G := G) (obs := obs) where
  fanoutBound := C.fanoutBound
  presentation := C.presentation
  data := C.data
  builder := C.builder

/-- Extract the fully split global assumptions from flat same-context
construction data. -/
def fullySplitGlobal
    (C : TrimmedPresentationFlatSameContextConstructionData
      (G := G) (obs := obs)) :
    TrimmedPresentationFullySplitGlobalConstructionAssumptions
      C.splitCore.toCoreConstructionData where
  splicing := {
    splicingConstructor := C.splicingConstructor
  }
  fanoutAssumption := {
    fanout := C.fanout
  }
  substitutabilityAssumption := {
    promise := C.promise
  }

/-- Convert flat same-context construction data to the
split-core/fully-split-global layer. -/
def toSplitCoreWithFullySplitGlobalAssumptions
    (C : TrimmedPresentationFlatSameContextConstructionData
      (G := G) (obs := obs)) :
    TrimmedPresentationSplitCoreWithFullySplitGlobalAssumptions
      (G := G) (obs := obs) where
  splitCore := C.splitCore
  fullySplitGlobal := C.fullySplitGlobal

/-- Convert flat same-context construction data to split-layered same-context
construction data. -/
def toSplitLayeredSameContextConstructionData
    (C : TrimmedPresentationFlatSameContextConstructionData
      (G := G) (obs := obs)) :
    TrimmedPresentationSplitLayeredSameContextConstructionData
      (G := G) (obs := obs) :=
  C.toSplitCoreWithFullySplitGlobalAssumptions.withSameContextTransport C.sameContextTransport

/-- Flat same-context construction data gives Gold-style identification for some
finite bound. -/
theorem exists_bounded_reachable_identification
    (C : TrimmedPresentationFlatSameContextConstructionData
      (G := G) (obs := obs)) :
    ExistsBoundedReachableIdentification G obs :=
  C.toSplitLayeredSameContextConstructionData.exists_bounded_reachable_identification

end TrimmedPresentationFlatSameContextConstructionData

end FlatConstructionData


section FlatConstructionExistential

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}

/-- Existence of flat direct exposing construction data. -/
def ExistsFlatExposingConstruction
    (G : WorkingMCFG N α) (obs : α → M) : Prop :=
  Nonempty
    (TrimmedPresentationFlatExposingConstructionData
      (G := G) (obs := obs))

/-- Existence of flat anchor-common construction data. -/
def ExistsFlatAnchorCommonConstruction
    (G : WorkingMCFG N α) (obs : α → M) : Prop :=
  Nonempty
    (TrimmedPresentationFlatAnchorCommonConstructionData
      (G := G) (obs := obs))

/-- Existence of flat same-context construction data. -/
def ExistsFlatSameContextConstruction
    (G : WorkingMCFG N α) (obs : α → M) : Prop :=
  Nonempty
    (TrimmedPresentationFlatSameContextConstructionData
      (G := G) (obs := obs))

/-- Flat exposing construction gives split layered exposing construction. -/
theorem existsSplitLayeredExposingConstruction_of_flat
    (h : ExistsFlatExposingConstruction G obs) :
    ExistsSplitLayeredExposingConstruction G obs :=
  match h with
  | ⟨C⟩ =>
      ⟨C.toSplitLayeredExposingConstructionData⟩

/-- Flat anchor-common construction gives split layered anchor-common
construction. -/
theorem existsSplitLayeredAnchorCommonConstruction_of_flat
    (h : ExistsFlatAnchorCommonConstruction G obs) :
    ExistsSplitLayeredAnchorCommonConstruction G obs :=
  match h with
  | ⟨C⟩ =>
      ⟨C.toSplitLayeredAnchorCommonConstructionData⟩

/-- Flat same-context construction gives split layered same-context
construction. -/
theorem existsSplitLayeredSameContextConstruction_of_flat
    (h : ExistsFlatSameContextConstruction G obs) :
    ExistsSplitLayeredSameContextConstruction G obs :=
  match h with
  | ⟨C⟩ =>
      ⟨C.toSplitLayeredSameContextConstructionData⟩

/-- Main theorem from flat exposing construction. -/
theorem existsFlatExposingConstruction_main_theorem
    (h : ExistsFlatExposingConstruction G obs) :
    ExistsBoundedReachableIdentification G obs :=
  trimmed_split_layered_exposing_construction_main_theorem
    (existsSplitLayeredExposingConstruction_of_flat h)

/-- Main theorem from flat anchor-common construction. -/
theorem existsFlatAnchorCommonConstruction_main_theorem
    (h : ExistsFlatAnchorCommonConstruction G obs) :
    ExistsBoundedReachableIdentification G obs :=
  trimmed_split_layered_anchor_common_construction_main_theorem
    (existsSplitLayeredAnchorCommonConstruction_of_flat h)

/-- Main theorem from flat same-context construction. -/
theorem existsFlatSameContextConstruction_main_theorem
    (h : ExistsFlatSameContextConstruction G obs) :
    ExistsBoundedReachableIdentification G obs :=
  trimmed_split_layered_same_context_construction_main_theorem
    (existsSplitLayeredSameContextConstruction_of_flat h)

end FlatConstructionExistential


section FlatConstructionTopLevelTheorems

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}

/-- Top-level theorem: flat exposing construction data gives Gold-style
identification for some finite bound. -/
theorem trimmed_flat_exposing_construction_main_theorem
    (h : ExistsFlatExposingConstruction G obs) :
    ExistsBoundedReachableIdentification G obs :=
  existsFlatExposingConstruction_main_theorem h

/-- Top-level theorem: flat anchor-common construction data gives Gold-style
identification for some finite bound. -/
theorem trimmed_flat_anchor_common_construction_main_theorem
    (h : ExistsFlatAnchorCommonConstruction G obs) :
    ExistsBoundedReachableIdentification G obs :=
  existsFlatAnchorCommonConstruction_main_theorem h

/-- Top-level theorem: flat same-context construction data gives Gold-style
identification for some finite bound. -/
theorem trimmed_flat_same_context_construction_main_theorem
    (h : ExistsFlatSameContextConstruction G obs) :
    ExistsBoundedReachableIdentification G obs :=
  existsFlatSameContextConstruction_main_theorem h

end FlatConstructionTopLevelTheorems

end MCFG
