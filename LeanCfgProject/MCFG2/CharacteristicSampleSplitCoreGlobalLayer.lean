/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG2.CharacteristicSampleCoreConstructionExistential

/-!
# CharacteristicSampleSplitCoreGlobalLayer.lean

One-hundred-sixth clean Lean experiment for the fixed-observation MCFG project.

`CharacteristicSampleCoreConstructionExistential.lean` introduced the split core

```lean
TrimmedPresentationSplitCoreConstructionData
```

and the split-layered route-specific construction records.

This file inserts one more useful layer:

```lean
TrimmedPresentationSplitCoreWithGlobalAssumptions
```

This record contains:

* the split core:
  `f`, `T`, `D`, and `builder`;
* the global assumptions:
  `NamedContextSplicingConstructor`, fanout, and fixed-observation promise.

It intentionally does **not** contain a transport witness.  Transport can be
added later as:

* exposing-context transport;
* anchor common-context transport;
* same-context transport;
* or the abstract transport-witness choice.

This makes the next construction tasks cleaner:

```text
construct split core
construct global assumptions
construct one transport witness
```

No new mathematical principle is introduced here.

No theorem here uses `sorry`.
-/

namespace MCFG

universe u v w

section SplitCoreGlobalLayer

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}

/-- A split core together with the global non-transport assumptions.

This is the construction layer immediately before choosing a semantic transport
route. -/
structure TrimmedPresentationSplitCoreWithGlobalAssumptions where
  splitCore : TrimmedPresentationSplitCoreConstructionData
    (G := G) (obs := obs)
  global :
    TrimmedPresentationGlobalConstructionAssumptions
      splitCore.toCoreConstructionData

namespace TrimmedPresentationSplitCoreWithGlobalAssumptions

/-- Recover the previous core construction package. -/
def core
    (C : TrimmedPresentationSplitCoreWithGlobalAssumptions
      (G := G) (obs := obs)) :
    TrimmedPresentationCoreConstructionData
      (G := G) (obs := obs) :=
  C.splitCore.toCoreConstructionData

/-- Recover the previous base construction package. -/
def base
    (C : TrimmedPresentationSplitCoreWithGlobalAssumptions
      (G := G) (obs := obs)) :
    TrimmedPresentationBaseConstructionData
      (G := G) (obs := obs) :=
  C.splitCore.toBaseConstructionData C.global

/-- Add an abstract transport-witness choice to the split-core/global layer. -/
def withTransportWitnessChoice
    (C : TrimmedPresentationSplitCoreWithGlobalAssumptions
      (G := G) (obs := obs))
    (W : TrimmedPresentationTransportWitnessChoice C.base) :
    TrimmedPresentationSplitLayeredTransportConstructionData
      (G := G) (obs := obs) where
  splitCore := C.splitCore
  global := C.global
  transport := W

/-- Add direct exposing-context transport to the split-core/global layer. -/
def withExposingTransport
    (C : TrimmedPresentationSplitCoreWithGlobalAssumptions
      (G := G) (obs := obs))
    (E : TrimmedPresentationExposingContextTransport C.core.data) :
    TrimmedPresentationSplitLayeredExposingConstructionData
      (G := G) (obs := obs) where
  splitCore := C.splitCore
  global := C.global
  exposingTransport := E

/-- Add anchor common-context transport to the split-core/global layer. -/
def withAnchorCommonTransport
    (C : TrimmedPresentationSplitCoreWithGlobalAssumptions
      (G := G) (obs := obs))
    (A : TrimmedPresentationAnchorCommonContextTransport C.core.data) :
    TrimmedPresentationSplitLayeredAnchorCommonConstructionData
      (G := G) (obs := obs) where
  splitCore := C.splitCore
  global := C.global
  commonTransport := A

/-- Add same-context transport to the split-core/global layer. -/
def withSameContextTransport
    (C : TrimmedPresentationSplitCoreWithGlobalAssumptions
      (G := G) (obs := obs))
    (S : TrimmedPresentationSameContextTransport C.core.data) :
    TrimmedPresentationSplitLayeredSameContextConstructionData
      (G := G) (obs := obs) where
  splitCore := C.splitCore
  global := C.global
  sameContextTransport := S

/-- An abstract transport witness over the base gives the main theorem. -/
theorem main_theorem_from_transport_choice
    (C : TrimmedPresentationSplitCoreWithGlobalAssumptions
      (G := G) (obs := obs))
    (W : TrimmedPresentationTransportWitnessChoice C.base) :
    ExistsBoundedReachableIdentification G obs :=
  (C.withTransportWitnessChoice W)
    .exists_bounded_reachable_identification

/-- Direct exposing transport over the core gives the main theorem. -/
theorem main_theorem_from_exposing_transport
    (C : TrimmedPresentationSplitCoreWithGlobalAssumptions
      (G := G) (obs := obs))
    (E : TrimmedPresentationExposingContextTransport C.core.data) :
    ExistsBoundedReachableIdentification G obs :=
  (C.withExposingTransport E)
    .exists_bounded_reachable_identification

/-- Anchor common-context transport over the core gives the main theorem. -/
theorem main_theorem_from_anchor_common_transport
    (C : TrimmedPresentationSplitCoreWithGlobalAssumptions
      (G := G) (obs := obs))
    (A : TrimmedPresentationAnchorCommonContextTransport C.core.data) :
    ExistsBoundedReachableIdentification G obs :=
  (C.withAnchorCommonTransport A)
    .exists_bounded_reachable_identification

/-- Same-context transport over the core gives the main theorem. -/
theorem main_theorem_from_same_context_transport
    (C : TrimmedPresentationSplitCoreWithGlobalAssumptions
      (G := G) (obs := obs))
    (S : TrimmedPresentationSameContextTransport C.core.data) :
    ExistsBoundedReachableIdentification G obs :=
  (C.withSameContextTransport S)
    .exists_bounded_reachable_identification

/-- An abstract transport witness over the base gives prefix exactness. -/
theorem prefix_exact_from_transport_choice
    (C : TrimmedPresentationSplitCoreWithGlobalAssumptions
      (G := G) (obs := obs))
    (W : TrimmedPresentationTransportWitnessChoice C.base) :
    ExistsBoundedPrefixExactIdentification G obs :=
  (C.withTransportWitnessChoice W)
    .exists_bounded_prefix_exact_identification

/-- An abstract transport witness over the base gives a positive characteristic
sample for some finite bound. -/
theorem characteristic_sample_from_transport_choice
    (C : TrimmedPresentationSplitCoreWithGlobalAssumptions
      (G := G) (obs := obs))
    (W : TrimmedPresentationTransportWitnessChoice C.base) :
    ExistsBoundedPositiveCharacteristicSample G obs :=
  (C.withTransportWitnessChoice W)
    .exists_bounded_positive_characteristic_sample

end TrimmedPresentationSplitCoreWithGlobalAssumptions

end SplitCoreGlobalLayer


section SplitCoreGlobalExistential

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}

/-- There exists a split core with global assumptions and an abstract transport
witness choice over its base. -/
def ExistsSplitCoreGlobalWithTransportChoice
    (G : WorkingMCFG N α) (obs : α → M) : Prop :=
  ∃ C : TrimmedPresentationSplitCoreWithGlobalAssumptions
      (G := G) (obs := obs),
    Nonempty (TrimmedPresentationTransportWitnessChoice C.base)

/-- There exists a split core with global assumptions and direct exposing
transport. -/
def ExistsSplitCoreGlobalWithExposingTransport
    (G : WorkingMCFG N α) (obs : α → M) : Prop :=
  ∃ C : TrimmedPresentationSplitCoreWithGlobalAssumptions
      (G := G) (obs := obs),
    Nonempty (TrimmedPresentationExposingContextTransport C.core.data)

/-- There exists a split core with global assumptions and anchor common-context
transport. -/
def ExistsSplitCoreGlobalWithAnchorCommonTransport
    (G : WorkingMCFG N α) (obs : α → M) : Prop :=
  ∃ C : TrimmedPresentationSplitCoreWithGlobalAssumptions
      (G := G) (obs := obs),
    Nonempty (TrimmedPresentationAnchorCommonContextTransport C.core.data)

/-- There exists a split core with global assumptions and same-context transport. -/
def ExistsSplitCoreGlobalWithSameContextTransport
    (G : WorkingMCFG N α) (obs : α → M) : Prop :=
  ∃ C : TrimmedPresentationSplitCoreWithGlobalAssumptions
      (G := G) (obs := obs),
    Nonempty (TrimmedPresentationSameContextTransport C.core.data)

/-- Split-core/global plus transport choice gives split-layered construction. -/
theorem existsSplitLayeredTransportConstruction_of_splitCoreGlobal
    (h : ExistsSplitCoreGlobalWithTransportChoice G obs) :
    ExistsSplitLayeredTransportConstruction G obs :=
  match h with
  | ⟨C, hW⟩ =>
      match hW with
      | ⟨W⟩ =>
          ⟨C.withTransportWitnessChoice W⟩

/-- Split-core/global plus exposing transport gives split-layered exposing
construction. -/
theorem existsSplitLayeredExposingConstruction_of_splitCoreGlobal
    (h : ExistsSplitCoreGlobalWithExposingTransport G obs) :
    ExistsSplitLayeredExposingConstruction G obs :=
  match h with
  | ⟨C, hE⟩ =>
      match hE with
      | ⟨E⟩ =>
          ⟨C.withExposingTransport E⟩

/-- Split-core/global plus anchor common-context transport gives split-layered
anchor-common construction. -/
theorem existsSplitLayeredAnchorCommonConstruction_of_splitCoreGlobal
    (h : ExistsSplitCoreGlobalWithAnchorCommonTransport G obs) :
    ExistsSplitLayeredAnchorCommonConstruction G obs :=
  match h with
  | ⟨C, hA⟩ =>
      match hA with
      | ⟨A⟩ =>
          ⟨C.withAnchorCommonTransport A⟩

/-- Split-core/global plus same-context transport gives split-layered
same-context construction. -/
theorem existsSplitLayeredSameContextConstruction_of_splitCoreGlobal
    (h : ExistsSplitCoreGlobalWithSameContextTransport G obs) :
    ExistsSplitLayeredSameContextConstruction G obs :=
  match h with
  | ⟨C, hS⟩ =>
      match hS with
      | ⟨S⟩ =>
          ⟨C.withSameContextTransport S⟩

/-- Main theorem from the split-core/global plus transport-choice interface. -/
theorem existsSplitCoreGlobalWithTransportChoice_main_theorem
    (h : ExistsSplitCoreGlobalWithTransportChoice G obs) :
    ExistsBoundedReachableIdentification G obs :=
  trimmed_split_layered_transport_construction_main_theorem
    (existsSplitLayeredTransportConstruction_of_splitCoreGlobal h)

/-- Main theorem from the split-core/global plus exposing-transport interface. -/
theorem existsSplitCoreGlobalWithExposingTransport_main_theorem
    (h : ExistsSplitCoreGlobalWithExposingTransport G obs) :
    ExistsBoundedReachableIdentification G obs :=
  trimmed_split_layered_exposing_construction_main_theorem
    (existsSplitLayeredExposingConstruction_of_splitCoreGlobal h)

/-- Main theorem from the split-core/global plus anchor-common-transport
interface. -/
theorem existsSplitCoreGlobalWithAnchorCommonTransport_main_theorem
    (h : ExistsSplitCoreGlobalWithAnchorCommonTransport G obs) :
    ExistsBoundedReachableIdentification G obs :=
  trimmed_split_layered_anchor_common_construction_main_theorem
    (existsSplitLayeredAnchorCommonConstruction_of_splitCoreGlobal h)

/-- Main theorem from the split-core/global plus same-context-transport
interface. -/
theorem existsSplitCoreGlobalWithSameContextTransport_main_theorem
    (h : ExistsSplitCoreGlobalWithSameContextTransport G obs) :
    ExistsBoundedReachableIdentification G obs :=
  trimmed_split_layered_same_context_construction_main_theorem
    (existsSplitLayeredSameContextConstruction_of_splitCoreGlobal h)

end SplitCoreGlobalExistential


section SplitCoreGlobalTopLevelTheorems

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}

/-- Top-level theorem: split core with global assumptions and any transport
choice gives Gold-style identification for some finite bound. -/
theorem trimmed_split_core_global_transport_choice_main_theorem
    (h : ExistsSplitCoreGlobalWithTransportChoice G obs) :
    ExistsBoundedReachableIdentification G obs :=
  existsSplitCoreGlobalWithTransportChoice_main_theorem h

/-- Top-level theorem: split core with global assumptions and exposing transport
gives Gold-style identification for some finite bound. -/
theorem trimmed_split_core_global_exposing_transport_main_theorem
    (h : ExistsSplitCoreGlobalWithExposingTransport G obs) :
    ExistsBoundedReachableIdentification G obs :=
  existsSplitCoreGlobalWithExposingTransport_main_theorem h

/-- Top-level theorem: split core with global assumptions and anchor
common-context transport gives Gold-style identification for some finite bound. -/
theorem trimmed_split_core_global_anchor_common_transport_main_theorem
    (h : ExistsSplitCoreGlobalWithAnchorCommonTransport G obs) :
    ExistsBoundedReachableIdentification G obs :=
  existsSplitCoreGlobalWithAnchorCommonTransport_main_theorem h

/-- Top-level theorem: split core with global assumptions and same-context
transport gives Gold-style identification for some finite bound. -/
theorem trimmed_split_core_global_same_context_transport_main_theorem
    (h : ExistsSplitCoreGlobalWithSameContextTransport G obs) :
    ExistsBoundedReachableIdentification G obs :=
  existsSplitCoreGlobalWithSameContextTransport_main_theorem h

end SplitCoreGlobalTopLevelTheorems

end MCFG
