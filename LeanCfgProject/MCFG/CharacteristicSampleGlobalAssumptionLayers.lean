/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG.CharacteristicSampleSplitCoreGlobalLayer

/-!
# CharacteristicSampleGlobalAssumptionLayers.lean

One-hundred-seventh clean Lean experiment for the fixed-observation MCFG
project.

`CharacteristicSampleSplitCoreGlobalLayer.lean` introduced

```lean
TrimmedPresentationSplitCoreWithGlobalAssumptions
```

where the global assumptions were still bundled as:

```text
NamedContextSplicingConstructor
+
fanout
+
fixed-observation substitutability promise.
```

This file splits that global layer into two pieces:

* a splicing-constructor assumption;
* target-level fanout/substitutability assumptions.

This is useful because the next real construction tasks are different in
nature:

```text
NamedContextSplicingConstructor      -- context algebra / bookkeeping
fanout + substitutability promise    -- theorem statement / target hypothesis
```

No new mathematical principle is introduced here.

No theorem here uses `sorry`.
-/

namespace MCFG

universe u v w

section GlobalAssumptionLayers

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}

/-- The global context-splicing assumption, separated from fanout and
substitutability. -/
structure TrimmedPresentationSplicingConstructionAssumption where
  splicingConstructor : NamedContextSplicingConstructor α

/-- Target-level global assumptions at a fixed fanout bound. -/
structure TrimmedPresentationTargetConstructionAssumptions
    (f : Nat) where
  fanout : G.FanoutAtMost f
  promise : FixedNamedTupleSubstitutable f obs G.StringLanguage

namespace TrimmedPresentationTargetConstructionAssumptions

/-- Repackage target assumptions at the fanout bound carried by a core. -/
def ofCore
    (K : TrimmedPresentationCoreConstructionData
      (G := G) (obs := obs))
    (A : TrimmedPresentationTargetConstructionAssumptions
      (G := G) (obs := obs) K.fanoutBound) :
    TrimmedPresentationTargetConstructionAssumptions
      (G := G) (obs := obs) K.fanoutBound :=
  A

end TrimmedPresentationTargetConstructionAssumptions


/-- The split global assumption package over a fixed core. -/
structure TrimmedPresentationSplitGlobalConstructionAssumptions
    (K : TrimmedPresentationCoreConstructionData
      (G := G) (obs := obs)) where
  splicing : TrimmedPresentationSplicingConstructionAssumption (α := α)
  target :
    TrimmedPresentationTargetConstructionAssumptions
      (G := G) (obs := obs) K.fanoutBound

namespace TrimmedPresentationSplitGlobalConstructionAssumptions

variable {K : TrimmedPresentationCoreConstructionData
  (G := G) (obs := obs)}

/-- Recombine split global assumptions into the previous global-assumption
package. -/
def toGlobalConstructionAssumptions
    (A : TrimmedPresentationSplitGlobalConstructionAssumptions K) :
    TrimmedPresentationGlobalConstructionAssumptions K where
  splicingConstructor := A.splicing.splicingConstructor
  fanout := A.target.fanout
  promise := A.target.promise

end TrimmedPresentationSplitGlobalConstructionAssumptions


namespace TrimmedPresentationGlobalConstructionAssumptions

variable {K : TrimmedPresentationCoreConstructionData
  (G := G) (obs := obs)}

/-- Forget a bundled global-assumption package into the split global-assumption
package. -/
def toSplitGlobalConstructionAssumptions
    (A : TrimmedPresentationGlobalConstructionAssumptions K) :
    TrimmedPresentationSplitGlobalConstructionAssumptions K where
  splicing := {
    splicingConstructor := A.splicingConstructor
  }
  target := {
    fanout := A.fanout
    promise := A.promise
  }

end TrimmedPresentationGlobalConstructionAssumptions

end GlobalAssumptionLayers


section SplitCoreWithSplitGlobal

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}

/-- Split core together with split global assumptions.

This is the same data as `TrimmedPresentationSplitCoreWithGlobalAssumptions`,
but with the splicing and target assumptions separated. -/
structure TrimmedPresentationSplitCoreWithSplitGlobalAssumptions where
  splitCore : TrimmedPresentationSplitCoreConstructionData
    (G := G) (obs := obs)
  splitGlobal :
    TrimmedPresentationSplitGlobalConstructionAssumptions
      splitCore.toCoreConstructionData

namespace TrimmedPresentationSplitCoreWithSplitGlobalAssumptions

/-- Recombine the split global assumptions. -/
def global
    (C : TrimmedPresentationSplitCoreWithSplitGlobalAssumptions
      (G := G) (obs := obs)) :
    TrimmedPresentationGlobalConstructionAssumptions
      C.splitCore.toCoreConstructionData :=
  C.splitGlobal.toGlobalConstructionAssumptions

/-- Convert to the previous split-core/global layer. -/
def toSplitCoreWithGlobalAssumptions
    (C : TrimmedPresentationSplitCoreWithSplitGlobalAssumptions
      (G := G) (obs := obs)) :
    TrimmedPresentationSplitCoreWithGlobalAssumptions
      (G := G) (obs := obs) where
  splitCore := C.splitCore
  global := C.global

/-- Recover the previous core construction package. -/
def core
    (C : TrimmedPresentationSplitCoreWithSplitGlobalAssumptions
      (G := G) (obs := obs)) :
    TrimmedPresentationCoreConstructionData
      (G := G) (obs := obs) :=
  C.splitCore.toCoreConstructionData

/-- Recover the previous base construction package. -/
def base
    (C : TrimmedPresentationSplitCoreWithSplitGlobalAssumptions
      (G := G) (obs := obs)) :
    TrimmedPresentationBaseConstructionData
      (G := G) (obs := obs) :=
  C.toSplitCoreWithGlobalAssumptions.base

/-- Add an abstract transport-witness choice. -/
def withTransportWitnessChoice
    (C : TrimmedPresentationSplitCoreWithSplitGlobalAssumptions
      (G := G) (obs := obs))
    (W : TrimmedPresentationTransportWitnessChoice C.base) :
    TrimmedPresentationSplitLayeredTransportConstructionData
      (G := G) (obs := obs) :=
  C.toSplitCoreWithGlobalAssumptions.withTransportWitnessChoice W

/-- Add direct exposing-context transport. -/
def withExposingTransport
    (C : TrimmedPresentationSplitCoreWithSplitGlobalAssumptions
      (G := G) (obs := obs))
    (E : TrimmedPresentationExposingContextTransport C.core.data) :
    TrimmedPresentationSplitLayeredExposingConstructionData
      (G := G) (obs := obs) :=
  C.toSplitCoreWithGlobalAssumptions.withExposingTransport E

/-- Add anchor common-context transport. -/
def withAnchorCommonTransport
    (C : TrimmedPresentationSplitCoreWithSplitGlobalAssumptions
      (G := G) (obs := obs))
    (A : TrimmedPresentationAnchorCommonContextTransport C.core.data) :
    TrimmedPresentationSplitLayeredAnchorCommonConstructionData
      (G := G) (obs := obs) :=
  C.toSplitCoreWithGlobalAssumptions.withAnchorCommonTransport A

/-- Add same-context transport. -/
def withSameContextTransport
    (C : TrimmedPresentationSplitCoreWithSplitGlobalAssumptions
      (G := G) (obs := obs))
    (S : TrimmedPresentationSameContextTransport C.core.data) :
    TrimmedPresentationSplitLayeredSameContextConstructionData
      (G := G) (obs := obs) :=
  C.toSplitCoreWithGlobalAssumptions.withSameContextTransport S

/-- An abstract transport witness over the base gives the main theorem. -/
theorem main_theorem_from_transport_choice
    (C : TrimmedPresentationSplitCoreWithSplitGlobalAssumptions
      (G := G) (obs := obs))
    (W : TrimmedPresentationTransportWitnessChoice C.base) :
    ExistsBoundedReachableIdentification G obs :=
  C.toSplitCoreWithGlobalAssumptions
    .main_theorem_from_transport_choice W

/-- Direct exposing transport over the core gives the main theorem. -/
theorem main_theorem_from_exposing_transport
    (C : TrimmedPresentationSplitCoreWithSplitGlobalAssumptions
      (G := G) (obs := obs))
    (E : TrimmedPresentationExposingContextTransport C.core.data) :
    ExistsBoundedReachableIdentification G obs :=
  C.toSplitCoreWithGlobalAssumptions
    .main_theorem_from_exposing_transport E

/-- Anchor common-context transport over the core gives the main theorem. -/
theorem main_theorem_from_anchor_common_transport
    (C : TrimmedPresentationSplitCoreWithSplitGlobalAssumptions
      (G := G) (obs := obs))
    (A : TrimmedPresentationAnchorCommonContextTransport C.core.data) :
    ExistsBoundedReachableIdentification G obs :=
  C.toSplitCoreWithGlobalAssumptions
    .main_theorem_from_anchor_common_transport A

/-- Same-context transport over the core gives the main theorem. -/
theorem main_theorem_from_same_context_transport
    (C : TrimmedPresentationSplitCoreWithSplitGlobalAssumptions
      (G := G) (obs := obs))
    (S : TrimmedPresentationSameContextTransport C.core.data) :
    ExistsBoundedReachableIdentification G obs :=
  C.toSplitCoreWithGlobalAssumptions
    .main_theorem_from_same_context_transport S

end TrimmedPresentationSplitCoreWithSplitGlobalAssumptions

end SplitCoreWithSplitGlobal


section SplitGlobalExistential

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}

/-- There exists a split core with split global assumptions and an abstract
transport witness choice over its base. -/
def ExistsSplitCoreSplitGlobalWithTransportChoice
    (G : WorkingMCFG N α) (obs : α → M) : Prop :=
  ∃ C : TrimmedPresentationSplitCoreWithSplitGlobalAssumptions
      (G := G) (obs := obs),
    Nonempty (TrimmedPresentationTransportWitnessChoice C.base)

/-- There exists a split core with split global assumptions and direct exposing
transport. -/
def ExistsSplitCoreSplitGlobalWithExposingTransport
    (G : WorkingMCFG N α) (obs : α → M) : Prop :=
  ∃ C : TrimmedPresentationSplitCoreWithSplitGlobalAssumptions
      (G := G) (obs := obs),
    Nonempty (TrimmedPresentationExposingContextTransport C.core.data)

/-- There exists a split core with split global assumptions and anchor
common-context transport. -/
def ExistsSplitCoreSplitGlobalWithAnchorCommonTransport
    (G : WorkingMCFG N α) (obs : α → M) : Prop :=
  ∃ C : TrimmedPresentationSplitCoreWithSplitGlobalAssumptions
      (G := G) (obs := obs),
    Nonempty (TrimmedPresentationAnchorCommonContextTransport C.core.data)

/-- There exists a split core with split global assumptions and same-context
transport. -/
def ExistsSplitCoreSplitGlobalWithSameContextTransport
    (G : WorkingMCFG N α) (obs : α → M) : Prop :=
  ∃ C : TrimmedPresentationSplitCoreWithSplitGlobalAssumptions
      (G := G) (obs := obs),
    Nonempty (TrimmedPresentationSameContextTransport C.core.data)

/-- Split-global interface implies the previous bundled-global transport-choice
interface. -/
theorem existsSplitCoreGlobalWithTransportChoice_of_splitGlobal
    (h : ExistsSplitCoreSplitGlobalWithTransportChoice G obs) :
    ExistsSplitCoreGlobalWithTransportChoice G obs :=
  match h with
  | ⟨C, hW⟩ =>
      ⟨C.toSplitCoreWithGlobalAssumptions, hW⟩

/-- Split-global exposing interface implies the previous bundled-global exposing
interface. -/
theorem existsSplitCoreGlobalWithExposingTransport_of_splitGlobal
    (h : ExistsSplitCoreSplitGlobalWithExposingTransport G obs) :
    ExistsSplitCoreGlobalWithExposingTransport G obs :=
  match h with
  | ⟨C, hE⟩ =>
      ⟨C.toSplitCoreWithGlobalAssumptions, hE⟩

/-- Split-global anchor-common interface implies the previous bundled-global
anchor-common interface. -/
theorem existsSplitCoreGlobalWithAnchorCommonTransport_of_splitGlobal
    (h : ExistsSplitCoreSplitGlobalWithAnchorCommonTransport G obs) :
    ExistsSplitCoreGlobalWithAnchorCommonTransport G obs :=
  match h with
  | ⟨C, hA⟩ =>
      ⟨C.toSplitCoreWithGlobalAssumptions, hA⟩

/-- Split-global same-context interface implies the previous bundled-global
same-context interface. -/
theorem existsSplitCoreGlobalWithSameContextTransport_of_splitGlobal
    (h : ExistsSplitCoreSplitGlobalWithSameContextTransport G obs) :
    ExistsSplitCoreGlobalWithSameContextTransport G obs :=
  match h with
  | ⟨C, hS⟩ =>
      ⟨C.toSplitCoreWithGlobalAssumptions, hS⟩

/-- Main theorem from the split-global transport-choice interface. -/
theorem existsSplitCoreSplitGlobalWithTransportChoice_main_theorem
    (h : ExistsSplitCoreSplitGlobalWithTransportChoice G obs) :
    ExistsBoundedReachableIdentification G obs :=
  trimmed_split_core_global_transport_choice_main_theorem
    (existsSplitCoreGlobalWithTransportChoice_of_splitGlobal h)

/-- Main theorem from the split-global exposing interface. -/
theorem existsSplitCoreSplitGlobalWithExposingTransport_main_theorem
    (h : ExistsSplitCoreSplitGlobalWithExposingTransport G obs) :
    ExistsBoundedReachableIdentification G obs :=
  trimmed_split_core_global_exposing_transport_main_theorem
    (existsSplitCoreGlobalWithExposingTransport_of_splitGlobal h)

/-- Main theorem from the split-global anchor-common interface. -/
theorem existsSplitCoreSplitGlobalWithAnchorCommonTransport_main_theorem
    (h : ExistsSplitCoreSplitGlobalWithAnchorCommonTransport G obs) :
    ExistsBoundedReachableIdentification G obs :=
  trimmed_split_core_global_anchor_common_transport_main_theorem
    (existsSplitCoreGlobalWithAnchorCommonTransport_of_splitGlobal h)

/-- Main theorem from the split-global same-context interface. -/
theorem existsSplitCoreSplitGlobalWithSameContextTransport_main_theorem
    (h : ExistsSplitCoreSplitGlobalWithSameContextTransport G obs) :
    ExistsBoundedReachableIdentification G obs :=
  trimmed_split_core_global_same_context_transport_main_theorem
    (existsSplitCoreGlobalWithSameContextTransport_of_splitGlobal h)

end SplitGlobalExistential


section SplitGlobalTopLevelTheorems

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}

/-- Top-level theorem: split core plus split global assumptions and any transport
choice gives Gold-style identification for some finite bound. -/
theorem trimmed_split_global_transport_choice_main_theorem
    (h : ExistsSplitCoreSplitGlobalWithTransportChoice G obs) :
    ExistsBoundedReachableIdentification G obs :=
  existsSplitCoreSplitGlobalWithTransportChoice_main_theorem h

/-- Top-level theorem: split core plus split global assumptions and exposing
transport gives Gold-style identification for some finite bound. -/
theorem trimmed_split_global_exposing_transport_main_theorem
    (h : ExistsSplitCoreSplitGlobalWithExposingTransport G obs) :
    ExistsBoundedReachableIdentification G obs :=
  existsSplitCoreSplitGlobalWithExposingTransport_main_theorem h

/-- Top-level theorem: split core plus split global assumptions and anchor
common-context transport gives Gold-style identification for some finite bound. -/
theorem trimmed_split_global_anchor_common_transport_main_theorem
    (h : ExistsSplitCoreSplitGlobalWithAnchorCommonTransport G obs) :
    ExistsBoundedReachableIdentification G obs :=
  existsSplitCoreSplitGlobalWithAnchorCommonTransport_main_theorem h

/-- Top-level theorem: split core plus split global assumptions and same-context
transport gives Gold-style identification for some finite bound. -/
theorem trimmed_split_global_same_context_transport_main_theorem
    (h : ExistsSplitCoreSplitGlobalWithSameContextTransport G obs) :
    ExistsBoundedReachableIdentification G obs :=
  existsSplitCoreSplitGlobalWithSameContextTransport_main_theorem h

end SplitGlobalTopLevelTheorems

end MCFG
