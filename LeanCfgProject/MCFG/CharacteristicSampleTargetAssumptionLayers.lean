/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG.CharacteristicSampleGlobalAssumptionLayers

/-!
# CharacteristicSampleTargetAssumptionLayers.lean

One-hundred-eighth clean Lean experiment for the fixed-observation MCFG project.

`CharacteristicSampleGlobalAssumptionLayers.lean` separated the global
assumptions into

```text
splicingConstructor
+
target assumptions.
```

This file splits the target assumptions one step further:

```text
fanout bound assumption
+
fixed-observation substitutability promise.
```

So the global side is now decomposed as:

```text
NamedContextSplicingConstructor
G.FanoutAtMost f
FixedNamedTupleSubstitutable f obs G.StringLanguage
```

This is bookkeeping only, but it is useful: the three assumptions have different
mathematical origins and should eventually be discharged by different arguments.

No theorem here uses `sorry`.
-/

namespace MCFG

universe u v w

section TargetAssumptionLayers

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}

/-- The target-language fanout assumption at a fixed bound. -/
structure TrimmedPresentationFanoutConstructionAssumption
    (f : Nat) where
  fanout : G.FanoutAtMost f

/-- The fixed-observation substitutability promise at a fixed bound. -/
structure TrimmedPresentationSubstitutabilityConstructionAssumption
    (f : Nat) where
  promise : FixedNamedTupleSubstitutable f obs G.StringLanguage

/-- Fully split target assumptions at a fixed fanout bound. -/
structure TrimmedPresentationSplitTargetConstructionAssumptions
    (f : Nat) where
  fanoutAssumption :
    TrimmedPresentationFanoutConstructionAssumption
      (G := G) f
  substitutabilityAssumption :
    TrimmedPresentationSubstitutabilityConstructionAssumption
      (G := G) (obs := obs) f

namespace TrimmedPresentationSplitTargetConstructionAssumptions

variable {f : Nat}

/-- Recombine fully split target assumptions into the previous bundled target
assumption package. -/
def toTargetConstructionAssumptions
    (A : TrimmedPresentationSplitTargetConstructionAssumptions
      (G := G) (obs := obs) f) :
    TrimmedPresentationTargetConstructionAssumptions
      (G := G) (obs := obs) f where
  fanout := A.fanoutAssumption.fanout
  promise := A.substitutabilityAssumption.promise

end TrimmedPresentationSplitTargetConstructionAssumptions


namespace TrimmedPresentationTargetConstructionAssumptions

variable {f : Nat}

/-- Split the previous bundled target assumptions into fanout and
substitutability pieces. -/
def toSplitTargetConstructionAssumptions
    (A : TrimmedPresentationTargetConstructionAssumptions
      (G := G) (obs := obs) f) :
    TrimmedPresentationSplitTargetConstructionAssumptions
      (G := G) (obs := obs) f where
  fanoutAssumption := {
    fanout := A.fanout
  }
  substitutabilityAssumption := {
    promise := A.promise
  }

end TrimmedPresentationTargetConstructionAssumptions

end TargetAssumptionLayers


section FullySplitGlobalAssumptions

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}

/-- Fully split global assumptions over a fixed core.

This separates all three global assumptions. -/
structure TrimmedPresentationFullySplitGlobalConstructionAssumptions
    (K : TrimmedPresentationCoreConstructionData
      (G := G) (obs := obs)) where
  splicing : TrimmedPresentationSplicingConstructionAssumption (α := α)
  fanoutAssumption :
    TrimmedPresentationFanoutConstructionAssumption
      (G := G) K.fanoutBound
  substitutabilityAssumption :
    TrimmedPresentationSubstitutabilityConstructionAssumption
      (G := G) (obs := obs) K.fanoutBound

namespace TrimmedPresentationFullySplitGlobalConstructionAssumptions

variable {K : TrimmedPresentationCoreConstructionData
  (G := G) (obs := obs)}

/-- Package the two target-side pieces together. -/
def target
    (A : TrimmedPresentationFullySplitGlobalConstructionAssumptions K) :
    TrimmedPresentationSplitTargetConstructionAssumptions
      (G := G) (obs := obs) K.fanoutBound where
  fanoutAssumption := A.fanoutAssumption
  substitutabilityAssumption := A.substitutabilityAssumption

/-- Recombine fully split global assumptions into the previous split-global
package. -/
def toSplitGlobalConstructionAssumptions
    (A : TrimmedPresentationFullySplitGlobalConstructionAssumptions K) :
    TrimmedPresentationSplitGlobalConstructionAssumptions K where
  splicing := A.splicing
  target := A.target.toTargetConstructionAssumptions

/-- Recombine fully split global assumptions into the older bundled-global
package. -/
def toGlobalConstructionAssumptions
    (A : TrimmedPresentationFullySplitGlobalConstructionAssumptions K) :
    TrimmedPresentationGlobalConstructionAssumptions K :=
  A.toSplitGlobalConstructionAssumptions.toGlobalConstructionAssumptions

end TrimmedPresentationFullySplitGlobalConstructionAssumptions


namespace TrimmedPresentationSplitGlobalConstructionAssumptions

variable {K : TrimmedPresentationCoreConstructionData
  (G := G) (obs := obs)}

/-- Split the previous split-global package one step further by separating the
target assumptions into fanout and substitutability pieces. -/
def toFullySplitGlobalConstructionAssumptions
    (A : TrimmedPresentationSplitGlobalConstructionAssumptions K) :
    TrimmedPresentationFullySplitGlobalConstructionAssumptions K where
  splicing := A.splicing
  fanoutAssumption := A.target.toSplitTargetConstructionAssumptions.fanoutAssumption
  substitutabilityAssumption :=
    A.target.toSplitTargetConstructionAssumptions.substitutabilityAssumption

end TrimmedPresentationSplitGlobalConstructionAssumptions

end FullySplitGlobalAssumptions


section SplitCoreWithFullySplitGlobal

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}

/-- Split core together with fully split global assumptions.

This is the same information as
`TrimmedPresentationSplitCoreWithSplitGlobalAssumptions`, but with fanout and
substitutability separated. -/
structure TrimmedPresentationSplitCoreWithFullySplitGlobalAssumptions where
  splitCore : TrimmedPresentationSplitCoreConstructionData
    (G := G) (obs := obs)
  fullySplitGlobal :
    TrimmedPresentationFullySplitGlobalConstructionAssumptions
      splitCore.toCoreConstructionData

namespace TrimmedPresentationSplitCoreWithFullySplitGlobalAssumptions

/-- Recombine the fully split global assumptions to the previous split-global
package. -/
def splitGlobal
    (C : TrimmedPresentationSplitCoreWithFullySplitGlobalAssumptions
      (G := G) (obs := obs)) :
    TrimmedPresentationSplitGlobalConstructionAssumptions
      C.splitCore.toCoreConstructionData :=
  C.fullySplitGlobal.toSplitGlobalConstructionAssumptions

/-- Recombine the fully split global assumptions to the bundled-global package. -/
def global
    (C : TrimmedPresentationSplitCoreWithFullySplitGlobalAssumptions
      (G := G) (obs := obs)) :
    TrimmedPresentationGlobalConstructionAssumptions
      C.splitCore.toCoreConstructionData :=
  C.fullySplitGlobal.toGlobalConstructionAssumptions

/-- Convert to the previous split-core/split-global layer. -/
def toSplitCoreWithSplitGlobalAssumptions
    (C : TrimmedPresentationSplitCoreWithFullySplitGlobalAssumptions
      (G := G) (obs := obs)) :
    TrimmedPresentationSplitCoreWithSplitGlobalAssumptions
      (G := G) (obs := obs) where
  splitCore := C.splitCore
  splitGlobal := C.splitGlobal

/-- Convert to the previous split-core/global layer. -/
def toSplitCoreWithGlobalAssumptions
    (C : TrimmedPresentationSplitCoreWithFullySplitGlobalAssumptions
      (G := G) (obs := obs)) :
    TrimmedPresentationSplitCoreWithGlobalAssumptions
      (G := G) (obs := obs) :=
  C.toSplitCoreWithSplitGlobalAssumptions
    .toSplitCoreWithGlobalAssumptions

/-- Recover the previous core construction package. -/
def core
    (C : TrimmedPresentationSplitCoreWithFullySplitGlobalAssumptions
      (G := G) (obs := obs)) :
    TrimmedPresentationCoreConstructionData
      (G := G) (obs := obs) :=
  C.splitCore.toCoreConstructionData

/-- Recover the previous base construction package. -/
def base
    (C : TrimmedPresentationSplitCoreWithFullySplitGlobalAssumptions
      (G := G) (obs := obs)) :
    TrimmedPresentationBaseConstructionData
      (G := G) (obs := obs) :=
  C.toSplitCoreWithGlobalAssumptions.base

/-- Add an abstract transport-witness choice. -/
def withTransportWitnessChoice
    (C : TrimmedPresentationSplitCoreWithFullySplitGlobalAssumptions
      (G := G) (obs := obs))
    (W : TrimmedPresentationTransportWitnessChoice C.base) :
    TrimmedPresentationSplitLayeredTransportConstructionData
      (G := G) (obs := obs) :=
  C.toSplitCoreWithGlobalAssumptions.withTransportWitnessChoice W

/-- Add direct exposing-context transport. -/
def withExposingTransport
    (C : TrimmedPresentationSplitCoreWithFullySplitGlobalAssumptions
      (G := G) (obs := obs))
    (E : TrimmedPresentationExposingContextTransport C.core.data) :
    TrimmedPresentationSplitLayeredExposingConstructionData
      (G := G) (obs := obs) :=
  C.toSplitCoreWithGlobalAssumptions.withExposingTransport E

/-- Add anchor common-context transport. -/
def withAnchorCommonTransport
    (C : TrimmedPresentationSplitCoreWithFullySplitGlobalAssumptions
      (G := G) (obs := obs))
    (A : TrimmedPresentationAnchorCommonContextTransport C.core.data) :
    TrimmedPresentationSplitLayeredAnchorCommonConstructionData
      (G := G) (obs := obs) :=
  C.toSplitCoreWithGlobalAssumptions.withAnchorCommonTransport A

/-- Add same-context transport. -/
def withSameContextTransport
    (C : TrimmedPresentationSplitCoreWithFullySplitGlobalAssumptions
      (G := G) (obs := obs))
    (S : TrimmedPresentationSameContextTransport C.core.data) :
    TrimmedPresentationSplitLayeredSameContextConstructionData
      (G := G) (obs := obs) :=
  C.toSplitCoreWithGlobalAssumptions.withSameContextTransport S

/-- An abstract transport witness over the base gives the main theorem. -/
theorem main_theorem_from_transport_choice
    (C : TrimmedPresentationSplitCoreWithFullySplitGlobalAssumptions
      (G := G) (obs := obs))
    (W : TrimmedPresentationTransportWitnessChoice C.base) :
    ExistsBoundedReachableIdentification G obs :=
  C.toSplitCoreWithGlobalAssumptions
    .main_theorem_from_transport_choice W

/-- Direct exposing transport over the core gives the main theorem. -/
theorem main_theorem_from_exposing_transport
    (C : TrimmedPresentationSplitCoreWithFullySplitGlobalAssumptions
      (G := G) (obs := obs))
    (E : TrimmedPresentationExposingContextTransport C.core.data) :
    ExistsBoundedReachableIdentification G obs :=
  C.toSplitCoreWithGlobalAssumptions
    .main_theorem_from_exposing_transport E

/-- Anchor common-context transport over the core gives the main theorem. -/
theorem main_theorem_from_anchor_common_transport
    (C : TrimmedPresentationSplitCoreWithFullySplitGlobalAssumptions
      (G := G) (obs := obs))
    (A : TrimmedPresentationAnchorCommonContextTransport C.core.data) :
    ExistsBoundedReachableIdentification G obs :=
  C.toSplitCoreWithGlobalAssumptions
    .main_theorem_from_anchor_common_transport A

/-- Same-context transport over the core gives the main theorem. -/
theorem main_theorem_from_same_context_transport
    (C : TrimmedPresentationSplitCoreWithFullySplitGlobalAssumptions
      (G := G) (obs := obs))
    (S : TrimmedPresentationSameContextTransport C.core.data) :
    ExistsBoundedReachableIdentification G obs :=
  C.toSplitCoreWithGlobalAssumptions
    .main_theorem_from_same_context_transport S

end TrimmedPresentationSplitCoreWithFullySplitGlobalAssumptions

end SplitCoreWithFullySplitGlobal


section FullySplitGlobalExistential

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}

/-- There exists a split core with fully split global assumptions and an
abstract transport witness choice over its base. -/
def ExistsSplitCoreFullySplitGlobalWithTransportChoice
    (G : WorkingMCFG N α) (obs : α → M) : Prop :=
  ∃ C : TrimmedPresentationSplitCoreWithFullySplitGlobalAssumptions
      (G := G) (obs := obs),
    Nonempty (TrimmedPresentationTransportWitnessChoice C.base)

/-- There exists a split core with fully split global assumptions and direct
exposing transport. -/
def ExistsSplitCoreFullySplitGlobalWithExposingTransport
    (G : WorkingMCFG N α) (obs : α → M) : Prop :=
  ∃ C : TrimmedPresentationSplitCoreWithFullySplitGlobalAssumptions
      (G := G) (obs := obs),
    Nonempty (TrimmedPresentationExposingContextTransport C.core.data)

/-- There exists a split core with fully split global assumptions and anchor
common-context transport. -/
def ExistsSplitCoreFullySplitGlobalWithAnchorCommonTransport
    (G : WorkingMCFG N α) (obs : α → M) : Prop :=
  ∃ C : TrimmedPresentationSplitCoreWithFullySplitGlobalAssumptions
      (G := G) (obs := obs),
    Nonempty (TrimmedPresentationAnchorCommonContextTransport C.core.data)

/-- There exists a split core with fully split global assumptions and
same-context transport. -/
def ExistsSplitCoreFullySplitGlobalWithSameContextTransport
    (G : WorkingMCFG N α) (obs : α → M) : Prop :=
  ∃ C : TrimmedPresentationSplitCoreWithFullySplitGlobalAssumptions
      (G := G) (obs := obs),
    Nonempty (TrimmedPresentationSameContextTransport C.core.data)

/-- Fully split global interface implies the previous split-global
transport-choice interface. -/
theorem existsSplitCoreSplitGlobalWithTransportChoice_of_fullySplitGlobal
    (h : ExistsSplitCoreFullySplitGlobalWithTransportChoice G obs) :
    ExistsSplitCoreSplitGlobalWithTransportChoice G obs :=
  match h with
  | ⟨C, hW⟩ =>
      ⟨C.toSplitCoreWithSplitGlobalAssumptions, hW⟩

/-- Fully split global exposing interface implies the previous split-global
exposing interface. -/
theorem existsSplitCoreSplitGlobalWithExposingTransport_of_fullySplitGlobal
    (h : ExistsSplitCoreFullySplitGlobalWithExposingTransport G obs) :
    ExistsSplitCoreSplitGlobalWithExposingTransport G obs :=
  match h with
  | ⟨C, hE⟩ =>
      ⟨C.toSplitCoreWithSplitGlobalAssumptions, hE⟩

/-- Fully split global anchor-common interface implies the previous split-global
anchor-common interface. -/
theorem existsSplitCoreSplitGlobalWithAnchorCommonTransport_of_fullySplitGlobal
    (h : ExistsSplitCoreFullySplitGlobalWithAnchorCommonTransport G obs) :
    ExistsSplitCoreSplitGlobalWithAnchorCommonTransport G obs :=
  match h with
  | ⟨C, hA⟩ =>
      ⟨C.toSplitCoreWithSplitGlobalAssumptions, hA⟩

/-- Fully split global same-context interface implies the previous split-global
same-context interface. -/
theorem existsSplitCoreSplitGlobalWithSameContextTransport_of_fullySplitGlobal
    (h : ExistsSplitCoreFullySplitGlobalWithSameContextTransport G obs) :
    ExistsSplitCoreSplitGlobalWithSameContextTransport G obs :=
  match h with
  | ⟨C, hS⟩ =>
      ⟨C.toSplitCoreWithSplitGlobalAssumptions, hS⟩

/-- Main theorem from the fully split global transport-choice interface. -/
theorem existsSplitCoreFullySplitGlobalWithTransportChoice_main_theorem
    (h : ExistsSplitCoreFullySplitGlobalWithTransportChoice G obs) :
    ExistsBoundedReachableIdentification G obs :=
  trimmed_split_global_transport_choice_main_theorem
    (existsSplitCoreSplitGlobalWithTransportChoice_of_fullySplitGlobal h)

/-- Main theorem from the fully split global exposing interface. -/
theorem existsSplitCoreFullySplitGlobalWithExposingTransport_main_theorem
    (h : ExistsSplitCoreFullySplitGlobalWithExposingTransport G obs) :
    ExistsBoundedReachableIdentification G obs :=
  trimmed_split_global_exposing_transport_main_theorem
    (existsSplitCoreSplitGlobalWithExposingTransport_of_fullySplitGlobal h)

/-- Main theorem from the fully split global anchor-common interface. -/
theorem existsSplitCoreFullySplitGlobalWithAnchorCommonTransport_main_theorem
    (h : ExistsSplitCoreFullySplitGlobalWithAnchorCommonTransport G obs) :
    ExistsBoundedReachableIdentification G obs :=
  trimmed_split_global_anchor_common_transport_main_theorem
    (existsSplitCoreSplitGlobalWithAnchorCommonTransport_of_fullySplitGlobal h)

/-- Main theorem from the fully split global same-context interface. -/
theorem existsSplitCoreFullySplitGlobalWithSameContextTransport_main_theorem
    (h : ExistsSplitCoreFullySplitGlobalWithSameContextTransport G obs) :
    ExistsBoundedReachableIdentification G obs :=
  trimmed_split_global_same_context_transport_main_theorem
    (existsSplitCoreSplitGlobalWithSameContextTransport_of_fullySplitGlobal h)

end FullySplitGlobalExistential


section FullySplitGlobalTopLevelTheorems

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}

/-- Top-level theorem: split core plus fully split global assumptions and any
transport choice gives Gold-style identification for some finite bound. -/
theorem trimmed_fully_split_global_transport_choice_main_theorem
    (h : ExistsSplitCoreFullySplitGlobalWithTransportChoice G obs) :
    ExistsBoundedReachableIdentification G obs :=
  existsSplitCoreFullySplitGlobalWithTransportChoice_main_theorem h

/-- Top-level theorem: split core plus fully split global assumptions and
exposing transport gives Gold-style identification for some finite bound. -/
theorem trimmed_fully_split_global_exposing_transport_main_theorem
    (h : ExistsSplitCoreFullySplitGlobalWithExposingTransport G obs) :
    ExistsBoundedReachableIdentification G obs :=
  existsSplitCoreFullySplitGlobalWithExposingTransport_main_theorem h

/-- Top-level theorem: split core plus fully split global assumptions and anchor
common-context transport gives Gold-style identification for some finite bound. -/
theorem trimmed_fully_split_global_anchor_common_transport_main_theorem
    (h : ExistsSplitCoreFullySplitGlobalWithAnchorCommonTransport G obs) :
    ExistsBoundedReachableIdentification G obs :=
  existsSplitCoreFullySplitGlobalWithAnchorCommonTransport_main_theorem h

/-- Top-level theorem: split core plus fully split global assumptions and
same-context transport gives Gold-style identification for some finite bound. -/
theorem trimmed_fully_split_global_same_context_transport_main_theorem
    (h : ExistsSplitCoreFullySplitGlobalWithSameContextTransport G obs) :
    ExistsBoundedReachableIdentification G obs :=
  existsSplitCoreFullySplitGlobalWithSameContextTransport_main_theorem h

end FullySplitGlobalTopLevelTheorems

end MCFG
