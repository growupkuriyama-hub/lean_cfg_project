/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG2.CharacteristicSamplePreferredAnchorCommonTargets

/-!
# CharacteristicSamplePreferredAnchorCommonTargetPieces.lean

One-hundred-nineteenth clean Lean experiment for the fixed-observation MCFG
project.

`CharacteristicSamplePreferredAnchorCommonTargets.lean` split the preferred
anchor-common construction route into the three major pieces:

```text
split core
fully split global assumptions
anchor-common transport.
```

This file gives each of those pieces an explicit paper-facing target name:

* `PaperPreferredSplitCoreTarget`;
* `PaperPreferredFullySplitGlobalTarget`;
* `PaperPreferredAnchorCommonTransportTarget`.

The combined record

```lean
PaperPreferredAnchorCommonSeparatedTargets
```

is equivalent, for theorem purposes, to the previous layered preferred
anchor-common construction data.  The goal is to make the next construction
phase extremely explicit: build the split core first, then the global
assumptions, then the anchor-common transport witness.

No new mathematical principle is introduced here.

No theorem here uses `sorry`.
-/

namespace MCFG

universe u v w

section PreferredAnchorCommonTargetPieces

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}

/-- Paper-facing target for the preferred split core construction. -/
structure PaperPreferredSplitCoreTarget where
  splitCore :
    TrimmedPresentationSplitCoreConstructionData
      (G := G) (obs := obs)

/-- Paper-facing target for the fully split global assumptions over a fixed
preferred split core. -/
structure PaperPreferredFullySplitGlobalTarget
    (K :
      TrimmedPresentationSplitCoreConstructionData
        (G := G) (obs := obs)) where
  fullySplitGlobal :
    TrimmedPresentationFullySplitGlobalConstructionAssumptions
      K.toCoreConstructionData

/-- Paper-facing target for the anchor-common transport witness over a fixed
preferred split core. -/
structure PaperPreferredAnchorCommonTransportTarget
    (K :
      TrimmedPresentationSplitCoreConstructionData
        (G := G) (obs := obs)) where
  commonTransport :
    TrimmedPresentationAnchorCommonContextTransport
      K.toCoreConstructionData.data

/-- The preferred anchor-common construction target with all three pieces named
separately. -/
structure PaperPreferredAnchorCommonSeparatedTargets where
  coreTarget :
    PaperPreferredSplitCoreTarget
      (G := G) (obs := obs)
  globalTarget :
    PaperPreferredFullySplitGlobalTarget coreTarget.splitCore
  transportTarget :
    PaperPreferredAnchorCommonTransportTarget coreTarget.splitCore

namespace PaperPreferredSplitCoreTarget

/-- Expose the reconstructed core package. -/
def core
    (K : PaperPreferredSplitCoreTarget
      (G := G) (obs := obs)) :
    TrimmedPresentationCoreConstructionData
      (G := G) (obs := obs) :=
  K.splitCore.toCoreConstructionData

/-- The fanout bound of the split core target. -/
def fanoutBound
    (K : PaperPreferredSplitCoreTarget
      (G := G) (obs := obs)) : Nat :=
  K.core.fanoutBound

/-- The trimmed output-type presentation of the split core target. -/
def presentation
    (K : PaperPreferredSplitCoreTarget
      (G := G) (obs := obs)) :
    TrimmedOutputTypePresentation G obs :=
  K.core.presentation

/-- The pre-core data of the split core target. -/
def data
    (K : PaperPreferredSplitCoreTarget
      (G := G) (obs := obs)) :
    TrimmedPresentationPreCoreData K.presentation K.fanoutBound :=
  K.core.data

/-- The grammar-rule builder of the split core target. -/
def builder
    (K : PaperPreferredSplitCoreTarget
      (G := G) (obs := obs)) :
    TrimmedPresentationGrammarRuleBuilder K.data :=
  K.core.builder

end PaperPreferredSplitCoreTarget


namespace PaperPreferredFullySplitGlobalTarget

variable {K :
  TrimmedPresentationSplitCoreConstructionData
    (G := G) (obs := obs)}

/-- Recombine the fully split global target into the bundled global assumptions. -/
def global
    (A : PaperPreferredFullySplitGlobalTarget K) :
    TrimmedPresentationGlobalConstructionAssumptions
      K.toCoreConstructionData :=
  A.fullySplitGlobal.toGlobalConstructionAssumptions

/-- The named-context splicing constructor contained in the global target. -/
def splicingConstructor
    (A : PaperPreferredFullySplitGlobalTarget K) :
    NamedContextSplicingConstructor α :=
  A.global.splicingConstructor

/-- The fanout assumption contained in the global target. -/
def fanout
    (A : PaperPreferredFullySplitGlobalTarget K) :
    G.FanoutAtMost K.toCoreConstructionData.fanoutBound :=
  A.global.fanout

/-- The substitutability promise contained in the global target. -/
def promise
    (A : PaperPreferredFullySplitGlobalTarget K) :
    FixedNamedTupleSubstitutable
      K.toCoreConstructionData.fanoutBound obs G.StringLanguage :=
  A.global.promise

end PaperPreferredFullySplitGlobalTarget


namespace PaperPreferredAnchorCommonTransportTarget

variable {K :
  TrimmedPresentationSplitCoreConstructionData
    (G := G) (obs := obs)}

/-- Expose the transport witness contained in the target. -/
def transport
    (T : PaperPreferredAnchorCommonTransportTarget K) :
    TrimmedPresentationAnchorCommonContextTransport
      K.toCoreConstructionData.data :=
  T.commonTransport

end PaperPreferredAnchorCommonTransportTarget


namespace PaperPreferredAnchorCommonSeparatedTargets

/-- Recover the split core. -/
def splitCore
    (C : PaperPreferredAnchorCommonSeparatedTargets
      (G := G) (obs := obs)) :
    TrimmedPresentationSplitCoreConstructionData
      (G := G) (obs := obs) :=
  C.coreTarget.splitCore

/-- Recover the fully split global assumptions. -/
def fullySplitGlobal
    (C : PaperPreferredAnchorCommonSeparatedTargets
      (G := G) (obs := obs)) :
    TrimmedPresentationFullySplitGlobalConstructionAssumptions
      C.splitCore.toCoreConstructionData :=
  C.globalTarget.fullySplitGlobal

/-- Recover the anchor-common transport witness. -/
def commonTransport
    (C : PaperPreferredAnchorCommonSeparatedTargets
      (G := G) (obs := obs)) :
    TrimmedPresentationAnchorCommonContextTransport
      C.splitCore.toCoreConstructionData.data :=
  C.transportTarget.commonTransport

/-- Convert separated targets to the layered preferred construction data. -/
def toLayeredConstructionData
    (C : PaperPreferredAnchorCommonSeparatedTargets
      (G := G) (obs := obs)) :
    PaperPreferredAnchorCommonLayeredConstructionData
      (G := G) (obs := obs) where
  splitCore := C.splitCore
  fullySplitGlobal := C.fullySplitGlobal
  commonTransport := C.commonTransport

/-- Convert separated targets to the flat preferred paper construction data. -/
def toPaperPreferredAnchorCommonConstructionData
    (C : PaperPreferredAnchorCommonSeparatedTargets
      (G := G) (obs := obs)) :
    PaperPreferredAnchorCommonConstructionData
      (G := G) (obs := obs) :=
  C.toLayeredConstructionData.toPaperPreferredAnchorCommonConstructionData

/-- Separated targets imply existence of the preferred layered construction
data. -/
theorem existsLayeredConstruction
    (C : PaperPreferredAnchorCommonSeparatedTargets
      (G := G) (obs := obs)) :
    ExistsPaperPreferredAnchorCommonLayeredConstruction G obs :=
  ⟨C.toLayeredConstructionData⟩

/-- Separated targets imply existence of the preferred paper construction data. -/
theorem existsPreferredConstruction
    (C : PaperPreferredAnchorCommonSeparatedTargets
      (G := G) (obs := obs)) :
    ExistsPaperPreferredAnchorCommonConstruction G obs :=
  ⟨C.toPaperPreferredAnchorCommonConstructionData⟩

/-- Separated targets imply the dependent preferred target interface. -/
theorem existsPreferredTargets
    (C : PaperPreferredAnchorCommonSeparatedTargets
      (G := G) (obs := obs)) :
    ExistsPaperPreferredAnchorCommonConstructionTargets G obs :=
  ⟨C.splitCore,
    ⟨⟨C.fullySplitGlobal⟩,
      ⟨C.commonTransport⟩⟩⟩

/-- Main theorem from separated preferred targets. -/
theorem main_theorem
    (C : PaperPreferredAnchorCommonSeparatedTargets
      (G := G) (obs := obs)) :
    PaperConstructiveIdentificationConclusion G obs :=
  trimmed_paper_preferred_anchor_common_layered_construction_main_theorem
    C.existsLayeredConstruction

/-- Conclusion package from separated preferred targets. -/
theorem conclusion_package
    (C : PaperPreferredAnchorCommonSeparatedTargets
      (G := G) (obs := obs)) :
    PaperConstructiveLearningConclusionPackage G obs :=
  trimmed_paper_preferred_anchor_common_layered_construction_conclusion_package
    C.existsLayeredConstruction

end PaperPreferredAnchorCommonSeparatedTargets

end PreferredAnchorCommonTargetPieces


section PreferredAnchorCommonTargetPiecesExistential

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}

/-- Existence of the preferred anchor-common construction with its three pieces
named separately. -/
def ExistsPaperPreferredAnchorCommonSeparatedTargets
    (G : WorkingMCFG N α) (obs : α → M) : Prop :=
  Nonempty
    (PaperPreferredAnchorCommonSeparatedTargets
      (G := G) (obs := obs))

/-- Separated target existence gives layered preferred construction existence. -/
theorem existsPaperPreferredAnchorCommonLayeredConstruction_of_separatedTargets
    (h : ExistsPaperPreferredAnchorCommonSeparatedTargets G obs) :
    ExistsPaperPreferredAnchorCommonLayeredConstruction G obs :=
  match h with
  | ⟨C⟩ => C.existsLayeredConstruction

/-- Separated target existence gives the dependent preferred target interface. -/
theorem existsPaperPreferredAnchorCommonConstructionTargets_of_separatedTargets
    (h : ExistsPaperPreferredAnchorCommonSeparatedTargets G obs) :
    ExistsPaperPreferredAnchorCommonConstructionTargets G obs :=
  match h with
  | ⟨C⟩ => C.existsPreferredTargets

/-- Separated target existence gives preferred construction existence. -/
theorem existsPaperPreferredAnchorCommonConstruction_of_separatedTargets
    (h : ExistsPaperPreferredAnchorCommonSeparatedTargets G obs) :
    ExistsPaperPreferredAnchorCommonConstruction G obs :=
  match h with
  | ⟨C⟩ => C.existsPreferredConstruction

/-- Main theorem from separated target existence. -/
theorem paperPreferredAnchorCommonSeparatedTargets_main_theorem
    (h : ExistsPaperPreferredAnchorCommonSeparatedTargets G obs) :
    PaperConstructiveIdentificationConclusion G obs :=
  match h with
  | ⟨C⟩ => C.main_theorem

/-- Conclusion package from separated target existence. -/
theorem paperPreferredAnchorCommonSeparatedTargets_conclusion_package
    (h : ExistsPaperPreferredAnchorCommonSeparatedTargets G obs) :
    PaperConstructiveLearningConclusionPackage G obs :=
  match h with
  | ⟨C⟩ => C.conclusion_package

end PreferredAnchorCommonTargetPiecesExistential


section PreferredAnchorCommonTargetPiecesTopLevel

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}

/-- Stable top-level theorem from separated preferred anchor-common targets. -/
theorem trimmed_paper_preferred_anchor_common_separated_targets_main_theorem
    (h : ExistsPaperPreferredAnchorCommonSeparatedTargets G obs) :
    PaperConstructiveIdentificationConclusion G obs :=
  paperPreferredAnchorCommonSeparatedTargets_main_theorem h

/-- Stable top-level conclusion-package theorem from separated preferred
anchor-common targets. -/
theorem trimmed_paper_preferred_anchor_common_separated_targets_conclusion_package
    (h : ExistsPaperPreferredAnchorCommonSeparatedTargets G obs) :
    PaperConstructiveLearningConclusionPackage G obs :=
  paperPreferredAnchorCommonSeparatedTargets_conclusion_package h

/-- Stable bridge from separated preferred targets to the dependent preferred
target interface. -/
theorem trimmed_paper_preferred_anchor_common_targets_of_separated_targets
    (h : ExistsPaperPreferredAnchorCommonSeparatedTargets G obs) :
    ExistsPaperPreferredAnchorCommonConstructionTargets G obs :=
  existsPaperPreferredAnchorCommonConstructionTargets_of_separatedTargets h

end PreferredAnchorCommonTargetPiecesTopLevel

end MCFG
