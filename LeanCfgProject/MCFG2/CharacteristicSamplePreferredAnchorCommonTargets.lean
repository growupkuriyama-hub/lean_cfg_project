/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG.CharacteristicSamplePreferredAnchorCommonConstruction

/-!
# CharacteristicSamplePreferredAnchorCommonTargets.lean

One-hundred-eighteenth clean Lean experiment for the fixed-observation MCFG
project.

`CharacteristicSamplePreferredAnchorCommonConstruction.lean` introduced the
paper-facing preferred construction record

```lean
PaperPreferredAnchorCommonConstructionData
```

for the anchor-common route.

This file splits that preferred construction target into the three pieces that
should be attacked next:

```text
split core construction data
fully split global assumptions
anchor-common transport witness.
```

The new record

```lean
PaperPreferredAnchorCommonLayeredConstructionData
```

is therefore a construction-facing version of the preferred route, but with the
hard pieces factored into stable named fields.

No new mathematical principle is introduced here.

No theorem here uses `sorry`.
-/

namespace MCFG

universe u v w

section PreferredAnchorCommonTargets

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}

/-- Preferred anchor-common construction data, split into core/global/transport
targets. -/
structure PaperPreferredAnchorCommonLayeredConstructionData where
  splitCore :
    TrimmedPresentationSplitCoreConstructionData
      (G := G) (obs := obs)
  fullySplitGlobal :
    TrimmedPresentationFullySplitGlobalConstructionAssumptions
      splitCore.toCoreConstructionData
  commonTransport :
    TrimmedPresentationAnchorCommonContextTransport
      splitCore.toCoreConstructionData.data

namespace PaperPreferredAnchorCommonLayeredConstructionData

/-- Recover the core construction package. -/
def core
    (C : PaperPreferredAnchorCommonLayeredConstructionData
      (G := G) (obs := obs)) :
    TrimmedPresentationCoreConstructionData
      (G := G) (obs := obs) :=
  C.splitCore.toCoreConstructionData

/-- Recover the bundled global assumptions. -/
def global
    (C : PaperPreferredAnchorCommonLayeredConstructionData
      (G := G) (obs := obs)) :
    TrimmedPresentationGlobalConstructionAssumptions C.core :=
  C.fullySplitGlobal.toGlobalConstructionAssumptions

/-- Recover the split-core/fully-split-global package. -/
def toSplitCoreWithFullySplitGlobalAssumptions
    (C : PaperPreferredAnchorCommonLayeredConstructionData
      (G := G) (obs := obs)) :
    TrimmedPresentationSplitCoreWithFullySplitGlobalAssumptions
      (G := G) (obs := obs) where
  splitCore := C.splitCore
  fullySplitGlobal := C.fullySplitGlobal

/-- Recover the split-layered anchor-common construction package. -/
def toSplitLayeredAnchorCommonConstructionData
    (C : PaperPreferredAnchorCommonLayeredConstructionData
      (G := G) (obs := obs)) :
    TrimmedPresentationSplitLayeredAnchorCommonConstructionData
      (G := G) (obs := obs) where
  splitCore := C.splitCore
  global := C.global
  commonTransport := C.commonTransport

/-- Convert the layered preferred target to the previous paper-facing preferred
flat record. -/
def toPaperPreferredAnchorCommonConstructionData
    (C : PaperPreferredAnchorCommonLayeredConstructionData
      (G := G) (obs := obs)) :
    PaperPreferredAnchorCommonConstructionData
      (G := G) (obs := obs) where
  fanoutBound := C.core.fanoutBound
  presentation := C.core.presentation
  data := C.core.data
  builder := C.core.builder
  splicingConstructor := C.global.splicingConstructor
  fanout := C.global.fanout
  promise := C.global.promise
  commonTransport := C.commonTransport

/-- Convert the layered preferred target to the flat anchor-common construction
record. -/
def toFlatAnchorCommonConstructionData
    (C : PaperPreferredAnchorCommonLayeredConstructionData
      (G := G) (obs := obs)) :
    TrimmedPresentationFlatAnchorCommonConstructionData
      (G := G) (obs := obs) :=
  C.toPaperPreferredAnchorCommonConstructionData
    .toFlatAnchorCommonConstructionData

/-- Existence of the flat anchor-common construction route. -/
theorem existsFlatAnchorCommonConstruction
    (C : PaperPreferredAnchorCommonLayeredConstructionData
      (G := G) (obs := obs)) :
    ExistsFlatAnchorCommonConstruction G obs :=
  ⟨C.toFlatAnchorCommonConstructionData⟩

/-- Existence of the paper-facing preferred construction route. -/
theorem existsPaperPreferredAnchorCommonConstruction
    (C : PaperPreferredAnchorCommonLayeredConstructionData
      (G := G) (obs := obs)) :
    ExistsPaperPreferredAnchorCommonConstruction G obs :=
  ⟨C.toPaperPreferredAnchorCommonConstructionData⟩

/-- Preferred route assumption from layered preferred target data. -/
theorem preferredRouteAssumption
    (C : PaperPreferredAnchorCommonLayeredConstructionData
      (G := G) (obs := obs)) :
    PaperPreferredConstructiveRouteAssumption G obs :=
  C.existsFlatAnchorCommonConstruction

/-- General paper route assumption from layered preferred target data. -/
theorem paperRouteAssumption
    (C : PaperPreferredAnchorCommonLayeredConstructionData
      (G := G) (obs := obs)) :
    PaperConstructiveRouteAssumption G obs :=
  paperConstructiveRouteAssumption_of_preferred
    C.preferredRouteAssumption

/-- Main theorem from layered preferred target data. -/
theorem main_theorem
    (C : PaperPreferredAnchorCommonLayeredConstructionData
      (G := G) (obs := obs)) :
    PaperConstructiveIdentificationConclusion G obs :=
  trimmed_paper_preferred_anchor_common_construction_main_theorem
    C.existsPaperPreferredAnchorCommonConstruction

/-- Conclusion package from layered preferred target data. -/
theorem conclusion_package
    (C : PaperPreferredAnchorCommonLayeredConstructionData
      (G := G) (obs := obs)) :
    PaperConstructiveLearningConclusionPackage G obs :=
  trimmed_paper_preferred_anchor_common_construction_conclusion_package
    C.existsPaperPreferredAnchorCommonConstruction

/-- Characteristic-sample conclusion from layered preferred target data. -/
theorem characteristic_sample
    (C : PaperPreferredAnchorCommonLayeredConstructionData
      (G := G) (obs := obs)) :
    PaperConstructiveCharacteristicSampleConclusion G obs :=
  trimmed_paper_preferred_anchor_common_construction_characteristic_sample
    C.existsPaperPreferredAnchorCommonConstruction

/-- Prefix-exact conclusion from layered preferred target data. -/
theorem prefix_exact
    (C : PaperPreferredAnchorCommonLayeredConstructionData
      (G := G) (obs := obs)) :
    PaperConstructivePrefixExactConclusion G obs :=
  trimmed_paper_preferred_anchor_common_construction_prefix_exact
    C.existsPaperPreferredAnchorCommonConstruction

end PaperPreferredAnchorCommonLayeredConstructionData

end PreferredAnchorCommonTargets


section PreferredAnchorCommonTargetExistentials

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}

/-- Existence of preferred anchor-common layered construction data. -/
def ExistsPaperPreferredAnchorCommonLayeredConstruction
    (G : WorkingMCFG N α) (obs : α → M) : Prop :=
  Nonempty
    (PaperPreferredAnchorCommonLayeredConstructionData
      (G := G) (obs := obs))

/-- The preferred construction target expressed as a dependent existential over
one split core. -/
def ExistsPaperPreferredAnchorCommonConstructionTargets
    (G : WorkingMCFG N α) (obs : α → M) : Prop :=
  ∃ K :
      TrimmedPresentationSplitCoreConstructionData
        (G := G) (obs := obs),
    Nonempty
      (TrimmedPresentationFullySplitGlobalConstructionAssumptions
        K.toCoreConstructionData) ∧
    Nonempty
      (TrimmedPresentationAnchorCommonContextTransport
        K.toCoreConstructionData.data)

/-- Build layered preferred construction data from the three split targets over
one core. -/
def paperPreferredAnchorCommonLayeredConstructionData_of_targets
    (K :
      TrimmedPresentationSplitCoreConstructionData
        (G := G) (obs := obs))
    (A :
      TrimmedPresentationFullySplitGlobalConstructionAssumptions
        K.toCoreConstructionData)
    (T :
      TrimmedPresentationAnchorCommonContextTransport
        K.toCoreConstructionData.data) :
    PaperPreferredAnchorCommonLayeredConstructionData
      (G := G) (obs := obs) where
  splitCore := K
  fullySplitGlobal := A
  commonTransport := T

/-- The dependent target interface gives layered preferred construction data. -/
theorem existsPaperPreferredAnchorCommonLayeredConstruction_of_targets
    (h : ExistsPaperPreferredAnchorCommonConstructionTargets G obs) :
    ExistsPaperPreferredAnchorCommonLayeredConstruction G obs :=
  match h with
  | ⟨K, hRest⟩ =>
      match hRest with
      | ⟨hA, hT⟩ =>
          match hA with
          | ⟨A⟩ =>
              match hT with
              | ⟨T⟩ =>
                  ⟨paperPreferredAnchorCommonLayeredConstructionData_of_targets
                    K A T⟩

/-- Layered preferred construction data gives the previous preferred paper-facing
construction existence. -/
theorem existsPaperPreferredAnchorCommonConstruction_of_layered
    (h : ExistsPaperPreferredAnchorCommonLayeredConstruction G obs) :
    ExistsPaperPreferredAnchorCommonConstruction G obs :=
  match h with
  | ⟨C⟩ => C.existsPaperPreferredAnchorCommonConstruction

/-- The dependent target interface gives the previous preferred paper-facing
construction existence. -/
theorem existsPaperPreferredAnchorCommonConstruction_of_targets
    (h : ExistsPaperPreferredAnchorCommonConstructionTargets G obs) :
    ExistsPaperPreferredAnchorCommonConstruction G obs :=
  existsPaperPreferredAnchorCommonConstruction_of_layered
    (existsPaperPreferredAnchorCommonLayeredConstruction_of_targets h)

/-- Main theorem from layered preferred construction existence. -/
theorem paperPreferredAnchorCommonLayeredConstruction_main_theorem
    (h : ExistsPaperPreferredAnchorCommonLayeredConstruction G obs) :
    PaperConstructiveIdentificationConclusion G obs :=
  match h with
  | ⟨C⟩ => C.main_theorem

/-- Main theorem from the dependent target interface. -/
theorem paperPreferredAnchorCommonConstructionTargets_main_theorem
    (h : ExistsPaperPreferredAnchorCommonConstructionTargets G obs) :
    PaperConstructiveIdentificationConclusion G obs :=
  paperPreferredAnchorCommonLayeredConstruction_main_theorem
    (existsPaperPreferredAnchorCommonLayeredConstruction_of_targets h)

/-- Conclusion package from layered preferred construction existence. -/
theorem paperPreferredAnchorCommonLayeredConstruction_conclusion_package
    (h : ExistsPaperPreferredAnchorCommonLayeredConstruction G obs) :
    PaperConstructiveLearningConclusionPackage G obs :=
  match h with
  | ⟨C⟩ => C.conclusion_package

/-- Conclusion package from the dependent target interface. -/
theorem paperPreferredAnchorCommonConstructionTargets_conclusion_package
    (h : ExistsPaperPreferredAnchorCommonConstructionTargets G obs) :
    PaperConstructiveLearningConclusionPackage G obs :=
  paperPreferredAnchorCommonLayeredConstruction_conclusion_package
    (existsPaperPreferredAnchorCommonLayeredConstruction_of_targets h)

end PreferredAnchorCommonTargetExistentials


section PreferredAnchorCommonTargetsTopLevel

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}

/-- Stable top-level theorem from layered preferred anchor-common construction
data. -/
theorem trimmed_paper_preferred_anchor_common_layered_construction_main_theorem
    (h : ExistsPaperPreferredAnchorCommonLayeredConstruction G obs) :
    PaperConstructiveIdentificationConclusion G obs :=
  paperPreferredAnchorCommonLayeredConstruction_main_theorem h

/-- Stable top-level theorem from the dependent preferred target interface. -/
theorem trimmed_paper_preferred_anchor_common_targets_main_theorem
    (h : ExistsPaperPreferredAnchorCommonConstructionTargets G obs) :
    PaperConstructiveIdentificationConclusion G obs :=
  paperPreferredAnchorCommonConstructionTargets_main_theorem h

/-- Stable top-level conclusion-package theorem from layered preferred
anchor-common construction data. -/
theorem trimmed_paper_preferred_anchor_common_layered_construction_conclusion_package
    (h : ExistsPaperPreferredAnchorCommonLayeredConstruction G obs) :
    PaperConstructiveLearningConclusionPackage G obs :=
  paperPreferredAnchorCommonLayeredConstruction_conclusion_package h

/-- Stable top-level conclusion-package theorem from the dependent preferred
target interface. -/
theorem trimmed_paper_preferred_anchor_common_targets_conclusion_package
    (h : ExistsPaperPreferredAnchorCommonConstructionTargets G obs) :
    PaperConstructiveLearningConclusionPackage G obs :=
  paperPreferredAnchorCommonConstructionTargets_conclusion_package h

end PreferredAnchorCommonTargetsTopLevel

end MCFG
