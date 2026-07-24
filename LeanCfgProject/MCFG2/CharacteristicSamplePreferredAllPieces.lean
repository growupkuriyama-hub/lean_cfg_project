/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG2.CharacteristicSamplePreferredGlobalPieces

/-!
# CharacteristicSamplePreferredAllPieces.lean

One-hundred-twenty-second clean Lean experiment for the fixed-observation MCFG
project.

This file gives the complete preferred anchor-common construction checklist one
stable paper-facing name:

```lean
PaperPreferredAnchorCommonAllPieces
```

The checklist consists of:

```text
fanout bound
trimmed output-type presentation
pre-core data
grammar-rule builder
named-context splicing constructor
fanout assumption
fixed-observation substitutability promise
anchor-common transport witness.
```

No new mathematical principle is introduced here.

No theorem here uses `sorry`.
-/

namespace MCFG

universe u v w

section PreferredAllPieces

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}

/-- Complete paper-facing checklist for the preferred anchor-common route. -/
structure PaperPreferredAnchorCommonAllPieces where
  fanoutBound : Nat
  presentation : TrimmedOutputTypePresentation G obs
  data : TrimmedPresentationPreCoreData presentation fanoutBound
  builder : TrimmedPresentationGrammarRuleBuilder data
  splicingConstructor : NamedContextSplicingConstructor α
  fanout : G.FanoutAtMost fanoutBound
  promise : FixedNamedTupleSubstitutable fanoutBound obs G.StringLanguage
  commonTransport : TrimmedPresentationAnchorCommonContextTransport data

namespace PaperPreferredAnchorCommonAllPieces

/-- The fanout-bound target contained in the complete checklist. -/
def toFanoutBoundTarget
    (C : PaperPreferredAnchorCommonAllPieces
      (G := G) (obs := obs)) :
    PaperPreferredFanoutBoundTarget :=
  { fanoutBound := C.fanoutBound }

/-- The presentation target contained in the complete checklist. -/
def toPresentationTarget
    (C : PaperPreferredAnchorCommonAllPieces
      (G := G) (obs := obs)) :
    PaperPreferredPresentationTarget
      (G := G) (obs := obs) where
  fanoutTarget := C.toFanoutBoundTarget
  presentation := C.presentation

/-- The pre-core target contained in the complete checklist. -/
def toPreCoreTarget
    (C : PaperPreferredAnchorCommonAllPieces
      (G := G) (obs := obs)) :
    PaperPreferredPreCoreTarget
      (G := G) (obs := obs) where
  presentationTarget := C.toPresentationTarget
  data := C.data

/-- The rule-builder target contained in the complete checklist. -/
def toRuleBuilderTarget
    (C : PaperPreferredAnchorCommonAllPieces
      (G := G) (obs := obs)) :
    PaperPreferredRuleBuilderTarget
      (G := G) (obs := obs) where
  preCoreTarget := C.toPreCoreTarget
  builder := C.builder

/-- The split core construction data contained in the complete checklist. -/
def toSplitCoreConstructionData
    (C : PaperPreferredAnchorCommonAllPieces
      (G := G) (obs := obs)) :
    TrimmedPresentationSplitCoreConstructionData
      (G := G) (obs := obs) :=
  C.toRuleBuilderTarget.toSplitCoreConstructionData

/-- The preferred split-core target contained in the complete checklist. -/
def toSplitCoreTarget
    (C : PaperPreferredAnchorCommonAllPieces
      (G := G) (obs := obs)) :
    PaperPreferredSplitCoreTarget
      (G := G) (obs := obs) :=
  C.toRuleBuilderTarget.toPreferredSplitCoreTarget

/-- The splicing-constructor target contained in the complete checklist. -/
def toSplicingConstructorTarget
    (C : PaperPreferredAnchorCommonAllPieces
      (G := G) (obs := obs)) :
    PaperPreferredSplicingConstructorTarget (α := α) where
  splicingConstructor := C.splicingConstructor

/-- The fanout-assumption target contained in the complete checklist. -/
def toFanoutAssumptionTarget
    (C : PaperPreferredAnchorCommonAllPieces
      (G := G) (obs := obs)) :
    PaperPreferredFanoutAssumptionTarget
      (G := G) C.toSplitCoreConstructionData where
  fanout := C.fanout

/-- The substitutability target contained in the complete checklist. -/
def toSubstitutabilityAssumptionTarget
    (C : PaperPreferredAnchorCommonAllPieces
      (G := G) (obs := obs)) :
    PaperPreferredSubstitutabilityAssumptionTarget
      (G := G) (obs := obs) C.toSplitCoreConstructionData where
  promise := C.promise

/-- The separated global target contained in the complete checklist. -/
def toSeparatedGlobalTarget
    (C : PaperPreferredAnchorCommonAllPieces
      (G := G) (obs := obs)) :
    PaperPreferredFullySplitGlobalSeparatedTarget
      (G := G) (obs := obs) C.toSplitCoreConstructionData where
  splicingTarget := C.toSplicingConstructorTarget
  fanoutTarget := C.toFanoutAssumptionTarget
  substitutabilityTarget := C.toSubstitutabilityAssumptionTarget

/-- The fully split global target contained in the complete checklist. -/
def toFullySplitGlobalTarget
    (C : PaperPreferredAnchorCommonAllPieces
      (G := G) (obs := obs)) :
    PaperPreferredFullySplitGlobalTarget C.toSplitCoreConstructionData :=
  C.toSeparatedGlobalTarget.toPreferredFullySplitGlobalTarget

/-- The anchor-common transport target contained in the complete checklist. -/
def toAnchorCommonTransportTarget
    (C : PaperPreferredAnchorCommonAllPieces
      (G := G) (obs := obs)) :
    PaperPreferredAnchorCommonTransportTarget C.toSplitCoreConstructionData where
  commonTransport := C.commonTransport

/-- Reassemble all pieces into the previous separated-global piecewise target. -/
def toPiecewiseSeparatedGlobalTargets
    (C : PaperPreferredAnchorCommonAllPieces
      (G := G) (obs := obs)) :
    PaperPreferredAnchorCommonPiecewiseSeparatedGlobalTargets
      (G := G) (obs := obs) where
  ruleBuilderTarget := C.toRuleBuilderTarget
  separatedGlobalTarget := C.toSeparatedGlobalTarget
  transportTarget := C.toAnchorCommonTransportTarget

/-- Reassemble all pieces into the previous piecewise target interface. -/
def toPiecewiseTargets
    (C : PaperPreferredAnchorCommonAllPieces
      (G := G) (obs := obs)) :
    ExistsPaperPreferredAnchorCommonPiecewiseTargets G obs :=
  C.toPiecewiseSeparatedGlobalTargets.toPiecewiseTargets

/-- Reassemble all pieces into separated preferred anchor-common targets. -/
def toSeparatedTargets
    (C : PaperPreferredAnchorCommonAllPieces
      (G := G) (obs := obs)) :
    PaperPreferredAnchorCommonSeparatedTargets
      (G := G) (obs := obs) :=
  C.toPiecewiseSeparatedGlobalTargets.toSeparatedTargets

/-- Reassemble all pieces into layered preferred construction data. -/
def toLayeredConstructionData
    (C : PaperPreferredAnchorCommonAllPieces
      (G := G) (obs := obs)) :
    PaperPreferredAnchorCommonLayeredConstructionData
      (G := G) (obs := obs) :=
  C.toSeparatedTargets.toLayeredConstructionData

/-- Reassemble all pieces into the preferred paper-facing construction data. -/
def toPaperPreferredAnchorCommonConstructionData
    (C : PaperPreferredAnchorCommonAllPieces
      (G := G) (obs := obs)) :
    PaperPreferredAnchorCommonConstructionData
      (G := G) (obs := obs) :=
  C.toLayeredConstructionData.toPaperPreferredAnchorCommonConstructionData

/-- All pieces give existence of separated-global piecewise targets. -/
theorem existsPiecewiseSeparatedGlobalTargets
    (C : PaperPreferredAnchorCommonAllPieces
      (G := G) (obs := obs)) :
    ExistsPaperPreferredAnchorCommonPiecewiseSeparatedGlobalTargets G obs :=
  ⟨C.toPiecewiseSeparatedGlobalTargets⟩

/-- All pieces give existence of the preferred paper-facing construction data. -/
theorem existsPreferredConstruction
    (C : PaperPreferredAnchorCommonAllPieces
      (G := G) (obs := obs)) :
    ExistsPaperPreferredAnchorCommonConstruction G obs :=
  ⟨C.toPaperPreferredAnchorCommonConstructionData⟩

/-- All pieces give the paper-facing main theorem. -/
theorem main_theorem
    (C : PaperPreferredAnchorCommonAllPieces
      (G := G) (obs := obs)) :
    PaperConstructiveIdentificationConclusion G obs :=
  trimmed_paper_preferred_anchor_common_separated_global_targets_main_theorem
    C.existsPiecewiseSeparatedGlobalTargets

/-- All pieces give the paper-facing conclusion package. -/
theorem conclusion_package
    (C : PaperPreferredAnchorCommonAllPieces
      (G := G) (obs := obs)) :
    PaperConstructiveLearningConclusionPackage G obs :=
  trimmed_paper_preferred_anchor_common_separated_global_targets_conclusion_package
    C.existsPiecewiseSeparatedGlobalTargets

end PaperPreferredAnchorCommonAllPieces

end PreferredAllPieces


section PreferredAllPiecesExistential

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}

/-- Existence of the complete paper-facing checklist for the preferred
anchor-common route. -/
def ExistsPaperPreferredAnchorCommonAllPieces
    (G : WorkingMCFG N α) (obs : α → M) : Prop :=
  Nonempty
    (PaperPreferredAnchorCommonAllPieces
      (G := G) (obs := obs))

/-- All-pieces existence gives separated-global piecewise target existence. -/
theorem existsPaperPreferredAnchorCommonPiecewiseSeparatedGlobalTargets_of_allPieces
    (h : ExistsPaperPreferredAnchorCommonAllPieces G obs) :
    ExistsPaperPreferredAnchorCommonPiecewiseSeparatedGlobalTargets G obs :=
  match h with
  | ⟨C⟩ => C.existsPiecewiseSeparatedGlobalTargets

/-- All-pieces existence gives preferred paper construction existence. -/
theorem existsPaperPreferredAnchorCommonConstruction_of_allPieces
    (h : ExistsPaperPreferredAnchorCommonAllPieces G obs) :
    ExistsPaperPreferredAnchorCommonConstruction G obs :=
  match h with
  | ⟨C⟩ => C.existsPreferredConstruction

/-- All-pieces existence gives the paper-facing main theorem. -/
theorem paperPreferredAnchorCommonAllPieces_main_theorem
    (h : ExistsPaperPreferredAnchorCommonAllPieces G obs) :
    PaperConstructiveIdentificationConclusion G obs :=
  match h with
  | ⟨C⟩ => C.main_theorem

/-- All-pieces existence gives the paper-facing conclusion package. -/
theorem paperPreferredAnchorCommonAllPieces_conclusion_package
    (h : ExistsPaperPreferredAnchorCommonAllPieces G obs) :
    PaperConstructiveLearningConclusionPackage G obs :=
  match h with
  | ⟨C⟩ => C.conclusion_package

end PreferredAllPiecesExistential


section PreferredAllPiecesTopLevel

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}

/-- Stable top-level theorem from the complete all-pieces checklist. -/
theorem trimmed_paper_preferred_anchor_common_all_pieces_main_theorem
    (h : ExistsPaperPreferredAnchorCommonAllPieces G obs) :
    PaperConstructiveIdentificationConclusion G obs :=
  paperPreferredAnchorCommonAllPieces_main_theorem h

/-- Stable top-level conclusion-package theorem from the complete all-pieces
checklist. -/
theorem trimmed_paper_preferred_anchor_common_all_pieces_conclusion_package
    (h : ExistsPaperPreferredAnchorCommonAllPieces G obs) :
    PaperConstructiveLearningConclusionPackage G obs :=
  paperPreferredAnchorCommonAllPieces_conclusion_package h

/-- Stable bridge from all-pieces existence to separated-global piecewise target
existence. -/
theorem trimmed_paper_preferred_anchor_common_separated_global_targets_of_all_pieces
    (h : ExistsPaperPreferredAnchorCommonAllPieces G obs) :
    ExistsPaperPreferredAnchorCommonPiecewiseSeparatedGlobalTargets G obs :=
  existsPaperPreferredAnchorCommonPiecewiseSeparatedGlobalTargets_of_allPieces h

end PreferredAllPiecesTopLevel

end MCFG
