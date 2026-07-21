/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG2.CharacteristicSamplePreferredAnchorCommonTargetPieces

/-!
# CharacteristicSamplePreferredSplitCorePieces.lean

One-hundred-twentieth clean Lean experiment for the fixed-observation MCFG
project.

`CharacteristicSamplePreferredAnchorCommonTargetPieces.lean` separated the
preferred anchor-common route into:

```text
split core target
fully split global target
anchor-common transport target.
```

This file splits the preferred split-core target itself into the four pieces
that should eventually be constructed concretely:

```text
fanout bound
trimmed output-type presentation
pre-core data
grammar-rule builder.
```

The final piece

```lean
PaperPreferredRuleBuilderTarget
```

reassembles to

```lean
PaperPreferredSplitCoreTarget
```

and can therefore be plugged back into the preferred anchor-common target route.

No new mathematical principle is introduced here.

No theorem here uses `sorry`.
-/

namespace MCFG

universe u v w

section PreferredSplitCorePieces

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}

/-- Paper-facing target for the fanout bound used in the preferred construction. -/
structure PaperPreferredFanoutBoundTarget where
  fanoutBound : Nat

/-- Paper-facing target for the trimmed output-type presentation at the selected
fanout bound. -/
structure PaperPreferredPresentationTarget where
  fanoutTarget : PaperPreferredFanoutBoundTarget
  presentation : TrimmedOutputTypePresentation G obs

namespace PaperPreferredPresentationTarget

/-- The fanout bound carried by the presentation target. -/
def fanoutBound
    (P : PaperPreferredPresentationTarget
      (G := G) (obs := obs)) : Nat :=
  P.fanoutTarget.fanoutBound

end PaperPreferredPresentationTarget

/-- Paper-facing target for the pre-core data over the preferred presentation. -/
structure PaperPreferredPreCoreTarget where
  presentationTarget :
    PaperPreferredPresentationTarget
      (G := G) (obs := obs)
  data :
    TrimmedPresentationPreCoreData
      presentationTarget.presentation
      presentationTarget.fanoutBound

namespace PaperPreferredPreCoreTarget

/-- The fanout bound inherited by the pre-core target. -/
def fanoutBound
    (D : PaperPreferredPreCoreTarget
      (G := G) (obs := obs)) : Nat :=
  D.presentationTarget.fanoutBound

/-- The trimmed output-type presentation inherited by the pre-core target. -/
def presentation
    (D : PaperPreferredPreCoreTarget
      (G := G) (obs := obs)) :
    TrimmedOutputTypePresentation G obs :=
  D.presentationTarget.presentation

end PaperPreferredPreCoreTarget

/-- Paper-facing target for the grammar-rule builder over the preferred pre-core
data. -/
structure PaperPreferredRuleBuilderTarget where
  preCoreTarget :
    PaperPreferredPreCoreTarget
      (G := G) (obs := obs)
  builder :
    TrimmedPresentationGrammarRuleBuilder preCoreTarget.data

namespace PaperPreferredRuleBuilderTarget

/-- The fanout bound inherited by the rule-builder target. -/
def fanoutBound
    (R : PaperPreferredRuleBuilderTarget
      (G := G) (obs := obs)) : Nat :=
  R.preCoreTarget.fanoutBound

/-- The trimmed output-type presentation inherited by the rule-builder target. -/
def presentation
    (R : PaperPreferredRuleBuilderTarget
      (G := G) (obs := obs)) :
    TrimmedOutputTypePresentation G obs :=
  R.preCoreTarget.presentation

/-- The pre-core data inherited by the rule-builder target. -/
def data
    (R : PaperPreferredRuleBuilderTarget
      (G := G) (obs := obs)) :
    TrimmedPresentationPreCoreData R.presentation R.fanoutBound :=
  R.preCoreTarget.data

/-- Reassemble the rule-builder target into split-core construction data. -/
def toSplitCoreConstructionData
    (R : PaperPreferredRuleBuilderTarget
      (G := G) (obs := obs)) :
    TrimmedPresentationSplitCoreConstructionData
      (G := G) (obs := obs) where
  fanoutBound := R.fanoutBound
  presentation := R.presentation
  data := R.data
  builder := R.builder

/-- Reassemble the rule-builder target into the preferred split-core target. -/
def toPreferredSplitCoreTarget
    (R : PaperPreferredRuleBuilderTarget
      (G := G) (obs := obs)) :
    PaperPreferredSplitCoreTarget
      (G := G) (obs := obs) where
  splitCore := R.toSplitCoreConstructionData

/-- Reassemble the rule-builder target into the older split core data. -/
def toSplitCore
    (R : PaperPreferredRuleBuilderTarget
      (G := G) (obs := obs)) :
    TrimmedPresentationSplitCoreConstructionData
      (G := G) (obs := obs) :=
  R.toSplitCoreConstructionData

/-- Combine split-core pieces with global and transport targets to obtain the
separated preferred anchor-common targets. -/
def toSeparatedTargets
    (R : PaperPreferredRuleBuilderTarget
      (G := G) (obs := obs))
    (A :
      PaperPreferredFullySplitGlobalTarget R.toSplitCoreConstructionData)
    (T :
      PaperPreferredAnchorCommonTransportTarget R.toSplitCoreConstructionData) :
    PaperPreferredAnchorCommonSeparatedTargets
      (G := G) (obs := obs) where
  coreTarget := R.toPreferredSplitCoreTarget
  globalTarget := A
  transportTarget := T

/-- Split-core pieces plus global and transport targets give the paper-facing
main theorem. -/
theorem main_theorem
    (R : PaperPreferredRuleBuilderTarget
      (G := G) (obs := obs))
    (A :
      PaperPreferredFullySplitGlobalTarget R.toSplitCoreConstructionData)
    (T :
      PaperPreferredAnchorCommonTransportTarget R.toSplitCoreConstructionData) :
    PaperConstructiveIdentificationConclusion G obs :=
  (R.toSeparatedTargets A T).main_theorem

/-- Split-core pieces plus global and transport targets give the full
paper-facing conclusion package. -/
theorem conclusion_package
    (R : PaperPreferredRuleBuilderTarget
      (G := G) (obs := obs))
    (A :
      PaperPreferredFullySplitGlobalTarget R.toSplitCoreConstructionData)
    (T :
      PaperPreferredAnchorCommonTransportTarget R.toSplitCoreConstructionData) :
    PaperConstructiveLearningConclusionPackage G obs :=
  (R.toSeparatedTargets A T).conclusion_package

end PaperPreferredRuleBuilderTarget

end PreferredSplitCorePieces


section PreferredSplitCorePiecesExistential

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}

/-- Existence of the preferred split-core pieces up to the rule-builder layer. -/
def ExistsPaperPreferredSplitCorePieces
    (G : WorkingMCFG N α) (obs : α → M) : Prop :=
  Nonempty
    (PaperPreferredRuleBuilderTarget
      (G := G) (obs := obs))

/-- Existence of the preferred split-core target. -/
def ExistsPaperPreferredSplitCoreTarget
    (G : WorkingMCFG N α) (obs : α → M) : Prop :=
  Nonempty
    (PaperPreferredSplitCoreTarget
      (G := G) (obs := obs))

/-- Split-core pieces give the preferred split-core target. -/
theorem existsPaperPreferredSplitCoreTarget_of_pieces
    (h : ExistsPaperPreferredSplitCorePieces G obs) :
    ExistsPaperPreferredSplitCoreTarget G obs :=
  match h with
  | ⟨R⟩ => ⟨R.toPreferredSplitCoreTarget⟩

/-- A piecewise preferred anchor-common target interface: construct split-core
pieces, then global target, then anchor-common transport target over the same
split core. -/
def ExistsPaperPreferredAnchorCommonPiecewiseTargets
    (G : WorkingMCFG N α) (obs : α → M) : Prop :=
  ∃ R :
      PaperPreferredRuleBuilderTarget
        (G := G) (obs := obs),
    Nonempty
      (PaperPreferredFullySplitGlobalTarget
        R.toSplitCoreConstructionData) ∧
    Nonempty
      (PaperPreferredAnchorCommonTransportTarget
        R.toSplitCoreConstructionData)

/-- Piecewise preferred targets give separated preferred anchor-common targets. -/
theorem existsPaperPreferredAnchorCommonSeparatedTargets_of_piecewise
    (h : ExistsPaperPreferredAnchorCommonPiecewiseTargets G obs) :
    ExistsPaperPreferredAnchorCommonSeparatedTargets G obs :=
  match h with
  | ⟨R, hRest⟩ =>
      match hRest with
      | ⟨hA, hT⟩ =>
          match hA with
          | ⟨A⟩ =>
              match hT with
              | ⟨T⟩ =>
                  ⟨R.toSeparatedTargets A T⟩

/-- Piecewise preferred targets give the dependent preferred target interface. -/
theorem existsPaperPreferredAnchorCommonConstructionTargets_of_piecewise
    (h : ExistsPaperPreferredAnchorCommonPiecewiseTargets G obs) :
    ExistsPaperPreferredAnchorCommonConstructionTargets G obs :=
  trimmed_paper_preferred_anchor_common_targets_of_separated_targets
    (existsPaperPreferredAnchorCommonSeparatedTargets_of_piecewise h)

/-- Main theorem from the piecewise preferred target interface. -/
theorem paperPreferredAnchorCommonPiecewiseTargets_main_theorem
    (h : ExistsPaperPreferredAnchorCommonPiecewiseTargets G obs) :
    PaperConstructiveIdentificationConclusion G obs :=
  trimmed_paper_preferred_anchor_common_separated_targets_main_theorem
    (existsPaperPreferredAnchorCommonSeparatedTargets_of_piecewise h)

/-- Conclusion package from the piecewise preferred target interface. -/
theorem paperPreferredAnchorCommonPiecewiseTargets_conclusion_package
    (h : ExistsPaperPreferredAnchorCommonPiecewiseTargets G obs) :
    PaperConstructiveLearningConclusionPackage G obs :=
  trimmed_paper_preferred_anchor_common_separated_targets_conclusion_package
    (existsPaperPreferredAnchorCommonSeparatedTargets_of_piecewise h)

end PreferredSplitCorePiecesExistential


section PreferredSplitCorePiecesTopLevel

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}

/-- Stable top-level theorem from the piecewise preferred target interface. -/
theorem trimmed_paper_preferred_anchor_common_piecewise_targets_main_theorem
    (h : ExistsPaperPreferredAnchorCommonPiecewiseTargets G obs) :
    PaperConstructiveIdentificationConclusion G obs :=
  paperPreferredAnchorCommonPiecewiseTargets_main_theorem h

/-- Stable top-level conclusion-package theorem from the piecewise preferred
target interface. -/
theorem trimmed_paper_preferred_anchor_common_piecewise_targets_conclusion_package
    (h : ExistsPaperPreferredAnchorCommonPiecewiseTargets G obs) :
    PaperConstructiveLearningConclusionPackage G obs :=
  paperPreferredAnchorCommonPiecewiseTargets_conclusion_package h

/-- Stable bridge from split-core pieces to the preferred split-core target. -/
theorem trimmed_paper_preferred_split_core_target_of_pieces
    (h : ExistsPaperPreferredSplitCorePieces G obs) :
    ExistsPaperPreferredSplitCoreTarget G obs :=
  existsPaperPreferredSplitCoreTarget_of_pieces h

end PreferredSplitCorePiecesTopLevel

end MCFG
