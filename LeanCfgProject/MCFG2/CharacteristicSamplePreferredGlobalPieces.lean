/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG.CharacteristicSamplePreferredSplitCorePieces

/-!
# CharacteristicSamplePreferredGlobalPieces.lean

One-hundred-twenty-first clean Lean experiment for the fixed-observation MCFG
project.

`CharacteristicSamplePreferredSplitCorePieces.lean` split the preferred
anchor-common route into a piecewise target:

```text
rule-builder target
+
fully split global target
+
anchor-common transport target.
```

This file splits the preferred fully split global target into the three global
pieces that have different mathematical origins:

```text
NamedContextSplicingConstructor
fanout assumption
fixed-observation substitutability promise.
```

The new record

```lean
PaperPreferredFullySplitGlobalSeparatedTarget
```

reassembles to the earlier

```lean
PaperPreferredFullySplitGlobalTarget.
```

No new mathematical principle is introduced here.

No theorem here uses `sorry`.
-/

namespace MCFG

universe u v w

section PreferredGlobalPieces

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}

/-- Paper-facing target for the named-context splicing constructor. -/
structure PaperPreferredSplicingConstructorTarget where
  splicingConstructor : NamedContextSplicingConstructor α

/-- Paper-facing target for the fanout assumption over a fixed preferred split
core. -/
structure PaperPreferredFanoutAssumptionTarget
    (K :
      TrimmedPresentationSplitCoreConstructionData
        (G := G) (obs := obs)) where
  fanout : G.FanoutAtMost K.toCoreConstructionData.fanoutBound

/-- Paper-facing target for the fixed-observation substitutability promise over
a fixed preferred split core. -/
structure PaperPreferredSubstitutabilityAssumptionTarget
    (K :
      TrimmedPresentationSplitCoreConstructionData
        (G := G) (obs := obs)) where
  promise :
    FixedNamedTupleSubstitutable
      K.toCoreConstructionData.fanoutBound obs G.StringLanguage

namespace PaperPreferredSplicingConstructorTarget

/-- Convert the paper-facing splicing target to the generic splicing assumption. -/
def toSplicingConstructionAssumption
    (S : PaperPreferredSplicingConstructorTarget (α := α)) :
    TrimmedPresentationSplicingConstructionAssumption (α := α) where
  splicingConstructor := S.splicingConstructor

end PaperPreferredSplicingConstructorTarget


namespace PaperPreferredFanoutAssumptionTarget

variable {K :
  TrimmedPresentationSplitCoreConstructionData
    (G := G) (obs := obs)}

/-- Convert the paper-facing fanout target to the generic fanout assumption. -/
def toFanoutConstructionAssumption
    (F : PaperPreferredFanoutAssumptionTarget (G := G) K) :
    TrimmedPresentationFanoutConstructionAssumption
      (G := G) K.toCoreConstructionData.fanoutBound where
  fanout := F.fanout

end PaperPreferredFanoutAssumptionTarget


namespace PaperPreferredSubstitutabilityAssumptionTarget

variable {K :
  TrimmedPresentationSplitCoreConstructionData
    (G := G) (obs := obs)}

/-- Convert the paper-facing substitutability target to the generic
substitutability assumption. -/
def toSubstitutabilityConstructionAssumption
    (P : PaperPreferredSubstitutabilityAssumptionTarget
      (G := G) (obs := obs) K) :
    TrimmedPresentationSubstitutabilityConstructionAssumption
      (G := G) (obs := obs) K.toCoreConstructionData.fanoutBound where
  promise := P.promise

end PaperPreferredSubstitutabilityAssumptionTarget


/-- Paper-facing global target with the three global pieces named separately. -/
structure PaperPreferredFullySplitGlobalSeparatedTarget
    (K :
      TrimmedPresentationSplitCoreConstructionData
        (G := G) (obs := obs)) where
  splicingTarget : PaperPreferredSplicingConstructorTarget (α := α)
  fanoutTarget : PaperPreferredFanoutAssumptionTarget (G := G) K
  substitutabilityTarget :
    PaperPreferredSubstitutabilityAssumptionTarget
      (G := G) (obs := obs) K

namespace PaperPreferredFullySplitGlobalSeparatedTarget

variable {K :
  TrimmedPresentationSplitCoreConstructionData
    (G := G) (obs := obs)}

/-- Reassemble separated global targets into fully split global assumptions. -/
def toFullySplitGlobalConstructionAssumptions
    (A : PaperPreferredFullySplitGlobalSeparatedTarget
      (G := G) (obs := obs) K) :
    TrimmedPresentationFullySplitGlobalConstructionAssumptions
      K.toCoreConstructionData where
  splicing := A.splicingTarget.toSplicingConstructionAssumption
  fanoutAssumption := A.fanoutTarget.toFanoutConstructionAssumption
  substitutabilityAssumption :=
    A.substitutabilityTarget.toSubstitutabilityConstructionAssumption

/-- Reassemble separated global targets into the preferred fully split global
target. -/
def toPreferredFullySplitGlobalTarget
    (A : PaperPreferredFullySplitGlobalSeparatedTarget
      (G := G) (obs := obs) K) :
    PaperPreferredFullySplitGlobalTarget K where
  fullySplitGlobal := A.toFullySplitGlobalConstructionAssumptions

/-- Reassemble separated global targets into bundled global assumptions. -/
def toGlobalConstructionAssumptions
    (A : PaperPreferredFullySplitGlobalSeparatedTarget
      (G := G) (obs := obs) K) :
    TrimmedPresentationGlobalConstructionAssumptions
      K.toCoreConstructionData :=
  A.toFullySplitGlobalConstructionAssumptions
    .toGlobalConstructionAssumptions

/-- The named-context splicing constructor contained in separated global
targets. -/
def splicingConstructor
    (A : PaperPreferredFullySplitGlobalSeparatedTarget
      (G := G) (obs := obs) K) :
    NamedContextSplicingConstructor α :=
  A.toGlobalConstructionAssumptions.splicingConstructor

/-- The fanout assumption contained in separated global targets. -/
def fanout
    (A : PaperPreferredFullySplitGlobalSeparatedTarget
      (G := G) (obs := obs) K) :
    G.FanoutAtMost K.toCoreConstructionData.fanoutBound :=
  A.toGlobalConstructionAssumptions.fanout

/-- The substitutability promise contained in separated global targets. -/
def promise
    (A : PaperPreferredFullySplitGlobalSeparatedTarget
      (G := G) (obs := obs) K) :
    FixedNamedTupleSubstitutable
      K.toCoreConstructionData.fanoutBound obs G.StringLanguage :=
  A.toGlobalConstructionAssumptions.promise

end PaperPreferredFullySplitGlobalSeparatedTarget

end PreferredGlobalPieces


section PreferredPiecewiseWithSeparatedGlobal

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}

/-- Preferred anchor-common targets with the global part also separated into
splicing/fanout/substitutability pieces. -/
structure PaperPreferredAnchorCommonPiecewiseSeparatedGlobalTargets where
  ruleBuilderTarget :
    PaperPreferredRuleBuilderTarget
      (G := G) (obs := obs)
  separatedGlobalTarget :
    PaperPreferredFullySplitGlobalSeparatedTarget
      ruleBuilderTarget.toSplitCoreConstructionData
  transportTarget :
    PaperPreferredAnchorCommonTransportTarget
      ruleBuilderTarget.toSplitCoreConstructionData

namespace PaperPreferredAnchorCommonPiecewiseSeparatedGlobalTargets

/-- Recover the preferred rule-builder target. -/
def ruleBuilder
    (C : PaperPreferredAnchorCommonPiecewiseSeparatedGlobalTargets
      (G := G) (obs := obs)) :
    PaperPreferredRuleBuilderTarget
      (G := G) (obs := obs) :=
  C.ruleBuilderTarget

/-- Recover the split core construction data. -/
def splitCore
    (C : PaperPreferredAnchorCommonPiecewiseSeparatedGlobalTargets
      (G := G) (obs := obs)) :
    TrimmedPresentationSplitCoreConstructionData
      (G := G) (obs := obs) :=
  C.ruleBuilderTarget.toSplitCoreConstructionData

/-- Recover the preferred fully split global target. -/
def globalTarget
    (C : PaperPreferredAnchorCommonPiecewiseSeparatedGlobalTargets
      (G := G) (obs := obs)) :
    PaperPreferredFullySplitGlobalTarget C.splitCore :=
  C.separatedGlobalTarget.toPreferredFullySplitGlobalTarget

/-- Recover the preferred anchor-common transport target. -/
def transport
    (C : PaperPreferredAnchorCommonPiecewiseSeparatedGlobalTargets
      (G := G) (obs := obs)) :
    PaperPreferredAnchorCommonTransportTarget C.splitCore :=
  C.transportTarget

/-- Convert to the previous piecewise target interface. -/
def toPiecewiseTargets
    (C : PaperPreferredAnchorCommonPiecewiseSeparatedGlobalTargets
      (G := G) (obs := obs)) :
    ExistsPaperPreferredAnchorCommonPiecewiseTargets G obs :=
  ⟨C.ruleBuilderTarget,
    ⟨⟨C.globalTarget⟩,
      ⟨C.transportTarget⟩⟩⟩

/-- Convert to separated preferred anchor-common targets. -/
def toSeparatedTargets
    (C : PaperPreferredAnchorCommonPiecewiseSeparatedGlobalTargets
      (G := G) (obs := obs)) :
    PaperPreferredAnchorCommonSeparatedTargets
      (G := G) (obs := obs) :=
  C.ruleBuilderTarget.toSeparatedTargets
    C.globalTarget
    C.transportTarget

/-- Main theorem from piecewise targets with separated global assumptions. -/
theorem main_theorem
    (C : PaperPreferredAnchorCommonPiecewiseSeparatedGlobalTargets
      (G := G) (obs := obs)) :
    PaperConstructiveIdentificationConclusion G obs :=
  trimmed_paper_preferred_anchor_common_piecewise_targets_main_theorem
    C.toPiecewiseTargets

/-- Conclusion package from piecewise targets with separated global assumptions. -/
theorem conclusion_package
    (C : PaperPreferredAnchorCommonPiecewiseSeparatedGlobalTargets
      (G := G) (obs := obs)) :
    PaperConstructiveLearningConclusionPackage G obs :=
  trimmed_paper_preferred_anchor_common_piecewise_targets_conclusion_package
    C.toPiecewiseTargets

end PaperPreferredAnchorCommonPiecewiseSeparatedGlobalTargets

end PreferredPiecewiseWithSeparatedGlobal


section PreferredGlobalPiecesExistential

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}

/-- Existence of preferred anchor-common piecewise targets with the global part
split into splicing/fanout/substitutability pieces. -/
def ExistsPaperPreferredAnchorCommonPiecewiseSeparatedGlobalTargets
    (G : WorkingMCFG N α) (obs : α → M) : Prop :=
  Nonempty
    (PaperPreferredAnchorCommonPiecewiseSeparatedGlobalTargets
      (G := G) (obs := obs))

/-- Separated-global piecewise targets give the previous piecewise target
interface. -/
theorem existsPaperPreferredAnchorCommonPiecewiseTargets_of_separatedGlobal
    (h :
      ExistsPaperPreferredAnchorCommonPiecewiseSeparatedGlobalTargets
        G obs) :
    ExistsPaperPreferredAnchorCommonPiecewiseTargets G obs :=
  match h with
  | ⟨C⟩ => C.toPiecewiseTargets

/-- Separated-global piecewise targets give separated preferred
anchor-common targets. -/
theorem existsPaperPreferredAnchorCommonSeparatedTargets_of_separatedGlobal
    (h :
      ExistsPaperPreferredAnchorCommonPiecewiseSeparatedGlobalTargets
        G obs) :
    ExistsPaperPreferredAnchorCommonSeparatedTargets G obs :=
  existsPaperPreferredAnchorCommonSeparatedTargets_of_piecewise
    (existsPaperPreferredAnchorCommonPiecewiseTargets_of_separatedGlobal h)

/-- Main theorem from separated-global piecewise targets. -/
theorem paperPreferredAnchorCommonSeparatedGlobalTargets_main_theorem
    (h :
      ExistsPaperPreferredAnchorCommonPiecewiseSeparatedGlobalTargets
        G obs) :
    PaperConstructiveIdentificationConclusion G obs :=
  trimmed_paper_preferred_anchor_common_piecewise_targets_main_theorem
    (existsPaperPreferredAnchorCommonPiecewiseTargets_of_separatedGlobal h)

/-- Conclusion package from separated-global piecewise targets. -/
theorem paperPreferredAnchorCommonSeparatedGlobalTargets_conclusion_package
    (h :
      ExistsPaperPreferredAnchorCommonPiecewiseSeparatedGlobalTargets
        G obs) :
    PaperConstructiveLearningConclusionPackage G obs :=
  trimmed_paper_preferred_anchor_common_piecewise_targets_conclusion_package
    (existsPaperPreferredAnchorCommonPiecewiseTargets_of_separatedGlobal h)

end PreferredGlobalPiecesExistential


section PreferredGlobalPiecesTopLevel

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}

/-- Stable top-level theorem from preferred piecewise targets with separated
global assumptions. -/
theorem trimmed_paper_preferred_anchor_common_separated_global_targets_main_theorem
    (h :
      ExistsPaperPreferredAnchorCommonPiecewiseSeparatedGlobalTargets
        G obs) :
    PaperConstructiveIdentificationConclusion G obs :=
  paperPreferredAnchorCommonSeparatedGlobalTargets_main_theorem h

/-- Stable top-level conclusion-package theorem from preferred piecewise targets
with separated global assumptions. -/
theorem trimmed_paper_preferred_anchor_common_separated_global_targets_conclusion_package
    (h :
      ExistsPaperPreferredAnchorCommonPiecewiseSeparatedGlobalTargets
        G obs) :
    PaperConstructiveLearningConclusionPackage G obs :=
  paperPreferredAnchorCommonSeparatedGlobalTargets_conclusion_package h

/-- Stable bridge from separated-global piecewise targets to the previous
piecewise target interface. -/
theorem trimmed_paper_preferred_anchor_common_piecewise_targets_of_separated_global
    (h :
      ExistsPaperPreferredAnchorCommonPiecewiseSeparatedGlobalTargets
        G obs) :
    ExistsPaperPreferredAnchorCommonPiecewiseTargets G obs :=
  existsPaperPreferredAnchorCommonPiecewiseTargets_of_separatedGlobal h

end PreferredGlobalPiecesTopLevel

end MCFG
