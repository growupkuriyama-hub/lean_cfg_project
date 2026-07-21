/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG.CharacteristicSamplePaperConstructiveRouteCorollaries

/-!
# CharacteristicSamplePreferredAnchorCommonConstruction.lean

One-hundred-seventeenth clean Lean experiment for the fixed-observation MCFG
project.

`CharacteristicSamplePaperConstructiveRouteCorollaries.lean` made the preferred
paper route explicit:

```lean
PaperPreferredConstructiveRouteAssumption G obs
```

which is just the anchor-common flat route:

```lean
ExistsFlatAnchorCommonConstruction G obs.
```

This file introduces a stable paper-facing data record for that preferred route:

```lean
PaperPreferredAnchorCommonConstructionData
```

It is intentionally definitionally close to
`TrimmedPresentationFlatAnchorCommonConstructionData`, but its name says what
the next construction phase is trying to build.

No new mathematical principle is introduced here.

No theorem here uses `sorry`.
-/

namespace MCFG

universe u v w

section PreferredAnchorCommonConstruction

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}

/-- Paper-facing data record for the preferred anchor-common constructive route.

Constructing this record is now the preferred concrete route toward the paper
constructive theorem. -/
structure PaperPreferredAnchorCommonConstructionData where
  fanoutBound : Nat
  presentation : TrimmedOutputTypePresentation G obs
  data : TrimmedPresentationPreCoreData presentation fanoutBound
  builder : TrimmedPresentationGrammarRuleBuilder data
  splicingConstructor : NamedContextSplicingConstructor α
  fanout : G.FanoutAtMost fanoutBound
  promise : FixedNamedTupleSubstitutable fanoutBound obs G.StringLanguage
  commonTransport : TrimmedPresentationAnchorCommonContextTransport data

namespace PaperPreferredAnchorCommonConstructionData

/-- Convert the paper-facing preferred data record to the flat anchor-common
construction record. -/
def toFlatAnchorCommonConstructionData
    (C : PaperPreferredAnchorCommonConstructionData
      (G := G) (obs := obs)) :
    TrimmedPresentationFlatAnchorCommonConstructionData
      (G := G) (obs := obs) where
  fanoutBound := C.fanoutBound
  presentation := C.presentation
  data := C.data
  builder := C.builder
  splicingConstructor := C.splicingConstructor
  fanout := C.fanout
  promise := C.promise
  commonTransport := C.commonTransport

/-- Convert the paper-facing preferred data record to the flat anchor-common
existence hypothesis. -/
theorem existsFlatAnchorCommonConstruction
    (C : PaperPreferredAnchorCommonConstructionData
      (G := G) (obs := obs)) :
    ExistsFlatAnchorCommonConstruction G obs :=
  ⟨C.toFlatAnchorCommonConstructionData⟩

/-- Convert the paper-facing preferred data record to the preferred route
assumption. -/
theorem preferredRouteAssumption
    (C : PaperPreferredAnchorCommonConstructionData
      (G := G) (obs := obs)) :
    PaperPreferredConstructiveRouteAssumption G obs :=
  C.existsFlatAnchorCommonConstruction

/-- Convert the paper-facing preferred data record to the general paper route
assumption. -/
theorem paperRouteAssumption
    (C : PaperPreferredAnchorCommonConstructionData
      (G := G) (obs := obs)) :
    PaperConstructiveRouteAssumption G obs :=
  paperConstructiveRouteAssumption_of_preferred
    C.preferredRouteAssumption

/-- The preferred data record gives the paper-facing characteristic-sample
conclusion. -/
theorem characteristic_sample
    (C : PaperPreferredAnchorCommonConstructionData
      (G := G) (obs := obs)) :
    PaperConstructiveCharacteristicSampleConclusion G obs :=
  paper_anchor_common_constructive_characteristic_sample_theorem
    C.existsFlatAnchorCommonConstruction

/-- The preferred data record gives the paper-facing prefix-exact conclusion. -/
theorem prefix_exact
    (C : PaperPreferredAnchorCommonConstructionData
      (G := G) (obs := obs)) :
    PaperConstructivePrefixExactConclusion G obs :=
  paper_anchor_common_constructive_prefix_exact_theorem
    C.existsFlatAnchorCommonConstruction

/-- The preferred data record gives the paper-facing main identification
conclusion. -/
theorem main_theorem
    (C : PaperPreferredAnchorCommonConstructionData
      (G := G) (obs := obs)) :
    PaperConstructiveIdentificationConclusion G obs :=
  paper_preferred_constructive_main_theorem
    C.preferredRouteAssumption

/-- The preferred data record gives the full paper-facing conclusion package. -/
theorem conclusion_package
    (C : PaperPreferredAnchorCommonConstructionData
      (G := G) (obs := obs)) :
    PaperConstructiveLearningConclusionPackage G obs :=
  paper_preferred_constructive_conclusion_package
    C.preferredRouteAssumption

/-- The preferred data record also gives the older bounded reachable
identification conclusion directly. -/
theorem exists_bounded_reachable_identification
    (C : PaperPreferredAnchorCommonConstructionData
      (G := G) (obs := obs)) :
    ExistsBoundedReachableIdentification G obs :=
  C.toFlatAnchorCommonConstructionData
    .exists_bounded_reachable_identification

end PaperPreferredAnchorCommonConstructionData

end PreferredAnchorCommonConstruction


section PreferredAnchorCommonExistential

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}

/-- Existence of the paper-facing preferred anchor-common construction data. -/
def ExistsPaperPreferredAnchorCommonConstruction
    (G : WorkingMCFG N α) (obs : α → M) : Prop :=
  Nonempty
    (PaperPreferredAnchorCommonConstructionData
      (G := G) (obs := obs))

/-- Preferred paper-facing construction data gives flat anchor-common
construction. -/
theorem existsFlatAnchorCommonConstruction_of_paperPreferred
    (h : ExistsPaperPreferredAnchorCommonConstruction G obs) :
    ExistsFlatAnchorCommonConstruction G obs :=
  match h with
  | ⟨C⟩ => C.existsFlatAnchorCommonConstruction

/-- Preferred paper-facing construction data gives the preferred route
assumption. -/
theorem paperPreferredRouteAssumption_of_paperPreferred
    (h : ExistsPaperPreferredAnchorCommonConstruction G obs) :
    PaperPreferredConstructiveRouteAssumption G obs :=
  existsFlatAnchorCommonConstruction_of_paperPreferred h

/-- Preferred paper-facing construction data gives the general paper route
assumption. -/
theorem paperConstructiveRouteAssumption_of_paperPreferred
    (h : ExistsPaperPreferredAnchorCommonConstruction G obs) :
    PaperConstructiveRouteAssumption G obs :=
  paperConstructiveRouteAssumption_of_preferred
    (paperPreferredRouteAssumption_of_paperPreferred h)

/-- Main theorem from existence of preferred paper-facing construction data. -/
theorem paperPreferredAnchorCommonConstruction_main_theorem
    (h : ExistsPaperPreferredAnchorCommonConstruction G obs) :
    PaperConstructiveIdentificationConclusion G obs :=
  trimmed_paper_preferred_constructive_main_theorem
    (paperPreferredRouteAssumption_of_paperPreferred h)

/-- Conclusion package from existence of preferred paper-facing construction
data. -/
theorem paperPreferredAnchorCommonConstruction_conclusion_package
    (h : ExistsPaperPreferredAnchorCommonConstruction G obs) :
    PaperConstructiveLearningConclusionPackage G obs :=
  trimmed_paper_preferred_constructive_conclusion_package
    (paperPreferredRouteAssumption_of_paperPreferred h)

/-- Characteristic-sample conclusion from existence of preferred paper-facing
construction data. -/
theorem paperPreferredAnchorCommonConstruction_characteristic_sample
    (h : ExistsPaperPreferredAnchorCommonConstruction G obs) :
    PaperConstructiveCharacteristicSampleConclusion G obs :=
  match h with
  | ⟨C⟩ => C.characteristic_sample

/-- Prefix-exact conclusion from existence of preferred paper-facing construction
data. -/
theorem paperPreferredAnchorCommonConstruction_prefix_exact
    (h : ExistsPaperPreferredAnchorCommonConstruction G obs) :
    PaperConstructivePrefixExactConclusion G obs :=
  match h with
  | ⟨C⟩ => C.prefix_exact

end PreferredAnchorCommonExistential


section PreferredAnchorCommonTopLevelTheorems

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}

/-- Stable top-level theorem for the preferred paper-facing anchor-common
construction data. -/
theorem trimmed_paper_preferred_anchor_common_construction_main_theorem
    (h : ExistsPaperPreferredAnchorCommonConstruction G obs) :
    PaperConstructiveIdentificationConclusion G obs :=
  paperPreferredAnchorCommonConstruction_main_theorem h

/-- Stable top-level conclusion-package theorem for the preferred paper-facing
anchor-common construction data. -/
theorem trimmed_paper_preferred_anchor_common_construction_conclusion_package
    (h : ExistsPaperPreferredAnchorCommonConstruction G obs) :
    PaperConstructiveLearningConclusionPackage G obs :=
  paperPreferredAnchorCommonConstruction_conclusion_package h

/-- Stable top-level characteristic-sample theorem for the preferred
paper-facing anchor-common construction data. -/
theorem trimmed_paper_preferred_anchor_common_construction_characteristic_sample
    (h : ExistsPaperPreferredAnchorCommonConstruction G obs) :
    PaperConstructiveCharacteristicSampleConclusion G obs :=
  paperPreferredAnchorCommonConstruction_characteristic_sample h

/-- Stable top-level prefix-exact theorem for the preferred paper-facing
anchor-common construction data. -/
theorem trimmed_paper_preferred_anchor_common_construction_prefix_exact
    (h : ExistsPaperPreferredAnchorCommonConstruction G obs) :
    PaperConstructivePrefixExactConclusion G obs :=
  paperPreferredAnchorCommonConstruction_prefix_exact h

end PreferredAnchorCommonTopLevelTheorems

end MCFG
