/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG2.CharacteristicSamplePaperConstructiveStatement

/-!
# CharacteristicSamplePaperConstructiveRouteCorollaries.lean

One-hundred-sixteenth clean Lean experiment for the fixed-observation MCFG
project.

`CharacteristicSamplePaperConstructiveStatement.lean` introduced the stable
paper-facing theorem

```lean
trimmed_paper_constructive_main_theorem
```

from the abstract paper route assumption

```lean
PaperConstructiveRouteAssumption G obs.
```

This file adds route-specific corollaries, especially for the preferred
anchor-common route.  The point is to make the next construction phase have a
very explicit target:

```lean
ExistsFlatAnchorCommonConstruction G obs
```

Once that preferred flat route is constructed, the paper-facing identification
conclusion follows immediately.

No new mathematical principle is introduced here.

No theorem here uses `sorry`.
-/

namespace MCFG

universe u v w

section PaperConstructiveRouteCorollaries

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}

/-- Paper-facing name for the direct exposing flat route. -/
def PaperExposingConstructiveRouteAssumption
    (G : WorkingMCFG N α) (obs : α → M) : Prop :=
  ExistsFlatExposingConstruction G obs

/-- Paper-facing name for the preferred anchor-common flat route. -/
def PaperAnchorCommonConstructiveRouteAssumption
    (G : WorkingMCFG N α) (obs : α → M) : Prop :=
  ExistsFlatAnchorCommonConstruction G obs

/-- Paper-facing name for the stronger same-context flat route. -/
def PaperSameContextConstructiveRouteAssumption
    (G : WorkingMCFG N α) (obs : α → M) : Prop :=
  ExistsFlatSameContextConstruction G obs

/-- Alias emphasizing that the anchor-common route is the preferred construction
route for the paper. -/
def PaperPreferredConstructiveRouteAssumption
    (G : WorkingMCFG N α) (obs : α → M) : Prop :=
  PaperAnchorCommonConstructiveRouteAssumption G obs

/-- Direct exposing route gives the general paper constructive route. -/
theorem paperConstructiveRouteAssumption_of_exposing
    (h : PaperExposingConstructiveRouteAssumption G obs) :
    PaperConstructiveRouteAssumption G obs :=
  Or.inl h

/-- Preferred anchor-common route gives the general paper constructive route. -/
theorem paperConstructiveRouteAssumption_of_anchorCommon
    (h : PaperAnchorCommonConstructiveRouteAssumption G obs) :
    PaperConstructiveRouteAssumption G obs :=
  Or.inr (Or.inl h)

/-- Strong same-context route gives the general paper constructive route. -/
theorem paperConstructiveRouteAssumption_of_sameContext
    (h : PaperSameContextConstructiveRouteAssumption G obs) :
    PaperConstructiveRouteAssumption G obs :=
  Or.inr (Or.inr h)

/-- Preferred route gives the general paper constructive route. -/
theorem paperConstructiveRouteAssumption_of_preferred
    (h : PaperPreferredConstructiveRouteAssumption G obs) :
    PaperConstructiveRouteAssumption G obs :=
  paperConstructiveRouteAssumption_of_anchorCommon h

/-- Direct exposing route gives the paper-facing characteristic-sample
conclusion. -/
theorem paper_exposing_constructive_characteristic_sample_theorem
    (h : PaperExposingConstructiveRouteAssumption G obs) :
    PaperConstructiveCharacteristicSampleConclusion G obs :=
  trimmed_paper_constructive_characteristic_sample_theorem
    (paperConstructiveRouteAssumption_of_exposing h)

/-- Preferred anchor-common route gives the paper-facing characteristic-sample
conclusion. -/
theorem paper_anchor_common_constructive_characteristic_sample_theorem
    (h : PaperAnchorCommonConstructiveRouteAssumption G obs) :
    PaperConstructiveCharacteristicSampleConclusion G obs :=
  trimmed_paper_constructive_characteristic_sample_theorem
    (paperConstructiveRouteAssumption_of_anchorCommon h)

/-- Strong same-context route gives the paper-facing characteristic-sample
conclusion. -/
theorem paper_same_context_constructive_characteristic_sample_theorem
    (h : PaperSameContextConstructiveRouteAssumption G obs) :
    PaperConstructiveCharacteristicSampleConclusion G obs :=
  trimmed_paper_constructive_characteristic_sample_theorem
    (paperConstructiveRouteAssumption_of_sameContext h)

/-- Direct exposing route gives the paper-facing prefix-exact conclusion. -/
theorem paper_exposing_constructive_prefix_exact_theorem
    (h : PaperExposingConstructiveRouteAssumption G obs) :
    PaperConstructivePrefixExactConclusion G obs :=
  trimmed_paper_constructive_prefix_exact_theorem
    (paperConstructiveRouteAssumption_of_exposing h)

/-- Preferred anchor-common route gives the paper-facing prefix-exact conclusion. -/
theorem paper_anchor_common_constructive_prefix_exact_theorem
    (h : PaperAnchorCommonConstructiveRouteAssumption G obs) :
    PaperConstructivePrefixExactConclusion G obs :=
  trimmed_paper_constructive_prefix_exact_theorem
    (paperConstructiveRouteAssumption_of_anchorCommon h)

/-- Strong same-context route gives the paper-facing prefix-exact conclusion. -/
theorem paper_same_context_constructive_prefix_exact_theorem
    (h : PaperSameContextConstructiveRouteAssumption G obs) :
    PaperConstructivePrefixExactConclusion G obs :=
  trimmed_paper_constructive_prefix_exact_theorem
    (paperConstructiveRouteAssumption_of_sameContext h)

/-- Direct exposing route gives the paper-facing main identification conclusion. -/
theorem paper_exposing_constructive_main_theorem
    (h : PaperExposingConstructiveRouteAssumption G obs) :
    PaperConstructiveIdentificationConclusion G obs :=
  trimmed_paper_constructive_main_theorem
    (paperConstructiveRouteAssumption_of_exposing h)

/-- Preferred anchor-common route gives the paper-facing main identification
conclusion. -/
theorem paper_anchor_common_constructive_main_theorem
    (h : PaperAnchorCommonConstructiveRouteAssumption G obs) :
    PaperConstructiveIdentificationConclusion G obs :=
  trimmed_paper_constructive_main_theorem
    (paperConstructiveRouteAssumption_of_anchorCommon h)

/-- Strong same-context route gives the paper-facing main identification
conclusion. -/
theorem paper_same_context_constructive_main_theorem
    (h : PaperSameContextConstructiveRouteAssumption G obs) :
    PaperConstructiveIdentificationConclusion G obs :=
  trimmed_paper_constructive_main_theorem
    (paperConstructiveRouteAssumption_of_sameContext h)

/-- Preferred anchor-common route gives the paper-facing main identification
conclusion. -/
theorem paper_preferred_constructive_main_theorem
    (h : PaperPreferredConstructiveRouteAssumption G obs) :
    PaperConstructiveIdentificationConclusion G obs :=
  paper_anchor_common_constructive_main_theorem h

/-- Direct exposing route gives the full paper-facing conclusion package. -/
theorem paper_exposing_constructive_conclusion_package
    (h : PaperExposingConstructiveRouteAssumption G obs) :
    PaperConstructiveLearningConclusionPackage G obs :=
  trimmed_paper_constructive_conclusion_package
    (paperConstructiveRouteAssumption_of_exposing h)

/-- Preferred anchor-common route gives the full paper-facing conclusion
package. -/
theorem paper_anchor_common_constructive_conclusion_package
    (h : PaperAnchorCommonConstructiveRouteAssumption G obs) :
    PaperConstructiveLearningConclusionPackage G obs :=
  trimmed_paper_constructive_conclusion_package
    (paperConstructiveRouteAssumption_of_anchorCommon h)

/-- Strong same-context route gives the full paper-facing conclusion package. -/
theorem paper_same_context_constructive_conclusion_package
    (h : PaperSameContextConstructiveRouteAssumption G obs) :
    PaperConstructiveLearningConclusionPackage G obs :=
  trimmed_paper_constructive_conclusion_package
    (paperConstructiveRouteAssumption_of_sameContext h)

/-- Preferred anchor-common route gives the full paper-facing conclusion
package. -/
theorem paper_preferred_constructive_conclusion_package
    (h : PaperPreferredConstructiveRouteAssumption G obs) :
    PaperConstructiveLearningConclusionPackage G obs :=
  paper_anchor_common_constructive_conclusion_package h

end PaperConstructiveRouteCorollaries


section PaperConstructiveRouteCorollariesTopLevel

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}

/-- Stable top-level theorem for the preferred anchor-common constructive route.

This is the next main construction target: prove
`ExistsFlatAnchorCommonConstruction G obs`, then this theorem immediately gives
the paper-facing identification conclusion. -/
theorem trimmed_paper_preferred_constructive_main_theorem
    (h : PaperPreferredConstructiveRouteAssumption G obs) :
    PaperConstructiveIdentificationConclusion G obs :=
  paper_preferred_constructive_main_theorem h

/-- Stable top-level theorem for the preferred anchor-common route, stated
without the alias. -/
theorem trimmed_paper_anchor_common_constructive_main_theorem
    (h : PaperAnchorCommonConstructiveRouteAssumption G obs) :
    PaperConstructiveIdentificationConclusion G obs :=
  paper_anchor_common_constructive_main_theorem h

/-- Stable top-level theorem for the direct exposing route. -/
theorem trimmed_paper_exposing_constructive_main_theorem
    (h : PaperExposingConstructiveRouteAssumption G obs) :
    PaperConstructiveIdentificationConclusion G obs :=
  paper_exposing_constructive_main_theorem h

/-- Stable top-level theorem for the stronger same-context route. -/
theorem trimmed_paper_same_context_constructive_main_theorem
    (h : PaperSameContextConstructiveRouteAssumption G obs) :
    PaperConstructiveIdentificationConclusion G obs :=
  paper_same_context_constructive_main_theorem h

/-- Stable top-level conclusion-package theorem for the preferred anchor-common
route. -/
theorem trimmed_paper_preferred_constructive_conclusion_package
    (h : PaperPreferredConstructiveRouteAssumption G obs) :
    PaperConstructiveLearningConclusionPackage G obs :=
  paper_preferred_constructive_conclusion_package h

/-- Stable top-level conclusion-package theorem for the preferred anchor-common
route, stated without the alias. -/
theorem trimmed_paper_anchor_common_constructive_conclusion_package
    (h : PaperAnchorCommonConstructiveRouteAssumption G obs) :
    PaperConstructiveLearningConclusionPackage G obs :=
  paper_anchor_common_constructive_conclusion_package h

end PaperConstructiveRouteCorollariesTopLevel

end MCFG
