/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG2.CharacteristicSampleConstructiveLearnabilityFacade

/-!
# CharacteristicSamplePaperConstructiveStatement.lean

One-hundred-fifteenth clean Lean experiment for the fixed-observation MCFG
project.

`CharacteristicSampleConstructiveLearnabilityFacade.lean` introduced short
constructive-learnability names such as

```lean
ConstructivelyLearnableByFlatRoutes
ConstructivelyIdentifiedByReachableLearner
```

This file adds an even thinner paper-facing statement layer.  The names here
are intentionally stable and descriptive, so that the paper/README/blueprint can
refer to them without exposing the internal construction hierarchy.

The key theorem is:

```lean
paper_constructive_learnability_main_theorem
```

No new mathematical principle is introduced here.

No theorem here uses `sorry`.
-/

namespace MCFG

universe u v w

section PaperConstructiveStatement

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}

/-- Paper-facing name for the constructive route hypothesis. -/
def PaperConstructiveRouteAssumption
    (G : WorkingMCFG N α) (obs : α → M) : Prop :=
  ConstructivelyLearnableByFlatRoutes G obs

/-- Paper-facing name for the constructive characteristic-sample conclusion. -/
def PaperConstructiveCharacteristicSampleConclusion
    (G : WorkingMCFG N α) (obs : α → M) : Prop :=
  ConstructiveCharacteristicSampleAvailable G obs

/-- Paper-facing name for the constructive prefix-exact conclusion. -/
def PaperConstructivePrefixExactConclusion
    (G : WorkingMCFG N α) (obs : α → M) : Prop :=
  ConstructivePrefixExactIdentificationAvailable G obs

/-- Paper-facing name for the constructive identification conclusion. -/
def PaperConstructiveIdentificationConclusion
    (G : WorkingMCFG N α) (obs : α → M) : Prop :=
  ConstructivelyIdentifiedByReachableLearner G obs

/-- Paper-facing name for the full constructive conclusion package. -/
def PaperConstructiveLearningConclusionPackage
    (G : WorkingMCFG N α) (obs : α → M) : Prop :=
  PaperConstructiveCharacteristicSampleConclusion G obs ∧
  PaperConstructivePrefixExactConclusion G obs ∧
  PaperConstructiveIdentificationConclusion G obs

/-- Convert the paper-facing hypothesis to the previous constructive facade. -/
theorem constructiveLearnable_of_paperConstructiveRoute
    (h : PaperConstructiveRouteAssumption G obs) :
    ConstructivelyLearnableByFlatRoutes G obs :=
  h

/-- Convert the previous constructive facade to the paper-facing hypothesis. -/
theorem paperConstructiveRoute_of_constructiveLearnable
    (h : ConstructivelyLearnableByFlatRoutes G obs) :
    PaperConstructiveRouteAssumption G obs :=
  h

/-- The paper-facing conclusion package is equivalent to the short summary
facade. -/
theorem paperConstructiveConclusionPackage_iff_summary :
    PaperConstructiveLearningConclusionPackage G obs ↔
      ConstructiveLearnabilitySummary G obs where
  mp := by
    intro h
    exact h
  mpr := by
    intro h
    exact h

/-- Paper-facing characteristic-sample theorem. -/
theorem paper_constructive_characteristic_sample_theorem
    (h : PaperConstructiveRouteAssumption G obs) :
    PaperConstructiveCharacteristicSampleConclusion G obs :=
  trimmed_constructively_learnable_characteristic_sample h

/-- Paper-facing prefix-exact theorem. -/
theorem paper_constructive_prefix_exact_theorem
    (h : PaperConstructiveRouteAssumption G obs) :
    PaperConstructivePrefixExactConclusion G obs :=
  trimmed_constructively_learnable_prefix_exact h

/-- Paper-facing main identification theorem. -/
theorem paper_constructive_learnability_main_theorem
    (h : PaperConstructiveRouteAssumption G obs) :
    PaperConstructiveIdentificationConclusion G obs :=
  trimmed_constructively_learnable_identified h

/-- Paper-facing theorem packaging all constructive conclusions. -/
theorem paper_constructive_learning_conclusion_package
    (h : PaperConstructiveRouteAssumption G obs) :
    PaperConstructiveLearningConclusionPackage G obs :=
  trimmed_constructively_learnable_summary h

/-- Direct paper-facing theorem from the final constructive assumptions. -/
theorem paper_constructive_learnability_main_theorem_of_assumptions
    (A :
      TrimmedPresentationConstructiveMainAssumptions
        (G := G) (obs := obs)) :
    PaperConstructiveIdentificationConclusion G obs :=
  trimmed_constructive_assumptions_identified A

/-- Direct paper-facing theorem from the route disjunction. -/
theorem paper_constructive_learnability_main_theorem_of_route_disjunction
    (h : ExistsFlatConstructionRouteDisjunction G obs) :
    PaperConstructiveIdentificationConclusion G obs :=
  trimmed_route_disjunction_identified h

/-- Direct paper-facing theorem from the any-flat facade. -/
theorem paper_constructive_learnability_main_theorem_of_any_flat
    (h : ExistsAnyFlatConstruction G obs) :
    PaperConstructiveIdentificationConclusion G obs :=
  trimmed_any_flat_identified h

end PaperConstructiveStatement


section PaperConstructiveTopLevelTheorems

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}

/-- Stable top-level paper theorem.

If the target admits one of the verified flat constructive routes, then it is
identified by the reachable learner for some finite fanout bound. -/
theorem trimmed_paper_constructive_main_theorem
    (h : PaperConstructiveRouteAssumption G obs) :
    PaperConstructiveIdentificationConclusion G obs :=
  paper_constructive_learnability_main_theorem h

/-- Stable top-level paper theorem packaging the characteristic-sample,
prefix-exact, and identification conclusions. -/
theorem trimmed_paper_constructive_conclusion_package
    (h : PaperConstructiveRouteAssumption G obs) :
    PaperConstructiveLearningConclusionPackage G obs :=
  paper_constructive_learning_conclusion_package h

/-- Stable top-level paper characteristic-sample theorem. -/
theorem trimmed_paper_constructive_characteristic_sample_theorem
    (h : PaperConstructiveRouteAssumption G obs) :
    PaperConstructiveCharacteristicSampleConclusion G obs :=
  paper_constructive_characteristic_sample_theorem h

/-- Stable top-level paper prefix-exact theorem. -/
theorem trimmed_paper_constructive_prefix_exact_theorem
    (h : PaperConstructiveRouteAssumption G obs) :
    PaperConstructivePrefixExactConclusion G obs :=
  paper_constructive_prefix_exact_theorem h

/-- Stable top-level paper theorem from the final constructive assumptions. -/
theorem trimmed_paper_constructive_main_theorem_of_assumptions
    (A :
      TrimmedPresentationConstructiveMainAssumptions
        (G := G) (obs := obs)) :
    PaperConstructiveIdentificationConclusion G obs :=
  paper_constructive_learnability_main_theorem_of_assumptions A

/-- Stable top-level paper theorem from the route disjunction. -/
theorem trimmed_paper_constructive_main_theorem_of_route_disjunction
    (h : ExistsFlatConstructionRouteDisjunction G obs) :
    PaperConstructiveIdentificationConclusion G obs :=
  paper_constructive_learnability_main_theorem_of_route_disjunction h

/-- Stable top-level paper theorem from the any-flat facade. -/
theorem trimmed_paper_constructive_main_theorem_of_any_flat
    (h : ExistsAnyFlatConstruction G obs) :
    PaperConstructiveIdentificationConclusion G obs :=
  paper_constructive_learnability_main_theorem_of_any_flat h

end PaperConstructiveTopLevelTheorems

end MCFG
