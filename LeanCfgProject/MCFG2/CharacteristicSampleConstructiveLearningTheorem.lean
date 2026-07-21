/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG.CharacteristicSampleFinalConstructionFacade

/-!
# CharacteristicSampleConstructiveLearningTheorem.lean

One-hundred-thirteenth clean Lean experiment for the fixed-observation MCFG
project.

`CharacteristicSampleFinalConstructionFacade.lean` introduced the stable final
construction facade

```lean
TrimmedPresentationConstructiveMainAssumptions
```

and the main theorem

```lean
trimmed_constructive_main_theorem
```

This file adds a final theorem-summary layer.  The main new statement packages
the three theorem-facing consequences together:

```text
finite positive characteristic sample
+
eventual prefix exactness
+
Gold-style identification.
```

It also adds convenient `Nonempty` versions of the final facade theorems.

No new mathematical principle is introduced here.

No theorem here uses `sorry`.
-/

namespace MCFG

universe u v w

section ConstructiveLearningSummary

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}

/-- A short facade name for the final constructive route hypothesis. -/
def ExistsConstructiveFlatRoute
    (G : WorkingMCFG N α) (obs : α → M) : Prop :=
  ExistsFlatConstructionRouteDisjunction G obs

/-- A short facade name for the final constructive learnability conclusion. -/
def ExistsConstructiveBoundedIdentification
    (G : WorkingMCFG N α) (obs : α → M) : Prop :=
  ExistsBoundedReachableIdentification G obs

/-- The three theorem-facing consequences of the constructive facade. -/
def ConstructiveLearningConsequences
    (G : WorkingMCFG N α) (obs : α → M) : Prop :=
  ExistsBoundedPositiveCharacteristicSample G obs ∧
  ExistsBoundedPrefixExactIdentification G obs ∧
  ExistsBoundedReachableIdentification G obs

/-- Constructive assumptions imply all three theorem-facing consequences. -/
theorem constructiveLearningConsequences_of_assumptions
    (A :
      TrimmedPresentationConstructiveMainAssumptions
        (G := G) (obs := obs)) :
    ConstructiveLearningConsequences G obs :=
  ⟨trimmed_constructive_characteristic_sample_theorem A,
    trimmed_constructive_prefix_exact_theorem A,
    trimmed_constructive_main_theorem A⟩

/-- A route disjunction implies all three theorem-facing consequences. -/
theorem constructiveLearningConsequences_of_route_disjunction
    (h : ExistsFlatConstructionRouteDisjunction G obs) :
    ConstructiveLearningConsequences G obs :=
  constructiveLearningConsequences_of_assumptions
    ({ route := h } :
      TrimmedPresentationConstructiveMainAssumptions
        (G := G) (obs := obs))

/-- The short route facade implies all three theorem-facing consequences. -/
theorem constructiveLearningConsequences_of_constructive_flat_route
    (h : ExistsConstructiveFlatRoute G obs) :
    ConstructiveLearningConsequences G obs :=
  constructiveLearningConsequences_of_route_disjunction h

/-- The any-flat facade implies all three theorem-facing consequences. -/
theorem constructiveLearningConsequences_of_any_flat
    (h : ExistsAnyFlatConstruction G obs) :
    ConstructiveLearningConsequences G obs :=
  constructiveLearningConsequences_of_assumptions
    (constructiveMainAssumptions_of_anyFlat h)

/-- Flat exposing construction implies all three theorem-facing consequences. -/
theorem constructiveLearningConsequences_of_flat_exposing
    (h : ExistsFlatExposingConstruction G obs) :
    ConstructiveLearningConsequences G obs :=
  constructiveLearningConsequences_of_assumptions
    (constructiveMainAssumptions_of_flatExposing h)

/-- Flat anchor-common construction implies all three theorem-facing
consequences. -/
theorem constructiveLearningConsequences_of_flat_anchor_common
    (h : ExistsFlatAnchorCommonConstruction G obs) :
    ConstructiveLearningConsequences G obs :=
  constructiveLearningConsequences_of_assumptions
    (constructiveMainAssumptions_of_flatAnchorCommon h)

/-- Flat same-context construction implies all three theorem-facing
consequences. -/
theorem constructiveLearningConsequences_of_flat_same_context
    (h : ExistsFlatSameContextConstruction G obs) :
    ConstructiveLearningConsequences G obs :=
  constructiveLearningConsequences_of_assumptions
    (constructiveMainAssumptions_of_flatSameContext h)

/-- Nonempty final constructive assumptions give the main theorem. -/
theorem constructiveMainAssumptions_main_theorem_of_nonempty
    (h :
      Nonempty
        (TrimmedPresentationConstructiveMainAssumptions
          (G := G) (obs := obs))) :
    ExistsBoundedReachableIdentification G obs :=
  match h with
  | ⟨A⟩ => trimmed_constructive_main_theorem A

/-- Nonempty final constructive assumptions give a positive characteristic
sample theorem. -/
theorem constructiveMainAssumptions_characteristic_sample_of_nonempty
    (h :
      Nonempty
        (TrimmedPresentationConstructiveMainAssumptions
          (G := G) (obs := obs))) :
    ExistsBoundedPositiveCharacteristicSample G obs :=
  match h with
  | ⟨A⟩ => trimmed_constructive_characteristic_sample_theorem A

/-- Nonempty final constructive assumptions give a prefix-exact theorem. -/
theorem constructiveMainAssumptions_prefix_exact_of_nonempty
    (h :
      Nonempty
        (TrimmedPresentationConstructiveMainAssumptions
          (G := G) (obs := obs))) :
    ExistsBoundedPrefixExactIdentification G obs :=
  match h with
  | ⟨A⟩ => trimmed_constructive_prefix_exact_theorem A

/-- Nonempty final constructive assumptions give all three theorem-facing
consequences. -/
theorem constructiveLearningConsequences_of_nonempty_assumptions
    (h :
      Nonempty
        (TrimmedPresentationConstructiveMainAssumptions
          (G := G) (obs := obs))) :
    ConstructiveLearningConsequences G obs :=
  match h with
  | ⟨A⟩ => constructiveLearningConsequences_of_assumptions A

/-- The final constructive route facade gives the short constructive
identification conclusion. -/
theorem constructiveBoundedIdentification_of_constructive_flat_route
    (h : ExistsConstructiveFlatRoute G obs) :
    ExistsConstructiveBoundedIdentification G obs :=
  trimmed_constructive_main_theorem_of_route_disjunction h

/-- Final constructive assumptions give the short constructive identification
conclusion. -/
theorem constructiveBoundedIdentification_of_assumptions
    (A :
      TrimmedPresentationConstructiveMainAssumptions
        (G := G) (obs := obs)) :
    ExistsConstructiveBoundedIdentification G obs :=
  trimmed_constructive_main_theorem A

end ConstructiveLearningSummary


section ConstructiveLearningTopLevelTheorems

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}

/-- Final summary theorem: constructive assumptions give characteristic sample,
prefix exactness, and Gold-style identification. -/
theorem trimmed_constructive_learning_consequences
    (A :
      TrimmedPresentationConstructiveMainAssumptions
        (G := G) (obs := obs)) :
    ConstructiveLearningConsequences G obs :=
  constructiveLearningConsequences_of_assumptions A

/-- Final summary theorem from the route disjunction. -/
theorem trimmed_constructive_learning_consequences_of_route_disjunction
    (h : ExistsFlatConstructionRouteDisjunction G obs) :
    ConstructiveLearningConsequences G obs :=
  constructiveLearningConsequences_of_route_disjunction h

/-- Final summary theorem from the short constructive route facade. -/
theorem trimmed_constructive_learning_consequences_of_constructive_flat_route
    (h : ExistsConstructiveFlatRoute G obs) :
    ConstructiveLearningConsequences G obs :=
  constructiveLearningConsequences_of_constructive_flat_route h

/-- Final summary theorem from the any-flat facade. -/
theorem trimmed_constructive_learning_consequences_of_any_flat
    (h : ExistsAnyFlatConstruction G obs) :
    ConstructiveLearningConsequences G obs :=
  constructiveLearningConsequences_of_any_flat h

/-- Final nonempty-facade main theorem. -/
theorem trimmed_constructive_main_theorem_of_nonempty_assumptions
    (h :
      Nonempty
        (TrimmedPresentationConstructiveMainAssumptions
          (G := G) (obs := obs))) :
    ExistsBoundedReachableIdentification G obs :=
  constructiveMainAssumptions_main_theorem_of_nonempty h

/-- Final nonempty-facade summary theorem. -/
theorem trimmed_constructive_learning_consequences_of_nonempty_assumptions
    (h :
      Nonempty
        (TrimmedPresentationConstructiveMainAssumptions
          (G := G) (obs := obs))) :
    ConstructiveLearningConsequences G obs :=
  constructiveLearningConsequences_of_nonempty_assumptions h

/-- Final theorem using the short conclusion name. -/
theorem trimmed_constructive_bounded_identification
    (A :
      TrimmedPresentationConstructiveMainAssumptions
        (G := G) (obs := obs)) :
    ExistsConstructiveBoundedIdentification G obs :=
  constructiveBoundedIdentification_of_assumptions A

/-- Final theorem using the short route and conclusion names. -/
theorem trimmed_constructive_bounded_identification_of_route
    (h : ExistsConstructiveFlatRoute G obs) :
    ExistsConstructiveBoundedIdentification G obs :=
  constructiveBoundedIdentification_of_constructive_flat_route h

end ConstructiveLearningTopLevelTheorems

end MCFG
