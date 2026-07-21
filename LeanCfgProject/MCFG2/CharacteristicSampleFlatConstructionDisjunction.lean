/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG2.CharacteristicSampleFlatConstructionChoice

/-!
# CharacteristicSampleFlatConstructionDisjunction.lean

One-hundred-eleventh clean Lean experiment for the fixed-observation MCFG
project.

`CharacteristicSampleFlatConstructionChoice.lean` packaged the three flat
construction routes into an inductive choice type.

For theorem statements in the paper, however, a disjunction is sometimes more
readable:

```text
flat exposing construction
∨ flat anchor-common construction
∨ flat same-context construction.
```

This file introduces that disjunctive facade and proves that it is equivalent
to the flat-choice facade for the purposes of the main theorem.

No new mathematical principle is introduced here.

No theorem here uses `sorry`.
-/

namespace MCFG

universe u v w

section FlatConstructionDisjunction

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}

/-- A paper-readable disjunction of the three flat construction routes. -/
def ExistsFlatConstructionRouteDisjunction
    (G : WorkingMCFG N α) (obs : α → M) : Prop :=
  ExistsFlatExposingConstruction G obs ∨
  ExistsFlatAnchorCommonConstruction G obs ∨
  ExistsFlatSameContextConstruction G obs

/-- The flat construction choice facade, under a shorter name. -/
def ExistsAnyFlatConstruction
    (G : WorkingMCFG N α) (obs : α → M) : Prop :=
  ExistsFlatConstructionChoice G obs

/-- A disjunction of flat routes gives the flat-choice facade. -/
theorem existsFlatConstructionChoice_of_routeDisjunction
    (h : ExistsFlatConstructionRouteDisjunction G obs) :
    ExistsFlatConstructionChoice G obs :=
  match h with
  | Or.inl hE =>
      existsFlatConstructionChoice_of_exposing hE
  | Or.inr (Or.inl hA) =>
      existsFlatConstructionChoice_of_anchorCommon hA
  | Or.inr (Or.inr hS) =>
      existsFlatConstructionChoice_of_sameContext hS

/-- The flat-choice facade gives the route disjunction. -/
theorem routeDisjunction_of_existsFlatConstructionChoice
    (h : ExistsFlatConstructionChoice G obs) :
    ExistsFlatConstructionRouteDisjunction G obs :=
  match h with
  | ⟨TrimmedPresentationFlatConstructionChoice.exposing C⟩ =>
      Or.inl ⟨C⟩
  | ⟨TrimmedPresentationFlatConstructionChoice.anchorCommon C⟩ =>
      Or.inr (Or.inl ⟨C⟩)
  | ⟨TrimmedPresentationFlatConstructionChoice.sameContext C⟩ =>
      Or.inr (Or.inr ⟨C⟩)

/-- The route disjunction is equivalent to the flat-choice facade. -/
theorem routeDisjunction_iff_flatConstructionChoice :
    ExistsFlatConstructionRouteDisjunction G obs ↔
      ExistsFlatConstructionChoice G obs where
  mp := existsFlatConstructionChoice_of_routeDisjunction
  mpr := routeDisjunction_of_existsFlatConstructionChoice

/-- The shorter alias is equivalent to the route disjunction. -/
theorem anyFlatConstruction_iff_routeDisjunction :
    ExistsAnyFlatConstruction G obs ↔
      ExistsFlatConstructionRouteDisjunction G obs where
  mp := routeDisjunction_of_existsFlatConstructionChoice
  mpr := existsFlatConstructionChoice_of_routeDisjunction

/-- Characteristic-sample theorem from the route disjunction. -/
theorem existsFlatConstructionRouteDisjunction_characteristic_sample
    (h : ExistsFlatConstructionRouteDisjunction G obs) :
    ExistsBoundedPositiveCharacteristicSample G obs :=
  trimmed_flat_construction_choice_characteristic_sample
    (existsFlatConstructionChoice_of_routeDisjunction h)

/-- Prefix-exact theorem from the route disjunction. -/
theorem existsFlatConstructionRouteDisjunction_prefix_exact
    (h : ExistsFlatConstructionRouteDisjunction G obs) :
    ExistsBoundedPrefixExactIdentification G obs :=
  trimmed_flat_construction_choice_prefix_exact
    (existsFlatConstructionChoice_of_routeDisjunction h)

/-- Main theorem from the route disjunction. -/
theorem existsFlatConstructionRouteDisjunction_main_theorem
    (h : ExistsFlatConstructionRouteDisjunction G obs) :
    ExistsBoundedReachableIdentification G obs :=
  trimmed_flat_construction_choice_main_theorem
    (existsFlatConstructionChoice_of_routeDisjunction h)

/-- Characteristic-sample theorem from the shorter any-flat facade. -/
theorem existsAnyFlatConstruction_characteristic_sample
    (h : ExistsAnyFlatConstruction G obs) :
    ExistsBoundedPositiveCharacteristicSample G obs :=
  trimmed_flat_construction_choice_characteristic_sample h

/-- Prefix-exact theorem from the shorter any-flat facade. -/
theorem existsAnyFlatConstruction_prefix_exact
    (h : ExistsAnyFlatConstruction G obs) :
    ExistsBoundedPrefixExactIdentification G obs :=
  trimmed_flat_construction_choice_prefix_exact h

/-- Main theorem from the shorter any-flat facade. -/
theorem existsAnyFlatConstruction_main_theorem
    (h : ExistsAnyFlatConstruction G obs) :
    ExistsBoundedReachableIdentification G obs :=
  trimmed_flat_construction_choice_main_theorem h

end FlatConstructionDisjunction


section FlatConstructionDisjunctionTopLevelTheorems

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}

/-- Top-level theorem: if any of the three flat construction routes exists, then
the reachable learner identifies the target for some finite bound. -/
theorem trimmed_flat_construction_route_disjunction_main_theorem
    (h : ExistsFlatConstructionRouteDisjunction G obs) :
    ExistsBoundedReachableIdentification G obs :=
  existsFlatConstructionRouteDisjunction_main_theorem h

/-- Top-level characteristic-sample theorem from the flat route disjunction. -/
theorem trimmed_flat_construction_route_disjunction_characteristic_sample
    (h : ExistsFlatConstructionRouteDisjunction G obs) :
    ExistsBoundedPositiveCharacteristicSample G obs :=
  existsFlatConstructionRouteDisjunction_characteristic_sample h

/-- Top-level prefix-exact theorem from the flat route disjunction. -/
theorem trimmed_flat_construction_route_disjunction_prefix_exact
    (h : ExistsFlatConstructionRouteDisjunction G obs) :
    ExistsBoundedPrefixExactIdentification G obs :=
  existsFlatConstructionRouteDisjunction_prefix_exact h

/-- Top-level theorem using the short any-flat construction facade. -/
theorem trimmed_any_flat_construction_main_theorem
    (h : ExistsAnyFlatConstruction G obs) :
    ExistsBoundedReachableIdentification G obs :=
  existsAnyFlatConstruction_main_theorem h

/-- Top-level characteristic-sample theorem using the short any-flat facade. -/
theorem trimmed_any_flat_construction_characteristic_sample
    (h : ExistsAnyFlatConstruction G obs) :
    ExistsBoundedPositiveCharacteristicSample G obs :=
  existsAnyFlatConstruction_characteristic_sample h

/-- Top-level prefix-exact theorem using the short any-flat facade. -/
theorem trimmed_any_flat_construction_prefix_exact
    (h : ExistsAnyFlatConstruction G obs) :
    ExistsBoundedPrefixExactIdentification G obs :=
  existsAnyFlatConstruction_prefix_exact h

end FlatConstructionDisjunctionTopLevelTheorems

end MCFG
