/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG2.CharacteristicSampleFlatConstructionDisjunction

/-!
# CharacteristicSampleFinalConstructionFacade.lean

One-hundred-twelfth clean Lean experiment for the fixed-observation MCFG
project.

The previous file introduced the paper-readable disjunction of the three flat
construction routes:

```text
flat exposing construction
∨ flat anchor-common construction
∨ flat same-context construction.
```

This file gives a final construction-facing facade.  It is intentionally thin:
the goal is to provide stable theorem names that can be cited from the paper,
README, or blueprint without exposing the internal layering choices.

The key package is

```lean
TrimmedPresentationConstructiveMainAssumptions
```

and the key theorem is

```lean
trimmed_constructive_main_theorem
```

which states that the constructive assumptions imply

```lean
ExistsBoundedReachableIdentification G obs.
```

No new mathematical principle is introduced here.

No theorem here uses `sorry`.
-/

namespace MCFG

universe u v w

section FinalConstructionFacade

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}

/-- Final construction-facing assumptions.

This is the compact facade: any one of the three flat construction routes is
enough. -/
structure TrimmedPresentationConstructiveMainAssumptions where
  route :
    ExistsFlatConstructionRouteDisjunction G obs

namespace TrimmedPresentationConstructiveMainAssumptions

/-- Convert the final facade to the flat-choice facade. -/
def toFlatConstructionChoice
    (A : TrimmedPresentationConstructiveMainAssumptions
      (G := G) (obs := obs)) :
    ExistsFlatConstructionChoice G obs :=
  existsFlatConstructionChoice_of_routeDisjunction A.route

/-- Convert the final facade to the shorter any-flat facade. -/
def toAnyFlatConstruction
    (A : TrimmedPresentationConstructiveMainAssumptions
      (G := G) (obs := obs)) :
    ExistsAnyFlatConstruction G obs :=
  A.toFlatConstructionChoice

/-- Characteristic-sample conclusion from the final construction facade. -/
theorem exists_bounded_positive_characteristic_sample
    (A : TrimmedPresentationConstructiveMainAssumptions
      (G := G) (obs := obs)) :
    ExistsBoundedPositiveCharacteristicSample G obs :=
  trimmed_flat_construction_route_disjunction_characteristic_sample A.route

/-- Prefix-exact conclusion from the final construction facade. -/
theorem exists_bounded_prefix_exact_identification
    (A : TrimmedPresentationConstructiveMainAssumptions
      (G := G) (obs := obs)) :
    ExistsBoundedPrefixExactIdentification G obs :=
  trimmed_flat_construction_route_disjunction_prefix_exact A.route

/-- Gold-style identification conclusion from the final construction facade. -/
theorem exists_bounded_reachable_identification
    (A : TrimmedPresentationConstructiveMainAssumptions
      (G := G) (obs := obs)) :
    ExistsBoundedReachableIdentification G obs :=
  trimmed_flat_construction_route_disjunction_main_theorem A.route

end TrimmedPresentationConstructiveMainAssumptions


/-- Build final constructive assumptions from flat exposing construction. -/
def constructiveMainAssumptions_of_flatExposing
    (h : ExistsFlatExposingConstruction G obs) :
    TrimmedPresentationConstructiveMainAssumptions
      (G := G) (obs := obs) where
  route := Or.inl h

/-- Build final constructive assumptions from flat anchor-common construction. -/
def constructiveMainAssumptions_of_flatAnchorCommon
    (h : ExistsFlatAnchorCommonConstruction G obs) :
    TrimmedPresentationConstructiveMainAssumptions
      (G := G) (obs := obs) where
  route := Or.inr (Or.inl h)

/-- Build final constructive assumptions from flat same-context construction. -/
def constructiveMainAssumptions_of_flatSameContext
    (h : ExistsFlatSameContextConstruction G obs) :
    TrimmedPresentationConstructiveMainAssumptions
      (G := G) (obs := obs) where
  route := Or.inr (Or.inr h)

/-- Build final constructive assumptions from a flat construction choice. -/
def constructiveMainAssumptions_of_flatChoice
    (h : ExistsFlatConstructionChoice G obs) :
    TrimmedPresentationConstructiveMainAssumptions
      (G := G) (obs := obs) where
  route := routeDisjunction_of_existsFlatConstructionChoice h

/-- Build final constructive assumptions from the short any-flat facade. -/
def constructiveMainAssumptions_of_anyFlat
    (h : ExistsAnyFlatConstruction G obs) :
    TrimmedPresentationConstructiveMainAssumptions
      (G := G) (obs := obs) :=
  constructiveMainAssumptions_of_flatChoice h

/-- Final facade theorem: constructive assumptions give a finite positive
characteristic sample for some bound. -/
theorem constructiveMainAssumptions_characteristic_sample
    (A : TrimmedPresentationConstructiveMainAssumptions
      (G := G) (obs := obs)) :
    ExistsBoundedPositiveCharacteristicSample G obs :=
  A.exists_bounded_positive_characteristic_sample

/-- Final facade theorem: constructive assumptions give eventual prefix
exactness for some bound. -/
theorem constructiveMainAssumptions_prefix_exact
    (A : TrimmedPresentationConstructiveMainAssumptions
      (G := G) (obs := obs)) :
    ExistsBoundedPrefixExactIdentification G obs :=
  A.exists_bounded_prefix_exact_identification

/-- Final facade theorem: constructive assumptions give Gold-style identification
for some bound. -/
theorem constructiveMainAssumptions_main_theorem
    (A : TrimmedPresentationConstructiveMainAssumptions
      (G := G) (obs := obs)) :
    ExistsBoundedReachableIdentification G obs :=
  A.exists_bounded_reachable_identification

end FinalConstructionFacade


section FinalConstructionTopLevelTheorems

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}

/-- Final named constructive theorem.

If one of the flat construction routes exists, then the reachable learner
identifies the target language for some finite fanout bound. -/
theorem trimmed_constructive_main_theorem
    (A :
      TrimmedPresentationConstructiveMainAssumptions
        (G := G) (obs := obs)) :
    ExistsBoundedReachableIdentification G obs :=
  constructiveMainAssumptions_main_theorem A

/-- Final named characteristic-sample theorem. -/
theorem trimmed_constructive_characteristic_sample_theorem
    (A :
      TrimmedPresentationConstructiveMainAssumptions
        (G := G) (obs := obs)) :
    ExistsBoundedPositiveCharacteristicSample G obs :=
  constructiveMainAssumptions_characteristic_sample A

/-- Final named prefix-exact theorem. -/
theorem trimmed_constructive_prefix_exact_theorem
    (A :
      TrimmedPresentationConstructiveMainAssumptions
        (G := G) (obs := obs)) :
    ExistsBoundedPrefixExactIdentification G obs :=
  constructiveMainAssumptions_prefix_exact A

/-- Direct final theorem from the paper-readable route disjunction. -/
theorem trimmed_constructive_main_theorem_of_route_disjunction
    (h : ExistsFlatConstructionRouteDisjunction G obs) :
    ExistsBoundedReachableIdentification G obs :=
  trimmed_constructive_main_theorem
    ({ route := h } :
      TrimmedPresentationConstructiveMainAssumptions
        (G := G) (obs := obs))

/-- Direct final theorem from the short any-flat facade. -/
theorem trimmed_constructive_main_theorem_of_any_flat
    (h : ExistsAnyFlatConstruction G obs) :
    ExistsBoundedReachableIdentification G obs :=
  trimmed_constructive_main_theorem
    (constructiveMainAssumptions_of_anyFlat h)

/-- Direct final theorem from flat exposing construction. -/
theorem trimmed_constructive_main_theorem_of_flat_exposing
    (h : ExistsFlatExposingConstruction G obs) :
    ExistsBoundedReachableIdentification G obs :=
  trimmed_constructive_main_theorem
    (constructiveMainAssumptions_of_flatExposing h)

/-- Direct final theorem from flat anchor-common construction. -/
theorem trimmed_constructive_main_theorem_of_flat_anchor_common
    (h : ExistsFlatAnchorCommonConstruction G obs) :
    ExistsBoundedReachableIdentification G obs :=
  trimmed_constructive_main_theorem
    (constructiveMainAssumptions_of_flatAnchorCommon h)

/-- Direct final theorem from flat same-context construction. -/
theorem trimmed_constructive_main_theorem_of_flat_same_context
    (h : ExistsFlatSameContextConstruction G obs) :
    ExistsBoundedReachableIdentification G obs :=
  trimmed_constructive_main_theorem
    (constructiveMainAssumptions_of_flatSameContext h)

end FinalConstructionTopLevelTheorems

end MCFG
