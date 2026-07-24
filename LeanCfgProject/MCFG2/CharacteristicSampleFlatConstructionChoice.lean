/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG2.CharacteristicSampleFlatConstructionData

/-!
# CharacteristicSampleFlatConstructionChoice.lean

One-hundred-tenth clean Lean experiment for the fixed-observation MCFG project.

`CharacteristicSampleFlatConstructionData.lean` introduced three flat,
route-specific construction records:

* `TrimmedPresentationFlatExposingConstructionData`;
* `TrimmedPresentationFlatAnchorCommonConstructionData`;
* `TrimmedPresentationFlatSameContextConstructionData`.

This file packages the three flat alternatives into one choice type:

```lean
TrimmedPresentationFlatConstructionChoice
```

The point is to provide a single final-facing statement:

```text
one of the flat construction routes exists
⇒ ∃ f, reachable learner at f identifies the target.
```

No new mathematical principle is introduced here.

No theorem here uses `sorry`.
-/

namespace MCFG

universe u v w

section FlatConstructionChoice

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}

/-- A choice among the flat construction routes. -/
inductive TrimmedPresentationFlatConstructionChoice where
  | exposing :
      TrimmedPresentationFlatExposingConstructionData
        (G := G) (obs := obs) →
      TrimmedPresentationFlatConstructionChoice
  | anchorCommon :
      TrimmedPresentationFlatAnchorCommonConstructionData
        (G := G) (obs := obs) →
      TrimmedPresentationFlatConstructionChoice
  | sameContext :
      TrimmedPresentationFlatSameContextConstructionData
        (G := G) (obs := obs) →
      TrimmedPresentationFlatConstructionChoice

namespace TrimmedPresentationFlatConstructionChoice

/-- Convert a flat construction choice to the split-layered transport interface. -/
def toSplitLayeredTransportConstructionData :
    TrimmedPresentationFlatConstructionChoice
      (G := G) (obs := obs) →
    TrimmedPresentationSplitLayeredTransportConstructionData
      (G := G) (obs := obs)
  | exposing C =>
      C.toSplitLayeredExposingConstructionData.toSplitLayeredTransportConstructionData
  | anchorCommon C =>
      C.toSplitLayeredAnchorCommonConstructionData.toSplitLayeredTransportConstructionData
  | sameContext C =>
      C.toSplitLayeredSameContextConstructionData.toSplitLayeredTransportConstructionData

/-- Convert a flat construction choice to the fully layered interface. -/
def toFullyLayeredTransportConstructionData
    (C : TrimmedPresentationFlatConstructionChoice
      (G := G) (obs := obs)) :
    TrimmedPresentationFullyLayeredConstructionData
      (G := G) (obs := obs) :=
  C.toSplitLayeredTransportConstructionData.toFullyLayeredTransportConstructionData

/-- Convert a flat construction choice to the transport-choice interface. -/
def toTransportConstructionChoice
    (C : TrimmedPresentationFlatConstructionChoice
      (G := G) (obs := obs)) :
    TrimmedPresentationTransportConstructionChoice
      (G := G) (obs := obs) :=
  C.toSplitLayeredTransportConstructionData.toTransportConstructionChoice

/-- A flat construction choice gives a finite positive characteristic sample for
some finite fanout bound. -/
theorem exists_bounded_positive_characteristic_sample
    (C : TrimmedPresentationFlatConstructionChoice
      (G := G) (obs := obs)) :
    ExistsBoundedPositiveCharacteristicSample G obs :=
  match C with
  | exposing E =>
      E.toSplitLayeredExposingConstructionData.toSplitLayeredTransportConstructionData.exists_bounded_positive_characteristic_sample
  | anchorCommon A =>
      A.toSplitLayeredAnchorCommonConstructionData.toSplitLayeredTransportConstructionData.exists_bounded_positive_characteristic_sample
  | sameContext S =>
      S.toSplitLayeredSameContextConstructionData.toSplitLayeredTransportConstructionData.exists_bounded_positive_characteristic_sample

/-- A flat construction choice gives eventual prefix exactness for some finite
fanout bound. -/
theorem exists_bounded_prefix_exact_identification
    (C : TrimmedPresentationFlatConstructionChoice
      (G := G) (obs := obs)) :
    ExistsBoundedPrefixExactIdentification G obs :=
  match C with
  | exposing E =>
      E.toSplitLayeredExposingConstructionData.toSplitLayeredTransportConstructionData.exists_bounded_prefix_exact_identification
  | anchorCommon A =>
      A.toSplitLayeredAnchorCommonConstructionData.toSplitLayeredTransportConstructionData.exists_bounded_prefix_exact_identification
  | sameContext S =>
      S.toSplitLayeredSameContextConstructionData.toSplitLayeredTransportConstructionData.exists_bounded_prefix_exact_identification

/-- A flat construction choice gives Gold-style identification for some finite
fanout bound. -/
theorem exists_bounded_reachable_identification
    (C : TrimmedPresentationFlatConstructionChoice
      (G := G) (obs := obs)) :
    ExistsBoundedReachableIdentification G obs :=
  match C with
  | exposing E =>
      E.exists_bounded_reachable_identification
  | anchorCommon A =>
      A.exists_bounded_reachable_identification
  | sameContext S =>
      S.exists_bounded_reachable_identification

end TrimmedPresentationFlatConstructionChoice

end FlatConstructionChoice


section FlatConstructionChoiceExistential

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}

/-- Existence of one flat construction route. -/
def ExistsFlatConstructionChoice
    (G : WorkingMCFG N α) (obs : α → M) : Prop :=
  Nonempty
    (TrimmedPresentationFlatConstructionChoice
      (G := G) (obs := obs))

/-- Flat exposing construction gives a flat construction choice. -/
theorem existsFlatConstructionChoice_of_exposing
    (h : ExistsFlatExposingConstruction G obs) :
    ExistsFlatConstructionChoice G obs :=
  match h with
  | ⟨C⟩ =>
      ⟨TrimmedPresentationFlatConstructionChoice.exposing C⟩

/-- Flat anchor-common construction gives a flat construction choice. -/
theorem existsFlatConstructionChoice_of_anchorCommon
    (h : ExistsFlatAnchorCommonConstruction G obs) :
    ExistsFlatConstructionChoice G obs :=
  match h with
  | ⟨C⟩ =>
      ⟨TrimmedPresentationFlatConstructionChoice.anchorCommon C⟩

/-- Flat same-context construction gives a flat construction choice. -/
theorem existsFlatConstructionChoice_of_sameContext
    (h : ExistsFlatSameContextConstruction G obs) :
    ExistsFlatConstructionChoice G obs :=
  match h with
  | ⟨C⟩ =>
      ⟨TrimmedPresentationFlatConstructionChoice.sameContext C⟩

/-- A flat construction choice gives split-layered transport construction. -/
theorem existsSplitLayeredTransportConstruction_of_flatChoice
    (h : ExistsFlatConstructionChoice G obs) :
    ExistsSplitLayeredTransportConstruction G obs :=
  match h with
  | ⟨C⟩ =>
      ⟨C.toSplitLayeredTransportConstructionData⟩

/-- A flat construction choice gives fully layered transport construction. -/
theorem existsFullyLayeredTransportConstruction_of_flatChoice
    (h : ExistsFlatConstructionChoice G obs) :
    ExistsFullyLayeredTransportConstruction G obs :=
  match h with
  | ⟨C⟩ =>
      ⟨C.toFullyLayeredTransportConstructionData⟩

/-- Characteristic-sample theorem from flat construction choice. -/
theorem existsFlatConstructionChoice_characteristic_sample
    (h : ExistsFlatConstructionChoice G obs) :
    ExistsBoundedPositiveCharacteristicSample G obs :=
  match h with
  | ⟨C⟩ =>
      C.exists_bounded_positive_characteristic_sample

/-- Prefix-exact theorem from flat construction choice. -/
theorem existsFlatConstructionChoice_prefix_exact
    (h : ExistsFlatConstructionChoice G obs) :
    ExistsBoundedPrefixExactIdentification G obs :=
  match h with
  | ⟨C⟩ =>
      C.exists_bounded_prefix_exact_identification

/-- Main theorem from flat construction choice. -/
theorem existsFlatConstructionChoice_main_theorem
    (h : ExistsFlatConstructionChoice G obs) :
    ExistsBoundedReachableIdentification G obs :=
  match h with
  | ⟨C⟩ =>
      C.exists_bounded_reachable_identification

/-- Main theorem from flat exposing construction, through flat choice. -/
theorem existsFlatExposingConstruction_main_theorem_via_choice
    (h : ExistsFlatExposingConstruction G obs) :
    ExistsBoundedReachableIdentification G obs :=
  existsFlatConstructionChoice_main_theorem
    (existsFlatConstructionChoice_of_exposing h)

/-- Main theorem from flat anchor-common construction, through flat choice. -/
theorem existsFlatAnchorCommonConstruction_main_theorem_via_choice
    (h : ExistsFlatAnchorCommonConstruction G obs) :
    ExistsBoundedReachableIdentification G obs :=
  existsFlatConstructionChoice_main_theorem
    (existsFlatConstructionChoice_of_anchorCommon h)

/-- Main theorem from flat same-context construction, through flat choice. -/
theorem existsFlatSameContextConstruction_main_theorem_via_choice
    (h : ExistsFlatSameContextConstruction G obs) :
    ExistsBoundedReachableIdentification G obs :=
  existsFlatConstructionChoice_main_theorem
    (existsFlatConstructionChoice_of_sameContext h)

end FlatConstructionChoiceExistential


section FlatConstructionChoiceTopLevelTheorems

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}

/-- Top-level theorem: existence of one flat construction route gives Gold-style
identification for some finite bound. -/
theorem trimmed_flat_construction_choice_main_theorem
    (h : ExistsFlatConstructionChoice G obs) :
    ExistsBoundedReachableIdentification G obs :=
  existsFlatConstructionChoice_main_theorem h

/-- Top-level characteristic-sample theorem from flat construction choice. -/
theorem trimmed_flat_construction_choice_characteristic_sample
    (h : ExistsFlatConstructionChoice G obs) :
    ExistsBoundedPositiveCharacteristicSample G obs :=
  existsFlatConstructionChoice_characteristic_sample h

/-- Top-level prefix-exact theorem from flat construction choice. -/
theorem trimmed_flat_construction_choice_prefix_exact
    (h : ExistsFlatConstructionChoice G obs) :
    ExistsBoundedPrefixExactIdentification G obs :=
  existsFlatConstructionChoice_prefix_exact h

/-- Top-level theorem: flat exposing construction gives identification through
the flat-choice interface. -/
theorem trimmed_flat_exposing_construction_main_theorem_via_choice
    (h : ExistsFlatExposingConstruction G obs) :
    ExistsBoundedReachableIdentification G obs :=
  existsFlatExposingConstruction_main_theorem_via_choice h

/-- Top-level theorem: flat anchor-common construction gives identification
through the flat-choice interface. -/
theorem trimmed_flat_anchor_common_construction_main_theorem_via_choice
    (h : ExistsFlatAnchorCommonConstruction G obs) :
    ExistsBoundedReachableIdentification G obs :=
  existsFlatAnchorCommonConstruction_main_theorem_via_choice h

/-- Top-level theorem: flat same-context construction gives identification
through the flat-choice interface. -/
theorem trimmed_flat_same_context_construction_main_theorem_via_choice
    (h : ExistsFlatSameContextConstruction G obs) :
    ExistsBoundedReachableIdentification G obs :=
  existsFlatSameContextConstruction_main_theorem_via_choice h

end FlatConstructionChoiceTopLevelTheorems

end MCFG
