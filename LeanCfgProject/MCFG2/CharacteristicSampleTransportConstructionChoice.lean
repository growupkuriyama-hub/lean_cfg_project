/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG2.CharacteristicSampleTransportConstructionDiagram

/-!
# CharacteristicSampleTransportConstructionChoice.lean

One-hundredth clean Lean experiment for the fixed-observation MCFG project.

The previous file recorded the construction-level diagram among the three
transport construction packages:

* direct exposing-context construction;
* preferred anchor common-context construction;
* stronger same-context construction.

This file packages the three alternatives into one construction-choice type:

```lean
TrimmedPresentationTransportConstructionChoice
```

The point is practical: a future construction attempt may succeed first by
building any one of the three routes.  The choice wrapper gives a single theorem
interface from any of them to the existential paper theorem.

No new mathematical principle is introduced here.

No theorem here uses `sorry`.
-/

namespace MCFG

universe u v w

section TransportConstructionChoice

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}

/-- A construction-facing choice among the currently available transport routes.

The preferred route is `anchorCommon`, but `exposing` and `sameContext` are kept
as useful direct/debugging alternatives. -/
inductive TrimmedPresentationTransportConstructionChoice where
  | exposing :
      TrimmedPresentationExposingTransportConstructionData
        (G := G) (obs := obs) →
      TrimmedPresentationTransportConstructionChoice
  | anchorCommon :
      TrimmedPresentationAnchorCommonTransportConstructionData
        (G := G) (obs := obs) →
      TrimmedPresentationTransportConstructionChoice
  | sameContext :
      TrimmedPresentationSameContextTransportConstructionData
        (G := G) (obs := obs) →
      TrimmedPresentationTransportConstructionChoice

namespace TrimmedPresentationTransportConstructionChoice

/-- Convert any construction choice to the direct exposing-construction route. -/
def toExposingTransportConstructionData :
    TrimmedPresentationTransportConstructionChoice
      (G := G) (obs := obs) →
    TrimmedPresentationExposingTransportConstructionData
      (G := G) (obs := obs)
  | exposing C => C
  | anchorCommon C => C.toExposingTransportConstructionData
  | sameContext C => C.toExposingTransportConstructionData

/-- A construction choice gives a finite positive characteristic sample for some
finite fanout bound. -/
theorem exists_bounded_positive_characteristic_sample
    (C : TrimmedPresentationTransportConstructionChoice
      (G := G) (obs := obs)) :
    ExistsBoundedPositiveCharacteristicSample G obs :=
  match C with
  | exposing E =>
      E.exists_bound_and_positive_characteristic_sample
  | anchorCommon A =>
      A.exists_bound_and_positive_characteristic_sample
  | sameContext S =>
      S.exists_bound_and_positive_characteristic_sample

/-- A construction choice gives eventual prefix exactness for some finite fanout
bound. -/
theorem exists_bounded_prefix_exact_identification
    (C : TrimmedPresentationTransportConstructionChoice
      (G := G) (obs := obs)) :
    ExistsBoundedPrefixExactIdentification G obs :=
  match C with
  | exposing E =>
      E.exists_bounded_prefix_exact_identification
  | anchorCommon A =>
      A.exists_bounded_prefix_exact_identification
  | sameContext S =>
      S.exists_bounded_prefix_exact_identification

/-- A construction choice gives Gold-style identification for some finite fanout
bound. -/
theorem exists_bounded_reachable_identification
    (C : TrimmedPresentationTransportConstructionChoice
      (G := G) (obs := obs)) :
    ExistsBoundedReachableIdentification G obs :=
  match C with
  | exposing E =>
      E.exists_bounded_reachable_identification
  | anchorCommon A =>
      A.exists_bounded_reachable_identification
  | sameContext S =>
      S.exists_bounded_reachable_identification

/-- A construction choice also gives Gold-style identification through the
direct exposing route. -/
theorem exists_bounded_reachable_identification_via_exposing
    (C : TrimmedPresentationTransportConstructionChoice
      (G := G) (obs := obs)) :
    ExistsBoundedReachableIdentification G obs :=
  C.toExposingTransportConstructionData
    .exists_bounded_reachable_identification

/-- A construction choice also gives prefix exactness through the direct
exposing route. -/
theorem exists_bounded_prefix_exact_identification_via_exposing
    (C : TrimmedPresentationTransportConstructionChoice
      (G := G) (obs := obs)) :
    ExistsBoundedPrefixExactIdentification G obs :=
  C.toExposingTransportConstructionData
    .exists_bounded_prefix_exact_identification

/-- A construction choice also gives a positive characteristic sample through
the direct exposing route. -/
theorem exists_bounded_positive_characteristic_sample_via_exposing
    (C : TrimmedPresentationTransportConstructionChoice
      (G := G) (obs := obs)) :
    ExistsBoundedPositiveCharacteristicSample G obs :=
  C.toExposingTransportConstructionData
    .exists_bound_and_positive_characteristic_sample

end TrimmedPresentationTransportConstructionChoice


section NonemptyChoice

/-- Nonempty exposing-construction data gives a nonempty construction choice. -/
theorem nonempty_transportConstructionChoice_of_exposing
    (h :
      Nonempty
        (TrimmedPresentationExposingTransportConstructionData
          (G := G) (obs := obs))) :
    Nonempty
      (TrimmedPresentationTransportConstructionChoice
        (G := G) (obs := obs)) :=
  match h with
  | ⟨C⟩ => ⟨TrimmedPresentationTransportConstructionChoice.exposing C⟩

/-- Nonempty anchor-common construction data gives a nonempty construction
choice. -/
theorem nonempty_transportConstructionChoice_of_anchorCommon
    (h :
      Nonempty
        (TrimmedPresentationAnchorCommonTransportConstructionData
          (G := G) (obs := obs))) :
    Nonempty
      (TrimmedPresentationTransportConstructionChoice
        (G := G) (obs := obs)) :=
  match h with
  | ⟨C⟩ => ⟨TrimmedPresentationTransportConstructionChoice.anchorCommon C⟩

/-- Nonempty same-context construction data gives a nonempty construction
choice. -/
theorem nonempty_transportConstructionChoice_of_sameContext
    (h :
      Nonempty
        (TrimmedPresentationSameContextTransportConstructionData
          (G := G) (obs := obs))) :
    Nonempty
      (TrimmedPresentationTransportConstructionChoice
        (G := G) (obs := obs)) :=
  match h with
  | ⟨C⟩ => ⟨TrimmedPresentationTransportConstructionChoice.sameContext C⟩

/-- Nonempty construction choice gives a positive characteristic sample for some
finite fanout bound. -/
theorem nonempty_transportConstructionChoice_exists_characteristic_sample
    (h :
      Nonempty
        (TrimmedPresentationTransportConstructionChoice
          (G := G) (obs := obs))) :
    ExistsBoundedPositiveCharacteristicSample G obs :=
  match h with
  | ⟨C⟩ => C.exists_bounded_positive_characteristic_sample

/-- Nonempty construction choice gives eventual prefix exactness for some finite
fanout bound. -/
theorem nonempty_transportConstructionChoice_prefix_exact
    (h :
      Nonempty
        (TrimmedPresentationTransportConstructionChoice
          (G := G) (obs := obs))) :
    ExistsBoundedPrefixExactIdentification G obs :=
  match h with
  | ⟨C⟩ => C.exists_bounded_prefix_exact_identification

/-- Nonempty construction choice gives Gold-style identification for some finite
fanout bound. -/
theorem nonempty_transportConstructionChoice_main_theorem
    (h :
      Nonempty
        (TrimmedPresentationTransportConstructionChoice
          (G := G) (obs := obs))) :
    ExistsBoundedReachableIdentification G obs :=
  match h with
  | ⟨C⟩ => C.exists_bounded_reachable_identification

/-- Nonempty construction choice gives Gold-style identification through the
exposing route. -/
theorem nonempty_transportConstructionChoice_main_theorem_via_exposing
    (h :
      Nonempty
        (TrimmedPresentationTransportConstructionChoice
          (G := G) (obs := obs))) :
    ExistsBoundedReachableIdentification G obs :=
  match h with
  | ⟨C⟩ => C.exists_bounded_reachable_identification_via_exposing

end NonemptyChoice

end TransportConstructionChoice


section TransportConstructionChoiceTheorems

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}

/-- Top-level theorem: any construction choice gives a finite positive
characteristic sample for some bound. -/
theorem trimmed_transport_construction_choice_exists_characteristic_sample
    (C :
      TrimmedPresentationTransportConstructionChoice
        (G := G) (obs := obs)) :
    ExistsBoundedPositiveCharacteristicSample G obs :=
  C.exists_bounded_positive_characteristic_sample

/-- Top-level theorem: any construction choice gives eventual prefix exactness
for some bound. -/
theorem trimmed_transport_construction_choice_prefix_exact_theorem
    (C :
      TrimmedPresentationTransportConstructionChoice
        (G := G) (obs := obs)) :
    ExistsBoundedPrefixExactIdentification G obs :=
  C.exists_bounded_prefix_exact_identification

/-- Top-level theorem: any construction choice gives Gold-style identification
for some bound. -/
theorem trimmed_transport_construction_choice_main_theorem
    (C :
      TrimmedPresentationTransportConstructionChoice
        (G := G) (obs := obs)) :
    ExistsBoundedReachableIdentification G obs :=
  C.exists_bounded_reachable_identification

/-- Top-level theorem: nonempty construction choice gives Gold-style
identification for some bound. -/
theorem trimmed_transport_construction_choice_main_theorem_of_nonempty
    (h :
      Nonempty
        (TrimmedPresentationTransportConstructionChoice
          (G := G) (obs := obs))) :
    ExistsBoundedReachableIdentification G obs :=
  nonempty_transportConstructionChoice_main_theorem h

/-- Top-level theorem: nonempty construction choice gives Gold-style
identification through exposing construction. -/
theorem trimmed_transport_construction_choice_main_theorem_of_nonempty_via_exposing
    (h :
      Nonempty
        (TrimmedPresentationTransportConstructionChoice
          (G := G) (obs := obs))) :
    ExistsBoundedReachableIdentification G obs :=
  nonempty_transportConstructionChoice_main_theorem_via_exposing h

end TransportConstructionChoiceTheorems

end MCFG
