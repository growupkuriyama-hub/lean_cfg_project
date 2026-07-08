/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG.CharacteristicSampleTransportConstructionChoice

/-!
# CharacteristicSampleTransportConstructionMainTheorem.lean

One-hundred-first clean Lean experiment for the fixed-observation MCFG project.

`CharacteristicSampleTransportConstructionChoice.lean` packaged the three
construction-facing transport routes into one choice type:

* direct exposing-context construction;
* preferred anchor common-context construction;
* stronger same-context construction.

This file gives paper-facing theorem names for that construction-choice layer.
The point is to have a single final construction-facing entrance:

```text
Nonempty TransportConstructionChoice
⇒ ∃ f, reachable learner at f identifies the target language.
```

This is not a new mathematical principle.  It is a stable theorem-name facade
for the construction phase.

No theorem here uses `sorry`.
-/

namespace MCFG

universe u v w

section TransportConstructionMainStatements

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]

/-- There is at least one available transport construction route. -/
def HasTransportConstructionChoice
    (G : WorkingMCFG N α) (obs : α → M) : Prop :=
  Nonempty
    (TrimmedPresentationTransportConstructionChoice
      (G := G) (obs := obs))

/-- Direct exposing construction data are available. -/
def HasExposingTransportConstruction
    (G : WorkingMCFG N α) (obs : α → M) : Prop :=
  Nonempty
    (TrimmedPresentationExposingTransportConstructionData
      (G := G) (obs := obs))

/-- Preferred anchor common-context construction data are available. -/
def HasAnchorCommonTransportConstruction
    (G : WorkingMCFG N α) (obs : α → M) : Prop :=
  Nonempty
    (TrimmedPresentationAnchorCommonTransportConstructionData
      (G := G) (obs := obs))

/-- Stronger same-context construction data are available. -/
def HasSameContextTransportConstruction
    (G : WorkingMCFG N α) (obs : α → M) : Prop :=
  Nonempty
    (TrimmedPresentationSameContextTransportConstructionData
      (G := G) (obs := obs))

end TransportConstructionMainStatements


section TransportConstructionAvailability

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}

/-- Direct exposing construction availability implies transport-construction
choice availability. -/
theorem hasTransportConstructionChoice_of_exposing
    (h : HasExposingTransportConstruction G obs) :
    HasTransportConstructionChoice G obs :=
  nonempty_transportConstructionChoice_of_exposing h

/-- Preferred anchor common-context construction availability implies
transport-construction choice availability. -/
theorem hasTransportConstructionChoice_of_anchorCommon
    (h : HasAnchorCommonTransportConstruction G obs) :
    HasTransportConstructionChoice G obs :=
  nonempty_transportConstructionChoice_of_anchorCommon h

/-- Stronger same-context construction availability implies transport-
construction choice availability. -/
theorem hasTransportConstructionChoice_of_sameContext
    (h : HasSameContextTransportConstruction G obs) :
    HasTransportConstructionChoice G obs :=
  nonempty_transportConstructionChoice_of_sameContext h

/-- Anchor common-context construction availability also gives direct exposing
construction availability through the construction diagram. -/
theorem hasExposingTransportConstruction_of_anchorCommon
    (h : HasAnchorCommonTransportConstruction G obs) :
    HasExposingTransportConstruction G obs :=
  trimmed_transport_construction_diagram_anchor_common_to_exposing h

/-- Same-context construction availability also gives direct exposing
construction availability through the construction diagram. -/
theorem hasExposingTransportConstruction_of_sameContext
    (h : HasSameContextTransportConstruction G obs) :
    HasExposingTransportConstruction G obs :=
  trimmed_transport_construction_diagram_same_context_to_exposing h

end TransportConstructionAvailability


section TransportConstructionMainTheorems

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}

/-- Main construction theorem from any available transport-construction choice:
there exists a finite positive characteristic sample for some bound. -/
theorem trimmed_transport_construction_main_exists_characteristic_sample
    (h : HasTransportConstructionChoice G obs) :
    ExistsBoundedPositiveCharacteristicSample G obs :=
  nonempty_transportConstructionChoice_exists_characteristic_sample h

/-- Main construction theorem from any available transport-construction choice:
there is eventual prefix exactness for some bound. -/
theorem trimmed_transport_construction_main_prefix_exact
    (h : HasTransportConstructionChoice G obs) :
    ExistsBoundedPrefixExactIdentification G obs :=
  nonempty_transportConstructionChoice_prefix_exact h

/-- Main construction theorem from any available transport-construction choice:
there is Gold-style identification for some bound. -/
theorem trimmed_transport_construction_main_identification
    (h : HasTransportConstructionChoice G obs) :
    ExistsBoundedReachableIdentification G obs :=
  nonempty_transportConstructionChoice_main_theorem h

/-- Main construction theorem, explicitly routed through direct exposing
construction. -/
theorem trimmed_transport_construction_main_identification_via_exposing
    (h : HasTransportConstructionChoice G obs) :
    ExistsBoundedReachableIdentification G obs :=
  nonempty_transportConstructionChoice_main_theorem_via_exposing h

/-- Direct exposing-construction theorem under the availability predicate. -/
theorem trimmed_exposing_transport_available_main_theorem
    (h : HasExposingTransportConstruction G obs) :
    ExistsBoundedReachableIdentification G obs :=
  trimmed_exposing_transport_construction_main_theorem_of_nonempty h

/-- Preferred anchor common-context construction theorem under the availability
predicate. -/
theorem trimmed_anchor_common_transport_available_main_theorem
    (h : HasAnchorCommonTransportConstruction G obs) :
    ExistsBoundedReachableIdentification G obs :=
  trimmed_anchor_common_transport_construction_main_theorem_of_nonempty h

/-- Preferred anchor common-context construction theorem through the exposing
route. -/
theorem trimmed_anchor_common_transport_available_main_theorem_via_exposing
    (h : HasAnchorCommonTransportConstruction G obs) :
    ExistsBoundedReachableIdentification G obs :=
  trimmed_transport_construction_diagram_anchor_common_main_via_exposing h

/-- Stronger same-context construction theorem under the availability predicate. -/
theorem trimmed_same_context_transport_available_main_theorem
    (h : HasSameContextTransportConstruction G obs) :
    ExistsBoundedReachableIdentification G obs :=
  trimmed_same_context_transport_construction_main_theorem_of_nonempty h

/-- Stronger same-context construction theorem through the exposing route. -/
theorem trimmed_same_context_transport_available_main_theorem_via_exposing
    (h : HasSameContextTransportConstruction G obs) :
    ExistsBoundedReachableIdentification G obs :=
  trimmed_transport_construction_diagram_same_context_main_via_exposing h

end TransportConstructionMainTheorems


section PaperFacingConstructionTheoremAliases

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}

/-- Paper-facing construction theorem name.

If at least one of the transport construction routes has been built, then the
reachable learner identifies the target language from positive data for some
finite fanout bound. -/
theorem trimmed_paper_transport_construction_theorem
    (h : HasTransportConstructionChoice G obs) :
    ExistsBoundedReachableIdentification G obs :=
  trimmed_transport_construction_main_identification h

/-- Paper-facing construction theorem for the preferred anchor common-context
route. -/
theorem trimmed_paper_anchor_common_transport_construction_theorem
    (h : HasAnchorCommonTransportConstruction G obs) :
    ExistsBoundedReachableIdentification G obs :=
  trimmed_anchor_common_transport_available_main_theorem h

/-- Paper-facing construction theorem for the direct exposing route. -/
theorem trimmed_paper_exposing_transport_construction_theorem
    (h : HasExposingTransportConstruction G obs) :
    ExistsBoundedReachableIdentification G obs :=
  trimmed_exposing_transport_available_main_theorem h

/-- Paper-facing construction theorem for the stronger same-context route. -/
theorem trimmed_paper_same_context_transport_construction_theorem
    (h : HasSameContextTransportConstruction G obs) :
    ExistsBoundedReachableIdentification G obs :=
  trimmed_same_context_transport_available_main_theorem h

/-- Paper-facing characteristic-sample theorem from any available transport
construction route. -/
theorem trimmed_paper_transport_construction_characteristic_sample_theorem
    (h : HasTransportConstructionChoice G obs) :
    ExistsBoundedPositiveCharacteristicSample G obs :=
  trimmed_transport_construction_main_exists_characteristic_sample h

/-- Paper-facing prefix-exact theorem from any available transport construction
route. -/
theorem trimmed_paper_transport_construction_prefix_exact_theorem
    (h : HasTransportConstructionChoice G obs) :
    ExistsBoundedPrefixExactIdentification G obs :=
  trimmed_transport_construction_main_prefix_exact h

end PaperFacingConstructionTheoremAliases

end MCFG
