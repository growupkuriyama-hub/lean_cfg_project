/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG.CharacteristicSampleSameContextTransportConstruction

/-!
# CharacteristicSampleTransportConstructionDiagram.lean

Ninety-ninth clean Lean experiment for the fixed-observation MCFG project.

The previous files introduced three construction-facing packages:

* `TrimmedPresentationExposingTransportConstructionData`;
* `TrimmedPresentationAnchorCommonTransportConstructionData`;
* `TrimmedPresentationSameContextTransportConstructionData`.

This file records the construction-level conversion diagram:

```text
AnchorCommonTransportConstructionData ⇒ ExposingTransportConstructionData
SameContextTransportConstructionData  ⇒ ExposingTransportConstructionData
```

and also exposes the corresponding `Nonempty` versions.  This is useful because
future construction attempts may prove any one of the stronger/common/direct
routes, while the theorem-facing endpoint can be reused uniformly.

No new mathematical principle is introduced here.

No theorem here uses `sorry`.
-/

namespace MCFG

universe u v w

section TransportConstructionDiagram

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}

/-- Construction-level diagram node: the direct exposing route. -/
abbrev ExposingTransportConstructionNode :=
  TrimmedPresentationExposingTransportConstructionData
    (G := G) (obs := obs)

/-- Construction-level diagram node: the preferred anchor common-context route. -/
abbrev AnchorCommonTransportConstructionNode :=
  TrimmedPresentationAnchorCommonTransportConstructionData
    (G := G) (obs := obs)

/-- Construction-level diagram node: the stronger same-context route. -/
abbrev SameContextTransportConstructionNode :=
  TrimmedPresentationSameContextTransportConstructionData
    (G := G) (obs := obs)

/-- Anchor common-context construction data maps to direct exposing construction
data. -/
def exposingConstruction_of_anchorCommonConstruction
    (C : AnchorCommonTransportConstructionNode (G := G) (obs := obs)) :
    ExposingTransportConstructionNode (G := G) (obs := obs) :=
  C.toExposingTransportConstructionData

/-- Same-context construction data maps to direct exposing construction data. -/
def exposingConstruction_of_sameContextConstruction
    (C : SameContextTransportConstructionNode (G := G) (obs := obs)) :
    ExposingTransportConstructionNode (G := G) (obs := obs) :=
  C.toExposingTransportConstructionData

/-- Nonempty anchor-common construction data gives nonempty exposing construction
data. -/
theorem nonempty_exposingConstruction_of_anchorCommonConstruction
    (h : Nonempty (AnchorCommonTransportConstructionNode
      (G := G) (obs := obs))) :
    Nonempty (ExposingTransportConstructionNode
      (G := G) (obs := obs)) :=
  match h with
  | ⟨C⟩ => ⟨C.toExposingTransportConstructionData⟩

/-- Nonempty same-context construction data gives nonempty exposing construction
data. -/
theorem nonempty_exposingConstruction_of_sameContextConstruction
    (h : Nonempty (SameContextTransportConstructionNode
      (G := G) (obs := obs))) :
    Nonempty (ExposingTransportConstructionNode
      (G := G) (obs := obs)) :=
  match h with
  | ⟨C⟩ => ⟨C.toExposingTransportConstructionData⟩

/-- Anchor common-context construction data gives the exposing-construction main
theorem through the diagram. -/
theorem anchorCommonConstruction_exposing_main_theorem
    (C : AnchorCommonTransportConstructionNode (G := G) (obs := obs)) :
    ExistsBoundedReachableIdentification G obs :=
  C.toExposingTransportConstructionData
    .exists_bounded_reachable_identification

/-- Same-context construction data gives the exposing-construction main theorem
through the diagram. -/
theorem sameContextConstruction_exposing_main_theorem
    (C : SameContextTransportConstructionNode (G := G) (obs := obs)) :
    ExistsBoundedReachableIdentification G obs :=
  C.toExposingTransportConstructionData
    .exists_bounded_reachable_identification

/-- Nonempty anchor-common construction data gives the exposing-construction
main theorem through the diagram. -/
theorem nonempty_anchorCommonConstruction_exposing_main_theorem
    (h : Nonempty (AnchorCommonTransportConstructionNode
      (G := G) (obs := obs))) :
    ExistsBoundedReachableIdentification G obs :=
  trimmed_exposing_transport_construction_main_theorem_of_nonempty
    (nonempty_exposingConstruction_of_anchorCommonConstruction h)

/-- Nonempty same-context construction data gives the exposing-construction main
theorem through the diagram. -/
theorem nonempty_sameContextConstruction_exposing_main_theorem
    (h : Nonempty (SameContextTransportConstructionNode
      (G := G) (obs := obs))) :
    ExistsBoundedReachableIdentification G obs :=
  trimmed_exposing_transport_construction_main_theorem_of_nonempty
    (nonempty_exposingConstruction_of_sameContextConstruction h)

/-- Anchor common-context construction data gives a positive characteristic
sample through the exposing-construction diagram. -/
theorem anchorCommonConstruction_exposing_characteristic_sample
    (C : AnchorCommonTransportConstructionNode (G := G) (obs := obs)) :
    ExistsBoundedPositiveCharacteristicSample G obs :=
  C.toExposingTransportConstructionData
    .exists_bound_and_positive_characteristic_sample

/-- Same-context construction data gives a positive characteristic sample through
the exposing-construction diagram. -/
theorem sameContextConstruction_exposing_characteristic_sample
    (C : SameContextTransportConstructionNode (G := G) (obs := obs)) :
    ExistsBoundedPositiveCharacteristicSample G obs :=
  C.toExposingTransportConstructionData
    .exists_bound_and_positive_characteristic_sample

/-- Nonempty anchor-common construction data gives a positive characteristic
sample through the exposing-construction diagram. -/
theorem nonempty_anchorCommonConstruction_exposing_characteristic_sample
    (h : Nonempty (AnchorCommonTransportConstructionNode
      (G := G) (obs := obs))) :
    ExistsBoundedPositiveCharacteristicSample G obs :=
  trimmed_exposing_transport_construction_characteristic_sample_of_nonempty
    (nonempty_exposingConstruction_of_anchorCommonConstruction h)

/-- Nonempty same-context construction data gives a positive characteristic
sample through the exposing-construction diagram. -/
theorem nonempty_sameContextConstruction_exposing_characteristic_sample
    (h : Nonempty (SameContextTransportConstructionNode
      (G := G) (obs := obs))) :
    ExistsBoundedPositiveCharacteristicSample G obs :=
  trimmed_exposing_transport_construction_characteristic_sample_of_nonempty
    (nonempty_exposingConstruction_of_sameContextConstruction h)

/-- Anchor common-context construction data gives prefix exactness through the
exposing-construction diagram. -/
theorem anchorCommonConstruction_exposing_prefix_exact
    (C : AnchorCommonTransportConstructionNode (G := G) (obs := obs)) :
    ExistsBoundedPrefixExactIdentification G obs :=
  C.toExposingTransportConstructionData
    .exists_bounded_prefix_exact_identification

/-- Same-context construction data gives prefix exactness through the
exposing-construction diagram. -/
theorem sameContextConstruction_exposing_prefix_exact
    (C : SameContextTransportConstructionNode (G := G) (obs := obs)) :
    ExistsBoundedPrefixExactIdentification G obs :=
  C.toExposingTransportConstructionData
    .exists_bounded_prefix_exact_identification

end TransportConstructionDiagram


section TransportConstructionDiagramTheorems

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}

/-- Top-level construction diagram theorem: nonempty anchor-common construction
data implies nonempty exposing construction data. -/
theorem trimmed_transport_construction_diagram_anchor_common_to_exposing
    (h :
      Nonempty
        (TrimmedPresentationAnchorCommonTransportConstructionData
          (G := G) (obs := obs))) :
    Nonempty
      (TrimmedPresentationExposingTransportConstructionData
        (G := G) (obs := obs)) :=
  nonempty_exposingConstruction_of_anchorCommonConstruction h

/-- Top-level construction diagram theorem: nonempty same-context construction
data implies nonempty exposing construction data. -/
theorem trimmed_transport_construction_diagram_same_context_to_exposing
    (h :
      Nonempty
        (TrimmedPresentationSameContextTransportConstructionData
          (G := G) (obs := obs))) :
    Nonempty
      (TrimmedPresentationExposingTransportConstructionData
        (G := G) (obs := obs)) :=
  nonempty_exposingConstruction_of_sameContextConstruction h

/-- Top-level theorem: nonempty anchor-common construction data gives
identification through the exposing route. -/
theorem trimmed_transport_construction_diagram_anchor_common_main_via_exposing
    (h :
      Nonempty
        (TrimmedPresentationAnchorCommonTransportConstructionData
          (G := G) (obs := obs))) :
    ExistsBoundedReachableIdentification G obs :=
  nonempty_anchorCommonConstruction_exposing_main_theorem h

/-- Top-level theorem: nonempty same-context construction data gives
identification through the exposing route. -/
theorem trimmed_transport_construction_diagram_same_context_main_via_exposing
    (h :
      Nonempty
        (TrimmedPresentationSameContextTransportConstructionData
          (G := G) (obs := obs))) :
    ExistsBoundedReachableIdentification G obs :=
  nonempty_sameContextConstruction_exposing_main_theorem h

end TransportConstructionDiagramTheorems

end MCFG
