/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG2.CharacteristicSampleTransportConstructionBase

/-!
# CharacteristicSampleTransportConstructionExistential.lean

One-hundred-second clean Lean experiment for the fixed-observation MCFG project.

`CharacteristicSampleTransportConstructionBase.lean` factored the construction
problem into:

```text
BaseConstructionData
+
TransportWitnessChoice over that base.
```

This file packages the corresponding existential interface:

```text
∃ base, Nonempty (TransportWitnessChoice base)
⇒ ExistsBoundedReachableIdentification.
```

This is useful for the next phase because the construction can now be attacked
in two independent-looking parts:

1. construct the common base data;
2. construct any one of the transport witnesses over that base.

No new mathematical principle is introduced here.

No theorem here uses `sorry`.
-/

namespace MCFG

universe u v w

section ExistentialBaseTransportConstruction

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}

/-- There exists base construction data and some transport witness choice over
that base. -/
def ExistsBaseWithTransportWitnessChoice
    (G : WorkingMCFG N α) (obs : α → M) : Prop :=
  ∃ B : TrimmedPresentationBaseConstructionData
      (G := G) (obs := obs),
    Nonempty (TrimmedPresentationTransportWitnessChoice B)

/-- There exists base construction data and a direct exposing-context transport
witness over that base. -/
def ExistsBaseWithExposingTransport
    (G : WorkingMCFG N α) (obs : α → M) : Prop :=
  ∃ B : TrimmedPresentationBaseConstructionData
      (G := G) (obs := obs),
    Nonempty (TrimmedPresentationExposingContextTransport B.data)

/-- There exists base construction data and an anchor common-context transport
witness over that base. -/
def ExistsBaseWithAnchorCommonTransport
    (G : WorkingMCFG N α) (obs : α → M) : Prop :=
  ∃ B : TrimmedPresentationBaseConstructionData
      (G := G) (obs := obs),
    Nonempty (TrimmedPresentationAnchorCommonContextTransport B.data)

/-- There exists base construction data and a same-context transport witness
over that base. -/
def ExistsBaseWithSameContextTransport
    (G : WorkingMCFG N α) (obs : α → M) : Prop :=
  ∃ B : TrimmedPresentationBaseConstructionData
      (G := G) (obs := obs),
    Nonempty (TrimmedPresentationSameContextTransport B.data)

/-- Direct exposing transport over a base gives a transport-witness choice over
that base. -/
theorem existsBaseWithTransportWitnessChoice_of_exposing
    (h : ExistsBaseWithExposingTransport G obs) :
    ExistsBaseWithTransportWitnessChoice G obs :=
  match h with
  | ⟨B, hE⟩ =>
      match hE with
      | ⟨E⟩ =>
          ⟨B, ⟨TrimmedPresentationTransportWitnessChoice.exposing E⟩⟩

/-- Anchor common-context transport over a base gives a transport-witness choice
over that base. -/
theorem existsBaseWithTransportWitnessChoice_of_anchorCommon
    (h : ExistsBaseWithAnchorCommonTransport G obs) :
    ExistsBaseWithTransportWitnessChoice G obs :=
  match h with
  | ⟨B, hC⟩ =>
      match hC with
      | ⟨C⟩ =>
          ⟨B, ⟨TrimmedPresentationTransportWitnessChoice.anchorCommon C⟩⟩

/-- Same-context transport over a base gives a transport-witness choice over
that base. -/
theorem existsBaseWithTransportWitnessChoice_of_sameContext
    (h : ExistsBaseWithSameContextTransport G obs) :
    ExistsBaseWithTransportWitnessChoice G obs :=
  match h with
  | ⟨B, hS⟩ =>
      match hS with
      | ⟨S⟩ =>
          ⟨B, ⟨TrimmedPresentationTransportWitnessChoice.sameContext S⟩⟩

/-- A base plus a transport-witness choice gives structured construction data. -/
def structuredTransportConstructionData
    (B : TrimmedPresentationBaseConstructionData
      (G := G) (obs := obs))
    (W : TrimmedPresentationTransportWitnessChoice B) :
    TrimmedPresentationStructuredTransportConstructionData
      (G := G) (obs := obs) where
  base := B
  transport := W

/-- Nonempty transport-witness choice over a given base gives nonempty structured
construction data. -/
theorem nonempty_structuredTransportConstructionData_of_base
    (B : TrimmedPresentationBaseConstructionData
      (G := G) (obs := obs))
    (hW : Nonempty (TrimmedPresentationTransportWitnessChoice B)) :
    Nonempty
      (TrimmedPresentationStructuredTransportConstructionData
        (G := G) (obs := obs)) :=
  match hW with
  | ⟨W⟩ => ⟨structuredTransportConstructionData B W⟩

/-- Existential base plus transport-witness choice gives nonempty structured
construction data. -/
theorem nonempty_structuredTransportConstructionData_of_existsBase
    (h : ExistsBaseWithTransportWitnessChoice G obs) :
    Nonempty
      (TrimmedPresentationStructuredTransportConstructionData
        (G := G) (obs := obs)) :=
  match h with
  | ⟨B, hW⟩ => nonempty_structuredTransportConstructionData_of_base B hW

/-- Existential base plus direct exposing transport gives nonempty structured
construction data. -/
theorem nonempty_structuredTransportConstructionData_of_exposing
    (h : ExistsBaseWithExposingTransport G obs) :
    Nonempty
      (TrimmedPresentationStructuredTransportConstructionData
        (G := G) (obs := obs)) :=
  nonempty_structuredTransportConstructionData_of_existsBase
    (existsBaseWithTransportWitnessChoice_of_exposing h)

/-- Existential base plus anchor common-context transport gives nonempty
structured construction data. -/
theorem nonempty_structuredTransportConstructionData_of_anchorCommon
    (h : ExistsBaseWithAnchorCommonTransport G obs) :
    Nonempty
      (TrimmedPresentationStructuredTransportConstructionData
        (G := G) (obs := obs)) :=
  nonempty_structuredTransportConstructionData_of_existsBase
    (existsBaseWithTransportWitnessChoice_of_anchorCommon h)

/-- Existential base plus same-context transport gives nonempty structured
construction data. -/
theorem nonempty_structuredTransportConstructionData_of_sameContext
    (h : ExistsBaseWithSameContextTransport G obs) :
    Nonempty
      (TrimmedPresentationStructuredTransportConstructionData
        (G := G) (obs := obs)) :=
  nonempty_structuredTransportConstructionData_of_existsBase
    (existsBaseWithTransportWitnessChoice_of_sameContext h)

/-- Main theorem from the existential base-plus-transport interface. -/
theorem existsBaseWithTransportWitnessChoice_main_theorem
    (h : ExistsBaseWithTransportWitnessChoice G obs) :
    ExistsBoundedReachableIdentification G obs :=
  trimmed_structured_transport_construction_main_theorem_of_nonempty
    (nonempty_structuredTransportConstructionData_of_existsBase h)

/-- Prefix-exact theorem from the existential base-plus-transport interface. -/
theorem existsBaseWithTransportWitnessChoice_prefix_exact
    (h : ExistsBaseWithTransportWitnessChoice G obs) :
    ExistsBoundedPrefixExactIdentification G obs :=
  match h with
  | ⟨B, hW⟩ =>
      match hW with
      | ⟨W⟩ => W.exists_bounded_prefix_exact_identification

/-- Characteristic-sample theorem from the existential base-plus-transport
interface. -/
theorem existsBaseWithTransportWitnessChoice_characteristic_sample
    (h : ExistsBaseWithTransportWitnessChoice G obs) :
    ExistsBoundedPositiveCharacteristicSample G obs :=
  match h with
  | ⟨B, hW⟩ =>
      match hW with
      | ⟨W⟩ => W.exists_bounded_positive_characteristic_sample

/-- Main theorem from an existential base plus direct exposing transport. -/
theorem existsBaseWithExposingTransport_main_theorem
    (h : ExistsBaseWithExposingTransport G obs) :
    ExistsBoundedReachableIdentification G obs :=
  existsBaseWithTransportWitnessChoice_main_theorem
    (existsBaseWithTransportWitnessChoice_of_exposing h)

/-- Main theorem from an existential base plus anchor common-context transport. -/
theorem existsBaseWithAnchorCommonTransport_main_theorem
    (h : ExistsBaseWithAnchorCommonTransport G obs) :
    ExistsBoundedReachableIdentification G obs :=
  existsBaseWithTransportWitnessChoice_main_theorem
    (existsBaseWithTransportWitnessChoice_of_anchorCommon h)

/-- Main theorem from an existential base plus same-context transport. -/
theorem existsBaseWithSameContextTransport_main_theorem
    (h : ExistsBaseWithSameContextTransport G obs) :
    ExistsBoundedReachableIdentification G obs :=
  existsBaseWithTransportWitnessChoice_main_theorem
    (existsBaseWithTransportWitnessChoice_of_sameContext h)

end ExistentialBaseTransportConstruction


section ExistentialBaseTransportConstructionTopLevel

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}

/-- Top-level theorem: if there exists base construction data with some
transport witness choice over it, then the reachable learner identifies the
target for some finite bound. -/
theorem trimmed_exists_base_transport_choice_main_theorem
    (h : ExistsBaseWithTransportWitnessChoice G obs) :
    ExistsBoundedReachableIdentification G obs :=
  existsBaseWithTransportWitnessChoice_main_theorem h

/-- Top-level theorem: if there exists base construction data with direct
exposing transport, then the reachable learner identifies the target for some
finite bound. -/
theorem trimmed_exists_base_exposing_transport_main_theorem
    (h : ExistsBaseWithExposingTransport G obs) :
    ExistsBoundedReachableIdentification G obs :=
  existsBaseWithExposingTransport_main_theorem h

/-- Top-level theorem: if there exists base construction data with anchor
common-context transport, then the reachable learner identifies the target for
some finite bound. -/
theorem trimmed_exists_base_anchor_common_transport_main_theorem
    (h : ExistsBaseWithAnchorCommonTransport G obs) :
    ExistsBoundedReachableIdentification G obs :=
  existsBaseWithAnchorCommonTransport_main_theorem h

/-- Top-level theorem: if there exists base construction data with same-context
transport, then the reachable learner identifies the target for some finite
bound. -/
theorem trimmed_exists_base_same_context_transport_main_theorem
    (h : ExistsBaseWithSameContextTransport G obs) :
    ExistsBoundedReachableIdentification G obs :=
  existsBaseWithSameContextTransport_main_theorem h

/-- Top-level prefix-exact theorem for the base-plus-transport interface. -/
theorem trimmed_exists_base_transport_choice_prefix_exact_theorem
    (h : ExistsBaseWithTransportWitnessChoice G obs) :
    ExistsBoundedPrefixExactIdentification G obs :=
  existsBaseWithTransportWitnessChoice_prefix_exact h

/-- Top-level characteristic-sample theorem for the base-plus-transport
interface. -/
theorem trimmed_exists_base_transport_choice_characteristic_sample
    (h : ExistsBaseWithTransportWitnessChoice G obs) :
    ExistsBoundedPositiveCharacteristicSample G obs :=
  existsBaseWithTransportWitnessChoice_characteristic_sample h

end ExistentialBaseTransportConstructionTopLevel

end MCFG
