/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG.CharacteristicSampleTransportConstructionChoice

/-!
# CharacteristicSampleTransportConstructionBase.lean

One-hundred-first clean Lean experiment for the fixed-observation MCFG project.

`CharacteristicSampleTransportConstructionChoice.lean` packaged the three
transport construction routes:

* exposing;
* anchor common-context;
* same-context.

Those construction packages still repeated a large common part:

```text
fanout bound
trimmed output-type presentation
pre-core data
grammar-rule builder
named-context splicing constructor
fanout and fixed-observation substitutability assumptions.
```

This file factors that common part into

```lean
TrimmedPresentationBaseConstructionData
```

and treats the transport witness as a separate choice over that base.

This gives the next construction-facing decomposition:

```text
BaseConstructionData
+
TransportWitnessChoice over that base
⇒ TransportConstructionChoice
⇒ ∃ f, reachable learner identifies the target.
```

No new mathematical principle is introduced here.

No theorem here uses `sorry`.
-/

namespace MCFG

universe u v w

section BaseConstructionData

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}

/-- Common construction data shared by all transport routes.

This record intentionally does not include any semantic transport witness. -/
structure TrimmedPresentationBaseConstructionData where
  fanoutBound : Nat
  presentation : TrimmedOutputTypePresentation G obs
  data : TrimmedPresentationPreCoreData presentation fanoutBound
  builder : TrimmedPresentationGrammarRuleBuilder data
  splicingConstructor : NamedContextSplicingConstructor α
  fanout : G.FanoutAtMost fanoutBound
  promise : FixedNamedTupleSubstitutable fanoutBound obs G.StringLanguage

namespace TrimmedPresentationBaseConstructionData

/-- Add direct exposing-context transport to base construction data. -/
def withExposingTransport
    (B : TrimmedPresentationBaseConstructionData
      (G := G) (obs := obs))
    (exposingTransport : TrimmedPresentationExposingContextTransport B.data) :
    TrimmedPresentationExposingTransportConstructionData
      (G := G) (obs := obs) where
  fanoutBound := B.fanoutBound
  presentation := B.presentation
  data := B.data
  builder := B.builder
  exposingTransport := exposingTransport
  splicingConstructor := B.splicingConstructor
  fanout := B.fanout
  promise := B.promise

/-- Add anchor common-context transport to base construction data. -/
def withAnchorCommonTransport
    (B : TrimmedPresentationBaseConstructionData
      (G := G) (obs := obs))
    (commonTransport : TrimmedPresentationAnchorCommonContextTransport B.data) :
    TrimmedPresentationAnchorCommonTransportConstructionData
      (G := G) (obs := obs) where
  fanoutBound := B.fanoutBound
  presentation := B.presentation
  data := B.data
  builder := B.builder
  commonTransport := commonTransport
  splicingConstructor := B.splicingConstructor
  fanout := B.fanout
  promise := B.promise

/-- Add same-context transport to base construction data. -/
def withSameContextTransport
    (B : TrimmedPresentationBaseConstructionData
      (G := G) (obs := obs))
    (sameContextTransport : TrimmedPresentationSameContextTransport B.data) :
    TrimmedPresentationSameContextTransportConstructionData
      (G := G) (obs := obs) where
  fanoutBound := B.fanoutBound
  presentation := B.presentation
  data := B.data
  builder := B.builder
  sameContextTransport := sameContextTransport
  splicingConstructor := B.splicingConstructor
  fanout := B.fanout
  promise := B.promise

end TrimmedPresentationBaseConstructionData

end BaseConstructionData


section TransportWitnessChoiceOverBase

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}

/-- A choice of semantic transport witness over a fixed base construction datum. -/
inductive TrimmedPresentationTransportWitnessChoice
    (B : TrimmedPresentationBaseConstructionData
      (G := G) (obs := obs)) where
  | exposing :
      TrimmedPresentationExposingContextTransport B.data →
      TrimmedPresentationTransportWitnessChoice B
  | anchorCommon :
      TrimmedPresentationAnchorCommonContextTransport B.data →
      TrimmedPresentationTransportWitnessChoice B
  | sameContext :
      TrimmedPresentationSameContextTransport B.data →
      TrimmedPresentationTransportWitnessChoice B

namespace TrimmedPresentationTransportWitnessChoice

variable {B : TrimmedPresentationBaseConstructionData
  (G := G) (obs := obs)}

/-- Convert a transport witness choice over a base datum to the previous
construction-choice package. -/
def toTransportConstructionChoice
    (W : TrimmedPresentationTransportWitnessChoice B) :
    TrimmedPresentationTransportConstructionChoice
      (G := G) (obs := obs) :=
  match W with
  | exposing E =>
      TrimmedPresentationTransportConstructionChoice.exposing
        (B.withExposingTransport E)
  | anchorCommon C =>
      TrimmedPresentationTransportConstructionChoice.anchorCommon
        (B.withAnchorCommonTransport C)
  | sameContext S =>
      TrimmedPresentationTransportConstructionChoice.sameContext
        (B.withSameContextTransport S)

/-- Convert a witness choice to direct exposing construction data. -/
def toExposingTransportConstructionData
    (W : TrimmedPresentationTransportWitnessChoice B) :
    TrimmedPresentationExposingTransportConstructionData
      (G := G) (obs := obs) :=
  W.toTransportConstructionChoice.toExposingTransportConstructionData

/-- A witness choice gives a finite positive characteristic sample for some
finite fanout bound. -/
theorem exists_bounded_positive_characteristic_sample
    (W : TrimmedPresentationTransportWitnessChoice B) :
    ExistsBoundedPositiveCharacteristicSample G obs :=
  W.toTransportConstructionChoice.exists_bounded_positive_characteristic_sample

/-- A witness choice gives eventual prefix exactness for some finite fanout
bound. -/
theorem exists_bounded_prefix_exact_identification
    (W : TrimmedPresentationTransportWitnessChoice B) :
    ExistsBoundedPrefixExactIdentification G obs :=
  W.toTransportConstructionChoice.exists_bounded_prefix_exact_identification

/-- A witness choice gives Gold-style identification for some finite fanout
bound. -/
theorem exists_bounded_reachable_identification
    (W : TrimmedPresentationTransportWitnessChoice B) :
    ExistsBoundedReachableIdentification G obs :=
  W.toTransportConstructionChoice.exists_bounded_reachable_identification

/-- A witness choice gives Gold-style identification through the exposing route. -/
theorem exists_bounded_reachable_identification_via_exposing
    (W : TrimmedPresentationTransportWitnessChoice B) :
    ExistsBoundedReachableIdentification G obs :=
  W.toTransportConstructionChoice
    .exists_bounded_reachable_identification_via_exposing

end TrimmedPresentationTransportWitnessChoice

end TransportWitnessChoiceOverBase


section StructuredTransportConstructionData

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}

/-- Structured construction data: a common base plus one chosen transport
witness over that base. -/
structure TrimmedPresentationStructuredTransportConstructionData where
  base : TrimmedPresentationBaseConstructionData
    (G := G) (obs := obs)
  transport : TrimmedPresentationTransportWitnessChoice base

namespace TrimmedPresentationStructuredTransportConstructionData

/-- Convert structured construction data to the previous construction-choice
package. -/
def toTransportConstructionChoice
    (C : TrimmedPresentationStructuredTransportConstructionData
      (G := G) (obs := obs)) :
    TrimmedPresentationTransportConstructionChoice
      (G := G) (obs := obs) :=
  C.transport.toTransportConstructionChoice

/-- Convert structured construction data to exposing construction data. -/
def toExposingTransportConstructionData
    (C : TrimmedPresentationStructuredTransportConstructionData
      (G := G) (obs := obs)) :
    TrimmedPresentationExposingTransportConstructionData
      (G := G) (obs := obs) :=
  C.toTransportConstructionChoice.toExposingTransportConstructionData

/-- The fanout bound selected by the base datum. -/
def fanoutBound
    (C : TrimmedPresentationStructuredTransportConstructionData
      (G := G) (obs := obs)) : Nat :=
  C.base.fanoutBound

/-- A structured construction datum gives a finite positive characteristic
sample for some finite fanout bound. -/
theorem exists_bounded_positive_characteristic_sample
    (C : TrimmedPresentationStructuredTransportConstructionData
      (G := G) (obs := obs)) :
    ExistsBoundedPositiveCharacteristicSample G obs :=
  C.toTransportConstructionChoice.exists_bounded_positive_characteristic_sample

/-- A structured construction datum gives eventual prefix exactness for some
finite fanout bound. -/
theorem exists_bounded_prefix_exact_identification
    (C : TrimmedPresentationStructuredTransportConstructionData
      (G := G) (obs := obs)) :
    ExistsBoundedPrefixExactIdentification G obs :=
  C.toTransportConstructionChoice.exists_bounded_prefix_exact_identification

/-- A structured construction datum gives Gold-style identification for some
finite fanout bound. -/
theorem exists_bounded_reachable_identification
    (C : TrimmedPresentationStructuredTransportConstructionData
      (G := G) (obs := obs)) :
    ExistsBoundedReachableIdentification G obs :=
  C.toTransportConstructionChoice.exists_bounded_reachable_identification

/-- A structured construction datum gives Gold-style identification through the
exposing route. -/
theorem exists_bounded_reachable_identification_via_exposing
    (C : TrimmedPresentationStructuredTransportConstructionData
      (G := G) (obs := obs)) :
    ExistsBoundedReachableIdentification G obs :=
  C.toTransportConstructionChoice
    .exists_bounded_reachable_identification_via_exposing

end TrimmedPresentationStructuredTransportConstructionData

end StructuredTransportConstructionData


section BaseConstructionTheorems

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}

/-- Top-level theorem: base construction data plus a transport witness choice
gives a positive characteristic sample for some bound. -/
theorem trimmed_base_transport_choice_exists_characteristic_sample
    (B : TrimmedPresentationBaseConstructionData
      (G := G) (obs := obs))
    (W : TrimmedPresentationTransportWitnessChoice B) :
    ExistsBoundedPositiveCharacteristicSample G obs :=
  W.exists_bounded_positive_characteristic_sample

/-- Top-level theorem: base construction data plus a transport witness choice
gives eventual prefix exactness for some bound. -/
theorem trimmed_base_transport_choice_prefix_exact_theorem
    (B : TrimmedPresentationBaseConstructionData
      (G := G) (obs := obs))
    (W : TrimmedPresentationTransportWitnessChoice B) :
    ExistsBoundedPrefixExactIdentification G obs :=
  W.exists_bounded_prefix_exact_identification

/-- Top-level theorem: base construction data plus a transport witness choice
gives Gold-style identification for some bound. -/
theorem trimmed_base_transport_choice_main_theorem
    (B : TrimmedPresentationBaseConstructionData
      (G := G) (obs := obs))
    (W : TrimmedPresentationTransportWitnessChoice B) :
    ExistsBoundedReachableIdentification G obs :=
  W.exists_bounded_reachable_identification

/-- Top-level theorem: structured construction data gives Gold-style
identification for some bound. -/
theorem trimmed_structured_transport_construction_main_theorem
    (C : TrimmedPresentationStructuredTransportConstructionData
      (G := G) (obs := obs)) :
    ExistsBoundedReachableIdentification G obs :=
  C.exists_bounded_reachable_identification

/-- Nonempty structured construction data gives Gold-style identification for
some bound. -/
theorem trimmed_structured_transport_construction_main_theorem_of_nonempty
    (h :
      Nonempty
        (TrimmedPresentationStructuredTransportConstructionData
          (G := G) (obs := obs))) :
    ExistsBoundedReachableIdentification G obs :=
  match h with
  | ⟨C⟩ => C.exists_bounded_reachable_identification

end BaseConstructionTheorems

end MCFG
