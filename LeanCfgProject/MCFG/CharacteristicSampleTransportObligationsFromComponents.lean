/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG.CharacteristicSampleTransportObligationsFromBuilders

/-!
# CharacteristicSampleTransportObligationsFromComponents.lean

Seventy-fifth clean Lean experiment for the fixed-observation MCFG project.

`CharacteristicSampleTransportObligationsFromBuilders.lean` connected the
transport-obligation routes to finite builders and positive finite-union
builders.

This file moves one level higher in the construction hierarchy.  It connects
the transport-obligation routes to:

* `TrimmedPresentationComponentPackage`;
* `TrimmedPresentationComponentEnumeration`.

Thus the route becomes:

```text
component package / component enumeration
⇒ positive finite-union builder
⇒ finite builder / witness sample
⇒ transport obligations
⇒ reachable identification.
```

No new semantic principle is introduced here.  The purpose is to make the
future componentwise construction of `CS(G̃₀)` feed directly into the final
transport theorem.

No theorem here uses `sorry`.
-/

namespace MCFG

universe u v w

section ExposingTransportFromComponentPackage

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}
variable {f : Nat}
variable {T : TrimmedOutputTypePresentation G obs}

/-- Exposing-context transport obligations whose sample side is supplied by a
component package. -/
structure TrimmedPresentationExposingTransportFromComponentPackage
    (D : TrimmedPresentationPreCoreData T f) where
  components : TrimmedPresentationComponentPackage D

  baseNonterminals : Finset N
  base_covers :
    ∀ A : N, A ∈ baseNonterminals

  arities : TrimmedPresentationRuleAritySelectors D
  exposingTransport : TrimmedPresentationExposingContextTransport D

  splicingConstructor : NamedContextSplicingConstructor α
  fanout : G.FanoutAtMost f
  promise : FixedNamedTupleSubstitutable f obs G.StringLanguage

namespace TrimmedPresentationExposingTransportFromComponentPackage

variable {D : TrimmedPresentationPreCoreData T f}

/-- The positive finite-union builder induced by the component package. -/
def toPositiveFiniteUnionBuilder
    (O : TrimmedPresentationExposingTransportFromComponentPackage D) :
    TrimmedPresentationPositiveFiniteUnionBuilder D :=
  O.components.toPositiveFiniteUnionBuilder

/-- Convert to the positive finite-union transport route. -/
def toTransportFromPositiveFiniteUnionBuilder
    (O : TrimmedPresentationExposingTransportFromComponentPackage D) :
    TrimmedPresentationExposingTransportFromPositiveFiniteUnionBuilder D where
  unionBuilder := O.toPositiveFiniteUnionBuilder
  baseNonterminals := O.baseNonterminals
  base_covers := O.base_covers
  arities := O.arities
  exposingTransport := O.exposingTransport
  splicingConstructor := O.splicingConstructor
  fanout := O.fanout
  promise := O.promise

/-- Convert to the finite-builder transport route. -/
def toTransportFromFiniteBuilder
    (O : TrimmedPresentationExposingTransportFromComponentPackage D) :
    TrimmedPresentationExposingTransportFromFiniteBuilder D :=
  O.toTransportFromPositiveFiniteUnionBuilder.toTransportFromFiniteBuilder

/-- Convert to the existing witness-sample transport route. -/
def toTransportFromWitnessSample
    (O : TrimmedPresentationExposingTransportFromComponentPackage D) :
    TrimmedPresentationExposingTransportFromWitnessSample
      D O.toTransportFromFiniteBuilder.builder.sample :=
  O.toTransportFromFiniteBuilder.toTransportFromWitnessSample

/-- Convert to the compact exposing-transport obligation package. -/
def toObligations
    (O : TrimmedPresentationExposingTransportFromComponentPackage D) :
    TrimmedPresentationExposingTransportObligations D :=
  O.toTransportFromFiniteBuilder.toObligations

/-- The finite sample produced by the resulting obligation package. -/
def sample
    (O : TrimmedPresentationExposingTransportFromComponentPackage D) :
    Finset (Word α) :=
  O.toTransportFromPositiveFiniteUnionBuilder.sample

/-- The produced finite sample is positive. -/
theorem sample_positive
    (O : TrimmedPresentationExposingTransportFromComponentPackage D) :
    (O.sample : Set (Word α)) ⊆ G.StringLanguage :=
  O.toTransportFromPositiveFiniteUnionBuilder.sample_positive

/-- The component package supplies distinguished start-word positivity through
the positive-union route. -/
theorem startWord_positive
    (O : TrimmedPresentationExposingTransportFromComponentPackage D) :
    D.startWord ∈ G.StringLanguage :=
  O.toTransportFromPositiveFiniteUnionBuilder.startWord_positive

/-- The produced finite sample contains all required witness words. -/
theorem contains_witnesses
    (O : TrimmedPresentationExposingTransportFromComponentPackage D) :
    TrimmedPresentationWitnessWordSet D ⊆
      (O.sample : Set (Word α)) :=
  O.toTransportFromPositiveFiniteUnionBuilder.contains_witnesses

/-- Convert directly to final reachable data. -/
def toFinalReachableData
    (O : TrimmedPresentationExposingTransportFromComponentPackage D) :
    FinalReachableData G O.sample obs f :=
  O.toTransportFromPositiveFiniteUnionBuilder.toFinalReachableData

/-- The produced sample is a characteristic sample for the reachable learner. -/
theorem characteristic_sample
    (O : TrimmedPresentationExposingTransportFromComponentPackage D) :
    CharacteristicSample
      (reachableHypLanguage obs f)
      (reachableSampleLearner (α := α))
      O.sample
      G.StringLanguage :=
  O.toTransportFromPositiveFiniteUnionBuilder.characteristic_sample

/-- Eventual prefix-exact reconstruction. -/
theorem prefix_exact_eventually
    (O : TrimmedPresentationExposingTransportFromComponentPackage D) :
    ∀ Ttxt : TextFor G.StringLanguage,
      ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
        ReachableSampleStringLanguage (Ttxt.prefixSample n) obs f =
          G.StringLanguage :=
  O.toTransportFromPositiveFiniteUnionBuilder.prefix_exact_eventually

/-- Reachable Gold identification. -/
theorem identifies_from_positive_text
    (O : TrimmedPresentationExposingTransportFromComponentPackage D) :
    ∀ Ttxt : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        Ttxt :=
  O.toTransportFromPositiveFiniteUnionBuilder.identifies_from_positive_text

end TrimmedPresentationExposingTransportFromComponentPackage

end ExposingTransportFromComponentPackage


section CommonContextFromComponentPackage

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}
variable {f : Nat}
variable {T : TrimmedOutputTypePresentation G obs}

/-- Common-context transport obligations whose sample side is supplied by a
component package. -/
structure TrimmedPresentationCommonContextFromComponentPackage
    (D : TrimmedPresentationPreCoreData T f) where
  components : TrimmedPresentationComponentPackage D

  commonData : TrimmedPresentationAnchorCommonContextCoreData D
  splicingConstructor : NamedContextSplicingConstructor α
  fanout : G.FanoutAtMost f
  promise : FixedNamedTupleSubstitutable f obs G.StringLanguage

namespace TrimmedPresentationCommonContextFromComponentPackage

variable {D : TrimmedPresentationPreCoreData T f}

/-- The positive finite-union builder induced by the component package. -/
def toPositiveFiniteUnionBuilder
    (O : TrimmedPresentationCommonContextFromComponentPackage D) :
    TrimmedPresentationPositiveFiniteUnionBuilder D :=
  O.components.toPositiveFiniteUnionBuilder

/-- Convert to the positive finite-union common-context route. -/
def toTransportFromPositiveFiniteUnionBuilder
    (O : TrimmedPresentationCommonContextFromComponentPackage D) :
    TrimmedPresentationCommonContextFromPositiveFiniteUnionBuilder D where
  unionBuilder := O.toPositiveFiniteUnionBuilder
  commonData := O.commonData
  splicingConstructor := O.splicingConstructor
  fanout := O.fanout
  promise := O.promise

/-- Convert to the finite-builder common-context route. -/
def toTransportFromFiniteBuilder
    (O : TrimmedPresentationCommonContextFromComponentPackage D) :
    TrimmedPresentationCommonContextFromFiniteBuilder D :=
  O.toTransportFromPositiveFiniteUnionBuilder.toTransportFromFiniteBuilder

/-- Convert to the existing witness-sample common-context route. -/
def toTransportFromWitnessSample
    (O : TrimmedPresentationCommonContextFromComponentPackage D) :
    TrimmedPresentationCommonContextFromWitnessSample
      D O.toTransportFromFiniteBuilder.builder.sample :=
  O.toTransportFromFiniteBuilder.toTransportFromWitnessSample

/-- Convert to the compact common-context obligation package. -/
def toObligations
    (O : TrimmedPresentationCommonContextFromComponentPackage D) :
    TrimmedPresentationCommonContextTransportObligations D :=
  O.toTransportFromFiniteBuilder.toObligations

/-- Convert to exposing-transport obligations through the common-context route. -/
def toExposingTransportObligations
    (O : TrimmedPresentationCommonContextFromComponentPackage D) :
    TrimmedPresentationExposingTransportObligations D :=
  O.toTransportFromFiniteBuilder.toExposingTransportObligations

/-- The finite sample produced by the resulting obligation package. -/
def sample
    (O : TrimmedPresentationCommonContextFromComponentPackage D) :
    Finset (Word α) :=
  O.toTransportFromPositiveFiniteUnionBuilder.sample

/-- The produced finite sample is positive. -/
theorem sample_positive
    (O : TrimmedPresentationCommonContextFromComponentPackage D) :
    (O.sample : Set (Word α)) ⊆ G.StringLanguage :=
  O.toTransportFromPositiveFiniteUnionBuilder.sample_positive

/-- The component package supplies distinguished start-word positivity through
the positive-union route. -/
theorem startWord_positive
    (O : TrimmedPresentationCommonContextFromComponentPackage D) :
    D.startWord ∈ G.StringLanguage :=
  O.toTransportFromPositiveFiniteUnionBuilder.startWord_positive

/-- The produced finite sample contains all required witness words. -/
theorem contains_witnesses
    (O : TrimmedPresentationCommonContextFromComponentPackage D) :
    TrimmedPresentationWitnessWordSet D ⊆
      (O.sample : Set (Word α)) :=
  O.toTransportFromPositiveFiniteUnionBuilder.contains_witnesses

/-- Convert directly to final reachable data. -/
def toFinalReachableData
    (O : TrimmedPresentationCommonContextFromComponentPackage D) :
    FinalReachableData G O.sample obs f :=
  O.toTransportFromPositiveFiniteUnionBuilder.toFinalReachableData

/-- The produced sample is a characteristic sample for the reachable learner. -/
theorem characteristic_sample
    (O : TrimmedPresentationCommonContextFromComponentPackage D) :
    CharacteristicSample
      (reachableHypLanguage obs f)
      (reachableSampleLearner (α := α))
      O.sample
      G.StringLanguage :=
  O.toTransportFromPositiveFiniteUnionBuilder.characteristic_sample

/-- Eventual prefix-exact reconstruction. -/
theorem prefix_exact_eventually
    (O : TrimmedPresentationCommonContextFromComponentPackage D) :
    ∀ Ttxt : TextFor G.StringLanguage,
      ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
        ReachableSampleStringLanguage (Ttxt.prefixSample n) obs f =
          G.StringLanguage :=
  O.toTransportFromPositiveFiniteUnionBuilder.prefix_exact_eventually

/-- Reachable Gold identification. -/
theorem identifies_from_positive_text
    (O : TrimmedPresentationCommonContextFromComponentPackage D) :
    ∀ Ttxt : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        Ttxt :=
  O.toTransportFromPositiveFiniteUnionBuilder.identifies_from_positive_text

end TrimmedPresentationCommonContextFromComponentPackage

end CommonContextFromComponentPackage


section ExposingTransportFromComponentEnumeration

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}
variable {f : Nat}
variable {T : TrimmedOutputTypePresentation G obs}

/-- Exposing-context transport obligations whose sample side is supplied by a
component enumeration. -/
structure TrimmedPresentationExposingTransportFromComponentEnumeration
    (D : TrimmedPresentationPreCoreData T f) where
  enumeration : TrimmedPresentationComponentEnumeration D

  baseNonterminals : Finset N
  base_covers :
    ∀ A : N, A ∈ baseNonterminals

  arities : TrimmedPresentationRuleAritySelectors D
  exposingTransport : TrimmedPresentationExposingContextTransport D

  splicingConstructor : NamedContextSplicingConstructor α
  fanout : G.FanoutAtMost f
  promise : FixedNamedTupleSubstitutable f obs G.StringLanguage

namespace TrimmedPresentationExposingTransportFromComponentEnumeration

variable {D : TrimmedPresentationPreCoreData T f}

/-- The component package induced by the enumeration. -/
def toComponentPackage
    (O : TrimmedPresentationExposingTransportFromComponentEnumeration D) :
    TrimmedPresentationComponentPackage D :=
  O.enumeration.toComponentPackage

/-- Convert to the component-package transport route. -/
def toTransportFromComponentPackage
    (O : TrimmedPresentationExposingTransportFromComponentEnumeration D) :
    TrimmedPresentationExposingTransportFromComponentPackage D where
  components := O.toComponentPackage
  baseNonterminals := O.baseNonterminals
  base_covers := O.base_covers
  arities := O.arities
  exposingTransport := O.exposingTransport
  splicingConstructor := O.splicingConstructor
  fanout := O.fanout
  promise := O.promise

/-- Convert to the positive finite-union transport route. -/
def toTransportFromPositiveFiniteUnionBuilder
    (O : TrimmedPresentationExposingTransportFromComponentEnumeration D) :
    TrimmedPresentationExposingTransportFromPositiveFiniteUnionBuilder D :=
  O.toTransportFromComponentPackage.toTransportFromPositiveFiniteUnionBuilder

/-- Convert to the compact exposing-transport obligation package. -/
def toObligations
    (O : TrimmedPresentationExposingTransportFromComponentEnumeration D) :
    TrimmedPresentationExposingTransportObligations D :=
  O.toTransportFromComponentPackage.toObligations

/-- The finite sample produced by the resulting obligation package. -/
def sample
    (O : TrimmedPresentationExposingTransportFromComponentEnumeration D) :
    Finset (Word α) :=
  O.toTransportFromComponentPackage.sample

/-- The produced finite sample is positive. -/
theorem sample_positive
    (O : TrimmedPresentationExposingTransportFromComponentEnumeration D) :
    (O.sample : Set (Word α)) ⊆ G.StringLanguage :=
  O.toTransportFromComponentPackage.sample_positive

/-- The produced finite sample contains all required witness words. -/
theorem contains_witnesses
    (O : TrimmedPresentationExposingTransportFromComponentEnumeration D) :
    TrimmedPresentationWitnessWordSet D ⊆
      (O.sample : Set (Word α)) :=
  O.toTransportFromComponentPackage.contains_witnesses

/-- Convert directly to final reachable data. -/
def toFinalReachableData
    (O : TrimmedPresentationExposingTransportFromComponentEnumeration D) :
    FinalReachableData G O.sample obs f :=
  O.toTransportFromComponentPackage.toFinalReachableData

/-- The produced sample is a characteristic sample for the reachable learner. -/
theorem characteristic_sample
    (O : TrimmedPresentationExposingTransportFromComponentEnumeration D) :
    CharacteristicSample
      (reachableHypLanguage obs f)
      (reachableSampleLearner (α := α))
      O.sample
      G.StringLanguage :=
  O.toTransportFromComponentPackage.characteristic_sample

/-- Eventual prefix-exact reconstruction. -/
theorem prefix_exact_eventually
    (O : TrimmedPresentationExposingTransportFromComponentEnumeration D) :
    ∀ Ttxt : TextFor G.StringLanguage,
      ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
        ReachableSampleStringLanguage (Ttxt.prefixSample n) obs f =
          G.StringLanguage :=
  O.toTransportFromComponentPackage.prefix_exact_eventually

/-- Reachable Gold identification. -/
theorem identifies_from_positive_text
    (O : TrimmedPresentationExposingTransportFromComponentEnumeration D) :
    ∀ Ttxt : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        Ttxt :=
  O.toTransportFromComponentPackage.identifies_from_positive_text

end TrimmedPresentationExposingTransportFromComponentEnumeration

end ExposingTransportFromComponentEnumeration


section CommonContextFromComponentEnumeration

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}
variable {f : Nat}
variable {T : TrimmedOutputTypePresentation G obs}

/-- Common-context transport obligations whose sample side is supplied by a
component enumeration. -/
structure TrimmedPresentationCommonContextFromComponentEnumeration
    (D : TrimmedPresentationPreCoreData T f) where
  enumeration : TrimmedPresentationComponentEnumeration D

  commonData : TrimmedPresentationAnchorCommonContextCoreData D
  splicingConstructor : NamedContextSplicingConstructor α
  fanout : G.FanoutAtMost f
  promise : FixedNamedTupleSubstitutable f obs G.StringLanguage

namespace TrimmedPresentationCommonContextFromComponentEnumeration

variable {D : TrimmedPresentationPreCoreData T f}

/-- The component package induced by the enumeration. -/
def toComponentPackage
    (O : TrimmedPresentationCommonContextFromComponentEnumeration D) :
    TrimmedPresentationComponentPackage D :=
  O.enumeration.toComponentPackage

/-- Convert to the component-package common-context route. -/
def toTransportFromComponentPackage
    (O : TrimmedPresentationCommonContextFromComponentEnumeration D) :
    TrimmedPresentationCommonContextFromComponentPackage D where
  components := O.toComponentPackage
  commonData := O.commonData
  splicingConstructor := O.splicingConstructor
  fanout := O.fanout
  promise := O.promise

/-- Convert to the positive finite-union common-context route. -/
def toTransportFromPositiveFiniteUnionBuilder
    (O : TrimmedPresentationCommonContextFromComponentEnumeration D) :
    TrimmedPresentationCommonContextFromPositiveFiniteUnionBuilder D :=
  O.toTransportFromComponentPackage.toTransportFromPositiveFiniteUnionBuilder

/-- Convert to the compact common-context obligation package. -/
def toObligations
    (O : TrimmedPresentationCommonContextFromComponentEnumeration D) :
    TrimmedPresentationCommonContextTransportObligations D :=
  O.toTransportFromComponentPackage.toObligations

/-- Convert to exposing-transport obligations through the common-context route. -/
def toExposingTransportObligations
    (O : TrimmedPresentationCommonContextFromComponentEnumeration D) :
    TrimmedPresentationExposingTransportObligations D :=
  O.toTransportFromComponentPackage.toExposingTransportObligations

/-- The finite sample produced by the resulting obligation package. -/
def sample
    (O : TrimmedPresentationCommonContextFromComponentEnumeration D) :
    Finset (Word α) :=
  O.toTransportFromComponentPackage.sample

/-- The produced finite sample is positive. -/
theorem sample_positive
    (O : TrimmedPresentationCommonContextFromComponentEnumeration D) :
    (O.sample : Set (Word α)) ⊆ G.StringLanguage :=
  O.toTransportFromComponentPackage.sample_positive

/-- The produced finite sample contains all required witness words. -/
theorem contains_witnesses
    (O : TrimmedPresentationCommonContextFromComponentEnumeration D) :
    TrimmedPresentationWitnessWordSet D ⊆
      (O.sample : Set (Word α)) :=
  O.toTransportFromComponentPackage.contains_witnesses

/-- Convert directly to final reachable data. -/
def toFinalReachableData
    (O : TrimmedPresentationCommonContextFromComponentEnumeration D) :
    FinalReachableData G O.sample obs f :=
  O.toTransportFromComponentPackage.toFinalReachableData

/-- The produced sample is a characteristic sample for the reachable learner. -/
theorem characteristic_sample
    (O : TrimmedPresentationCommonContextFromComponentEnumeration D) :
    CharacteristicSample
      (reachableHypLanguage obs f)
      (reachableSampleLearner (α := α))
      O.sample
      G.StringLanguage :=
  O.toTransportFromComponentPackage.characteristic_sample

/-- Eventual prefix-exact reconstruction. -/
theorem prefix_exact_eventually
    (O : TrimmedPresentationCommonContextFromComponentEnumeration D) :
    ∀ Ttxt : TextFor G.StringLanguage,
      ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
        ReachableSampleStringLanguage (Ttxt.prefixSample n) obs f =
          G.StringLanguage :=
  O.toTransportFromComponentPackage.prefix_exact_eventually

/-- Reachable Gold identification. -/
theorem identifies_from_positive_text
    (O : TrimmedPresentationCommonContextFromComponentEnumeration D) :
    ∀ Ttxt : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        Ttxt :=
  O.toTransportFromComponentPackage.identifies_from_positive_text

end TrimmedPresentationCommonContextFromComponentEnumeration

end CommonContextFromComponentEnumeration


section MainTheoremsFromComponentTransportObligations

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}
variable {f : Nat}
variable {T : TrimmedOutputTypePresentation G obs}
variable {D : TrimmedPresentationPreCoreData T f}

/-- Stable top-level reachable identification theorem from exposing transport
and a component package. -/
theorem trimmed_exposing_transport_from_component_package_reachable_identification
    (O : TrimmedPresentationExposingTransportFromComponentPackage D) :
    ∀ Ttxt : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        Ttxt :=
  O.identifies_from_positive_text

/-- Stable top-level prefix-exact theorem from exposing transport and a
component package. -/
theorem trimmed_exposing_transport_from_component_package_prefix_exact
    (O : TrimmedPresentationExposingTransportFromComponentPackage D) :
    ∀ Ttxt : TextFor G.StringLanguage,
      ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
        ReachableSampleStringLanguage (Ttxt.prefixSample n) obs f =
          G.StringLanguage :=
  O.prefix_exact_eventually

/-- Stable top-level reachable identification theorem from common-context
transport and a component package. -/
theorem trimmed_common_context_from_component_package_reachable_identification
    (O : TrimmedPresentationCommonContextFromComponentPackage D) :
    ∀ Ttxt : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        Ttxt :=
  O.identifies_from_positive_text

/-- Stable top-level prefix-exact theorem from common-context transport and a
component package. -/
theorem trimmed_common_context_from_component_package_prefix_exact
    (O : TrimmedPresentationCommonContextFromComponentPackage D) :
    ∀ Ttxt : TextFor G.StringLanguage,
      ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
        ReachableSampleStringLanguage (Ttxt.prefixSample n) obs f =
          G.StringLanguage :=
  O.prefix_exact_eventually

/-- Stable top-level reachable identification theorem from exposing transport
and a component enumeration. -/
theorem trimmed_exposing_transport_from_component_enumeration_reachable_identification
    (O : TrimmedPresentationExposingTransportFromComponentEnumeration D) :
    ∀ Ttxt : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        Ttxt :=
  O.identifies_from_positive_text

/-- Stable top-level prefix-exact theorem from exposing transport and a
component enumeration. -/
theorem trimmed_exposing_transport_from_component_enumeration_prefix_exact
    (O : TrimmedPresentationExposingTransportFromComponentEnumeration D) :
    ∀ Ttxt : TextFor G.StringLanguage,
      ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
        ReachableSampleStringLanguage (Ttxt.prefixSample n) obs f =
          G.StringLanguage :=
  O.prefix_exact_eventually

/-- Stable top-level reachable identification theorem from common-context
transport and a component enumeration. -/
theorem trimmed_common_context_from_component_enumeration_reachable_identification
    (O : TrimmedPresentationCommonContextFromComponentEnumeration D) :
    ∀ Ttxt : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        Ttxt :=
  O.identifies_from_positive_text

/-- Stable top-level prefix-exact theorem from common-context transport and a
component enumeration. -/
theorem trimmed_common_context_from_component_enumeration_prefix_exact
    (O : TrimmedPresentationCommonContextFromComponentEnumeration D) :
    ∀ Ttxt : TextFor G.StringLanguage,
      ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
        ReachableSampleStringLanguage (Ttxt.prefixSample n) obs f =
          G.StringLanguage :=
  O.prefix_exact_eventually

end MainTheoremsFromComponentTransportObligations

end MCFG
