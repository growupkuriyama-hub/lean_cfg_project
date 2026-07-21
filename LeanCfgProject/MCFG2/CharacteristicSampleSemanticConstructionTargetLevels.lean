/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG.CharacteristicSampleSemanticConstructionTargets

/-!
# CharacteristicSampleSemanticConstructionTargetLevels.lean

Eighty-first clean Lean experiment for the fixed-observation MCFG project.

`CharacteristicSampleSemanticConstructionTargets.lean` named the main semantic
construction targets at the rule-coverage and grammar-rule-builder levels.

This file fills in the neighboring levels:

* component package + common-context transport;
* component package + exposing-context transport;
* component enumeration + common-context transport;
* component enumeration + exposing-context transport.

These wrappers do not add new mathematics.  They make the hierarchy of future
construction goals explicit:

```text
component enumeration
⇒ component package
⇒ positive finite-union builder
⇒ witness sample
⇒ transport obligations
⇒ reachable identification.
```

No theorem here uses `sorry`.
-/

namespace MCFG

universe u v w

section ComponentPackageCommonContextTarget

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}
variable {f : Nat}
variable {T : TrimmedOutputTypePresentation G obs}

/-- Semantic construction target at the component-package level using
common-context transport. -/
structure TrimmedPresentationComponentPackageCommonContextTarget
    (D : TrimmedPresentationPreCoreData T f) where
  components : TrimmedPresentationComponentPackage D
  commonData : TrimmedPresentationAnchorCommonContextCoreData D
  splicingConstructor : NamedContextSplicingConstructor α
  fanout : G.FanoutAtMost f
  promise : FixedNamedTupleSubstitutable f obs G.StringLanguage

namespace TrimmedPresentationComponentPackageCommonContextTarget

variable {D : TrimmedPresentationPreCoreData T f}

/-- View the target through the established common-context component route. -/
def toCommonContextFromComponentPackage
    (C : TrimmedPresentationComponentPackageCommonContextTarget D) :
    TrimmedPresentationCommonContextFromComponentPackage D where
  components := C.components
  commonData := C.commonData
  splicingConstructor := C.splicingConstructor
  fanout := C.fanout
  promise := C.promise

/-- Convert to common-context transport obligations. -/
def toCommonContextTransportObligations
    (C : TrimmedPresentationComponentPackageCommonContextTarget D) :
    TrimmedPresentationCommonContextTransportObligations D :=
  C.toCommonContextFromComponentPackage.toObligations

/-- Convert to exposing-transport obligations through the common-context route. -/
def toExposingTransportObligations
    (C : TrimmedPresentationComponentPackageCommonContextTarget D) :
    TrimmedPresentationExposingTransportObligations D :=
  C.toCommonContextFromComponentPackage.toExposingTransportObligations

/-- The finite sample produced by the target. -/
def sample
    (C : TrimmedPresentationComponentPackageCommonContextTarget D) :
    Finset (Word α) :=
  C.toCommonContextFromComponentPackage.sample

/-- The finite sample is positive. -/
theorem sample_positive
    (C : TrimmedPresentationComponentPackageCommonContextTarget D) :
    (C.sample : Set (Word α)) ⊆ G.StringLanguage :=
  C.toCommonContextFromComponentPackage.sample_positive

/-- The finite sample contains all required witness words. -/
theorem contains_witnesses
    (C : TrimmedPresentationComponentPackageCommonContextTarget D) :
    TrimmedPresentationWitnessWordSet D ⊆
      (C.sample : Set (Word α)) :=
  C.toCommonContextFromComponentPackage.contains_witnesses

/-- Convert directly to final reachable data. -/
def toFinalReachableData
    (C : TrimmedPresentationComponentPackageCommonContextTarget D) :
    FinalReachableData G C.sample obs f :=
  C.toCommonContextFromComponentPackage.toFinalReachableData

/-- The produced sample is a characteristic sample for the reachable learner. -/
theorem characteristic_sample
    (C : TrimmedPresentationComponentPackageCommonContextTarget D) :
    CharacteristicSample
      (reachableHypLanguage obs f)
      (reachableSampleLearner (α := α))
      C.sample
      G.StringLanguage :=
  C.toCommonContextFromComponentPackage.characteristic_sample

/-- Exact reconstruction for every positive finite superset of the produced
sample. -/
theorem exact_for_positive_superset
    (C : TrimmedPresentationComponentPackageCommonContextTarget D)
    {K : Finset (Word α)}
    (hCK : (C.sample : Set (Word α)) ⊆ (K : Set (Word α)))
    (hKpos : (K : Set (Word α)) ⊆ G.StringLanguage) :
    ReachableSampleStringLanguage K obs f = G.StringLanguage :=
  C.toFinalReachableData.exact_for_positive_superset hCK hKpos

/-- Eventual prefix-exact reconstruction. -/
theorem prefix_exact_eventually
    (C : TrimmedPresentationComponentPackageCommonContextTarget D) :
    ∀ Ttxt : TextFor G.StringLanguage,
      ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
        ReachableSampleStringLanguage (Ttxt.prefixSample n) obs f =
          G.StringLanguage :=
  C.toCommonContextFromComponentPackage.prefix_exact_eventually

/-- Reachable Gold identification. -/
theorem identifies_from_positive_text
    (C : TrimmedPresentationComponentPackageCommonContextTarget D) :
    ∀ Ttxt : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        Ttxt :=
  C.toCommonContextFromComponentPackage.identifies_from_positive_text

end TrimmedPresentationComponentPackageCommonContextTarget

end ComponentPackageCommonContextTarget


section ComponentPackageExposingTarget

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}
variable {f : Nat}
variable {T : TrimmedOutputTypePresentation G obs}

/-- Semantic construction target at the component-package level using direct
exposing-context transport. -/
structure TrimmedPresentationComponentPackageExposingTarget
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

namespace TrimmedPresentationComponentPackageExposingTarget

variable {D : TrimmedPresentationPreCoreData T f}

/-- View the target through the established exposing component route. -/
def toExposingTransportFromComponentPackage
    (C : TrimmedPresentationComponentPackageExposingTarget D) :
    TrimmedPresentationExposingTransportFromComponentPackage D where
  components := C.components
  baseNonterminals := C.baseNonterminals
  base_covers := C.base_covers
  arities := C.arities
  exposingTransport := C.exposingTransport
  splicingConstructor := C.splicingConstructor
  fanout := C.fanout
  promise := C.promise

/-- Convert to exposing-transport obligations. -/
def toExposingTransportObligations
    (C : TrimmedPresentationComponentPackageExposingTarget D) :
    TrimmedPresentationExposingTransportObligations D :=
  C.toExposingTransportFromComponentPackage.toObligations

/-- The finite sample produced by the target. -/
def sample
    (C : TrimmedPresentationComponentPackageExposingTarget D) :
    Finset (Word α) :=
  C.toExposingTransportFromComponentPackage.sample

/-- The finite sample is positive. -/
theorem sample_positive
    (C : TrimmedPresentationComponentPackageExposingTarget D) :
    (C.sample : Set (Word α)) ⊆ G.StringLanguage :=
  C.toExposingTransportFromComponentPackage.sample_positive

/-- The finite sample contains all required witness words. -/
theorem contains_witnesses
    (C : TrimmedPresentationComponentPackageExposingTarget D) :
    TrimmedPresentationWitnessWordSet D ⊆
      (C.sample : Set (Word α)) :=
  C.toExposingTransportFromComponentPackage.contains_witnesses

/-- Convert directly to final reachable data. -/
def toFinalReachableData
    (C : TrimmedPresentationComponentPackageExposingTarget D) :
    FinalReachableData G C.sample obs f :=
  C.toExposingTransportFromComponentPackage.toFinalReachableData

/-- The produced sample is a characteristic sample for the reachable learner. -/
theorem characteristic_sample
    (C : TrimmedPresentationComponentPackageExposingTarget D) :
    CharacteristicSample
      (reachableHypLanguage obs f)
      (reachableSampleLearner (α := α))
      C.sample
      G.StringLanguage :=
  C.toExposingTransportFromComponentPackage.characteristic_sample

/-- Exact reconstruction for every positive finite superset of the produced
sample. -/
theorem exact_for_positive_superset
    (C : TrimmedPresentationComponentPackageExposingTarget D)
    {K : Finset (Word α)}
    (hCK : (C.sample : Set (Word α)) ⊆ (K : Set (Word α)))
    (hKpos : (K : Set (Word α)) ⊆ G.StringLanguage) :
    ReachableSampleStringLanguage K obs f = G.StringLanguage :=
  C.toFinalReachableData.exact_for_positive_superset hCK hKpos

/-- Eventual prefix-exact reconstruction. -/
theorem prefix_exact_eventually
    (C : TrimmedPresentationComponentPackageExposingTarget D) :
    ∀ Ttxt : TextFor G.StringLanguage,
      ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
        ReachableSampleStringLanguage (Ttxt.prefixSample n) obs f =
          G.StringLanguage :=
  C.toExposingTransportFromComponentPackage.prefix_exact_eventually

/-- Reachable Gold identification. -/
theorem identifies_from_positive_text
    (C : TrimmedPresentationComponentPackageExposingTarget D) :
    ∀ Ttxt : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        Ttxt :=
  C.toExposingTransportFromComponentPackage.identifies_from_positive_text

end TrimmedPresentationComponentPackageExposingTarget

end ComponentPackageExposingTarget


section ComponentEnumerationCommonContextTarget

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}
variable {f : Nat}
variable {T : TrimmedOutputTypePresentation G obs}

/-- Semantic construction target at the component-enumeration level using
common-context transport. -/
structure TrimmedPresentationComponentEnumerationCommonContextTarget
    (D : TrimmedPresentationPreCoreData T f) where
  enumeration : TrimmedPresentationComponentEnumeration D
  commonData : TrimmedPresentationAnchorCommonContextCoreData D
  splicingConstructor : NamedContextSplicingConstructor α
  fanout : G.FanoutAtMost f
  promise : FixedNamedTupleSubstitutable f obs G.StringLanguage

namespace TrimmedPresentationComponentEnumerationCommonContextTarget

variable {D : TrimmedPresentationPreCoreData T f}

/-- Convert the enumeration to its component package. -/
def toComponentPackage
    (C : TrimmedPresentationComponentEnumerationCommonContextTarget D) :
    TrimmedPresentationComponentPackage D :=
  C.enumeration.toComponentPackage

/-- Convert to the component-package common-context target. -/
def toComponentPackageCommonContextTarget
    (C : TrimmedPresentationComponentEnumerationCommonContextTarget D) :
    TrimmedPresentationComponentPackageCommonContextTarget D where
  components := C.toComponentPackage
  commonData := C.commonData
  splicingConstructor := C.splicingConstructor
  fanout := C.fanout
  promise := C.promise

/-- View the target through the established common-context enumeration route. -/
def toCommonContextFromComponentEnumeration
    (C : TrimmedPresentationComponentEnumerationCommonContextTarget D) :
    TrimmedPresentationCommonContextFromComponentEnumeration D where
  enumeration := C.enumeration
  commonData := C.commonData
  splicingConstructor := C.splicingConstructor
  fanout := C.fanout
  promise := C.promise

/-- Convert to common-context transport obligations. -/
def toCommonContextTransportObligations
    (C : TrimmedPresentationComponentEnumerationCommonContextTarget D) :
    TrimmedPresentationCommonContextTransportObligations D :=
  C.toCommonContextFromComponentEnumeration.toObligations

/-- The finite sample produced by the target. -/
def sample
    (C : TrimmedPresentationComponentEnumerationCommonContextTarget D) :
    Finset (Word α) :=
  C.toCommonContextFromComponentEnumeration.sample

/-- The finite sample is positive. -/
theorem sample_positive
    (C : TrimmedPresentationComponentEnumerationCommonContextTarget D) :
    (C.sample : Set (Word α)) ⊆ G.StringLanguage :=
  C.toCommonContextFromComponentEnumeration.sample_positive

/-- The finite sample contains all required witness words. -/
theorem contains_witnesses
    (C : TrimmedPresentationComponentEnumerationCommonContextTarget D) :
    TrimmedPresentationWitnessWordSet D ⊆
      (C.sample : Set (Word α)) :=
  C.toCommonContextFromComponentEnumeration.contains_witnesses

/-- Convert directly to final reachable data. -/
def toFinalReachableData
    (C : TrimmedPresentationComponentEnumerationCommonContextTarget D) :
    FinalReachableData G C.sample obs f :=
  C.toCommonContextFromComponentEnumeration.toFinalReachableData

/-- The produced sample is a characteristic sample for the reachable learner. -/
theorem characteristic_sample
    (C : TrimmedPresentationComponentEnumerationCommonContextTarget D) :
    CharacteristicSample
      (reachableHypLanguage obs f)
      (reachableSampleLearner (α := α))
      C.sample
      G.StringLanguage :=
  C.toCommonContextFromComponentEnumeration.characteristic_sample

/-- Eventual prefix-exact reconstruction. -/
theorem prefix_exact_eventually
    (C : TrimmedPresentationComponentEnumerationCommonContextTarget D) :
    ∀ Ttxt : TextFor G.StringLanguage,
      ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
        ReachableSampleStringLanguage (Ttxt.prefixSample n) obs f =
          G.StringLanguage :=
  C.toCommonContextFromComponentEnumeration.prefix_exact_eventually

/-- Reachable Gold identification. -/
theorem identifies_from_positive_text
    (C : TrimmedPresentationComponentEnumerationCommonContextTarget D) :
    ∀ Ttxt : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        Ttxt :=
  C.toCommonContextFromComponentEnumeration.identifies_from_positive_text

end TrimmedPresentationComponentEnumerationCommonContextTarget

end ComponentEnumerationCommonContextTarget


section ComponentEnumerationExposingTarget

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}
variable {f : Nat}
variable {T : TrimmedOutputTypePresentation G obs}

/-- Semantic construction target at the component-enumeration level using direct
exposing-context transport. -/
structure TrimmedPresentationComponentEnumerationExposingTarget
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

namespace TrimmedPresentationComponentEnumerationExposingTarget

variable {D : TrimmedPresentationPreCoreData T f}

/-- Convert the enumeration to its component package. -/
def toComponentPackage
    (C : TrimmedPresentationComponentEnumerationExposingTarget D) :
    TrimmedPresentationComponentPackage D :=
  C.enumeration.toComponentPackage

/-- Convert to the component-package exposing target. -/
def toComponentPackageExposingTarget
    (C : TrimmedPresentationComponentEnumerationExposingTarget D) :
    TrimmedPresentationComponentPackageExposingTarget D where
  components := C.toComponentPackage
  baseNonterminals := C.baseNonterminals
  base_covers := C.base_covers
  arities := C.arities
  exposingTransport := C.exposingTransport
  splicingConstructor := C.splicingConstructor
  fanout := C.fanout
  promise := C.promise

/-- View the target through the established exposing enumeration route. -/
def toExposingTransportFromComponentEnumeration
    (C : TrimmedPresentationComponentEnumerationExposingTarget D) :
    TrimmedPresentationExposingTransportFromComponentEnumeration D where
  enumeration := C.enumeration
  baseNonterminals := C.baseNonterminals
  base_covers := C.base_covers
  arities := C.arities
  exposingTransport := C.exposingTransport
  splicingConstructor := C.splicingConstructor
  fanout := C.fanout
  promise := C.promise

/-- Convert to exposing-transport obligations. -/
def toExposingTransportObligations
    (C : TrimmedPresentationComponentEnumerationExposingTarget D) :
    TrimmedPresentationExposingTransportObligations D :=
  C.toExposingTransportFromComponentEnumeration.toObligations

/-- The finite sample produced by the target. -/
def sample
    (C : TrimmedPresentationComponentEnumerationExposingTarget D) :
    Finset (Word α) :=
  C.toExposingTransportFromComponentEnumeration.sample

/-- The finite sample is positive. -/
theorem sample_positive
    (C : TrimmedPresentationComponentEnumerationExposingTarget D) :
    (C.sample : Set (Word α)) ⊆ G.StringLanguage :=
  C.toExposingTransportFromComponentEnumeration.sample_positive

/-- The finite sample contains all required witness words. -/
theorem contains_witnesses
    (C : TrimmedPresentationComponentEnumerationExposingTarget D) :
    TrimmedPresentationWitnessWordSet D ⊆
      (C.sample : Set (Word α)) :=
  C.toExposingTransportFromComponentEnumeration.contains_witnesses

/-- Convert directly to final reachable data. -/
def toFinalReachableData
    (C : TrimmedPresentationComponentEnumerationExposingTarget D) :
    FinalReachableData G C.sample obs f :=
  C.toExposingTransportFromComponentEnumeration.toFinalReachableData

/-- The produced sample is a characteristic sample for the reachable learner. -/
theorem characteristic_sample
    (C : TrimmedPresentationComponentEnumerationExposingTarget D) :
    CharacteristicSample
      (reachableHypLanguage obs f)
      (reachableSampleLearner (α := α))
      C.sample
      G.StringLanguage :=
  C.toExposingTransportFromComponentEnumeration.characteristic_sample

/-- Eventual prefix-exact reconstruction. -/
theorem prefix_exact_eventually
    (C : TrimmedPresentationComponentEnumerationExposingTarget D) :
    ∀ Ttxt : TextFor G.StringLanguage,
      ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
        ReachableSampleStringLanguage (Ttxt.prefixSample n) obs f =
          G.StringLanguage :=
  C.toExposingTransportFromComponentEnumeration.prefix_exact_eventually

/-- Reachable Gold identification. -/
theorem identifies_from_positive_text
    (C : TrimmedPresentationComponentEnumerationExposingTarget D) :
    ∀ Ttxt : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        Ttxt :=
  C.toExposingTransportFromComponentEnumeration.identifies_from_positive_text

end TrimmedPresentationComponentEnumerationExposingTarget

end ComponentEnumerationExposingTarget


section MainTheoremsFromComponentTargetLevels

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}
variable {f : Nat}
variable {T : TrimmedOutputTypePresentation G obs}
variable {D : TrimmedPresentationPreCoreData T f}

/-- Reachable identification from component-package common-context target. -/
theorem trimmed_component_package_common_context_target_reachable_identification
    (C : TrimmedPresentationComponentPackageCommonContextTarget D) :
    ∀ Ttxt : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        Ttxt :=
  C.identifies_from_positive_text

/-- Prefix exactness from component-package common-context target. -/
theorem trimmed_component_package_common_context_target_prefix_exact
    (C : TrimmedPresentationComponentPackageCommonContextTarget D) :
    ∀ Ttxt : TextFor G.StringLanguage,
      ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
        ReachableSampleStringLanguage (Ttxt.prefixSample n) obs f =
          G.StringLanguage :=
  C.prefix_exact_eventually

/-- Reachable identification from component-package exposing target. -/
theorem trimmed_component_package_exposing_target_reachable_identification
    (C : TrimmedPresentationComponentPackageExposingTarget D) :
    ∀ Ttxt : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        Ttxt :=
  C.identifies_from_positive_text

/-- Prefix exactness from component-package exposing target. -/
theorem trimmed_component_package_exposing_target_prefix_exact
    (C : TrimmedPresentationComponentPackageExposingTarget D) :
    ∀ Ttxt : TextFor G.StringLanguage,
      ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
        ReachableSampleStringLanguage (Ttxt.prefixSample n) obs f =
          G.StringLanguage :=
  C.prefix_exact_eventually

/-- Reachable identification from component-enumeration common-context target. -/
theorem trimmed_component_enumeration_common_context_target_reachable_identification
    (C : TrimmedPresentationComponentEnumerationCommonContextTarget D) :
    ∀ Ttxt : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        Ttxt :=
  C.identifies_from_positive_text

/-- Prefix exactness from component-enumeration common-context target. -/
theorem trimmed_component_enumeration_common_context_target_prefix_exact
    (C : TrimmedPresentationComponentEnumerationCommonContextTarget D) :
    ∀ Ttxt : TextFor G.StringLanguage,
      ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
        ReachableSampleStringLanguage (Ttxt.prefixSample n) obs f =
          G.StringLanguage :=
  C.prefix_exact_eventually

/-- Reachable identification from component-enumeration exposing target. -/
theorem trimmed_component_enumeration_exposing_target_reachable_identification
    (C : TrimmedPresentationComponentEnumerationExposingTarget D) :
    ∀ Ttxt : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        Ttxt :=
  C.identifies_from_positive_text

/-- Prefix exactness from component-enumeration exposing target. -/
theorem trimmed_component_enumeration_exposing_target_prefix_exact
    (C : TrimmedPresentationComponentEnumerationExposingTarget D) :
    ∀ Ttxt : TextFor G.StringLanguage,
      ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
        ReachableSampleStringLanguage (Ttxt.prefixSample n) obs f =
          G.StringLanguage :=
  C.prefix_exact_eventually

end MainTheoremsFromComponentTargetLevels

end MCFG
