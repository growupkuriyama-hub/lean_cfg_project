/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG.CharacteristicSampleSemanticTransportTargets

/-!
# CharacteristicSampleSemanticTransportTargetLevels.lean

Eighty-third clean Lean experiment for the fixed-observation MCFG project.

`CharacteristicSampleSemanticTransportTargets.lean` introduced the convenient
grammar-rule-builder targets

```text
GrammarRuleBuilder + AnchorCommonContextTransport
GrammarRuleBuilder + ExposingContextTransport
```

where the finite-cover and arity information are inherited from the builder.

This file adds the analogous lower-level targets for:

* rule coverage;
* component package;
* component enumeration.

For the common-context variants, the target now asks only for
`TrimmedPresentationAnchorCommonContextTransport D` plus explicit finite-cover
and arity selectors.  The corresponding
`TrimmedPresentationAnchorCommonContextCoreData D` is assembled internally.

No new semantic principle is introduced here.

No theorem here uses `sorry`.
-/

namespace MCFG

universe u v w

section RuleCoverageCommonTransportTarget

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}
variable {f : Nat}
variable {T : TrimmedOutputTypePresentation G obs}

/-- Rule-coverage-level semantic target using anchor common-context transport
directly. -/
structure TrimmedPresentationRuleCoverageCommonTransportTarget
    (D : TrimmedPresentationPreCoreData T f) where
  coverage : TrimmedPresentationRuleCoveragePackage D
  baseNonterminals : Finset N
  base_covers :
    ∀ A : N, A ∈ baseNonterminals
  arities : TrimmedPresentationRuleAritySelectors D
  commonTransport : TrimmedPresentationAnchorCommonContextTransport D
  splicingConstructor : NamedContextSplicingConstructor α
  fanout : G.FanoutAtMost f
  promise : FixedNamedTupleSubstitutable f obs G.StringLanguage

namespace TrimmedPresentationRuleCoverageCommonTransportTarget

variable {D : TrimmedPresentationPreCoreData T f}

/-- Assemble anchor common-context core data from the explicit finite cover,
arity selectors, and semantic common-transport evidence. -/
def toAnchorCommonContextCoreData
    (C : TrimmedPresentationRuleCoverageCommonTransportTarget D) :
    TrimmedPresentationAnchorCommonContextCoreData D where
  baseNonterminals := C.baseNonterminals
  base_covers := C.base_covers
  arities := C.arities
  commonTransport := C.commonTransport

/-- Convert to the previously named rule-coverage common-context target. -/
def toRuleCoverageCommonContextTarget
    (C : TrimmedPresentationRuleCoverageCommonTransportTarget D) :
    TrimmedPresentationRuleCoverageCommonContextTarget D where
  coverage := C.coverage
  commonData := C.toAnchorCommonContextCoreData
  splicingConstructor := C.splicingConstructor
  fanout := C.fanout
  promise := C.promise

/-- Convert to the common-context-from-rule-coverage route. -/
def toCommonContextFromRuleCoverage
    (C : TrimmedPresentationRuleCoverageCommonTransportTarget D) :
    TrimmedPresentationCommonContextFromRuleCoverage D :=
  C.toRuleCoverageCommonContextTarget.toCommonContextFromRuleCoverage

/-- Convert to common-context transport obligations. -/
def toCommonContextTransportObligations
    (C : TrimmedPresentationRuleCoverageCommonTransportTarget D) :
    TrimmedPresentationCommonContextTransportObligations D :=
  C.toCommonContextFromRuleCoverage.toObligations

/-- Convert to exposing-transport obligations through the common-context route. -/
def toExposingTransportObligations
    (C : TrimmedPresentationRuleCoverageCommonTransportTarget D) :
    TrimmedPresentationExposingTransportObligations D :=
  C.toCommonContextFromRuleCoverage.toExposingTransportObligations

/-- The finite sample produced by the target. -/
def sample
    (C : TrimmedPresentationRuleCoverageCommonTransportTarget D) :
    Finset (Word α) :=
  C.toRuleCoverageCommonContextTarget.sample

/-- The finite sample is positive. -/
theorem sample_positive
    (C : TrimmedPresentationRuleCoverageCommonTransportTarget D) :
    (C.sample : Set (Word α)) ⊆ G.StringLanguage :=
  C.toRuleCoverageCommonContextTarget.sample_positive

/-- The finite sample contains all required witness words. -/
theorem contains_witnesses
    (C : TrimmedPresentationRuleCoverageCommonTransportTarget D) :
    TrimmedPresentationWitnessWordSet D ⊆
      (C.sample : Set (Word α)) :=
  C.toRuleCoverageCommonContextTarget.contains_witnesses

/-- Convert directly to final reachable data. -/
def toFinalReachableData
    (C : TrimmedPresentationRuleCoverageCommonTransportTarget D) :
    FinalReachableData G C.sample obs f :=
  C.toRuleCoverageCommonContextTarget.toFinalReachableData

/-- The produced sample is a characteristic sample for the reachable learner. -/
theorem characteristic_sample
    (C : TrimmedPresentationRuleCoverageCommonTransportTarget D) :
    CharacteristicSample
      (reachableHypLanguage obs f)
      (reachableSampleLearner (α := α))
      C.sample
      G.StringLanguage :=
  C.toRuleCoverageCommonContextTarget.characteristic_sample

/-- Exact reconstruction for every positive finite superset of the produced
sample. -/
theorem exact_for_positive_superset
    (C : TrimmedPresentationRuleCoverageCommonTransportTarget D)
    {K : Finset (Word α)}
    (hCK : (C.sample : Set (Word α)) ⊆ (K : Set (Word α)))
    (hKpos : (K : Set (Word α)) ⊆ G.StringLanguage) :
    ReachableSampleStringLanguage K obs f = G.StringLanguage :=
  C.toFinalReachableData.exact_for_positive_superset hCK hKpos

/-- Eventual prefix-exact reconstruction. -/
theorem prefix_exact_eventually
    (C : TrimmedPresentationRuleCoverageCommonTransportTarget D) :
    ∀ Ttxt : TextFor G.StringLanguage,
      ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
        ReachableSampleStringLanguage (Ttxt.prefixSample n) obs f =
          G.StringLanguage :=
  C.toRuleCoverageCommonContextTarget.prefix_exact_eventually

/-- Reachable Gold identification. -/
theorem identifies_from_positive_text
    (C : TrimmedPresentationRuleCoverageCommonTransportTarget D) :
    ∀ Ttxt : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        Ttxt :=
  C.toRuleCoverageCommonContextTarget.identifies_from_positive_text

end TrimmedPresentationRuleCoverageCommonTransportTarget

end RuleCoverageCommonTransportTarget


section ComponentPackageCommonTransportTarget

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}
variable {f : Nat}
variable {T : TrimmedOutputTypePresentation G obs}

/-- Component-package-level semantic target using anchor common-context
transport directly. -/
structure TrimmedPresentationComponentPackageCommonTransportTarget
    (D : TrimmedPresentationPreCoreData T f) where
  components : TrimmedPresentationComponentPackage D
  baseNonterminals : Finset N
  base_covers :
    ∀ A : N, A ∈ baseNonterminals
  arities : TrimmedPresentationRuleAritySelectors D
  commonTransport : TrimmedPresentationAnchorCommonContextTransport D
  splicingConstructor : NamedContextSplicingConstructor α
  fanout : G.FanoutAtMost f
  promise : FixedNamedTupleSubstitutable f obs G.StringLanguage

namespace TrimmedPresentationComponentPackageCommonTransportTarget

variable {D : TrimmedPresentationPreCoreData T f}

/-- Assemble anchor common-context core data. -/
def toAnchorCommonContextCoreData
    (C : TrimmedPresentationComponentPackageCommonTransportTarget D) :
    TrimmedPresentationAnchorCommonContextCoreData D where
  baseNonterminals := C.baseNonterminals
  base_covers := C.base_covers
  arities := C.arities
  commonTransport := C.commonTransport

/-- Convert to the component-package common-context target. -/
def toComponentPackageCommonContextTarget
    (C : TrimmedPresentationComponentPackageCommonTransportTarget D) :
    TrimmedPresentationComponentPackageCommonContextTarget D where
  components := C.components
  commonData := C.toAnchorCommonContextCoreData
  splicingConstructor := C.splicingConstructor
  fanout := C.fanout
  promise := C.promise

/-- Convert to the common-context-from-component-package route. -/
def toCommonContextFromComponentPackage
    (C : TrimmedPresentationComponentPackageCommonTransportTarget D) :
    TrimmedPresentationCommonContextFromComponentPackage D :=
  C.toComponentPackageCommonContextTarget.toCommonContextFromComponentPackage

/-- Convert to common-context transport obligations. -/
def toCommonContextTransportObligations
    (C : TrimmedPresentationComponentPackageCommonTransportTarget D) :
    TrimmedPresentationCommonContextTransportObligations D :=
  C.toCommonContextFromComponentPackage.toObligations

/-- Convert to exposing-transport obligations through the common-context route. -/
def toExposingTransportObligations
    (C : TrimmedPresentationComponentPackageCommonTransportTarget D) :
    TrimmedPresentationExposingTransportObligations D :=
  C.toCommonContextFromComponentPackage.toExposingTransportObligations

/-- The finite sample produced by the target. -/
def sample
    (C : TrimmedPresentationComponentPackageCommonTransportTarget D) :
    Finset (Word α) :=
  C.toComponentPackageCommonContextTarget.sample

/-- The finite sample is positive. -/
theorem sample_positive
    (C : TrimmedPresentationComponentPackageCommonTransportTarget D) :
    (C.sample : Set (Word α)) ⊆ G.StringLanguage :=
  C.toComponentPackageCommonContextTarget.sample_positive

/-- The finite sample contains all required witness words. -/
theorem contains_witnesses
    (C : TrimmedPresentationComponentPackageCommonTransportTarget D) :
    TrimmedPresentationWitnessWordSet D ⊆
      (C.sample : Set (Word α)) :=
  C.toComponentPackageCommonContextTarget.contains_witnesses

/-- Convert directly to final reachable data. -/
def toFinalReachableData
    (C : TrimmedPresentationComponentPackageCommonTransportTarget D) :
    FinalReachableData G C.sample obs f :=
  C.toComponentPackageCommonContextTarget.toFinalReachableData

/-- The produced sample is a characteristic sample for the reachable learner. -/
theorem characteristic_sample
    (C : TrimmedPresentationComponentPackageCommonTransportTarget D) :
    CharacteristicSample
      (reachableHypLanguage obs f)
      (reachableSampleLearner (α := α))
      C.sample
      G.StringLanguage :=
  C.toComponentPackageCommonContextTarget.characteristic_sample

/-- Exact reconstruction for every positive finite superset of the produced
sample. -/
theorem exact_for_positive_superset
    (C : TrimmedPresentationComponentPackageCommonTransportTarget D)
    {K : Finset (Word α)}
    (hCK : (C.sample : Set (Word α)) ⊆ (K : Set (Word α)))
    (hKpos : (K : Set (Word α)) ⊆ G.StringLanguage) :
    ReachableSampleStringLanguage K obs f = G.StringLanguage :=
  C.toFinalReachableData.exact_for_positive_superset hCK hKpos

/-- Eventual prefix-exact reconstruction. -/
theorem prefix_exact_eventually
    (C : TrimmedPresentationComponentPackageCommonTransportTarget D) :
    ∀ Ttxt : TextFor G.StringLanguage,
      ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
        ReachableSampleStringLanguage (Ttxt.prefixSample n) obs f =
          G.StringLanguage :=
  C.toComponentPackageCommonContextTarget.prefix_exact_eventually

/-- Reachable Gold identification. -/
theorem identifies_from_positive_text
    (C : TrimmedPresentationComponentPackageCommonTransportTarget D) :
    ∀ Ttxt : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        Ttxt :=
  C.toComponentPackageCommonContextTarget.identifies_from_positive_text

end TrimmedPresentationComponentPackageCommonTransportTarget

end ComponentPackageCommonTransportTarget


section ComponentEnumerationCommonTransportTarget

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}
variable {f : Nat}
variable {T : TrimmedOutputTypePresentation G obs}

/-- Component-enumeration-level semantic target using anchor common-context
transport directly. -/
structure TrimmedPresentationComponentEnumerationCommonTransportTarget
    (D : TrimmedPresentationPreCoreData T f) where
  enumeration : TrimmedPresentationComponentEnumeration D
  baseNonterminals : Finset N
  base_covers :
    ∀ A : N, A ∈ baseNonterminals
  arities : TrimmedPresentationRuleAritySelectors D
  commonTransport : TrimmedPresentationAnchorCommonContextTransport D
  splicingConstructor : NamedContextSplicingConstructor α
  fanout : G.FanoutAtMost f
  promise : FixedNamedTupleSubstitutable f obs G.StringLanguage

namespace TrimmedPresentationComponentEnumerationCommonTransportTarget

variable {D : TrimmedPresentationPreCoreData T f}

/-- Convert the enumeration to its component package. -/
def toComponentPackage
    (C : TrimmedPresentationComponentEnumerationCommonTransportTarget D) :
    TrimmedPresentationComponentPackage D :=
  C.enumeration.toComponentPackage

/-- Convert to the component-package common-transport target. -/
def toComponentPackageCommonTransportTarget
    (C : TrimmedPresentationComponentEnumerationCommonTransportTarget D) :
    TrimmedPresentationComponentPackageCommonTransportTarget D where
  components := C.toComponentPackage
  baseNonterminals := C.baseNonterminals
  base_covers := C.base_covers
  arities := C.arities
  commonTransport := C.commonTransport
  splicingConstructor := C.splicingConstructor
  fanout := C.fanout
  promise := C.promise

/-- Assemble anchor common-context core data. -/
def toAnchorCommonContextCoreData
    (C : TrimmedPresentationComponentEnumerationCommonTransportTarget D) :
    TrimmedPresentationAnchorCommonContextCoreData D :=
  C.toComponentPackageCommonTransportTarget.toAnchorCommonContextCoreData

/-- Convert to the component-enumeration common-context target. -/
def toComponentEnumerationCommonContextTarget
    (C : TrimmedPresentationComponentEnumerationCommonTransportTarget D) :
    TrimmedPresentationComponentEnumerationCommonContextTarget D where
  enumeration := C.enumeration
  commonData := C.toAnchorCommonContextCoreData
  splicingConstructor := C.splicingConstructor
  fanout := C.fanout
  promise := C.promise

/-- Convert to the established common-context component-enumeration route. -/
def toCommonContextFromComponentEnumeration
    (C : TrimmedPresentationComponentEnumerationCommonTransportTarget D) :
    TrimmedPresentationCommonContextFromComponentEnumeration D :=
  C.toComponentEnumerationCommonContextTarget.toCommonContextFromComponentEnumeration

/-- Convert to common-context transport obligations. -/
def toCommonContextTransportObligations
    (C : TrimmedPresentationComponentEnumerationCommonTransportTarget D) :
    TrimmedPresentationCommonContextTransportObligations D :=
  C.toCommonContextFromComponentEnumeration.toObligations

/-- Convert to exposing-transport obligations through the common-context route. -/
def toExposingTransportObligations
    (C : TrimmedPresentationComponentEnumerationCommonTransportTarget D) :
    TrimmedPresentationExposingTransportObligations D :=
  C.toCommonContextFromComponentEnumeration.toExposingTransportObligations

/-- The finite sample produced by the target. -/
def sample
    (C : TrimmedPresentationComponentEnumerationCommonTransportTarget D) :
    Finset (Word α) :=
  C.toComponentEnumerationCommonContextTarget.sample

/-- The finite sample is positive. -/
theorem sample_positive
    (C : TrimmedPresentationComponentEnumerationCommonTransportTarget D) :
    (C.sample : Set (Word α)) ⊆ G.StringLanguage :=
  C.toComponentEnumerationCommonContextTarget.sample_positive

/-- The finite sample contains all required witness words. -/
theorem contains_witnesses
    (C : TrimmedPresentationComponentEnumerationCommonTransportTarget D) :
    TrimmedPresentationWitnessWordSet D ⊆
      (C.sample : Set (Word α)) :=
  C.toComponentEnumerationCommonContextTarget.contains_witnesses

/-- Convert directly to final reachable data. -/
def toFinalReachableData
    (C : TrimmedPresentationComponentEnumerationCommonTransportTarget D) :
    FinalReachableData G C.sample obs f :=
  C.toComponentEnumerationCommonContextTarget.toFinalReachableData

/-- The produced sample is a characteristic sample for the reachable learner. -/
theorem characteristic_sample
    (C : TrimmedPresentationComponentEnumerationCommonTransportTarget D) :
    CharacteristicSample
      (reachableHypLanguage obs f)
      (reachableSampleLearner (α := α))
      C.sample
      G.StringLanguage :=
  C.toComponentEnumerationCommonContextTarget.characteristic_sample

/-- Exact reconstruction for every positive finite superset of the produced
sample. -/
theorem exact_for_positive_superset
    (C : TrimmedPresentationComponentEnumerationCommonTransportTarget D)
    {K : Finset (Word α)}
    (hCK : (C.sample : Set (Word α)) ⊆ (K : Set (Word α)))
    (hKpos : (K : Set (Word α)) ⊆ G.StringLanguage) :
    ReachableSampleStringLanguage K obs f = G.StringLanguage :=
  C.toFinalReachableData.exact_for_positive_superset hCK hKpos

/-- Eventual prefix-exact reconstruction. -/
theorem prefix_exact_eventually
    (C : TrimmedPresentationComponentEnumerationCommonTransportTarget D) :
    ∀ Ttxt : TextFor G.StringLanguage,
      ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
        ReachableSampleStringLanguage (Ttxt.prefixSample n) obs f =
          G.StringLanguage :=
  C.toComponentEnumerationCommonContextTarget.prefix_exact_eventually

/-- Reachable Gold identification. -/
theorem identifies_from_positive_text
    (C : TrimmedPresentationComponentEnumerationCommonTransportTarget D) :
    ∀ Ttxt : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        Ttxt :=
  C.toComponentEnumerationCommonContextTarget.identifies_from_positive_text

end TrimmedPresentationComponentEnumerationCommonTransportTarget

end ComponentEnumerationCommonTransportTarget


section MainTheoremsFromLowerSemanticTransportTargets

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}
variable {f : Nat}
variable {T : TrimmedOutputTypePresentation G obs}
variable {D : TrimmedPresentationPreCoreData T f}

/-- Reachable identification from rule coverage plus anchor common-context
transport. -/
theorem trimmed_rule_coverage_common_transport_target_reachable_identification
    (C : TrimmedPresentationRuleCoverageCommonTransportTarget D) :
    ∀ Ttxt : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        Ttxt :=
  C.identifies_from_positive_text

/-- Prefix exactness from rule coverage plus anchor common-context transport. -/
theorem trimmed_rule_coverage_common_transport_target_prefix_exact
    (C : TrimmedPresentationRuleCoverageCommonTransportTarget D) :
    ∀ Ttxt : TextFor G.StringLanguage,
      ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
        ReachableSampleStringLanguage (Ttxt.prefixSample n) obs f =
          G.StringLanguage :=
  C.prefix_exact_eventually

/-- Positive finite-superset exactness from rule coverage plus anchor
common-context transport. -/
theorem trimmed_rule_coverage_common_transport_target_exact_for_positive_superset
    (C : TrimmedPresentationRuleCoverageCommonTransportTarget D)
    {K : Finset (Word α)}
    (hCK : (C.sample : Set (Word α)) ⊆ (K : Set (Word α)))
    (hKpos : (K : Set (Word α)) ⊆ G.StringLanguage) :
    ReachableSampleStringLanguage K obs f = G.StringLanguage :=
  C.exact_for_positive_superset hCK hKpos

/-- Reachable identification from component package plus anchor common-context
transport. -/
theorem trimmed_component_package_common_transport_target_reachable_identification
    (C : TrimmedPresentationComponentPackageCommonTransportTarget D) :
    ∀ Ttxt : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        Ttxt :=
  C.identifies_from_positive_text

/-- Prefix exactness from component package plus anchor common-context
transport. -/
theorem trimmed_component_package_common_transport_target_prefix_exact
    (C : TrimmedPresentationComponentPackageCommonTransportTarget D) :
    ∀ Ttxt : TextFor G.StringLanguage,
      ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
        ReachableSampleStringLanguage (Ttxt.prefixSample n) obs f =
          G.StringLanguage :=
  C.prefix_exact_eventually

/-- Reachable identification from component enumeration plus anchor
common-context transport. -/
theorem trimmed_component_enumeration_common_transport_target_reachable_identification
    (C : TrimmedPresentationComponentEnumerationCommonTransportTarget D) :
    ∀ Ttxt : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        Ttxt :=
  C.identifies_from_positive_text

/-- Prefix exactness from component enumeration plus anchor common-context
transport. -/
theorem trimmed_component_enumeration_common_transport_target_prefix_exact
    (C : TrimmedPresentationComponentEnumerationCommonTransportTarget D) :
    ∀ Ttxt : TextFor G.StringLanguage,
      ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
        ReachableSampleStringLanguage (Ttxt.prefixSample n) obs f =
          G.StringLanguage :=
  C.prefix_exact_eventually

end MainTheoremsFromLowerSemanticTransportTargets

end MCFG
