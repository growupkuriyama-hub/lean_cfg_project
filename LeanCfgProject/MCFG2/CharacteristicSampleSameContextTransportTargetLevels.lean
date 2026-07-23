/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG2.CharacteristicSampleSameContextTransportTargets

/-!
# CharacteristicSampleSameContextTransportTargetLevels.lean

Eighty-fifth clean Lean experiment for the fixed-observation MCFG project.

`CharacteristicSampleSameContextTransportTargets.lean` introduced the
grammar-rule-builder target based on the strong same-context transport
assumption.

This file adds the lower-level variants:

* rule coverage + same-context transport;
* component package + same-context transport;
* component enumeration + same-context transport.

The route used here is intentionally simple:

```text
SameContextTransport
⇒ ExposingContextTransport
⇒ existing exposing target
⇒ reachable identification.
```

Thus these targets are useful debugging/proof-search entrances: a proof of the
stronger same-context transport principle immediately gives the final theorem
at each finite-sample construction level.

No new semantic principle is introduced here.

No theorem here uses `sorry`.
-/

namespace MCFG

universe u v w

section RuleCoverageSameContextTransportTarget

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}
variable {f : Nat}
variable {T : TrimmedOutputTypePresentation G obs}

/-- Rule-coverage-level semantic target using the stronger same-context
transport assumption. -/
structure TrimmedPresentationRuleCoverageSameContextTransportTarget
    (D : TrimmedPresentationPreCoreData T f) where
  coverage : TrimmedPresentationRuleCoveragePackage D
  baseNonterminals : Finset N
  base_covers :
    ∀ A : N, A ∈ baseNonterminals
  arities : TrimmedPresentationRuleAritySelectors D
  sameContextTransport : TrimmedPresentationSameContextTransport D
  splicingConstructor : NamedContextSplicingConstructor α
  fanout : G.FanoutAtMost f
  promise : FixedNamedTupleSubstitutable f obs G.StringLanguage

namespace TrimmedPresentationRuleCoverageSameContextTransportTarget

variable {D : TrimmedPresentationPreCoreData T f}

/-- Same-context transport induces exposing-context transport. -/
def exposingTransport
    (C : TrimmedPresentationRuleCoverageSameContextTransportTarget D) :
    TrimmedPresentationExposingContextTransport D :=
  TrimmedPresentationExposingContextTransport.ofSameContextTransport
    C.sameContextTransport

/-- Convert to the rule-coverage exposing target. -/
def toRuleCoverageExposingTarget
    (C : TrimmedPresentationRuleCoverageSameContextTransportTarget D) :
    TrimmedPresentationRuleCoverageExposingTarget D where
  coverage := C.coverage
  baseNonterminals := C.baseNonterminals
  base_covers := C.base_covers
  arities := C.arities
  exposingTransport := C.exposingTransport
  splicingConstructor := C.splicingConstructor
  fanout := C.fanout
  promise := C.promise

/-- Convert to the established exposing-from-rule-coverage route. -/
def toExposingTransportFromRuleCoverage
    (C : TrimmedPresentationRuleCoverageSameContextTransportTarget D) :
    TrimmedPresentationExposingTransportFromRuleCoverage D :=
  C.toRuleCoverageExposingTarget.toExposingTransportFromRuleCoverage

/-- Convert to exposing-transport obligations. -/
def toExposingTransportObligations
    (C : TrimmedPresentationRuleCoverageSameContextTransportTarget D) :
    TrimmedPresentationExposingTransportObligations D :=
  C.toExposingTransportFromRuleCoverage.toObligations

/-- The finite sample produced by the target. -/
noncomputable def sample
    (C : TrimmedPresentationRuleCoverageSameContextTransportTarget D) :
    Finset (Word α) :=
  C.toRuleCoverageExposingTarget.sample

/-- The finite sample is positive. -/
theorem sample_positive
    (C : TrimmedPresentationRuleCoverageSameContextTransportTarget D) :
    (C.sample : Set (Word α)) ⊆ G.StringLanguage :=
  C.toRuleCoverageExposingTarget.sample_positive

/-- The finite sample contains all required witness words. -/
theorem contains_witnesses
    (C : TrimmedPresentationRuleCoverageSameContextTransportTarget D) :
    TrimmedPresentationWitnessWordSet D ⊆
      (C.sample : Set (Word α)) :=
  C.toRuleCoverageExposingTarget.contains_witnesses

/-- Convert directly to final reachable data. -/
noncomputable def toFinalReachableData
    (C : TrimmedPresentationRuleCoverageSameContextTransportTarget D) :
    FinalReachableData G C.sample obs f :=
  C.toRuleCoverageExposingTarget.toFinalReachableData

/-- The produced sample is a characteristic sample for the reachable learner. -/
theorem characteristic_sample
    (C : TrimmedPresentationRuleCoverageSameContextTransportTarget D) :
    CharacteristicSample
      (reachableHypLanguage obs f)
      (reachableSampleLearner (α := α))
      C.sample
      G.StringLanguage :=
  C.toRuleCoverageExposingTarget.characteristic_sample

/-- Exact reconstruction for every positive finite superset of the produced
sample. -/
theorem exact_for_positive_superset
    (C : TrimmedPresentationRuleCoverageSameContextTransportTarget D)
    {K : Finset (Word α)}
    (hCK : (C.sample : Set (Word α)) ⊆ (K : Set (Word α)))
    (hKpos : (K : Set (Word α)) ⊆ G.StringLanguage) :
    ReachableSampleStringLanguage K obs f = G.StringLanguage :=
  C.toFinalReachableData.exact_for_positive_superset hCK hKpos

/-- Eventual prefix-exact reconstruction. -/
theorem prefix_exact_eventually
    (C : TrimmedPresentationRuleCoverageSameContextTransportTarget D) :
    ∀ Ttxt : TextFor G.StringLanguage,
      ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
        ReachableSampleStringLanguage (Ttxt.prefixSample n) obs f =
          G.StringLanguage :=
  C.toRuleCoverageExposingTarget.prefix_exact_eventually

/-- Reachable Gold identification. -/
theorem identifies_from_positive_text
    (C : TrimmedPresentationRuleCoverageSameContextTransportTarget D) :
    ∀ Ttxt : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        Ttxt :=
  C.toRuleCoverageExposingTarget.identifies_from_positive_text

end TrimmedPresentationRuleCoverageSameContextTransportTarget

end RuleCoverageSameContextTransportTarget


section ComponentPackageSameContextTransportTarget

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}
variable {f : Nat}
variable {T : TrimmedOutputTypePresentation G obs}

/-- Component-package-level semantic target using the stronger same-context
transport assumption. -/
structure TrimmedPresentationComponentPackageSameContextTransportTarget
    (D : TrimmedPresentationPreCoreData T f) where
  components : TrimmedPresentationComponentPackage D
  baseNonterminals : Finset N
  base_covers :
    ∀ A : N, A ∈ baseNonterminals
  arities : TrimmedPresentationRuleAritySelectors D
  sameContextTransport : TrimmedPresentationSameContextTransport D
  splicingConstructor : NamedContextSplicingConstructor α
  fanout : G.FanoutAtMost f
  promise : FixedNamedTupleSubstitutable f obs G.StringLanguage

namespace TrimmedPresentationComponentPackageSameContextTransportTarget

variable {D : TrimmedPresentationPreCoreData T f}

/-- Same-context transport induces exposing-context transport. -/
def exposingTransport
    (C : TrimmedPresentationComponentPackageSameContextTransportTarget D) :
    TrimmedPresentationExposingContextTransport D :=
  TrimmedPresentationExposingContextTransport.ofSameContextTransport
    C.sameContextTransport

/-- Convert to the component-package exposing target. -/
def toComponentPackageExposingTarget
    (C : TrimmedPresentationComponentPackageSameContextTransportTarget D) :
    TrimmedPresentationComponentPackageExposingTarget D where
  components := C.components
  baseNonterminals := C.baseNonterminals
  base_covers := C.base_covers
  arities := C.arities
  exposingTransport := C.exposingTransport
  splicingConstructor := C.splicingConstructor
  fanout := C.fanout
  promise := C.promise

/-- Convert to the established exposing-from-component-package route. -/
def toExposingTransportFromComponentPackage
    (C : TrimmedPresentationComponentPackageSameContextTransportTarget D) :
    TrimmedPresentationExposingTransportFromComponentPackage D :=
  C.toComponentPackageExposingTarget.toExposingTransportFromComponentPackage

/-- Convert to exposing-transport obligations. -/
def toExposingTransportObligations
    (C : TrimmedPresentationComponentPackageSameContextTransportTarget D) :
    TrimmedPresentationExposingTransportObligations D :=
  C.toExposingTransportFromComponentPackage.toObligations

/-- The finite sample produced by the target. -/
noncomputable def sample
    (C : TrimmedPresentationComponentPackageSameContextTransportTarget D) :
    Finset (Word α) :=
  C.toComponentPackageExposingTarget.sample

/-- The finite sample is positive. -/
theorem sample_positive
    (C : TrimmedPresentationComponentPackageSameContextTransportTarget D) :
    (C.sample : Set (Word α)) ⊆ G.StringLanguage :=
  C.toComponentPackageExposingTarget.sample_positive

/-- The finite sample contains all required witness words. -/
theorem contains_witnesses
    (C : TrimmedPresentationComponentPackageSameContextTransportTarget D) :
    TrimmedPresentationWitnessWordSet D ⊆
      (C.sample : Set (Word α)) :=
  C.toComponentPackageExposingTarget.contains_witnesses

/-- Convert directly to final reachable data. -/
noncomputable def toFinalReachableData
    (C : TrimmedPresentationComponentPackageSameContextTransportTarget D) :
    FinalReachableData G C.sample obs f :=
  C.toComponentPackageExposingTarget.toFinalReachableData

/-- The produced sample is a characteristic sample for the reachable learner. -/
theorem characteristic_sample
    (C : TrimmedPresentationComponentPackageSameContextTransportTarget D) :
    CharacteristicSample
      (reachableHypLanguage obs f)
      (reachableSampleLearner (α := α))
      C.sample
      G.StringLanguage :=
  C.toComponentPackageExposingTarget.characteristic_sample

/-- Exact reconstruction for every positive finite superset of the produced
sample. -/
theorem exact_for_positive_superset
    (C : TrimmedPresentationComponentPackageSameContextTransportTarget D)
    {K : Finset (Word α)}
    (hCK : (C.sample : Set (Word α)) ⊆ (K : Set (Word α)))
    (hKpos : (K : Set (Word α)) ⊆ G.StringLanguage) :
    ReachableSampleStringLanguage K obs f = G.StringLanguage :=
  C.toFinalReachableData.exact_for_positive_superset hCK hKpos

/-- Eventual prefix-exact reconstruction. -/
theorem prefix_exact_eventually
    (C : TrimmedPresentationComponentPackageSameContextTransportTarget D) :
    ∀ Ttxt : TextFor G.StringLanguage,
      ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
        ReachableSampleStringLanguage (Ttxt.prefixSample n) obs f =
          G.StringLanguage :=
  C.toComponentPackageExposingTarget.prefix_exact_eventually

/-- Reachable Gold identification. -/
theorem identifies_from_positive_text
    (C : TrimmedPresentationComponentPackageSameContextTransportTarget D) :
    ∀ Ttxt : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        Ttxt :=
  C.toComponentPackageExposingTarget.identifies_from_positive_text

end TrimmedPresentationComponentPackageSameContextTransportTarget

end ComponentPackageSameContextTransportTarget


section ComponentEnumerationSameContextTransportTarget

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}
variable {f : Nat}
variable {T : TrimmedOutputTypePresentation G obs}

/-- Component-enumeration-level semantic target using the stronger same-context
transport assumption. -/
structure TrimmedPresentationComponentEnumerationSameContextTransportTarget
    (D : TrimmedPresentationPreCoreData T f) where
  enumeration : TrimmedPresentationComponentEnumeration D
  baseNonterminals : Finset N
  base_covers :
    ∀ A : N, A ∈ baseNonterminals
  arities : TrimmedPresentationRuleAritySelectors D
  sameContextTransport : TrimmedPresentationSameContextTransport D
  splicingConstructor : NamedContextSplicingConstructor α
  fanout : G.FanoutAtMost f
  promise : FixedNamedTupleSubstitutable f obs G.StringLanguage

namespace TrimmedPresentationComponentEnumerationSameContextTransportTarget

variable {D : TrimmedPresentationPreCoreData T f}

/-- Same-context transport induces exposing-context transport. -/
def exposingTransport
    (C : TrimmedPresentationComponentEnumerationSameContextTransportTarget D) :
    TrimmedPresentationExposingContextTransport D :=
  TrimmedPresentationExposingContextTransport.ofSameContextTransport
    C.sameContextTransport

/-- Convert to the component-enumeration exposing target. -/
def toComponentEnumerationExposingTarget
    (C : TrimmedPresentationComponentEnumerationSameContextTransportTarget D) :
    TrimmedPresentationComponentEnumerationExposingTarget D where
  enumeration := C.enumeration
  baseNonterminals := C.baseNonterminals
  base_covers := C.base_covers
  arities := C.arities
  exposingTransport := C.exposingTransport
  splicingConstructor := C.splicingConstructor
  fanout := C.fanout
  promise := C.promise

/-- Convert to the established exposing-from-component-enumeration route. -/
def toExposingTransportFromComponentEnumeration
    (C : TrimmedPresentationComponentEnumerationSameContextTransportTarget D) :
    TrimmedPresentationExposingTransportFromComponentEnumeration D :=
  C.toComponentEnumerationExposingTarget.toExposingTransportFromComponentEnumeration

/-- Convert to exposing-transport obligations. -/
def toExposingTransportObligations
    (C : TrimmedPresentationComponentEnumerationSameContextTransportTarget D) :
    TrimmedPresentationExposingTransportObligations D :=
  C.toExposingTransportFromComponentEnumeration.toObligations

/-- The finite sample produced by the target. -/
noncomputable def sample
    (C : TrimmedPresentationComponentEnumerationSameContextTransportTarget D) :
    Finset (Word α) :=
  C.toComponentEnumerationExposingTarget.sample

/-- The finite sample is positive. -/
theorem sample_positive
    (C : TrimmedPresentationComponentEnumerationSameContextTransportTarget D) :
    (C.sample : Set (Word α)) ⊆ G.StringLanguage :=
  C.toComponentEnumerationExposingTarget.sample_positive

/-- The finite sample contains all required witness words. -/
theorem contains_witnesses
    (C : TrimmedPresentationComponentEnumerationSameContextTransportTarget D) :
    TrimmedPresentationWitnessWordSet D ⊆
      (C.sample : Set (Word α)) :=
  C.toComponentEnumerationExposingTarget.contains_witnesses

/-- Convert directly to final reachable data. -/
noncomputable def toFinalReachableData
    (C : TrimmedPresentationComponentEnumerationSameContextTransportTarget D) :
    FinalReachableData G C.sample obs f :=
  C.toComponentEnumerationExposingTarget.toFinalReachableData

/-- The produced sample is a characteristic sample for the reachable learner. -/
theorem characteristic_sample
    (C : TrimmedPresentationComponentEnumerationSameContextTransportTarget D) :
    CharacteristicSample
      (reachableHypLanguage obs f)
      (reachableSampleLearner (α := α))
      C.sample
      G.StringLanguage :=
  C.toComponentEnumerationExposingTarget.characteristic_sample

/-- Exact reconstruction for every positive finite superset of the produced
sample. -/
theorem exact_for_positive_superset
    (C : TrimmedPresentationComponentEnumerationSameContextTransportTarget D)
    {K : Finset (Word α)}
    (hCK : (C.sample : Set (Word α)) ⊆ (K : Set (Word α)))
    (hKpos : (K : Set (Word α)) ⊆ G.StringLanguage) :
    ReachableSampleStringLanguage K obs f = G.StringLanguage :=
  C.toFinalReachableData.exact_for_positive_superset hCK hKpos

/-- Eventual prefix-exact reconstruction. -/
theorem prefix_exact_eventually
    (C : TrimmedPresentationComponentEnumerationSameContextTransportTarget D) :
    ∀ Ttxt : TextFor G.StringLanguage,
      ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
        ReachableSampleStringLanguage (Ttxt.prefixSample n) obs f =
          G.StringLanguage :=
  C.toComponentEnumerationExposingTarget.prefix_exact_eventually

/-- Reachable Gold identification. -/
theorem identifies_from_positive_text
    (C : TrimmedPresentationComponentEnumerationSameContextTransportTarget D) :
    ∀ Ttxt : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        Ttxt :=
  C.toComponentEnumerationExposingTarget.identifies_from_positive_text

end TrimmedPresentationComponentEnumerationSameContextTransportTarget

end ComponentEnumerationSameContextTransportTarget


section MainTheoremsFromLowerSameContextTransportTargets

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}
variable {f : Nat}
variable {T : TrimmedOutputTypePresentation G obs}
variable {D : TrimmedPresentationPreCoreData T f}

/-- Reachable identification from rule coverage plus same-context transport. -/
theorem trimmed_rule_coverage_same_context_transport_target_reachable_identification
    (C : TrimmedPresentationRuleCoverageSameContextTransportTarget D) :
    ∀ Ttxt : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        Ttxt :=
  C.identifies_from_positive_text

/-- Prefix exactness from rule coverage plus same-context transport. -/
theorem trimmed_rule_coverage_same_context_transport_target_prefix_exact
    (C : TrimmedPresentationRuleCoverageSameContextTransportTarget D) :
    ∀ Ttxt : TextFor G.StringLanguage,
      ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
        ReachableSampleStringLanguage (Ttxt.prefixSample n) obs f =
          G.StringLanguage :=
  C.prefix_exact_eventually

/-- Positive finite-superset exactness from rule coverage plus same-context
transport. -/
theorem trimmed_rule_coverage_same_context_transport_target_exact_for_positive_superset
    (C : TrimmedPresentationRuleCoverageSameContextTransportTarget D)
    {K : Finset (Word α)}
    (hCK : (C.sample : Set (Word α)) ⊆ (K : Set (Word α)))
    (hKpos : (K : Set (Word α)) ⊆ G.StringLanguage) :
    ReachableSampleStringLanguage K obs f = G.StringLanguage :=
  C.exact_for_positive_superset hCK hKpos

/-- Reachable identification from component package plus same-context
transport. -/
theorem trimmed_component_package_same_context_transport_target_reachable_identification
    (C : TrimmedPresentationComponentPackageSameContextTransportTarget D) :
    ∀ Ttxt : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        Ttxt :=
  C.identifies_from_positive_text

/-- Prefix exactness from component package plus same-context transport. -/
theorem trimmed_component_package_same_context_transport_target_prefix_exact
    (C : TrimmedPresentationComponentPackageSameContextTransportTarget D) :
    ∀ Ttxt : TextFor G.StringLanguage,
      ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
        ReachableSampleStringLanguage (Ttxt.prefixSample n) obs f =
          G.StringLanguage :=
  C.prefix_exact_eventually

/-- Reachable identification from component enumeration plus same-context
transport. -/
theorem trimmed_component_enumeration_same_context_transport_target_reachable_identification
    (C : TrimmedPresentationComponentEnumerationSameContextTransportTarget D) :
    ∀ Ttxt : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        Ttxt :=
  C.identifies_from_positive_text

/-- Prefix exactness from component enumeration plus same-context transport. -/
theorem trimmed_component_enumeration_same_context_transport_target_prefix_exact
    (C : TrimmedPresentationComponentEnumerationSameContextTransportTarget D) :
    ∀ Ttxt : TextFor G.StringLanguage,
      ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
        ReachableSampleStringLanguage (Ttxt.prefixSample n) obs f =
          G.StringLanguage :=
  C.prefix_exact_eventually

end MainTheoremsFromLowerSameContextTransportTargets

end MCFG
