/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG2.CharacteristicSampleSemanticTransportTargetDiagram

/-!
# CharacteristicSampleCommonToExposingTargetDiagram.lean

Eighty-seventh clean Lean experiment for the fixed-observation MCFG project.

The preceding file recorded the diagram

```text
SameContextTransport ⇒ ExposingContextTransport
```

at several finite-sample construction levels.

This file records the analogous diagram for anchor common-context transport:

```text
AnchorCommonContextTransport ⇒ ExposingContextTransport.
```

At each target level, the common-context transport target maps to the
corresponding exposing transport target:

* grammar-rule builder;
* rule coverage;
* component package;
* component enumeration.

No new semantic principle is introduced here.  The exposing transport is
obtained through the already packaged common-context obligation route.

No theorem here uses `sorry`.
-/

namespace MCFG

universe u v w

section CommonToExposingDiagram

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}
variable {f : Nat}
variable {T : TrimmedOutputTypePresentation G obs}
variable {D : TrimmedPresentationPreCoreData T f}

namespace TrimmedPresentationGrammarBuilderCommonTransportTarget

/-- Grammar-builder common-transport target viewed as the corresponding
grammar-builder exposing-transport target. -/
def toGrammarBuilderExposingTransportTarget
    (C : TrimmedPresentationGrammarBuilderCommonTransportTarget D) :
    TrimmedPresentationGrammarBuilderExposingTransportTarget D where
  builder := C.builder
  exposingTransport := C.toExposingTransportObligations.exposingTransport
  splicingConstructor := C.splicingConstructor
  fanout := C.fanout
  promise := C.promise

/-- Grammar-builder common-transport target viewed as the older
grammar-builder exposing target. -/
def toGrammarBuilderExposingTarget
    (C : TrimmedPresentationGrammarBuilderCommonTransportTarget D) :
    TrimmedPresentationGrammarBuilderExposingTarget D :=
  C.toGrammarBuilderExposingTransportTarget.toGrammarBuilderExposingTarget

/-- Final reachable data obtained through the exposing leg. -/
noncomputable def toFinalReachableDataViaExposing
    (C : TrimmedPresentationGrammarBuilderCommonTransportTarget D) :
    FinalReachableData G
      C.toGrammarBuilderExposingTransportTarget.sample obs f :=
  C.toGrammarBuilderExposingTransportTarget.toFinalReachableData

/-- Reachable identification through the exposing leg. -/
theorem identifies_from_positive_text_via_exposing
    (C : TrimmedPresentationGrammarBuilderCommonTransportTarget D) :
    ∀ Ttxt : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        Ttxt :=
  C.toGrammarBuilderExposingTransportTarget.identifies_from_positive_text

/-- Prefix exactness through the exposing leg. -/
theorem prefix_exact_eventually_via_exposing
    (C : TrimmedPresentationGrammarBuilderCommonTransportTarget D) :
    ∀ Ttxt : TextFor G.StringLanguage,
      ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
        ReachableSampleStringLanguage (Ttxt.prefixSample n) obs f =
          G.StringLanguage :=
  C.toGrammarBuilderExposingTransportTarget.prefix_exact_eventually

/-- Positive finite-superset exactness through the exposing leg. -/
theorem exact_for_positive_superset_via_exposing
    (C : TrimmedPresentationGrammarBuilderCommonTransportTarget D)
    {K : Finset (Word α)}
    (hCK :
      (C.toGrammarBuilderExposingTransportTarget.sample : Set (Word α)) ⊆
        (K : Set (Word α)))
    (hKpos : (K : Set (Word α)) ⊆ G.StringLanguage) :
    ReachableSampleStringLanguage K obs f = G.StringLanguage :=
  C.toGrammarBuilderExposingTransportTarget.exact_for_positive_superset hCK hKpos

end TrimmedPresentationGrammarBuilderCommonTransportTarget


namespace TrimmedPresentationRuleCoverageCommonTransportTarget

/-- Rule-coverage common-transport target viewed as the corresponding exposing
target. -/
def toRuleCoverageExposingTransportTarget
    (C : TrimmedPresentationRuleCoverageCommonTransportTarget D) :
    TrimmedPresentationRuleCoverageExposingTarget D where
  coverage := C.coverage
  baseNonterminals := C.baseNonterminals
  base_covers := C.base_covers
  arities := C.arities
  exposingTransport := C.toExposingTransportObligations.exposingTransport
  splicingConstructor := C.splicingConstructor
  fanout := C.fanout
  promise := C.promise

/-- Reachable identification through the exposing leg. -/
theorem identifies_from_positive_text_via_exposing
    (C : TrimmedPresentationRuleCoverageCommonTransportTarget D) :
    ∀ Ttxt : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        Ttxt :=
  C.toRuleCoverageExposingTransportTarget.identifies_from_positive_text

/-- Prefix exactness through the exposing leg. -/
theorem prefix_exact_eventually_via_exposing
    (C : TrimmedPresentationRuleCoverageCommonTransportTarget D) :
    ∀ Ttxt : TextFor G.StringLanguage,
      ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
        ReachableSampleStringLanguage (Ttxt.prefixSample n) obs f =
          G.StringLanguage :=
  C.toRuleCoverageExposingTransportTarget.prefix_exact_eventually

/-- Positive finite-superset exactness through the exposing leg. -/
theorem exact_for_positive_superset_via_exposing
    (C : TrimmedPresentationRuleCoverageCommonTransportTarget D)
    {K : Finset (Word α)}
    (hCK :
      (C.toRuleCoverageExposingTransportTarget.sample : Set (Word α)) ⊆
        (K : Set (Word α)))
    (hKpos : (K : Set (Word α)) ⊆ G.StringLanguage) :
    ReachableSampleStringLanguage K obs f = G.StringLanguage :=
  C.toRuleCoverageExposingTransportTarget.exact_for_positive_superset hCK hKpos

end TrimmedPresentationRuleCoverageCommonTransportTarget


namespace TrimmedPresentationComponentPackageCommonTransportTarget

/-- Component-package common-transport target viewed as the corresponding
exposing target. -/
def toComponentPackageExposingTransportTarget
    (C : TrimmedPresentationComponentPackageCommonTransportTarget D) :
    TrimmedPresentationComponentPackageExposingTarget D where
  components := C.components
  baseNonterminals := C.baseNonterminals
  base_covers := C.base_covers
  arities := C.arities
  exposingTransport := C.toExposingTransportObligations.exposingTransport
  splicingConstructor := C.splicingConstructor
  fanout := C.fanout
  promise := C.promise

/-- Reachable identification through the exposing leg. -/
theorem identifies_from_positive_text_via_exposing
    (C : TrimmedPresentationComponentPackageCommonTransportTarget D) :
    ∀ Ttxt : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        Ttxt :=
  C.toComponentPackageExposingTransportTarget.identifies_from_positive_text

/-- Prefix exactness through the exposing leg. -/
theorem prefix_exact_eventually_via_exposing
    (C : TrimmedPresentationComponentPackageCommonTransportTarget D) :
    ∀ Ttxt : TextFor G.StringLanguage,
      ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
        ReachableSampleStringLanguage (Ttxt.prefixSample n) obs f =
          G.StringLanguage :=
  C.toComponentPackageExposingTransportTarget.prefix_exact_eventually

/-- Positive finite-superset exactness through the exposing leg. -/
theorem exact_for_positive_superset_via_exposing
    (C : TrimmedPresentationComponentPackageCommonTransportTarget D)
    {K : Finset (Word α)}
    (hCK :
      (C.toComponentPackageExposingTransportTarget.sample : Set (Word α)) ⊆
        (K : Set (Word α)))
    (hKpos : (K : Set (Word α)) ⊆ G.StringLanguage) :
    ReachableSampleStringLanguage K obs f = G.StringLanguage :=
  C.toComponentPackageExposingTransportTarget.exact_for_positive_superset hCK hKpos

end TrimmedPresentationComponentPackageCommonTransportTarget


namespace TrimmedPresentationComponentEnumerationCommonTransportTarget

/-- Component-enumeration common-transport target viewed as the corresponding
exposing target. -/
def toComponentEnumerationExposingTransportTarget
    (C : TrimmedPresentationComponentEnumerationCommonTransportTarget D) :
    TrimmedPresentationComponentEnumerationExposingTarget D where
  enumeration := C.enumeration
  baseNonterminals := C.baseNonterminals
  base_covers := C.base_covers
  arities := C.arities
  exposingTransport := C.toExposingTransportObligations.exposingTransport
  splicingConstructor := C.splicingConstructor
  fanout := C.fanout
  promise := C.promise

/-- Reachable identification through the exposing leg. -/
theorem identifies_from_positive_text_via_exposing
    (C : TrimmedPresentationComponentEnumerationCommonTransportTarget D) :
    ∀ Ttxt : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        Ttxt :=
  C.toComponentEnumerationExposingTransportTarget.identifies_from_positive_text

/-- Prefix exactness through the exposing leg. -/
theorem prefix_exact_eventually_via_exposing
    (C : TrimmedPresentationComponentEnumerationCommonTransportTarget D) :
    ∀ Ttxt : TextFor G.StringLanguage,
      ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
        ReachableSampleStringLanguage (Ttxt.prefixSample n) obs f =
          G.StringLanguage :=
  C.toComponentEnumerationExposingTransportTarget.prefix_exact_eventually

/-- Positive finite-superset exactness through the exposing leg. -/
theorem exact_for_positive_superset_via_exposing
    (C : TrimmedPresentationComponentEnumerationCommonTransportTarget D)
    {K : Finset (Word α)}
    (hCK :
      (C.toComponentEnumerationExposingTransportTarget.sample : Set (Word α)) ⊆
        (K : Set (Word α)))
    (hKpos : (K : Set (Word α)) ⊆ G.StringLanguage) :
    ReachableSampleStringLanguage K obs f = G.StringLanguage :=
  C.toComponentEnumerationExposingTransportTarget.exact_for_positive_superset hCK hKpos

end TrimmedPresentationComponentEnumerationCommonTransportTarget

end CommonToExposingDiagram


section CommonToExposingDiagramTheorems

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}
variable {f : Nat}
variable {T : TrimmedOutputTypePresentation G obs}
variable {D : TrimmedPresentationPreCoreData T f}

/-- Diagram theorem: grammar-builder common-transport target identifies through
the exposing leg. -/
theorem trimmed_diagram_grammar_builder_common_to_exposing_identification
    (C : TrimmedPresentationGrammarBuilderCommonTransportTarget D) :
    ∀ Ttxt : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        Ttxt :=
  C.identifies_from_positive_text_via_exposing

/-- Diagram theorem: grammar-builder common-transport target is prefix-exact
through the exposing leg. -/
theorem trimmed_diagram_grammar_builder_common_to_exposing_prefix_exact
    (C : TrimmedPresentationGrammarBuilderCommonTransportTarget D) :
    ∀ Ttxt : TextFor G.StringLanguage,
      ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
        ReachableSampleStringLanguage (Ttxt.prefixSample n) obs f =
          G.StringLanguage :=
  C.prefix_exact_eventually_via_exposing

/-- Diagram theorem: rule-coverage common-transport target identifies through
the exposing leg. -/
theorem trimmed_diagram_rule_coverage_common_to_exposing_identification
    (C : TrimmedPresentationRuleCoverageCommonTransportTarget D) :
    ∀ Ttxt : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        Ttxt :=
  C.identifies_from_positive_text_via_exposing

/-- Diagram theorem: component-package common-transport target identifies
through the exposing leg. -/
theorem trimmed_diagram_component_package_common_to_exposing_identification
    (C : TrimmedPresentationComponentPackageCommonTransportTarget D) :
    ∀ Ttxt : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        Ttxt :=
  C.identifies_from_positive_text_via_exposing

/-- Diagram theorem: component-enumeration common-transport target identifies
through the exposing leg. -/
theorem trimmed_diagram_component_enumeration_common_to_exposing_identification
    (C : TrimmedPresentationComponentEnumerationCommonTransportTarget D) :
    ∀ Ttxt : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        Ttxt :=
  C.identifies_from_positive_text_via_exposing

end CommonToExposingDiagramTheorems

end MCFG
