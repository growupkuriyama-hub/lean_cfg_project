/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG2.CharacteristicSampleCommonToExposingTargetDiagram

/-!
# CharacteristicSampleSemanticMainTheorems.lean

Eighty-eighth clean Lean experiment for the fixed-observation MCFG project.

The previous files introduced many transport targets and diagrams.  This file
collects the theorem-facing names that are closest to the paper-level statement.

The preferred semantic entrance is the common-context route:

```text
GrammarRuleBuilder
+ AnchorCommonContextTransport
+ NamedContextSplicingConstructor
+ fanout/promise
⇒ reachable identification.
```

For debugging and comparison, this file also records the same final conclusion
from:

* direct exposing-context transport;
* stronger same-context transport;
* rule-coverage level common/exposing/same transport;
* component-package and component-enumeration level transport.

No new mathematical principle is introduced here.  This file is a theorem-name
index for the already verified target hierarchy.

No theorem here uses `sorry`.
-/

namespace MCFG

universe u v w

section GrammarBuilderMainTheorems

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}
variable {f : Nat}
variable {T : TrimmedOutputTypePresentation G obs}
variable {D : TrimmedPresentationPreCoreData T f}

/-- Paper-facing main theorem name for the preferred grammar-builder +
anchor-common-context transport route. -/
theorem trimmed_main_grammar_builder_common_transport_identifies
    (C : TrimmedPresentationGrammarBuilderCommonTransportTarget D) :
    ∀ Ttxt : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        Ttxt :=
  C.identifies_from_positive_text

/-- Prefix-exact version of the preferred grammar-builder +
anchor-common-context transport route. -/
theorem trimmed_main_grammar_builder_common_transport_prefix_exact
    (C : TrimmedPresentationGrammarBuilderCommonTransportTarget D) :
    ∀ Ttxt : TextFor G.StringLanguage,
      ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
        ReachableSampleStringLanguage (Ttxt.prefixSample n) obs f =
          G.StringLanguage :=
  C.prefix_exact_eventually

/-- Finite positive-superset exactness for the preferred grammar-builder +
anchor-common-context transport route. -/
theorem trimmed_main_grammar_builder_common_transport_exact_for_positive_superset
    (C : TrimmedPresentationGrammarBuilderCommonTransportTarget D)
    {K : Finset (Word α)}
    (hCK : (C.sample : Set (Word α)) ⊆ (K : Set (Word α)))
    (hKpos : (K : Set (Word α)) ⊆ G.StringLanguage) :
    ReachableSampleStringLanguage K obs f = G.StringLanguage :=
  C.exact_for_positive_superset hCK hKpos

/-- Paper-facing theorem name for the direct exposing-transport route. -/
theorem trimmed_main_grammar_builder_exposing_transport_identifies
    (C : TrimmedPresentationGrammarBuilderExposingTransportTarget D) :
    ∀ Ttxt : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        Ttxt :=
  C.identifies_from_positive_text

/-- Prefix-exact theorem for the direct exposing-transport route. -/
theorem trimmed_main_grammar_builder_exposing_transport_prefix_exact
    (C : TrimmedPresentationGrammarBuilderExposingTransportTarget D) :
    ∀ Ttxt : TextFor G.StringLanguage,
      ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
        ReachableSampleStringLanguage (Ttxt.prefixSample n) obs f =
          G.StringLanguage :=
  C.prefix_exact_eventually

/-- Finite positive-superset exactness for the direct exposing-transport route. -/
theorem trimmed_main_grammar_builder_exposing_transport_exact_for_positive_superset
    (C : TrimmedPresentationGrammarBuilderExposingTransportTarget D)
    {K : Finset (Word α)}
    (hCK : (C.sample : Set (Word α)) ⊆ (K : Set (Word α)))
    (hKpos : (K : Set (Word α)) ⊆ G.StringLanguage) :
    ReachableSampleStringLanguage K obs f = G.StringLanguage :=
  C.exact_for_positive_superset hCK hKpos

/-- Debugging theorem name for the stronger same-context transport route. -/
theorem trimmed_main_grammar_builder_same_context_transport_identifies
    (C : TrimmedPresentationGrammarBuilderSameContextTransportTarget D) :
    ∀ Ttxt : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        Ttxt :=
  C.identifies_from_positive_text

/-- Prefix-exact theorem for the stronger same-context transport route. -/
theorem trimmed_main_grammar_builder_same_context_transport_prefix_exact
    (C : TrimmedPresentationGrammarBuilderSameContextTransportTarget D) :
    ∀ Ttxt : TextFor G.StringLanguage,
      ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
        ReachableSampleStringLanguage (Ttxt.prefixSample n) obs f =
          G.StringLanguage :=
  C.prefix_exact_eventually

/-- Finite positive-superset exactness for the stronger same-context route. -/
theorem trimmed_main_grammar_builder_same_context_transport_exact_for_positive_superset
    (C : TrimmedPresentationGrammarBuilderSameContextTransportTarget D)
    {K : Finset (Word α)}
    (hCK : (C.sample : Set (Word α)) ⊆ (K : Set (Word α)))
    (hKpos : (K : Set (Word α)) ⊆ G.StringLanguage) :
    ReachableSampleStringLanguage K obs f = G.StringLanguage :=
  C.exact_for_positive_superset hCK hKpos

end GrammarBuilderMainTheorems


section RuleCoverageMainTheorems

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}
variable {f : Nat}
variable {T : TrimmedOutputTypePresentation G obs}
variable {D : TrimmedPresentationPreCoreData T f}

/-- Rule-coverage-level main theorem using anchor common-context transport. -/
theorem trimmed_main_rule_coverage_common_transport_identifies
    (C : TrimmedPresentationRuleCoverageCommonTransportTarget D) :
    ∀ Ttxt : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        Ttxt :=
  C.identifies_from_positive_text

/-- Rule-coverage-level prefix exactness using anchor common-context transport. -/
theorem trimmed_main_rule_coverage_common_transport_prefix_exact
    (C : TrimmedPresentationRuleCoverageCommonTransportTarget D) :
    ∀ Ttxt : TextFor G.StringLanguage,
      ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
        ReachableSampleStringLanguage (Ttxt.prefixSample n) obs f =
          G.StringLanguage :=
  C.prefix_exact_eventually

/-- Rule-coverage-level finite positive-superset exactness using anchor
common-context transport. -/
theorem trimmed_main_rule_coverage_common_transport_exact_for_positive_superset
    (C : TrimmedPresentationRuleCoverageCommonTransportTarget D)
    {K : Finset (Word α)}
    (hCK : (C.sample : Set (Word α)) ⊆ (K : Set (Word α)))
    (hKpos : (K : Set (Word α)) ⊆ G.StringLanguage) :
    ReachableSampleStringLanguage K obs f = G.StringLanguage :=
  C.exact_for_positive_superset hCK hKpos

/-- Rule-coverage-level main theorem using direct exposing-context transport. -/
theorem trimmed_main_rule_coverage_exposing_transport_identifies
    (C : TrimmedPresentationRuleCoverageExposingTarget D) :
    ∀ Ttxt : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        Ttxt :=
  C.identifies_from_positive_text

/-- Rule-coverage-level prefix exactness using direct exposing-context
transport. -/
theorem trimmed_main_rule_coverage_exposing_transport_prefix_exact
    (C : TrimmedPresentationRuleCoverageExposingTarget D) :
    ∀ Ttxt : TextFor G.StringLanguage,
      ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
        ReachableSampleStringLanguage (Ttxt.prefixSample n) obs f =
          G.StringLanguage :=
  C.prefix_exact_eventually

/-- Rule-coverage-level main theorem using stronger same-context transport. -/
theorem trimmed_main_rule_coverage_same_context_transport_identifies
    (C : TrimmedPresentationRuleCoverageSameContextTransportTarget D) :
    ∀ Ttxt : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        Ttxt :=
  C.identifies_from_positive_text

/-- Rule-coverage-level prefix exactness using stronger same-context transport. -/
theorem trimmed_main_rule_coverage_same_context_transport_prefix_exact
    (C : TrimmedPresentationRuleCoverageSameContextTransportTarget D) :
    ∀ Ttxt : TextFor G.StringLanguage,
      ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
        ReachableSampleStringLanguage (Ttxt.prefixSample n) obs f =
          G.StringLanguage :=
  C.prefix_exact_eventually

end RuleCoverageMainTheorems


section ComponentLevelMainTheorems

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}
variable {f : Nat}
variable {T : TrimmedOutputTypePresentation G obs}
variable {D : TrimmedPresentationPreCoreData T f}

/-- Component-package-level main theorem using anchor common-context transport. -/
theorem trimmed_main_component_package_common_transport_identifies
    (C : TrimmedPresentationComponentPackageCommonTransportTarget D) :
    ∀ Ttxt : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        Ttxt :=
  C.identifies_from_positive_text

/-- Component-package-level prefix exactness using anchor common-context
transport. -/
theorem trimmed_main_component_package_common_transport_prefix_exact
    (C : TrimmedPresentationComponentPackageCommonTransportTarget D) :
    ∀ Ttxt : TextFor G.StringLanguage,
      ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
        ReachableSampleStringLanguage (Ttxt.prefixSample n) obs f =
          G.StringLanguage :=
  C.prefix_exact_eventually

/-- Component-package-level main theorem using exposing-context transport. -/
theorem trimmed_main_component_package_exposing_transport_identifies
    (C : TrimmedPresentationComponentPackageExposingTarget D) :
    ∀ Ttxt : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        Ttxt :=
  C.identifies_from_positive_text

/-- Component-package-level main theorem using same-context transport. -/
theorem trimmed_main_component_package_same_context_transport_identifies
    (C : TrimmedPresentationComponentPackageSameContextTransportTarget D) :
    ∀ Ttxt : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        Ttxt :=
  C.identifies_from_positive_text

/-- Component-enumeration-level main theorem using anchor common-context
transport. -/
theorem trimmed_main_component_enumeration_common_transport_identifies
    (C : TrimmedPresentationComponentEnumerationCommonTransportTarget D) :
    ∀ Ttxt : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        Ttxt :=
  C.identifies_from_positive_text

/-- Component-enumeration-level prefix exactness using anchor common-context
transport. -/
theorem trimmed_main_component_enumeration_common_transport_prefix_exact
    (C : TrimmedPresentationComponentEnumerationCommonTransportTarget D) :
    ∀ Ttxt : TextFor G.StringLanguage,
      ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
        ReachableSampleStringLanguage (Ttxt.prefixSample n) obs f =
          G.StringLanguage :=
  C.prefix_exact_eventually

/-- Component-enumeration-level main theorem using exposing-context transport. -/
theorem trimmed_main_component_enumeration_exposing_transport_identifies
    (C : TrimmedPresentationComponentEnumerationExposingTarget D) :
    ∀ Ttxt : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        Ttxt :=
  C.identifies_from_positive_text

/-- Component-enumeration-level main theorem using same-context transport. -/
theorem trimmed_main_component_enumeration_same_context_transport_identifies
    (C : TrimmedPresentationComponentEnumerationSameContextTransportTarget D) :
    ∀ Ttxt : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        Ttxt :=
  C.identifies_from_positive_text

end ComponentLevelMainTheorems


section DiagramFacingMainTheorems

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}
variable {f : Nat}
variable {T : TrimmedOutputTypePresentation G obs}
variable {D : TrimmedPresentationPreCoreData T f}

/-- Same-context grammar-builder route, explicitly through the exposing leg. -/
theorem trimmed_main_same_context_via_exposing_identifies
    (C : TrimmedPresentationGrammarBuilderSameContextTransportTarget D) :
    ∀ Ttxt : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        Ttxt :=
  C.identifies_from_positive_text_via_exposing

/-- Common-context grammar-builder route, explicitly through the exposing leg. -/
theorem trimmed_main_common_context_via_exposing_identifies
    (C : TrimmedPresentationGrammarBuilderCommonTransportTarget D) :
    ∀ Ttxt : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        Ttxt :=
  C.identifies_from_positive_text_via_exposing

/-- Same-context grammar-builder route, prefix-exact through the exposing leg. -/
theorem trimmed_main_same_context_via_exposing_prefix_exact
    (C : TrimmedPresentationGrammarBuilderSameContextTransportTarget D) :
    ∀ Ttxt : TextFor G.StringLanguage,
      ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
        ReachableSampleStringLanguage (Ttxt.prefixSample n) obs f =
          G.StringLanguage :=
  C.prefix_exact_eventually_via_exposing

/-- Common-context grammar-builder route, prefix-exact through the exposing leg. -/
theorem trimmed_main_common_context_via_exposing_prefix_exact
    (C : TrimmedPresentationGrammarBuilderCommonTransportTarget D) :
    ∀ Ttxt : TextFor G.StringLanguage,
      ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
        ReachableSampleStringLanguage (Ttxt.prefixSample n) obs f =
          G.StringLanguage :=
  C.prefix_exact_eventually_via_exposing

end DiagramFacingMainTheorems

end MCFG
