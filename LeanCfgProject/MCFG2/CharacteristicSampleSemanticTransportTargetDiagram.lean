/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG2.CharacteristicSampleSameContextTransportTargetLevels

/-!
# CharacteristicSampleSemanticTransportTargetDiagram.lean

Eighty-sixth clean Lean experiment for the fixed-observation MCFG project.

The preceding files introduced three semantic transport entrances:

* same-context transport;
* exposing-context transport;
* anchor common-context transport.

This file records the most basic conversion diagram for the same-context
route.  At each finite-sample construction level, same-context transport
induces exposing-context transport, and therefore the same-context target maps
to the corresponding exposing target.

The levels covered here are:

* grammar-rule builder;
* rule coverage;
* component package;
* component enumeration.

No new semantic principle is introduced here.  The conversion is the already
verified

```lean
TrimmedPresentationExposingContextTransport.ofSameContextTransport
```

lifted to the target records.

No theorem here uses `sorry`.
-/

namespace MCFG

universe u v w

section SameToExposingDiagram

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}
variable {f : Nat}
variable {T : TrimmedOutputTypePresentation G obs}
variable {D : TrimmedPresentationPreCoreData T f}

namespace TrimmedPresentationGrammarBuilderSameContextTransportTarget

/-- Same-context grammar-builder target viewed as an exposing-transport
grammar-builder target. -/
def toGrammarBuilderExposingTransportTarget
    (C : TrimmedPresentationGrammarBuilderSameContextTransportTarget D) :
    TrimmedPresentationGrammarBuilderExposingTransportTarget D where
  builder := C.builder
  exposingTransport :=
    TrimmedPresentationExposingContextTransport.ofSameContextTransport
      C.sameContextTransport
  splicingConstructor := C.splicingConstructor
  fanout := C.fanout
  promise := C.promise

/-- Same-context grammar-builder target viewed as the older grammar-builder
exposing target. -/
def toGrammarBuilderExposingTarget
    (C : TrimmedPresentationGrammarBuilderSameContextTransportTarget D) :
    TrimmedPresentationGrammarBuilderExposingTarget D :=
  C.toGrammarBuilderExposingTransportTarget.toGrammarBuilderExposingTarget

/-- The final reachable data obtained through the exposing leg agrees
definitionally with the exposing-target route. -/
noncomputable def toFinalReachableDataViaExposing
    (C : TrimmedPresentationGrammarBuilderSameContextTransportTarget D) :
    FinalReachableData G C.toGrammarBuilderExposingTransportTarget.sample obs f :=
  C.toGrammarBuilderExposingTransportTarget.toFinalReachableData

/-- Reachable identification through the exposing leg. -/
theorem identifies_from_positive_text_via_exposing
    (C : TrimmedPresentationGrammarBuilderSameContextTransportTarget D) :
    ∀ Ttxt : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        Ttxt :=
  C.toGrammarBuilderExposingTransportTarget.identifies_from_positive_text

/-- Prefix exactness through the exposing leg. -/
theorem prefix_exact_eventually_via_exposing
    (C : TrimmedPresentationGrammarBuilderSameContextTransportTarget D) :
    ∀ Ttxt : TextFor G.StringLanguage,
      ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
        ReachableSampleStringLanguage (Ttxt.prefixSample n) obs f =
          G.StringLanguage :=
  C.toGrammarBuilderExposingTransportTarget.prefix_exact_eventually

end TrimmedPresentationGrammarBuilderSameContextTransportTarget


namespace TrimmedPresentationRuleCoverageSameContextTransportTarget

/-- Same-context rule-coverage target viewed as the corresponding exposing
target. -/
def toRuleCoverageExposingTransportTarget
    (C : TrimmedPresentationRuleCoverageSameContextTransportTarget D) :
    TrimmedPresentationRuleCoverageExposingTarget D :=
  C.toRuleCoverageExposingTarget

/-- Reachable identification through the exposing leg. -/
theorem identifies_from_positive_text_via_exposing
    (C : TrimmedPresentationRuleCoverageSameContextTransportTarget D) :
    ∀ Ttxt : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        Ttxt :=
  C.toRuleCoverageExposingTransportTarget.identifies_from_positive_text

/-- Prefix exactness through the exposing leg. -/
theorem prefix_exact_eventually_via_exposing
    (C : TrimmedPresentationRuleCoverageSameContextTransportTarget D) :
    ∀ Ttxt : TextFor G.StringLanguage,
      ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
        ReachableSampleStringLanguage (Ttxt.prefixSample n) obs f =
          G.StringLanguage :=
  C.toRuleCoverageExposingTransportTarget.prefix_exact_eventually

end TrimmedPresentationRuleCoverageSameContextTransportTarget


namespace TrimmedPresentationComponentPackageSameContextTransportTarget

/-- Same-context component-package target viewed as the corresponding exposing
target. -/
def toComponentPackageExposingTransportTarget
    (C : TrimmedPresentationComponentPackageSameContextTransportTarget D) :
    TrimmedPresentationComponentPackageExposingTarget D :=
  C.toComponentPackageExposingTarget

/-- Reachable identification through the exposing leg. -/
theorem identifies_from_positive_text_via_exposing
    (C : TrimmedPresentationComponentPackageSameContextTransportTarget D) :
    ∀ Ttxt : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        Ttxt :=
  C.toComponentPackageExposingTransportTarget.identifies_from_positive_text

/-- Prefix exactness through the exposing leg. -/
theorem prefix_exact_eventually_via_exposing
    (C : TrimmedPresentationComponentPackageSameContextTransportTarget D) :
    ∀ Ttxt : TextFor G.StringLanguage,
      ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
        ReachableSampleStringLanguage (Ttxt.prefixSample n) obs f =
          G.StringLanguage :=
  C.toComponentPackageExposingTransportTarget.prefix_exact_eventually

end TrimmedPresentationComponentPackageSameContextTransportTarget


namespace TrimmedPresentationComponentEnumerationSameContextTransportTarget

/-- Same-context component-enumeration target viewed as the corresponding
exposing target. -/
def toComponentEnumerationExposingTransportTarget
    (C : TrimmedPresentationComponentEnumerationSameContextTransportTarget D) :
    TrimmedPresentationComponentEnumerationExposingTarget D :=
  C.toComponentEnumerationExposingTarget

/-- Reachable identification through the exposing leg. -/
theorem identifies_from_positive_text_via_exposing
    (C : TrimmedPresentationComponentEnumerationSameContextTransportTarget D) :
    ∀ Ttxt : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        Ttxt :=
  C.toComponentEnumerationExposingTransportTarget.identifies_from_positive_text

/-- Prefix exactness through the exposing leg. -/
theorem prefix_exact_eventually_via_exposing
    (C : TrimmedPresentationComponentEnumerationSameContextTransportTarget D) :
    ∀ Ttxt : TextFor G.StringLanguage,
      ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
        ReachableSampleStringLanguage (Ttxt.prefixSample n) obs f =
          G.StringLanguage :=
  C.toComponentEnumerationExposingTransportTarget.prefix_exact_eventually

end TrimmedPresentationComponentEnumerationSameContextTransportTarget

end SameToExposingDiagram


section DiagramTheorems

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}
variable {f : Nat}
variable {T : TrimmedOutputTypePresentation G obs}
variable {D : TrimmedPresentationPreCoreData T f}

/-- Diagram theorem: grammar-builder same-context target identifies through the
exposing leg. -/
theorem trimmed_diagram_grammar_builder_same_to_exposing_identification
    (C : TrimmedPresentationGrammarBuilderSameContextTransportTarget D) :
    ∀ Ttxt : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        Ttxt :=
  C.identifies_from_positive_text_via_exposing

/-- Diagram theorem: grammar-builder same-context target is prefix-exact through
the exposing leg. -/
theorem trimmed_diagram_grammar_builder_same_to_exposing_prefix_exact
    (C : TrimmedPresentationGrammarBuilderSameContextTransportTarget D) :
    ∀ Ttxt : TextFor G.StringLanguage,
      ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
        ReachableSampleStringLanguage (Ttxt.prefixSample n) obs f =
          G.StringLanguage :=
  C.prefix_exact_eventually_via_exposing

/-- Diagram theorem: rule-coverage same-context target identifies through the
exposing leg. -/
theorem trimmed_diagram_rule_coverage_same_to_exposing_identification
    (C : TrimmedPresentationRuleCoverageSameContextTransportTarget D) :
    ∀ Ttxt : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        Ttxt :=
  C.identifies_from_positive_text_via_exposing

/-- Diagram theorem: component-package same-context target identifies through
the exposing leg. -/
theorem trimmed_diagram_component_package_same_to_exposing_identification
    (C : TrimmedPresentationComponentPackageSameContextTransportTarget D) :
    ∀ Ttxt : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        Ttxt :=
  C.identifies_from_positive_text_via_exposing

/-- Diagram theorem: component-enumeration same-context target identifies
through the exposing leg. -/
theorem trimmed_diagram_component_enumeration_same_to_exposing_identification
    (C : TrimmedPresentationComponentEnumerationSameContextTransportTarget D) :
    ∀ Ttxt : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        Ttxt :=
  C.identifies_from_positive_text_via_exposing

end DiagramTheorems

end MCFG
