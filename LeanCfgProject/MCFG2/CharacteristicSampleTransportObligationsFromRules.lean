/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG.CharacteristicSampleTransportObligationsFromComponents

/-!
# CharacteristicSampleTransportObligationsFromRules.lean

Seventy-sixth clean Lean experiment for the fixed-observation MCFG project.

The preceding file connected component packages/enumerations to the transport
obligation routes.  This file moves one level higher and connects the
rule-oriented construction layers:

* `TrimmedPresentationRuleEnumeration`;
* `TrimmedPresentationRuleCoveragePackage`;
* `TrimmedPresentationGrammarRuleBuilder`.

The route is now:

```text
rule enumeration / rule coverage / grammar-rule builder
⇒ component package
⇒ positive finite-union builder
⇒ witness sample
⇒ transport obligations
⇒ reachable identification.
```

No new semantic principle is introduced here.  This is interface plumbing for
the future concrete `CS(G̃₀)` construction.

No theorem here uses `sorry`.
-/

namespace MCFG

universe u v w

section ExposingTransportFromRuleEnumeration

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}
variable {f : Nat}
variable {T : TrimmedOutputTypePresentation G obs}

/-- Exposing-context transport obligations whose sample side is supplied by a
rule enumeration. -/
structure TrimmedPresentationExposingTransportFromRuleEnumeration
    (D : TrimmedPresentationPreCoreData T f) where
  ruleEnumeration : TrimmedPresentationRuleEnumeration D

  baseNonterminals : Finset N
  base_covers :
    ∀ A : N, A ∈ baseNonterminals

  arities : TrimmedPresentationRuleAritySelectors D
  exposingTransport : TrimmedPresentationExposingContextTransport D

  splicingConstructor : NamedContextSplicingConstructor α
  fanout : G.FanoutAtMost f
  promise : FixedNamedTupleSubstitutable f obs G.StringLanguage

namespace TrimmedPresentationExposingTransportFromRuleEnumeration

variable {D : TrimmedPresentationPreCoreData T f}

/-- The component package induced by the rule enumeration. -/
def toComponentPackage
    (O : TrimmedPresentationExposingTransportFromRuleEnumeration D) :
    TrimmedPresentationComponentPackage D :=
  O.ruleEnumeration.toComponentPackage

/-- Convert to the component-package transport route. -/
def toTransportFromComponentPackage
    (O : TrimmedPresentationExposingTransportFromRuleEnumeration D) :
    TrimmedPresentationExposingTransportFromComponentPackage D where
  components := O.toComponentPackage
  baseNonterminals := O.baseNonterminals
  base_covers := O.base_covers
  arities := O.arities
  exposingTransport := O.exposingTransport
  splicingConstructor := O.splicingConstructor
  fanout := O.fanout
  promise := O.promise

/-- Convert to the compact exposing-transport obligation package. -/
def toObligations
    (O : TrimmedPresentationExposingTransportFromRuleEnumeration D) :
    TrimmedPresentationExposingTransportObligations D :=
  O.toTransportFromComponentPackage.toObligations

/-- The finite sample produced by the resulting obligation package. -/
def sample
    (O : TrimmedPresentationExposingTransportFromRuleEnumeration D) :
    Finset (Word α) :=
  O.toTransportFromComponentPackage.sample

/-- The produced finite sample is positive. -/
theorem sample_positive
    (O : TrimmedPresentationExposingTransportFromRuleEnumeration D) :
    (O.sample : Set (Word α)) ⊆ G.StringLanguage :=
  O.toTransportFromComponentPackage.sample_positive

/-- The produced finite sample contains all required witness words. -/
theorem contains_witnesses
    (O : TrimmedPresentationExposingTransportFromRuleEnumeration D) :
    TrimmedPresentationWitnessWordSet D ⊆
      (O.sample : Set (Word α)) :=
  O.toTransportFromComponentPackage.contains_witnesses

/-- Convert directly to final reachable data. -/
def toFinalReachableData
    (O : TrimmedPresentationExposingTransportFromRuleEnumeration D) :
    FinalReachableData G O.sample obs f :=
  O.toTransportFromComponentPackage.toFinalReachableData

/-- The produced sample is a characteristic sample for the reachable learner. -/
theorem characteristic_sample
    (O : TrimmedPresentationExposingTransportFromRuleEnumeration D) :
    CharacteristicSample
      (reachableHypLanguage obs f)
      (reachableSampleLearner (α := α))
      O.sample
      G.StringLanguage :=
  O.toTransportFromComponentPackage.characteristic_sample

/-- Eventual prefix-exact reconstruction. -/
theorem prefix_exact_eventually
    (O : TrimmedPresentationExposingTransportFromRuleEnumeration D) :
    ∀ Ttxt : TextFor G.StringLanguage,
      ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
        ReachableSampleStringLanguage (Ttxt.prefixSample n) obs f =
          G.StringLanguage :=
  O.toTransportFromComponentPackage.prefix_exact_eventually

/-- Reachable Gold identification. -/
theorem identifies_from_positive_text
    (O : TrimmedPresentationExposingTransportFromRuleEnumeration D) :
    ∀ Ttxt : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        Ttxt :=
  O.toTransportFromComponentPackage.identifies_from_positive_text

end TrimmedPresentationExposingTransportFromRuleEnumeration

end ExposingTransportFromRuleEnumeration


section CommonContextFromRuleEnumeration

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}
variable {f : Nat}
variable {T : TrimmedOutputTypePresentation G obs}

/-- Common-context transport obligations whose sample side is supplied by a
rule enumeration. -/
structure TrimmedPresentationCommonContextFromRuleEnumeration
    (D : TrimmedPresentationPreCoreData T f) where
  ruleEnumeration : TrimmedPresentationRuleEnumeration D

  commonData : TrimmedPresentationAnchorCommonContextCoreData D
  splicingConstructor : NamedContextSplicingConstructor α
  fanout : G.FanoutAtMost f
  promise : FixedNamedTupleSubstitutable f obs G.StringLanguage

namespace TrimmedPresentationCommonContextFromRuleEnumeration

variable {D : TrimmedPresentationPreCoreData T f}

/-- The component package induced by the rule enumeration. -/
def toComponentPackage
    (O : TrimmedPresentationCommonContextFromRuleEnumeration D) :
    TrimmedPresentationComponentPackage D :=
  O.ruleEnumeration.toComponentPackage

/-- Convert to the component-package common-context route. -/
def toTransportFromComponentPackage
    (O : TrimmedPresentationCommonContextFromRuleEnumeration D) :
    TrimmedPresentationCommonContextFromComponentPackage D where
  components := O.toComponentPackage
  commonData := O.commonData
  splicingConstructor := O.splicingConstructor
  fanout := O.fanout
  promise := O.promise

/-- Convert to the compact common-context obligation package. -/
def toObligations
    (O : TrimmedPresentationCommonContextFromRuleEnumeration D) :
    TrimmedPresentationCommonContextTransportObligations D :=
  O.toTransportFromComponentPackage.toObligations

/-- Convert to exposing-transport obligations through the common-context route. -/
def toExposingTransportObligations
    (O : TrimmedPresentationCommonContextFromRuleEnumeration D) :
    TrimmedPresentationExposingTransportObligations D :=
  O.toTransportFromComponentPackage.toExposingTransportObligations

/-- The finite sample produced by the resulting obligation package. -/
def sample
    (O : TrimmedPresentationCommonContextFromRuleEnumeration D) :
    Finset (Word α) :=
  O.toTransportFromComponentPackage.sample

/-- The produced finite sample is positive. -/
theorem sample_positive
    (O : TrimmedPresentationCommonContextFromRuleEnumeration D) :
    (O.sample : Set (Word α)) ⊆ G.StringLanguage :=
  O.toTransportFromComponentPackage.sample_positive

/-- The produced finite sample contains all required witness words. -/
theorem contains_witnesses
    (O : TrimmedPresentationCommonContextFromRuleEnumeration D) :
    TrimmedPresentationWitnessWordSet D ⊆
      (O.sample : Set (Word α)) :=
  O.toTransportFromComponentPackage.contains_witnesses

/-- Convert directly to final reachable data. -/
def toFinalReachableData
    (O : TrimmedPresentationCommonContextFromRuleEnumeration D) :
    FinalReachableData G O.sample obs f :=
  O.toTransportFromComponentPackage.toFinalReachableData

/-- The produced sample is a characteristic sample for the reachable learner. -/
theorem characteristic_sample
    (O : TrimmedPresentationCommonContextFromRuleEnumeration D) :
    CharacteristicSample
      (reachableHypLanguage obs f)
      (reachableSampleLearner (α := α))
      O.sample
      G.StringLanguage :=
  O.toTransportFromComponentPackage.characteristic_sample

/-- Eventual prefix-exact reconstruction. -/
theorem prefix_exact_eventually
    (O : TrimmedPresentationCommonContextFromRuleEnumeration D) :
    ∀ Ttxt : TextFor G.StringLanguage,
      ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
        ReachableSampleStringLanguage (Ttxt.prefixSample n) obs f =
          G.StringLanguage :=
  O.toTransportFromComponentPackage.prefix_exact_eventually

/-- Reachable Gold identification. -/
theorem identifies_from_positive_text
    (O : TrimmedPresentationCommonContextFromRuleEnumeration D) :
    ∀ Ttxt : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        Ttxt :=
  O.toTransportFromComponentPackage.identifies_from_positive_text

end TrimmedPresentationCommonContextFromRuleEnumeration

end CommonContextFromRuleEnumeration


section ExposingTransportFromRuleCoverage

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}
variable {f : Nat}
variable {T : TrimmedOutputTypePresentation G obs}

/-- Exposing-context transport obligations whose sample side is supplied by a
rule-coverage package. -/
structure TrimmedPresentationExposingTransportFromRuleCoverage
    (D : TrimmedPresentationPreCoreData T f) where
  coverage : TrimmedPresentationRuleCoveragePackage D

  baseNonterminals : Finset N
  base_covers :
    ∀ A : N, A ∈ baseNonterminals

  arities : TrimmedPresentationRuleAritySelectors D
  exposingTransport : TrimmedPresentationExposingContextTransport D

  splicingConstructor : NamedContextSplicingConstructor α
  fanout : G.FanoutAtMost f
  promise : FixedNamedTupleSubstitutable f obs G.StringLanguage

namespace TrimmedPresentationExposingTransportFromRuleCoverage

variable {D : TrimmedPresentationPreCoreData T f}

/-- The rule enumeration induced by coverage. -/
def toRuleEnumeration
    (O : TrimmedPresentationExposingTransportFromRuleCoverage D) :
    TrimmedPresentationRuleEnumeration D :=
  O.coverage.toRuleEnumeration

/-- Convert to the rule-enumeration transport route. -/
def toTransportFromRuleEnumeration
    (O : TrimmedPresentationExposingTransportFromRuleCoverage D) :
    TrimmedPresentationExposingTransportFromRuleEnumeration D where
  ruleEnumeration := O.toRuleEnumeration
  baseNonterminals := O.baseNonterminals
  base_covers := O.base_covers
  arities := O.arities
  exposingTransport := O.exposingTransport
  splicingConstructor := O.splicingConstructor
  fanout := O.fanout
  promise := O.promise

/-- Convert to the compact exposing-transport obligation package. -/
def toObligations
    (O : TrimmedPresentationExposingTransportFromRuleCoverage D) :
    TrimmedPresentationExposingTransportObligations D :=
  O.toTransportFromRuleEnumeration.toObligations

/-- The finite sample produced by the resulting obligation package. -/
def sample
    (O : TrimmedPresentationExposingTransportFromRuleCoverage D) :
    Finset (Word α) :=
  O.toTransportFromRuleEnumeration.sample

/-- The produced finite sample is positive. -/
theorem sample_positive
    (O : TrimmedPresentationExposingTransportFromRuleCoverage D) :
    (O.sample : Set (Word α)) ⊆ G.StringLanguage :=
  O.toTransportFromRuleEnumeration.sample_positive

/-- The produced finite sample contains all required witness words. -/
theorem contains_witnesses
    (O : TrimmedPresentationExposingTransportFromRuleCoverage D) :
    TrimmedPresentationWitnessWordSet D ⊆
      (O.sample : Set (Word α)) :=
  O.toTransportFromRuleEnumeration.contains_witnesses

/-- Convert directly to final reachable data. -/
def toFinalReachableData
    (O : TrimmedPresentationExposingTransportFromRuleCoverage D) :
    FinalReachableData G O.sample obs f :=
  O.toTransportFromRuleEnumeration.toFinalReachableData

/-- The produced sample is a characteristic sample for the reachable learner. -/
theorem characteristic_sample
    (O : TrimmedPresentationExposingTransportFromRuleCoverage D) :
    CharacteristicSample
      (reachableHypLanguage obs f)
      (reachableSampleLearner (α := α))
      O.sample
      G.StringLanguage :=
  O.toTransportFromRuleEnumeration.characteristic_sample

/-- Eventual prefix-exact reconstruction. -/
theorem prefix_exact_eventually
    (O : TrimmedPresentationExposingTransportFromRuleCoverage D) :
    ∀ Ttxt : TextFor G.StringLanguage,
      ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
        ReachableSampleStringLanguage (Ttxt.prefixSample n) obs f =
          G.StringLanguage :=
  O.toTransportFromRuleEnumeration.prefix_exact_eventually

/-- Reachable Gold identification. -/
theorem identifies_from_positive_text
    (O : TrimmedPresentationExposingTransportFromRuleCoverage D) :
    ∀ Ttxt : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        Ttxt :=
  O.toTransportFromRuleEnumeration.identifies_from_positive_text

end TrimmedPresentationExposingTransportFromRuleCoverage

end ExposingTransportFromRuleCoverage


section CommonContextFromRuleCoverage

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}
variable {f : Nat}
variable {T : TrimmedOutputTypePresentation G obs}

/-- Common-context transport obligations whose sample side is supplied by a
rule-coverage package. -/
structure TrimmedPresentationCommonContextFromRuleCoverage
    (D : TrimmedPresentationPreCoreData T f) where
  coverage : TrimmedPresentationRuleCoveragePackage D

  commonData : TrimmedPresentationAnchorCommonContextCoreData D
  splicingConstructor : NamedContextSplicingConstructor α
  fanout : G.FanoutAtMost f
  promise : FixedNamedTupleSubstitutable f obs G.StringLanguage

namespace TrimmedPresentationCommonContextFromRuleCoverage

variable {D : TrimmedPresentationPreCoreData T f}

/-- The rule enumeration induced by coverage. -/
def toRuleEnumeration
    (O : TrimmedPresentationCommonContextFromRuleCoverage D) :
    TrimmedPresentationRuleEnumeration D :=
  O.coverage.toRuleEnumeration

/-- Convert to the rule-enumeration common-context route. -/
def toTransportFromRuleEnumeration
    (O : TrimmedPresentationCommonContextFromRuleCoverage D) :
    TrimmedPresentationCommonContextFromRuleEnumeration D where
  ruleEnumeration := O.toRuleEnumeration
  commonData := O.commonData
  splicingConstructor := O.splicingConstructor
  fanout := O.fanout
  promise := O.promise

/-- Convert to the compact common-context obligation package. -/
def toObligations
    (O : TrimmedPresentationCommonContextFromRuleCoverage D) :
    TrimmedPresentationCommonContextTransportObligations D :=
  O.toTransportFromRuleEnumeration.toObligations

/-- Convert to exposing-transport obligations through the common-context route. -/
def toExposingTransportObligations
    (O : TrimmedPresentationCommonContextFromRuleCoverage D) :
    TrimmedPresentationExposingTransportObligations D :=
  O.toTransportFromRuleEnumeration.toExposingTransportObligations

/-- The finite sample produced by the resulting obligation package. -/
def sample
    (O : TrimmedPresentationCommonContextFromRuleCoverage D) :
    Finset (Word α) :=
  O.toTransportFromRuleEnumeration.sample

/-- The produced finite sample is positive. -/
theorem sample_positive
    (O : TrimmedPresentationCommonContextFromRuleCoverage D) :
    (O.sample : Set (Word α)) ⊆ G.StringLanguage :=
  O.toTransportFromRuleEnumeration.sample_positive

/-- The produced finite sample contains all required witness words. -/
theorem contains_witnesses
    (O : TrimmedPresentationCommonContextFromRuleCoverage D) :
    TrimmedPresentationWitnessWordSet D ⊆
      (O.sample : Set (Word α)) :=
  O.toTransportFromRuleEnumeration.contains_witnesses

/-- Convert directly to final reachable data. -/
def toFinalReachableData
    (O : TrimmedPresentationCommonContextFromRuleCoverage D) :
    FinalReachableData G O.sample obs f :=
  O.toTransportFromRuleEnumeration.toFinalReachableData

/-- The produced sample is a characteristic sample for the reachable learner. -/
theorem characteristic_sample
    (O : TrimmedPresentationCommonContextFromRuleCoverage D) :
    CharacteristicSample
      (reachableHypLanguage obs f)
      (reachableSampleLearner (α := α))
      O.sample
      G.StringLanguage :=
  O.toTransportFromRuleEnumeration.characteristic_sample

/-- Eventual prefix-exact reconstruction. -/
theorem prefix_exact_eventually
    (O : TrimmedPresentationCommonContextFromRuleCoverage D) :
    ∀ Ttxt : TextFor G.StringLanguage,
      ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
        ReachableSampleStringLanguage (Ttxt.prefixSample n) obs f =
          G.StringLanguage :=
  O.toTransportFromRuleEnumeration.prefix_exact_eventually

/-- Reachable Gold identification. -/
theorem identifies_from_positive_text
    (O : TrimmedPresentationCommonContextFromRuleCoverage D) :
    ∀ Ttxt : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        Ttxt :=
  O.toTransportFromRuleEnumeration.identifies_from_positive_text

end TrimmedPresentationCommonContextFromRuleCoverage

end CommonContextFromRuleCoverage


section ExposingTransportFromGrammarRuleBuilder

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}
variable {f : Nat}
variable {T : TrimmedOutputTypePresentation G obs}

/-- Exposing-context transport obligations whose sample side is supplied by the
grammar-rule builder. -/
structure TrimmedPresentationExposingTransportFromGrammarRuleBuilder
    (D : TrimmedPresentationPreCoreData T f) where
  builder : TrimmedPresentationGrammarRuleBuilder D
  exposingTransport : TrimmedPresentationExposingContextTransport D

  splicingConstructor : NamedContextSplicingConstructor α
  fanout : G.FanoutAtMost f
  promise : FixedNamedTupleSubstitutable f obs G.StringLanguage

namespace TrimmedPresentationExposingTransportFromGrammarRuleBuilder

variable {D : TrimmedPresentationPreCoreData T f}

/-- Arity selectors extracted from the grammar-rule builder. -/
def arities
    (O : TrimmedPresentationExposingTransportFromGrammarRuleBuilder D) :
    TrimmedPresentationRuleAritySelectors D where
  terminal_arity := O.builder.terminal_arity
  start_arity := O.builder.start_arity

/-- The component package induced by the grammar-rule builder. -/
def toComponentPackage
    (O : TrimmedPresentationExposingTransportFromGrammarRuleBuilder D) :
    TrimmedPresentationComponentPackage D :=
  O.builder.toComponentPackage

/-- Convert to the component-package transport route. -/
def toTransportFromComponentPackage
    (O : TrimmedPresentationExposingTransportFromGrammarRuleBuilder D) :
    TrimmedPresentationExposingTransportFromComponentPackage D where
  components := O.toComponentPackage
  baseNonterminals := O.builder.baseNonterminals
  base_covers := O.builder.base_covers
  arities := O.arities
  exposingTransport := O.exposingTransport
  splicingConstructor := O.splicingConstructor
  fanout := O.fanout
  promise := O.promise

/-- Convert to the compact exposing-transport obligation package. -/
def toObligations
    (O : TrimmedPresentationExposingTransportFromGrammarRuleBuilder D) :
    TrimmedPresentationExposingTransportObligations D :=
  O.toTransportFromComponentPackage.toObligations

/-- The finite sample produced by the resulting obligation package. -/
def sample
    (O : TrimmedPresentationExposingTransportFromGrammarRuleBuilder D) :
    Finset (Word α) :=
  O.toTransportFromComponentPackage.sample

/-- The produced finite sample is positive. -/
theorem sample_positive
    (O : TrimmedPresentationExposingTransportFromGrammarRuleBuilder D) :
    (O.sample : Set (Word α)) ⊆ G.StringLanguage :=
  O.toTransportFromComponentPackage.sample_positive

/-- The produced finite sample contains all required witness words. -/
theorem contains_witnesses
    (O : TrimmedPresentationExposingTransportFromGrammarRuleBuilder D) :
    TrimmedPresentationWitnessWordSet D ⊆
      (O.sample : Set (Word α)) :=
  O.toTransportFromComponentPackage.contains_witnesses

/-- Convert directly to final reachable data. -/
def toFinalReachableData
    (O : TrimmedPresentationExposingTransportFromGrammarRuleBuilder D) :
    FinalReachableData G O.sample obs f :=
  O.toTransportFromComponentPackage.toFinalReachableData

/-- The produced sample is a characteristic sample for the reachable learner. -/
theorem characteristic_sample
    (O : TrimmedPresentationExposingTransportFromGrammarRuleBuilder D) :
    CharacteristicSample
      (reachableHypLanguage obs f)
      (reachableSampleLearner (α := α))
      O.sample
      G.StringLanguage :=
  O.toTransportFromComponentPackage.characteristic_sample

/-- Eventual prefix-exact reconstruction. -/
theorem prefix_exact_eventually
    (O : TrimmedPresentationExposingTransportFromGrammarRuleBuilder D) :
    ∀ Ttxt : TextFor G.StringLanguage,
      ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
        ReachableSampleStringLanguage (Ttxt.prefixSample n) obs f =
          G.StringLanguage :=
  O.toTransportFromComponentPackage.prefix_exact_eventually

/-- Reachable Gold identification. -/
theorem identifies_from_positive_text
    (O : TrimmedPresentationExposingTransportFromGrammarRuleBuilder D) :
    ∀ Ttxt : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        Ttxt :=
  O.toTransportFromComponentPackage.identifies_from_positive_text

end TrimmedPresentationExposingTransportFromGrammarRuleBuilder

end ExposingTransportFromGrammarRuleBuilder


section CommonContextFromGrammarRuleBuilder

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}
variable {f : Nat}
variable {T : TrimmedOutputTypePresentation G obs}

/-- Common-context transport obligations whose sample side is supplied by the
grammar-rule builder. -/
structure TrimmedPresentationCommonContextFromGrammarRuleBuilder
    (D : TrimmedPresentationPreCoreData T f) where
  builder : TrimmedPresentationGrammarRuleBuilder D
  commonData : TrimmedPresentationAnchorCommonContextCoreData D

  splicingConstructor : NamedContextSplicingConstructor α
  fanout : G.FanoutAtMost f
  promise : FixedNamedTupleSubstitutable f obs G.StringLanguage

namespace TrimmedPresentationCommonContextFromGrammarRuleBuilder

variable {D : TrimmedPresentationPreCoreData T f}

/-- Convert to the component-package common-context route. -/
def toTransportFromComponentPackage
    (O : TrimmedPresentationCommonContextFromGrammarRuleBuilder D) :
    TrimmedPresentationCommonContextFromComponentPackage D where
  components := O.builder.toComponentPackage
  commonData := O.commonData
  splicingConstructor := O.splicingConstructor
  fanout := O.fanout
  promise := O.promise

/-- Convert to the compact common-context obligation package. -/
def toObligations
    (O : TrimmedPresentationCommonContextFromGrammarRuleBuilder D) :
    TrimmedPresentationCommonContextTransportObligations D :=
  O.toTransportFromComponentPackage.toObligations

/-- Convert to exposing-transport obligations through the common-context route. -/
def toExposingTransportObligations
    (O : TrimmedPresentationCommonContextFromGrammarRuleBuilder D) :
    TrimmedPresentationExposingTransportObligations D :=
  O.toTransportFromComponentPackage.toExposingTransportObligations

/-- The finite sample produced by the resulting obligation package. -/
def sample
    (O : TrimmedPresentationCommonContextFromGrammarRuleBuilder D) :
    Finset (Word α) :=
  O.toTransportFromComponentPackage.sample

/-- The produced finite sample is positive. -/
theorem sample_positive
    (O : TrimmedPresentationCommonContextFromGrammarRuleBuilder D) :
    (O.sample : Set (Word α)) ⊆ G.StringLanguage :=
  O.toTransportFromComponentPackage.sample_positive

/-- The produced finite sample contains all required witness words. -/
theorem contains_witnesses
    (O : TrimmedPresentationCommonContextFromGrammarRuleBuilder D) :
    TrimmedPresentationWitnessWordSet D ⊆
      (O.sample : Set (Word α)) :=
  O.toTransportFromComponentPackage.contains_witnesses

/-- Convert directly to final reachable data. -/
def toFinalReachableData
    (O : TrimmedPresentationCommonContextFromGrammarRuleBuilder D) :
    FinalReachableData G O.sample obs f :=
  O.toTransportFromComponentPackage.toFinalReachableData

/-- The produced sample is a characteristic sample for the reachable learner. -/
theorem characteristic_sample
    (O : TrimmedPresentationCommonContextFromGrammarRuleBuilder D) :
    CharacteristicSample
      (reachableHypLanguage obs f)
      (reachableSampleLearner (α := α))
      O.sample
      G.StringLanguage :=
  O.toTransportFromComponentPackage.characteristic_sample

/-- Eventual prefix-exact reconstruction. -/
theorem prefix_exact_eventually
    (O : TrimmedPresentationCommonContextFromGrammarRuleBuilder D) :
    ∀ Ttxt : TextFor G.StringLanguage,
      ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
        ReachableSampleStringLanguage (Ttxt.prefixSample n) obs f =
          G.StringLanguage :=
  O.toTransportFromComponentPackage.prefix_exact_eventually

/-- Reachable Gold identification. -/
theorem identifies_from_positive_text
    (O : TrimmedPresentationCommonContextFromGrammarRuleBuilder D) :
    ∀ Ttxt : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        Ttxt :=
  O.toTransportFromComponentPackage.identifies_from_positive_text

end TrimmedPresentationCommonContextFromGrammarRuleBuilder

end CommonContextFromGrammarRuleBuilder


section MainTheoremsFromRuleTransportObligations

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}
variable {f : Nat}
variable {T : TrimmedOutputTypePresentation G obs}
variable {D : TrimmedPresentationPreCoreData T f}

/-- Stable top-level reachable identification theorem from exposing transport
and rule enumeration. -/
theorem trimmed_exposing_transport_from_rule_enumeration_reachable_identification
    (O : TrimmedPresentationExposingTransportFromRuleEnumeration D) :
    ∀ Ttxt : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        Ttxt :=
  O.identifies_from_positive_text

/-- Stable top-level prefix-exact theorem from exposing transport and rule
enumeration. -/
theorem trimmed_exposing_transport_from_rule_enumeration_prefix_exact
    (O : TrimmedPresentationExposingTransportFromRuleEnumeration D) :
    ∀ Ttxt : TextFor G.StringLanguage,
      ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
        ReachableSampleStringLanguage (Ttxt.prefixSample n) obs f =
          G.StringLanguage :=
  O.prefix_exact_eventually

/-- Stable top-level reachable identification theorem from common-context
transport and rule enumeration. -/
theorem trimmed_common_context_from_rule_enumeration_reachable_identification
    (O : TrimmedPresentationCommonContextFromRuleEnumeration D) :
    ∀ Ttxt : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        Ttxt :=
  O.identifies_from_positive_text

/-- Stable top-level prefix-exact theorem from common-context transport and rule
enumeration. -/
theorem trimmed_common_context_from_rule_enumeration_prefix_exact
    (O : TrimmedPresentationCommonContextFromRuleEnumeration D) :
    ∀ Ttxt : TextFor G.StringLanguage,
      ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
        ReachableSampleStringLanguage (Ttxt.prefixSample n) obs f =
          G.StringLanguage :=
  O.prefix_exact_eventually

/-- Stable top-level reachable identification theorem from exposing transport
and rule coverage. -/
theorem trimmed_exposing_transport_from_rule_coverage_reachable_identification
    (O : TrimmedPresentationExposingTransportFromRuleCoverage D) :
    ∀ Ttxt : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        Ttxt :=
  O.identifies_from_positive_text

/-- Stable top-level prefix-exact theorem from exposing transport and rule
coverage. -/
theorem trimmed_exposing_transport_from_rule_coverage_prefix_exact
    (O : TrimmedPresentationExposingTransportFromRuleCoverage D) :
    ∀ Ttxt : TextFor G.StringLanguage,
      ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
        ReachableSampleStringLanguage (Ttxt.prefixSample n) obs f =
          G.StringLanguage :=
  O.prefix_exact_eventually

/-- Stable top-level reachable identification theorem from common-context
transport and rule coverage. -/
theorem trimmed_common_context_from_rule_coverage_reachable_identification
    (O : TrimmedPresentationCommonContextFromRuleCoverage D) :
    ∀ Ttxt : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        Ttxt :=
  O.identifies_from_positive_text

/-- Stable top-level prefix-exact theorem from common-context transport and rule
coverage. -/
theorem trimmed_common_context_from_rule_coverage_prefix_exact
    (O : TrimmedPresentationCommonContextFromRuleCoverage D) :
    ∀ Ttxt : TextFor G.StringLanguage,
      ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
        ReachableSampleStringLanguage (Ttxt.prefixSample n) obs f =
          G.StringLanguage :=
  O.prefix_exact_eventually

/-- Stable top-level reachable identification theorem from exposing transport
and grammar-rule builder. -/
theorem trimmed_exposing_transport_from_grammar_rule_builder_reachable_identification
    (O : TrimmedPresentationExposingTransportFromGrammarRuleBuilder D) :
    ∀ Ttxt : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        Ttxt :=
  O.identifies_from_positive_text

/-- Stable top-level prefix-exact theorem from exposing transport and
grammar-rule builder. -/
theorem trimmed_exposing_transport_from_grammar_rule_builder_prefix_exact
    (O : TrimmedPresentationExposingTransportFromGrammarRuleBuilder D) :
    ∀ Ttxt : TextFor G.StringLanguage,
      ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
        ReachableSampleStringLanguage (Ttxt.prefixSample n) obs f =
          G.StringLanguage :=
  O.prefix_exact_eventually

/-- Stable top-level reachable identification theorem from common-context
transport and grammar-rule builder. -/
theorem trimmed_common_context_from_grammar_rule_builder_reachable_identification
    (O : TrimmedPresentationCommonContextFromGrammarRuleBuilder D) :
    ∀ Ttxt : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        Ttxt :=
  O.identifies_from_positive_text

/-- Stable top-level prefix-exact theorem from common-context transport and
grammar-rule builder. -/
theorem trimmed_common_context_from_grammar_rule_builder_prefix_exact
    (O : TrimmedPresentationCommonContextFromGrammarRuleBuilder D) :
    ∀ Ttxt : TextFor G.StringLanguage,
      ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
        ReachableSampleStringLanguage (Ttxt.prefixSample n) obs f =
          G.StringLanguage :=
  O.prefix_exact_eventually

end MainTheoremsFromRuleTransportObligations

end MCFG
