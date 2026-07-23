/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG2.CharacteristicSampleTransportObligationsFromAnchorData

/-!
# CharacteristicSampleSemanticConstructionTargets.lean

Eightieth clean Lean experiment for the fixed-observation MCFG project.

The previous files organized many endpoint wrappers for the transport routes.
This file starts naming the *semantic construction targets* that remain to be
built in a future concrete proof.

The most useful target is:

```text
GrammarRuleBuilder
+ AnchorCommonContextCoreData
+ splicing/fanout/promise
⇒ reachable identification.
```

Intuitively:

* `GrammarRuleBuilder` supplies the finite characteristic sample by enumerating
  anchor/terminal/binary/start witnesses;
* `AnchorCommonContextCoreData` supplies the semantic common-context transport
  needed to turn type equality into language-membership transport;
* `NamedContextSplicingConstructor`, fanout, and fixed-observation
  substitutability are the global final-theorem assumptions.

This file packages that target and also provides exposing-transport and
rule-coverage variants.

No new semantic principle is introduced here.  The file only gives stable names
for the next construction goals.

No theorem here uses `sorry`.
-/

namespace MCFG

universe u v w

section GrammarBuilderCommonContextTarget

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}
variable {f : Nat}
variable {T : TrimmedOutputTypePresentation G obs}

/-- The main semantic construction target after the endpoint cleanup.

A value of this structure says that we have:

* a grammar-rule builder for the finite witness sample;
* anchor common-context core data for semantic transport;
* the global splicing/fanout/substitutability assumptions.

This is close to the intended concrete `CS(G̃₀)` theorem shape. -/
structure TrimmedPresentationGrammarBuilderCommonContextTarget
    (D : TrimmedPresentationPreCoreData T f) where
  builder : TrimmedPresentationGrammarRuleBuilder D
  commonData : TrimmedPresentationAnchorCommonContextCoreData D
  splicingConstructor : NamedContextSplicingConstructor α
  fanout : G.FanoutAtMost f
  promise : FixedNamedTupleSubstitutable f obs G.StringLanguage

namespace TrimmedPresentationGrammarBuilderCommonContextTarget

variable {D : TrimmedPresentationPreCoreData T f}

/-- View the target as the already-established common-context-from-grammar-rule
builder route. -/
def toCommonContextFromGrammarRuleBuilder
    (C : TrimmedPresentationGrammarBuilderCommonContextTarget D) :
    TrimmedPresentationCommonContextFromGrammarRuleBuilder D where
  builder := C.builder
  commonData := C.commonData
  splicingConstructor := C.splicingConstructor
  fanout := C.fanout
  promise := C.promise

/-- View the target as compact common-context transport obligations. -/
noncomputable def toCommonContextTransportObligations
    (C : TrimmedPresentationGrammarBuilderCommonContextTarget D) :
    TrimmedPresentationCommonContextTransportObligations D :=
  C.toCommonContextFromGrammarRuleBuilder.toObligations

/-- View the target as exposing-transport obligations through the common-context
route. -/
noncomputable def toExposingTransportObligations
    (C : TrimmedPresentationGrammarBuilderCommonContextTarget D) :
    TrimmedPresentationExposingTransportObligations D :=
  C.toCommonContextFromGrammarRuleBuilder.toExposingTransportObligations

/-- View the target as a grammar-rule transport endpoint. -/
noncomputable def toGrammarRuleTransportEndpoint
    (C : TrimmedPresentationGrammarBuilderCommonContextTarget D) :
    TrimmedPresentationGrammarRuleTransportEndpoint D :=
  C.toCommonContextTransportObligations.toGrammarRuleTransportEndpoint

/-- The finite sample produced by the target. -/
noncomputable def sample
    (C : TrimmedPresentationGrammarBuilderCommonContextTarget D) :
    Finset (Word α) :=
  C.toCommonContextFromGrammarRuleBuilder.sample

/-- The finite sample is positive. -/
theorem sample_positive
    (C : TrimmedPresentationGrammarBuilderCommonContextTarget D) :
    (C.sample : Set (Word α)) ⊆ G.StringLanguage :=
  C.toCommonContextFromGrammarRuleBuilder.sample_positive

/-- The finite sample contains all required witness words. -/
theorem contains_witnesses
    (C : TrimmedPresentationGrammarBuilderCommonContextTarget D) :
    TrimmedPresentationWitnessWordSet D ⊆
      (C.sample : Set (Word α)) :=
  C.toCommonContextFromGrammarRuleBuilder.contains_witnesses

/-- Convert directly to final reachable data. -/
noncomputable def toFinalReachableData
    (C : TrimmedPresentationGrammarBuilderCommonContextTarget D) :
    FinalReachableData G C.sample obs f :=
  C.toCommonContextFromGrammarRuleBuilder.toFinalReachableData

/-- The produced sample is a characteristic sample for the reachable learner. -/
theorem characteristic_sample
    (C : TrimmedPresentationGrammarBuilderCommonContextTarget D) :
    CharacteristicSample
      (reachableHypLanguage obs f)
      (reachableSampleLearner (α := α))
      C.sample
      G.StringLanguage :=
  C.toCommonContextFromGrammarRuleBuilder.characteristic_sample

/-- Exact reconstruction for every positive finite superset of the produced
sample. -/
theorem exact_for_positive_superset
    (C : TrimmedPresentationGrammarBuilderCommonContextTarget D)
    {K : Finset (Word α)}
    (hCK : (C.sample : Set (Word α)) ⊆ (K : Set (Word α)))
    (hKpos : (K : Set (Word α)) ⊆ G.StringLanguage) :
    ReachableSampleStringLanguage K obs f = G.StringLanguage :=
  C.toFinalReachableData.exact_for_positive_superset hCK hKpos

/-- Eventual prefix-exact reconstruction. -/
theorem prefix_exact_eventually
    (C : TrimmedPresentationGrammarBuilderCommonContextTarget D) :
    ∀ Ttxt : TextFor G.StringLanguage,
      ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
        ReachableSampleStringLanguage (Ttxt.prefixSample n) obs f =
          G.StringLanguage :=
  C.toCommonContextFromGrammarRuleBuilder.prefix_exact_eventually

/-- Reachable Gold identification. -/
theorem identifies_from_positive_text
    (C : TrimmedPresentationGrammarBuilderCommonContextTarget D) :
    ∀ Ttxt : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        Ttxt :=
  C.toCommonContextFromGrammarRuleBuilder.identifies_from_positive_text

/-- Pointwise eventual correctness on one positive text. -/
theorem eventually_correct_on_text
    (C : TrimmedPresentationGrammarBuilderCommonContextTarget D)
    (Ttxt : TextFor G.StringLanguage) :
    EventuallyCorrectOnText
      (reachableHypLanguage obs f)
      (reachableSampleLearner (α := α))
      Ttxt :=
  C.identifies_from_positive_text Ttxt

end TrimmedPresentationGrammarBuilderCommonContextTarget

end GrammarBuilderCommonContextTarget


section GrammarBuilderExposingTarget

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}
variable {f : Nat}
variable {T : TrimmedOutputTypePresentation G obs}

/-- The analogous semantic construction target using exposing-context transport
directly instead of common-context transport. -/
structure TrimmedPresentationGrammarBuilderExposingTarget
    (D : TrimmedPresentationPreCoreData T f) where
  builder : TrimmedPresentationGrammarRuleBuilder D
  exposingTransport : TrimmedPresentationExposingContextTransport D
  splicingConstructor : NamedContextSplicingConstructor α
  fanout : G.FanoutAtMost f
  promise : FixedNamedTupleSubstitutable f obs G.StringLanguage

namespace TrimmedPresentationGrammarBuilderExposingTarget

variable {D : TrimmedPresentationPreCoreData T f}

/-- View the target as the already-established exposing-from-grammar-rule
builder route. -/
def toExposingTransportFromGrammarRuleBuilder
    (C : TrimmedPresentationGrammarBuilderExposingTarget D) :
    TrimmedPresentationExposingTransportFromGrammarRuleBuilder D where
  builder := C.builder
  exposingTransport := C.exposingTransport
  splicingConstructor := C.splicingConstructor
  fanout := C.fanout
  promise := C.promise

/-- View the target as compact exposing-transport obligations. -/
noncomputable def toExposingTransportObligations
    (C : TrimmedPresentationGrammarBuilderExposingTarget D) :
    TrimmedPresentationExposingTransportObligations D :=
  C.toExposingTransportFromGrammarRuleBuilder.toObligations

/-- View the target as a grammar-rule transport endpoint. -/
noncomputable def toGrammarRuleTransportEndpoint
    (C : TrimmedPresentationGrammarBuilderExposingTarget D) :
    TrimmedPresentationGrammarRuleTransportEndpoint D :=
  C.toExposingTransportObligations.toGrammarRuleTransportEndpoint

/-- The finite sample produced by the target. -/
noncomputable def sample
    (C : TrimmedPresentationGrammarBuilderExposingTarget D) :
    Finset (Word α) :=
  C.toExposingTransportFromGrammarRuleBuilder.sample

/-- The finite sample is positive. -/
theorem sample_positive
    (C : TrimmedPresentationGrammarBuilderExposingTarget D) :
    (C.sample : Set (Word α)) ⊆ G.StringLanguage :=
  C.toExposingTransportFromGrammarRuleBuilder.sample_positive

/-- The finite sample contains all required witness words. -/
theorem contains_witnesses
    (C : TrimmedPresentationGrammarBuilderExposingTarget D) :
    TrimmedPresentationWitnessWordSet D ⊆
      (C.sample : Set (Word α)) :=
  C.toExposingTransportFromGrammarRuleBuilder.contains_witnesses

/-- Convert directly to final reachable data. -/
noncomputable def toFinalReachableData
    (C : TrimmedPresentationGrammarBuilderExposingTarget D) :
    FinalReachableData G C.sample obs f :=
  C.toExposingTransportFromGrammarRuleBuilder.toFinalReachableData

/-- The produced sample is a characteristic sample for the reachable learner. -/
theorem characteristic_sample
    (C : TrimmedPresentationGrammarBuilderExposingTarget D) :
    CharacteristicSample
      (reachableHypLanguage obs f)
      (reachableSampleLearner (α := α))
      C.sample
      G.StringLanguage :=
  C.toExposingTransportFromGrammarRuleBuilder.characteristic_sample

/-- Exact reconstruction for every positive finite superset of the produced
sample. -/
theorem exact_for_positive_superset
    (C : TrimmedPresentationGrammarBuilderExposingTarget D)
    {K : Finset (Word α)}
    (hCK : (C.sample : Set (Word α)) ⊆ (K : Set (Word α)))
    (hKpos : (K : Set (Word α)) ⊆ G.StringLanguage) :
    ReachableSampleStringLanguage K obs f = G.StringLanguage :=
  C.toFinalReachableData.exact_for_positive_superset hCK hKpos

/-- Eventual prefix-exact reconstruction. -/
theorem prefix_exact_eventually
    (C : TrimmedPresentationGrammarBuilderExposingTarget D) :
    ∀ Ttxt : TextFor G.StringLanguage,
      ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
        ReachableSampleStringLanguage (Ttxt.prefixSample n) obs f =
          G.StringLanguage :=
  C.toExposingTransportFromGrammarRuleBuilder.prefix_exact_eventually

/-- Reachable Gold identification. -/
theorem identifies_from_positive_text
    (C : TrimmedPresentationGrammarBuilderExposingTarget D) :
    ∀ Ttxt : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        Ttxt :=
  C.toExposingTransportFromGrammarRuleBuilder.identifies_from_positive_text

/-- Pointwise eventual correctness on one positive text. -/
theorem eventually_correct_on_text
    (C : TrimmedPresentationGrammarBuilderExposingTarget D)
    (Ttxt : TextFor G.StringLanguage) :
    EventuallyCorrectOnText
      (reachableHypLanguage obs f)
      (reachableSampleLearner (α := α))
      Ttxt :=
  C.identifies_from_positive_text Ttxt

end TrimmedPresentationGrammarBuilderExposingTarget

end GrammarBuilderExposingTarget


section RuleCoverageCommonContextTarget

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}
variable {f : Nat}
variable {T : TrimmedOutputTypePresentation G obs}

/-- A slightly lower-level semantic construction target using a rule-coverage
package instead of the grammar-rule builder. -/
structure TrimmedPresentationRuleCoverageCommonContextTarget
    (D : TrimmedPresentationPreCoreData T f) where
  coverage : TrimmedPresentationRuleCoveragePackage D
  commonData : TrimmedPresentationAnchorCommonContextCoreData D
  splicingConstructor : NamedContextSplicingConstructor α
  fanout : G.FanoutAtMost f
  promise : FixedNamedTupleSubstitutable f obs G.StringLanguage

namespace TrimmedPresentationRuleCoverageCommonContextTarget

variable {D : TrimmedPresentationPreCoreData T f}

/-- View the target through the common-context-from-rule-coverage route. -/
def toCommonContextFromRuleCoverage
    (C : TrimmedPresentationRuleCoverageCommonContextTarget D) :
    TrimmedPresentationCommonContextFromRuleCoverage D where
  coverage := C.coverage
  commonData := C.commonData
  splicingConstructor := C.splicingConstructor
  fanout := C.fanout
  promise := C.promise

/-- The finite sample produced by the target. -/
noncomputable def sample
    (C : TrimmedPresentationRuleCoverageCommonContextTarget D) :
    Finset (Word α) :=
  C.toCommonContextFromRuleCoverage.sample

/-- The finite sample is positive. -/
theorem sample_positive
    (C : TrimmedPresentationRuleCoverageCommonContextTarget D) :
    (C.sample : Set (Word α)) ⊆ G.StringLanguage :=
  C.toCommonContextFromRuleCoverage.sample_positive

/-- The finite sample contains all required witness words. -/
theorem contains_witnesses
    (C : TrimmedPresentationRuleCoverageCommonContextTarget D) :
    TrimmedPresentationWitnessWordSet D ⊆
      (C.sample : Set (Word α)) :=
  C.toCommonContextFromRuleCoverage.contains_witnesses

/-- Convert directly to final reachable data. -/
noncomputable def toFinalReachableData
    (C : TrimmedPresentationRuleCoverageCommonContextTarget D) :
    FinalReachableData G C.sample obs f :=
  C.toCommonContextFromRuleCoverage.toFinalReachableData

/-- The produced sample is a characteristic sample for the reachable learner. -/
theorem characteristic_sample
    (C : TrimmedPresentationRuleCoverageCommonContextTarget D) :
    CharacteristicSample
      (reachableHypLanguage obs f)
      (reachableSampleLearner (α := α))
      C.sample
      G.StringLanguage :=
  C.toCommonContextFromRuleCoverage.characteristic_sample

/-- Eventual prefix-exact reconstruction. -/
theorem prefix_exact_eventually
    (C : TrimmedPresentationRuleCoverageCommonContextTarget D) :
    ∀ Ttxt : TextFor G.StringLanguage,
      ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
        ReachableSampleStringLanguage (Ttxt.prefixSample n) obs f =
          G.StringLanguage :=
  C.toCommonContextFromRuleCoverage.prefix_exact_eventually

/-- Reachable Gold identification. -/
theorem identifies_from_positive_text
    (C : TrimmedPresentationRuleCoverageCommonContextTarget D) :
    ∀ Ttxt : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        Ttxt :=
  C.toCommonContextFromRuleCoverage.identifies_from_positive_text

end TrimmedPresentationRuleCoverageCommonContextTarget

end RuleCoverageCommonContextTarget


section RuleCoverageExposingTarget

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}
variable {f : Nat}
variable {T : TrimmedOutputTypePresentation G obs}

/-- A slightly lower-level semantic construction target using rule coverage and
direct exposing-context transport. -/
structure TrimmedPresentationRuleCoverageExposingTarget
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

namespace TrimmedPresentationRuleCoverageExposingTarget

variable {D : TrimmedPresentationPreCoreData T f}

/-- View the target through the exposing-from-rule-coverage route. -/
def toExposingTransportFromRuleCoverage
    (C : TrimmedPresentationRuleCoverageExposingTarget D) :
    TrimmedPresentationExposingTransportFromRuleCoverage D where
  coverage := C.coverage
  baseNonterminals := C.baseNonterminals
  base_covers := C.base_covers
  arities := C.arities
  exposingTransport := C.exposingTransport
  splicingConstructor := C.splicingConstructor
  fanout := C.fanout
  promise := C.promise

/-- The finite sample produced by the target. -/
noncomputable def sample
    (C : TrimmedPresentationRuleCoverageExposingTarget D) :
    Finset (Word α) :=
  C.toExposingTransportFromRuleCoverage.sample

/-- The finite sample is positive. -/
theorem sample_positive
    (C : TrimmedPresentationRuleCoverageExposingTarget D) :
    (C.sample : Set (Word α)) ⊆ G.StringLanguage :=
  C.toExposingTransportFromRuleCoverage.sample_positive

/-- The finite sample contains all required witness words. -/
theorem contains_witnesses
    (C : TrimmedPresentationRuleCoverageExposingTarget D) :
    TrimmedPresentationWitnessWordSet D ⊆
      (C.sample : Set (Word α)) :=
  C.toExposingTransportFromRuleCoverage.contains_witnesses

/-- Convert directly to final reachable data. -/
noncomputable def toFinalReachableData
    (C : TrimmedPresentationRuleCoverageExposingTarget D) :
    FinalReachableData G C.sample obs f :=
  C.toExposingTransportFromRuleCoverage.toFinalReachableData

/-- The produced sample is a characteristic sample for the reachable learner. -/
theorem characteristic_sample
    (C : TrimmedPresentationRuleCoverageExposingTarget D) :
    CharacteristicSample
      (reachableHypLanguage obs f)
      (reachableSampleLearner (α := α))
      C.sample
      G.StringLanguage :=
  C.toExposingTransportFromRuleCoverage.characteristic_sample

/-- Eventual prefix-exact reconstruction. -/
theorem prefix_exact_eventually
    (C : TrimmedPresentationRuleCoverageExposingTarget D) :
    ∀ Ttxt : TextFor G.StringLanguage,
      ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
        ReachableSampleStringLanguage (Ttxt.prefixSample n) obs f =
          G.StringLanguage :=
  C.toExposingTransportFromRuleCoverage.prefix_exact_eventually

/-- Reachable Gold identification. -/
theorem identifies_from_positive_text
    (C : TrimmedPresentationRuleCoverageExposingTarget D) :
    ∀ Ttxt : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        Ttxt :=
  C.toExposingTransportFromRuleCoverage.identifies_from_positive_text

end TrimmedPresentationRuleCoverageExposingTarget

end RuleCoverageExposingTarget


section MainTheoremsFromSemanticConstructionTargets

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}
variable {f : Nat}
variable {T : TrimmedOutputTypePresentation G obs}
variable {D : TrimmedPresentationPreCoreData T f}

/-- Stable theorem name for the main grammar-builder + common-context semantic
construction target. -/
theorem trimmed_semantic_target_common_context_reachable_identification
    (C : TrimmedPresentationGrammarBuilderCommonContextTarget D) :
    ∀ Ttxt : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        Ttxt :=
  C.identifies_from_positive_text

/-- Prefix-exact version for the main grammar-builder + common-context semantic
construction target. -/
theorem trimmed_semantic_target_common_context_prefix_exact
    (C : TrimmedPresentationGrammarBuilderCommonContextTarget D) :
    ∀ Ttxt : TextFor G.StringLanguage,
      ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
        ReachableSampleStringLanguage (Ttxt.prefixSample n) obs f =
          G.StringLanguage :=
  C.prefix_exact_eventually

/-- Stable theorem name for the grammar-builder + exposing-transport semantic
construction target. -/
theorem trimmed_semantic_target_exposing_reachable_identification
    (C : TrimmedPresentationGrammarBuilderExposingTarget D) :
    ∀ Ttxt : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        Ttxt :=
  C.identifies_from_positive_text

/-- Prefix-exact version for the grammar-builder + exposing-transport semantic
construction target. -/
theorem trimmed_semantic_target_exposing_prefix_exact
    (C : TrimmedPresentationGrammarBuilderExposingTarget D) :
    ∀ Ttxt : TextFor G.StringLanguage,
      ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
        ReachableSampleStringLanguage (Ttxt.prefixSample n) obs f =
          G.StringLanguage :=
  C.prefix_exact_eventually

/-- Stable theorem name for the rule-coverage + common-context semantic target. -/
theorem trimmed_rule_coverage_common_context_target_reachable_identification
    (C : TrimmedPresentationRuleCoverageCommonContextTarget D) :
    ∀ Ttxt : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        Ttxt :=
  C.identifies_from_positive_text

/-- Prefix-exact theorem for the rule-coverage + common-context semantic target. -/
theorem trimmed_rule_coverage_common_context_target_prefix_exact
    (C : TrimmedPresentationRuleCoverageCommonContextTarget D) :
    ∀ Ttxt : TextFor G.StringLanguage,
      ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
        ReachableSampleStringLanguage (Ttxt.prefixSample n) obs f =
          G.StringLanguage :=
  C.prefix_exact_eventually

/-- Stable theorem name for the rule-coverage + exposing-transport semantic
target. -/
theorem trimmed_rule_coverage_exposing_target_reachable_identification
    (C : TrimmedPresentationRuleCoverageExposingTarget D) :
    ∀ Ttxt : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        Ttxt :=
  C.identifies_from_positive_text

/-- Prefix-exact theorem for the rule-coverage + exposing-transport semantic
target. -/
theorem trimmed_rule_coverage_exposing_target_prefix_exact
    (C : TrimmedPresentationRuleCoverageExposingTarget D) :
    ∀ Ttxt : TextFor G.StringLanguage,
      ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
        ReachableSampleStringLanguage (Ttxt.prefixSample n) obs f =
          G.StringLanguage :=
  C.prefix_exact_eventually

end MainTheoremsFromSemanticConstructionTargets

end MCFG
