/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG2.CharacteristicSampleTransportObligationsFromRules

/-!
# CharacteristicSampleTransportObligationsFromRuleData.lean

Seventy-seventh clean Lean experiment for the fixed-observation MCFG project.

The previous files connected increasingly concrete finite-sample construction
layers to the transport-obligation routes.  This file records the neighboring
rule-data routes:

* `TrimmedPresentationGrammarRuleData`;
* `TrimmedPresentationGrammarRuleTransportData`;
* `TrimmedPresentationRuleTransportFinalData`.

The point is mostly organizational.  There are now two parallel ways to enter
the final theorem:

1. direct witness-positivity data:

```text
GrammarRuleData
⇒ GrammarRuleBuilder
⇒ characteristic sample
⇒ FinalReachableData;
```

2. semantic transport data:

```text
GrammarRuleTransportData / RuleTransportFinalData
⇒ characteristic sample
⇒ FinalReachableData.
```

This file gives these routes stable endpoint wrappers and theorem names, making
it easier to compare them with the newer exposing/common-context obligation
routes.

No theorem here uses `sorry`.
-/

namespace MCFG

universe u v w

section GrammarRuleDataEndpoint

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}
variable {f : Nat}
variable {T : TrimmedOutputTypePresentation G obs}

/-- Final wrapper for the direct grammar-rule-data route. -/
structure TrimmedPresentationGrammarRuleDataEndpoint
    (D : TrimmedPresentationPreCoreData T f) where
  grammarData : TrimmedPresentationGrammarRuleData D
  splicingConstructor : NamedContextSplicingConstructor α
  fanout : G.FanoutAtMost f
  promise : FixedNamedTupleSubstitutable f obs G.StringLanguage

namespace TrimmedPresentationGrammarRuleDataEndpoint

variable {D : TrimmedPresentationPreCoreData T f}

/-- Convert to the grammar-rule builder used by the characteristic-sample
construction. -/
def toGrammarRuleBuilder
    (E : TrimmedPresentationGrammarRuleDataEndpoint D) :
    TrimmedPresentationGrammarRuleBuilder D :=
  E.grammarData.toGrammarRuleBuilder

/-- The finite sample produced by the direct grammar-rule-data route. -/
noncomputable def sample
    (E : TrimmedPresentationGrammarRuleDataEndpoint D) :
    Finset (Word α) :=
  E.grammarData.sample

/-- The finite sample is positive. -/
theorem sample_positive
    (E : TrimmedPresentationGrammarRuleDataEndpoint D) :
    (E.sample : Set (Word α)) ⊆ G.StringLanguage :=
  E.grammarData.sample_positive

/-- The finite sample contains all required witness words. -/
theorem contains_witnesses
    (E : TrimmedPresentationGrammarRuleDataEndpoint D) :
    TrimmedPresentationWitnessWordSet D ⊆
      (E.sample : Set (Word α)) :=
  E.grammarData.contains_witnesses

/-- Convert directly to final reachable data. -/
noncomputable def toFinalReachableData
    (E : TrimmedPresentationGrammarRuleDataEndpoint D) :
    FinalReachableData G E.sample obs f :=
  E.grammarData.toFinalReachableData
    E.splicingConstructor E.fanout E.promise

/-- The produced finite sample is a characteristic sample for the reachable
learner. -/
theorem characteristic_sample
    (E : TrimmedPresentationGrammarRuleDataEndpoint D) :
    CharacteristicSample
      (reachableHypLanguage obs f)
      (reachableSampleLearner (α := α))
      E.sample
      G.StringLanguage :=
  E.grammarData.characteristic_sample
    E.splicingConstructor E.fanout E.promise

/-- Exact reconstruction for every positive finite superset of the produced
sample. -/
theorem exact_for_positive_superset
    (E : TrimmedPresentationGrammarRuleDataEndpoint D)
    {K : Finset (Word α)}
    (hEK : (E.sample : Set (Word α)) ⊆ (K : Set (Word α)))
    (hKpos : (K : Set (Word α)) ⊆ G.StringLanguage) :
    ReachableSampleStringLanguage K obs f = G.StringLanguage :=
  E.toFinalReachableData.exact_for_positive_superset hEK hKpos

/-- Eventual prefix-exact reconstruction. -/
theorem prefix_exact_eventually
    (E : TrimmedPresentationGrammarRuleDataEndpoint D) :
    ∀ Ttxt : TextFor G.StringLanguage,
      ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
        ReachableSampleStringLanguage (Ttxt.prefixSample n) obs f =
          G.StringLanguage :=
  E.grammarData.prefix_exact_eventually
    E.splicingConstructor E.fanout E.promise

/-- Reachable Gold identification. -/
theorem identifies_from_positive_text
    (E : TrimmedPresentationGrammarRuleDataEndpoint D) :
    ∀ Ttxt : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        Ttxt :=
  E.grammarData.identifies_from_positive_text
    E.splicingConstructor E.fanout E.promise

end TrimmedPresentationGrammarRuleDataEndpoint

end GrammarRuleDataEndpoint


section GrammarRuleTransportEndpoint

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}
variable {f : Nat}
variable {T : TrimmedOutputTypePresentation G obs}

/-- Final wrapper for the grammar-rule-transport-data route. -/
structure TrimmedPresentationGrammarRuleTransportEndpoint
    (D : TrimmedPresentationPreCoreData T f) where
  transportData : TrimmedPresentationGrammarRuleTransportData D
  splicingConstructor : NamedContextSplicingConstructor α
  fanout : G.FanoutAtMost f
  promise : FixedNamedTupleSubstitutable f obs G.StringLanguage

namespace TrimmedPresentationGrammarRuleTransportEndpoint

variable {D : TrimmedPresentationPreCoreData T f}

/-- Convert to direct grammar-rule data. -/
def toGrammarRuleData
    (E : TrimmedPresentationGrammarRuleTransportEndpoint D) :
    TrimmedPresentationGrammarRuleData D :=
  E.transportData.toGrammarRuleData

/-- Convert to the grammar-rule builder. -/
def toGrammarRuleBuilder
    (E : TrimmedPresentationGrammarRuleTransportEndpoint D) :
    TrimmedPresentationGrammarRuleBuilder D :=
  E.transportData.toGrammarRuleData.toGrammarRuleBuilder

/-- The finite sample produced by the transport-data route. -/
noncomputable def sample
    (E : TrimmedPresentationGrammarRuleTransportEndpoint D) :
    Finset (Word α) :=
  E.transportData.sample

/-- The finite sample is positive. -/
theorem sample_positive
    (E : TrimmedPresentationGrammarRuleTransportEndpoint D) :
    (E.sample : Set (Word α)) ⊆ G.StringLanguage :=
  E.transportData.sample_positive

/-- The finite sample contains all required witness words. -/
theorem contains_witnesses
    (E : TrimmedPresentationGrammarRuleTransportEndpoint D) :
    TrimmedPresentationWitnessWordSet D ⊆
      (E.sample : Set (Word α)) :=
  E.transportData.contains_witnesses

/-- Convert directly to final reachable data. -/
noncomputable def toFinalReachableData
    (E : TrimmedPresentationGrammarRuleTransportEndpoint D) :
    FinalReachableData G E.sample obs f :=
  E.transportData.toFinalReachableData
    E.splicingConstructor E.fanout E.promise

/-- The produced finite sample is a characteristic sample for the reachable
learner. -/
theorem characteristic_sample
    (E : TrimmedPresentationGrammarRuleTransportEndpoint D) :
    CharacteristicSample
      (reachableHypLanguage obs f)
      (reachableSampleLearner (α := α))
      E.sample
      G.StringLanguage :=
  E.transportData.characteristic_sample
    E.splicingConstructor E.fanout E.promise

/-- Exact reconstruction for every positive finite superset of the produced
sample. -/
theorem exact_for_positive_superset
    (E : TrimmedPresentationGrammarRuleTransportEndpoint D)
    {K : Finset (Word α)}
    (hEK : (E.sample : Set (Word α)) ⊆ (K : Set (Word α)))
    (hKpos : (K : Set (Word α)) ⊆ G.StringLanguage) :
    ReachableSampleStringLanguage K obs f = G.StringLanguage :=
  E.toFinalReachableData.exact_for_positive_superset hEK hKpos

/-- Eventual prefix-exact reconstruction. -/
theorem prefix_exact_eventually
    (E : TrimmedPresentationGrammarRuleTransportEndpoint D) :
    ∀ Ttxt : TextFor G.StringLanguage,
      ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
        ReachableSampleStringLanguage (Ttxt.prefixSample n) obs f =
          G.StringLanguage :=
  E.transportData.prefix_exact_eventually
    E.splicingConstructor E.fanout E.promise

/-- Reachable Gold identification. -/
theorem identifies_from_positive_text
    (E : TrimmedPresentationGrammarRuleTransportEndpoint D) :
    ∀ Ttxt : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        Ttxt :=
  E.transportData.identifies_from_positive_text
    E.splicingConstructor E.fanout E.promise

end TrimmedPresentationGrammarRuleTransportEndpoint

end GrammarRuleTransportEndpoint


section RuleTransportFinalEndpoint

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}
variable {f : Nat}
variable {T : TrimmedOutputTypePresentation G obs}

/-- A thin endpoint wrapper around the already-final rule-transport data. -/
structure TrimmedPresentationRuleTransportEndpoint
    (D : TrimmedPresentationPreCoreData T f) where
  finalData : TrimmedPresentationRuleTransportFinalData D

namespace TrimmedPresentationRuleTransportEndpoint

variable {D : TrimmedPresentationPreCoreData T f}

/-- Convert to grammar-rule transport data. -/
def toGrammarRuleTransportData
    (E : TrimmedPresentationRuleTransportEndpoint D) :
    TrimmedPresentationGrammarRuleTransportData D :=
  E.finalData.transportData

/-- Convert to grammar-rule data. -/
def toGrammarRuleData
    (E : TrimmedPresentationRuleTransportEndpoint D) :
    TrimmedPresentationGrammarRuleData D :=
  E.finalData.toGrammarRuleData

/-- The finite sample produced by rule-transport final data. -/
noncomputable def sample
    (E : TrimmedPresentationRuleTransportEndpoint D) :
    Finset (Word α) :=
  E.finalData.sample

/-- The finite sample is positive. -/
theorem sample_positive
    (E : TrimmedPresentationRuleTransportEndpoint D) :
    (E.sample : Set (Word α)) ⊆ G.StringLanguage :=
  E.finalData.sample_positive

/-- The finite sample contains all required witness words. -/
theorem contains_witnesses
    (E : TrimmedPresentationRuleTransportEndpoint D) :
    TrimmedPresentationWitnessWordSet D ⊆
      (E.sample : Set (Word α)) :=
  E.finalData.contains_witnesses

/-- Convert directly to final reachable data. -/
noncomputable def toFinalReachableData
    (E : TrimmedPresentationRuleTransportEndpoint D) :
    FinalReachableData G E.sample obs f :=
  E.finalData.toFinalReachableData

/-- The produced finite sample is a characteristic sample for the reachable
learner. -/
theorem characteristic_sample
    (E : TrimmedPresentationRuleTransportEndpoint D) :
    CharacteristicSample
      (reachableHypLanguage obs f)
      (reachableSampleLearner (α := α))
      E.sample
      G.StringLanguage :=
  E.finalData.characteristic_sample

/-- Exact reconstruction for every positive finite superset of the produced
sample. -/
theorem exact_for_positive_superset
    (E : TrimmedPresentationRuleTransportEndpoint D)
    {K : Finset (Word α)}
    (hEK : (E.sample : Set (Word α)) ⊆ (K : Set (Word α)))
    (hKpos : (K : Set (Word α)) ⊆ G.StringLanguage) :
    ReachableSampleStringLanguage K obs f = G.StringLanguage :=
  E.finalData.exact_for_positive_superset hEK hKpos

/-- Exact reconstruction at a positive-text prefix containing the produced
sample. -/
theorem exact_at_seen_prefix
    (E : TrimmedPresentationRuleTransportEndpoint D)
    (Ttxt : TextFor G.StringLanguage)
    {n : Nat}
    (hseen : (E.sample : Set (Word α)) ⊆
      (Ttxt.prefixSample n : Set (Word α))) :
    ReachableSampleStringLanguage (Ttxt.prefixSample n) obs f =
      G.StringLanguage :=
  E.finalData.exact_at_seen_prefix Ttxt hseen

/-- Eventual prefix-exact reconstruction. -/
theorem prefix_exact_eventually
    (E : TrimmedPresentationRuleTransportEndpoint D) :
    ∀ Ttxt : TextFor G.StringLanguage,
      ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
        ReachableSampleStringLanguage (Ttxt.prefixSample n) obs f =
          G.StringLanguage :=
  E.finalData.prefix_exact_eventually

/-- Reachable Gold identification. -/
theorem identifies_from_positive_text
    (E : TrimmedPresentationRuleTransportEndpoint D) :
    ∀ Ttxt : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        Ttxt :=
  E.finalData.identifies_from_positive_text

/-- Pointwise eventual correctness on one positive text. -/
theorem eventually_correct_on_text
    (E : TrimmedPresentationRuleTransportEndpoint D)
    (Ttxt : TextFor G.StringLanguage) :
    EventuallyCorrectOnText
      (reachableHypLanguage obs f)
      (reachableSampleLearner (α := α))
      Ttxt :=
  E.identifies_from_positive_text Ttxt

end TrimmedPresentationRuleTransportEndpoint

end RuleTransportFinalEndpoint


section ConversionsFromTransportObligations

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}
variable {f : Nat}
variable {T : TrimmedOutputTypePresentation G obs}
variable {D : TrimmedPresentationPreCoreData T f}

namespace TrimmedPresentationExposingTransportObligations

/-- Exposing-transport obligations induce a grammar-rule transport endpoint. -/
def toGrammarRuleTransportEndpoint
    (O : TrimmedPresentationExposingTransportObligations D) :
    TrimmedPresentationGrammarRuleTransportEndpoint D where
  transportData := O.toGrammarRuleTransportData
  splicingConstructor := O.splicingConstructor
  fanout := O.fanout
  promise := O.promise

/-- Exposing-transport obligations induce the direct grammar-rule-data endpoint. -/
def toGrammarRuleDataEndpoint
    (O : TrimmedPresentationExposingTransportObligations D) :
    TrimmedPresentationGrammarRuleDataEndpoint D where
  grammarData := O.toGrammarRuleTransportData.toGrammarRuleData
  splicingConstructor := O.splicingConstructor
  fanout := O.fanout
  promise := O.promise

end TrimmedPresentationExposingTransportObligations

namespace TrimmedPresentationCommonContextTransportObligations

/-- Common-context obligations induce a grammar-rule transport endpoint. -/
def toGrammarRuleTransportEndpoint
    (O : TrimmedPresentationCommonContextTransportObligations D) :
    TrimmedPresentationGrammarRuleTransportEndpoint D where
  transportData := O.toGrammarRuleTransportData
  splicingConstructor := O.splicingConstructor
  fanout := O.fanout
  promise := O.promise

/-- Common-context obligations induce the direct grammar-rule-data endpoint. -/
def toGrammarRuleDataEndpoint
    (O : TrimmedPresentationCommonContextTransportObligations D) :
    TrimmedPresentationGrammarRuleDataEndpoint D where
  grammarData := O.toGrammarRuleTransportData.toGrammarRuleData
  splicingConstructor := O.splicingConstructor
  fanout := O.fanout
  promise := O.promise

end TrimmedPresentationCommonContextTransportObligations

end ConversionsFromTransportObligations


section MainTheoremsFromRuleDataEndpoints

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}
variable {f : Nat}
variable {T : TrimmedOutputTypePresentation G obs}
variable {D : TrimmedPresentationPreCoreData T f}

/-- Stable top-level reachable identification theorem from direct
grammar-rule-data endpoint. -/
theorem trimmed_grammar_rule_data_endpoint_reachable_identification
    (E : TrimmedPresentationGrammarRuleDataEndpoint D) :
    ∀ Ttxt : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        Ttxt :=
  E.identifies_from_positive_text

/-- Stable top-level prefix-exact theorem from direct grammar-rule-data
endpoint. -/
theorem trimmed_grammar_rule_data_endpoint_prefix_exact
    (E : TrimmedPresentationGrammarRuleDataEndpoint D) :
    ∀ Ttxt : TextFor G.StringLanguage,
      ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
        ReachableSampleStringLanguage (Ttxt.prefixSample n) obs f =
          G.StringLanguage :=
  E.prefix_exact_eventually

/-- Stable top-level reachable identification theorem from grammar-rule
transport endpoint. -/
theorem trimmed_grammar_rule_transport_endpoint_reachable_identification
    (E : TrimmedPresentationGrammarRuleTransportEndpoint D) :
    ∀ Ttxt : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        Ttxt :=
  E.identifies_from_positive_text

/-- Stable top-level prefix-exact theorem from grammar-rule transport endpoint. -/
theorem trimmed_grammar_rule_transport_endpoint_prefix_exact
    (E : TrimmedPresentationGrammarRuleTransportEndpoint D) :
    ∀ Ttxt : TextFor G.StringLanguage,
      ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
        ReachableSampleStringLanguage (Ttxt.prefixSample n) obs f =
          G.StringLanguage :=
  E.prefix_exact_eventually

/-- Stable top-level reachable identification theorem from rule-transport
endpoint. -/
theorem trimmed_rule_transport_endpoint_reachable_identification
    (E : TrimmedPresentationRuleTransportEndpoint D) :
    ∀ Ttxt : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        Ttxt :=
  E.identifies_from_positive_text

/-- Stable top-level prefix-exact theorem from rule-transport endpoint. -/
theorem trimmed_rule_transport_endpoint_prefix_exact
    (E : TrimmedPresentationRuleTransportEndpoint D) :
    ∀ Ttxt : TextFor G.StringLanguage,
      ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
        ReachableSampleStringLanguage (Ttxt.prefixSample n) obs f =
          G.StringLanguage :=
  E.prefix_exact_eventually

/-- Stable top-level positive finite-superset exactness theorem from
rule-transport endpoint. -/
theorem trimmed_rule_transport_endpoint_exact_for_positive_superset
    (E : TrimmedPresentationRuleTransportEndpoint D)
    {K : Finset (Word α)}
    (hEK : (E.sample : Set (Word α)) ⊆ (K : Set (Word α)))
    (hKpos : (K : Set (Word α)) ⊆ G.StringLanguage) :
    ReachableSampleStringLanguage K obs f = G.StringLanguage :=
  E.exact_for_positive_superset hEK hKpos

end MainTheoremsFromRuleDataEndpoints

end MCFG
