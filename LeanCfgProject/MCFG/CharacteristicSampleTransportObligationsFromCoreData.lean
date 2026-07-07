/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG.CharacteristicSampleTransportObligationsFromRuleData

/-!
# CharacteristicSampleTransportObligationsFromCoreData.lean

Seventy-eighth clean Lean experiment for the fixed-observation MCFG project.

The previous file gave endpoint wrappers for grammar-rule data and rule
transport data.  This file gives analogous endpoint wrappers for the higher
core-data interfaces already present in the development:

* `TrimmedPresentationExposingCoreFinalData`;
* `TrimmedPresentationSameContextCoreData`.

The purpose is organizational.  We now have stable endpoint names for the main
transport-oriented entrances:

```text
ExposingCoreFinalData
⇒ FinalReachableData;
SameContextCoreData + start evidence + splicing/fanout/promise
⇒ ExposingCoreFinalData
⇒ FinalReachableData.
```

No new semantic principle is introduced here.

No theorem here uses `sorry`.
-/

namespace MCFG

universe u v w

section ExposingCoreFinalEndpoint

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}
variable {f : Nat}
variable {T : TrimmedOutputTypePresentation G obs}

/-- Thin endpoint wrapper around the separated exposing-core final data. -/
structure TrimmedPresentationExposingCoreFinalEndpoint
    (D : TrimmedPresentationPreCoreData T f) where
  finalData : TrimmedPresentationExposingCoreFinalData D

namespace TrimmedPresentationExposingCoreFinalEndpoint

variable {D : TrimmedPresentationPreCoreData T f}

/-- The underlying exposing-transport core data. -/
def toExposingTransportCoreData
    (E : TrimmedPresentationExposingCoreFinalEndpoint D) :
    TrimmedPresentationExposingTransportCoreData D :=
  E.finalData.coreData

/-- The compact start-word evidence. -/
def startEvidence
    (E : TrimmedPresentationExposingCoreFinalEndpoint D) :
    TrimmedPresentationStartWordEvidence D :=
  E.finalData.startEvidence

/-- Convert to exposing-transport data. -/
def toExposingTransportData
    (E : TrimmedPresentationExposingCoreFinalEndpoint D) :
    TrimmedPresentationExposingTransportData D :=
  E.finalData.toExposingTransportData

/-- Convert to rule-witness transport. -/
def toRuleWitnessTransport
    (E : TrimmedPresentationExposingCoreFinalEndpoint D) :
    TrimmedPresentationRuleWitnessTransport D E.finalData.coreData.arities :=
  E.finalData.toRuleWitnessTransport

/-- Convert to grammar-rule transport data. -/
def toGrammarRuleTransportData
    (E : TrimmedPresentationExposingCoreFinalEndpoint D) :
    TrimmedPresentationGrammarRuleTransportData D :=
  E.finalData.toGrammarRuleTransportData

/-- Convert to rule-transport final data. -/
def toRuleTransportFinalData
    (E : TrimmedPresentationExposingCoreFinalEndpoint D) :
    TrimmedPresentationRuleTransportFinalData D :=
  E.finalData.toRuleTransportFinalData

/-- The finite sample produced by the endpoint. -/
def sample
    (E : TrimmedPresentationExposingCoreFinalEndpoint D) :
    Finset (Word α) :=
  E.finalData.sample

/-- The finite sample is positive. -/
theorem sample_positive
    (E : TrimmedPresentationExposingCoreFinalEndpoint D) :
    (E.sample : Set (Word α)) ⊆ G.StringLanguage :=
  E.finalData.sample_positive

/-- The finite sample contains all required witness words. -/
theorem contains_witnesses
    (E : TrimmedPresentationExposingCoreFinalEndpoint D) :
    TrimmedPresentationWitnessWordSet D ⊆
      (E.sample : Set (Word α)) :=
  E.finalData.contains_witnesses

/-- Convert directly to final reachable data. -/
def toFinalReachableData
    (E : TrimmedPresentationExposingCoreFinalEndpoint D) :
    FinalReachableData G E.sample obs f :=
  E.finalData.toFinalReachableData

/-- The finite sample is a characteristic sample for the reachable learner. -/
theorem characteristic_sample
    (E : TrimmedPresentationExposingCoreFinalEndpoint D) :
    CharacteristicSample
      (reachableHypLanguage obs f)
      (reachableSampleLearner (α := α))
      E.sample
      G.StringLanguage :=
  E.finalData.characteristic_sample

/-- Exact reconstruction for every positive finite superset of the produced
sample. -/
theorem exact_for_positive_superset
    (E : TrimmedPresentationExposingCoreFinalEndpoint D)
    {K : Finset (Word α)}
    (hEK : (E.sample : Set (Word α)) ⊆ (K : Set (Word α)))
    (hKpos : (K : Set (Word α)) ⊆ G.StringLanguage) :
    ReachableSampleStringLanguage K obs f = G.StringLanguage :=
  E.finalData.exact_for_positive_superset hEK hKpos

/-- Exact reconstruction at a positive-text prefix containing the produced
sample. -/
theorem exact_at_seen_prefix
    (E : TrimmedPresentationExposingCoreFinalEndpoint D)
    (Ttxt : TextFor G.StringLanguage)
    {n : Nat}
    (hseen : (E.sample : Set (Word α)) ⊆
      (Ttxt.prefixSample n : Set (Word α))) :
    ReachableSampleStringLanguage (Ttxt.prefixSample n) obs f =
      G.StringLanguage :=
  E.finalData.exact_at_seen_prefix Ttxt hseen

/-- Eventual prefix-exact reconstruction. -/
theorem prefix_exact_eventually
    (E : TrimmedPresentationExposingCoreFinalEndpoint D) :
    ∀ Ttxt : TextFor G.StringLanguage,
      ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
        ReachableSampleStringLanguage (Ttxt.prefixSample n) obs f =
          G.StringLanguage :=
  E.finalData.prefix_exact_eventually

/-- Reachable Gold identification. -/
theorem identifies_from_positive_text
    (E : TrimmedPresentationExposingCoreFinalEndpoint D) :
    ∀ Ttxt : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        Ttxt :=
  E.finalData.identifies_from_positive_text

/-- Pointwise eventual correctness on one positive text. -/
theorem eventually_correct_on_text
    (E : TrimmedPresentationExposingCoreFinalEndpoint D)
    (Ttxt : TextFor G.StringLanguage) :
    EventuallyCorrectOnText
      (reachableHypLanguage obs f)
      (reachableSampleLearner (α := α))
      Ttxt :=
  E.identifies_from_positive_text Ttxt

/-- View the exposing-core final endpoint as a rule-transport endpoint. -/
def toRuleTransportEndpoint
    (E : TrimmedPresentationExposingCoreFinalEndpoint D) :
    TrimmedPresentationRuleTransportEndpoint D where
  finalData := E.toRuleTransportFinalData

/-- View the exposing-core final endpoint as a grammar-rule transport endpoint. -/
def toGrammarRuleTransportEndpoint
    (E : TrimmedPresentationExposingCoreFinalEndpoint D) :
    TrimmedPresentationGrammarRuleTransportEndpoint D where
  transportData := E.toGrammarRuleTransportData
  splicingConstructor := E.finalData.splicingConstructor
  fanout := E.finalData.fanout
  promise := E.finalData.promise

end TrimmedPresentationExposingCoreFinalEndpoint

end ExposingCoreFinalEndpoint


section SameContextCoreEndpoint

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}
variable {f : Nat}
variable {T : TrimmedOutputTypePresentation G obs}

/-- Endpoint wrapper for the same-context core route with compact start-word
evidence. -/
structure TrimmedPresentationSameContextCoreEndpoint
    (D : TrimmedPresentationPreCoreData T f) where
  coreData : TrimmedPresentationSameContextCoreData D
  startEvidence : TrimmedPresentationStartWordEvidence D
  splicingConstructor : NamedContextSplicingConstructor α
  fanout : G.FanoutAtMost f
  promise : FixedNamedTupleSubstitutable f obs G.StringLanguage

namespace TrimmedPresentationSameContextCoreEndpoint

variable {D : TrimmedPresentationPreCoreData T f}

/-- Convert same-context core data to exposing-transport core data. -/
def toExposingTransportCoreData
    (E : TrimmedPresentationSameContextCoreEndpoint D) :
    TrimmedPresentationExposingTransportCoreData D :=
  E.coreData.toExposingTransportCoreData

/-- Convert same-context core data to context-transport data. -/
def toContextTransportData
    (E : TrimmedPresentationSameContextCoreEndpoint D) :
    TrimmedPresentationContextTransportData D :=
  E.coreData.toContextTransportData E.startEvidence

/-- Convert same-context core data to exposing-transport data. -/
def toExposingTransportData
    (E : TrimmedPresentationSameContextCoreEndpoint D) :
    TrimmedPresentationExposingTransportData D :=
  E.coreData.toExposingTransportData E.startEvidence

/-- Convert to the separated exposing-core final data. -/
def toExposingCoreFinalData
    (E : TrimmedPresentationSameContextCoreEndpoint D) :
    TrimmedPresentationExposingCoreFinalData D :=
  E.coreData.toExposingCoreFinalData
    E.startEvidence E.splicingConstructor E.fanout E.promise

/-- Convert to exposing-core final endpoint. -/
def toExposingCoreFinalEndpoint
    (E : TrimmedPresentationSameContextCoreEndpoint D) :
    TrimmedPresentationExposingCoreFinalEndpoint D where
  finalData := E.toExposingCoreFinalData

/-- Convert to rule-witness transport. -/
def toRuleWitnessTransport
    (E : TrimmedPresentationSameContextCoreEndpoint D) :
    TrimmedPresentationRuleWitnessTransport D E.coreData.arities :=
  E.coreData.toRuleWitnessTransport E.startEvidence

/-- Convert to grammar-rule transport data. -/
def toGrammarRuleTransportData
    (E : TrimmedPresentationSameContextCoreEndpoint D) :
    TrimmedPresentationGrammarRuleTransportData D :=
  E.coreData.toGrammarRuleTransportData E.startEvidence

/-- The finite sample produced by the same-context endpoint. -/
def sample
    (E : TrimmedPresentationSameContextCoreEndpoint D) :
    Finset (Word α) :=
  E.coreData.sample E.startEvidence

/-- The finite sample is positive. -/
theorem sample_positive
    (E : TrimmedPresentationSameContextCoreEndpoint D) :
    (E.sample : Set (Word α)) ⊆ G.StringLanguage :=
  E.coreData.sample_positive E.startEvidence

/-- The finite sample contains all required witness words. -/
theorem contains_witnesses
    (E : TrimmedPresentationSameContextCoreEndpoint D) :
    TrimmedPresentationWitnessWordSet D ⊆
      (E.sample : Set (Word α)) :=
  E.coreData.contains_witnesses E.startEvidence

/-- Convert directly to final reachable data. -/
def toFinalReachableData
    (E : TrimmedPresentationSameContextCoreEndpoint D) :
    FinalReachableData G E.sample obs f :=
  E.coreData.toFinalReachableData
    E.startEvidence E.splicingConstructor E.fanout E.promise

/-- The finite sample is a characteristic sample for the reachable learner. -/
theorem characteristic_sample
    (E : TrimmedPresentationSameContextCoreEndpoint D) :
    CharacteristicSample
      (reachableHypLanguage obs f)
      (reachableSampleLearner (α := α))
      E.sample
      G.StringLanguage :=
  E.coreData.characteristic_sample
    E.startEvidence E.splicingConstructor E.fanout E.promise

/-- Exact reconstruction for every positive finite superset of the produced
sample. -/
theorem exact_for_positive_superset
    (E : TrimmedPresentationSameContextCoreEndpoint D)
    {K : Finset (Word α)}
    (hEK : (E.sample : Set (Word α)) ⊆ (K : Set (Word α)))
    (hKpos : (K : Set (Word α)) ⊆ G.StringLanguage) :
    ReachableSampleStringLanguage K obs f = G.StringLanguage :=
  E.coreData.exact_for_positive_superset
    E.startEvidence E.splicingConstructor E.fanout E.promise hEK hKpos

/-- Exact reconstruction at a positive-text prefix containing the produced
sample. -/
theorem exact_at_seen_prefix
    (E : TrimmedPresentationSameContextCoreEndpoint D)
    (Ttxt : TextFor G.StringLanguage)
    {n : Nat}
    (hseen : (E.sample : Set (Word α)) ⊆
      (Ttxt.prefixSample n : Set (Word α))) :
    ReachableSampleStringLanguage (Ttxt.prefixSample n) obs f =
      G.StringLanguage :=
  E.coreData.exact_at_seen_prefix
    E.startEvidence E.splicingConstructor E.fanout E.promise Ttxt hseen

/-- Eventual prefix-exact reconstruction. -/
theorem prefix_exact_eventually
    (E : TrimmedPresentationSameContextCoreEndpoint D) :
    ∀ Ttxt : TextFor G.StringLanguage,
      ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
        ReachableSampleStringLanguage (Ttxt.prefixSample n) obs f =
          G.StringLanguage :=
  E.coreData.prefix_exact_eventually
    E.startEvidence E.splicingConstructor E.fanout E.promise

/-- Reachable Gold identification. -/
theorem identifies_from_positive_text
    (E : TrimmedPresentationSameContextCoreEndpoint D) :
    ∀ Ttxt : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        Ttxt :=
  E.coreData.identifies_from_positive_text
    E.startEvidence E.splicingConstructor E.fanout E.promise

/-- Pointwise eventual correctness on one positive text. -/
theorem eventually_correct_on_text
    (E : TrimmedPresentationSameContextCoreEndpoint D)
    (Ttxt : TextFor G.StringLanguage) :
    EventuallyCorrectOnText
      (reachableHypLanguage obs f)
      (reachableSampleLearner (α := α))
      Ttxt :=
  E.identifies_from_positive_text Ttxt

/-- View the same-context endpoint as a grammar-rule transport endpoint. -/
def toGrammarRuleTransportEndpoint
    (E : TrimmedPresentationSameContextCoreEndpoint D) :
    TrimmedPresentationGrammarRuleTransportEndpoint D where
  transportData := E.toGrammarRuleTransportData
  splicingConstructor := E.splicingConstructor
  fanout := E.fanout
  promise := E.promise

/-- View the same-context endpoint as a rule-transport endpoint. -/
def toRuleTransportEndpoint
    (E : TrimmedPresentationSameContextCoreEndpoint D) :
    TrimmedPresentationRuleTransportEndpoint D :=
  E.toExposingCoreFinalEndpoint.toRuleTransportEndpoint

end TrimmedPresentationSameContextCoreEndpoint

end SameContextCoreEndpoint


section SameContextCoreEndpointFromStartWordSample

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}
variable {f : Nat}
variable {T : TrimmedOutputTypePresentation G obs}
variable {D : TrimmedPresentationPreCoreData T f}
variable {S : Finset (Word α)}

/-- Endpoint wrapper for the same-context core route where start-word evidence
comes from a positive finite sample. -/
structure TrimmedPresentationSameContextCoreEndpointFromSample
    (D : TrimmedPresentationPreCoreData T f)
    (S : Finset (Word α)) where
  coreData : TrimmedPresentationSameContextCoreData D
  startSampleEvidence : TrimmedPresentationStartWordSampleEvidence D S
  splicingConstructor : NamedContextSplicingConstructor α
  fanout : G.FanoutAtMost f
  promise : FixedNamedTupleSubstitutable f obs G.StringLanguage

namespace TrimmedPresentationSameContextCoreEndpointFromSample

/-- Extract compact start-word evidence. -/
def startEvidence
    (E : TrimmedPresentationSameContextCoreEndpointFromSample D S) :
    TrimmedPresentationStartWordEvidence D :=
  E.startSampleEvidence.toStartWordEvidence

/-- Convert to the compact same-context endpoint. -/
def toSameContextCoreEndpoint
    (E : TrimmedPresentationSameContextCoreEndpointFromSample D S) :
    TrimmedPresentationSameContextCoreEndpoint D where
  coreData := E.coreData
  startEvidence := E.startEvidence
  splicingConstructor := E.splicingConstructor
  fanout := E.fanout
  promise := E.promise

/-- Convert to exposing-core final endpoint. -/
def toExposingCoreFinalEndpoint
    (E : TrimmedPresentationSameContextCoreEndpointFromSample D S) :
    TrimmedPresentationExposingCoreFinalEndpoint D :=
  E.toSameContextCoreEndpoint.toExposingCoreFinalEndpoint

/-- The finite sample produced by this endpoint. -/
def sample
    (E : TrimmedPresentationSameContextCoreEndpointFromSample D S) :
    Finset (Word α) :=
  E.toSameContextCoreEndpoint.sample

/-- The finite sample is positive. -/
theorem sample_positive
    (E : TrimmedPresentationSameContextCoreEndpointFromSample D S) :
    (E.sample : Set (Word α)) ⊆ G.StringLanguage :=
  E.toSameContextCoreEndpoint.sample_positive

/-- The auxiliary sample supplies distinguished start-word positivity. -/
theorem startWord_positive
    (E : TrimmedPresentationSameContextCoreEndpointFromSample D S) :
    D.startWord ∈ G.StringLanguage :=
  E.startSampleEvidence.startWord_positive

/-- The finite sample contains all required witness words. -/
theorem contains_witnesses
    (E : TrimmedPresentationSameContextCoreEndpointFromSample D S) :
    TrimmedPresentationWitnessWordSet D ⊆
      (E.sample : Set (Word α)) :=
  E.toSameContextCoreEndpoint.contains_witnesses

/-- Convert directly to final reachable data. -/
def toFinalReachableData
    (E : TrimmedPresentationSameContextCoreEndpointFromSample D S) :
    FinalReachableData G E.sample obs f :=
  E.toSameContextCoreEndpoint.toFinalReachableData

/-- The produced finite sample is a characteristic sample for the reachable
learner. -/
theorem characteristic_sample
    (E : TrimmedPresentationSameContextCoreEndpointFromSample D S) :
    CharacteristicSample
      (reachableHypLanguage obs f)
      (reachableSampleLearner (α := α))
      E.sample
      G.StringLanguage :=
  E.toSameContextCoreEndpoint.characteristic_sample

/-- Exact reconstruction for every positive finite superset of the produced
sample. -/
theorem exact_for_positive_superset
    (E : TrimmedPresentationSameContextCoreEndpointFromSample D S)
    {K : Finset (Word α)}
    (hEK : (E.sample : Set (Word α)) ⊆ (K : Set (Word α)))
    (hKpos : (K : Set (Word α)) ⊆ G.StringLanguage) :
    ReachableSampleStringLanguage K obs f = G.StringLanguage :=
  E.toSameContextCoreEndpoint.exact_for_positive_superset hEK hKpos

/-- Eventual prefix-exact reconstruction. -/
theorem prefix_exact_eventually
    (E : TrimmedPresentationSameContextCoreEndpointFromSample D S) :
    ∀ Ttxt : TextFor G.StringLanguage,
      ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
        ReachableSampleStringLanguage (Ttxt.prefixSample n) obs f =
          G.StringLanguage :=
  E.toSameContextCoreEndpoint.prefix_exact_eventually

/-- Reachable Gold identification. -/
theorem identifies_from_positive_text
    (E : TrimmedPresentationSameContextCoreEndpointFromSample D S) :
    ∀ Ttxt : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        Ttxt :=
  E.toSameContextCoreEndpoint.identifies_from_positive_text

end TrimmedPresentationSameContextCoreEndpointFromSample

end SameContextCoreEndpointFromStartWordSample


section ConversionsFromCoreEndpointsToObligations

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}
variable {f : Nat}
variable {T : TrimmedOutputTypePresentation G obs}
variable {D : TrimmedPresentationPreCoreData T f}

namespace TrimmedPresentationExposingCoreFinalEndpoint

/-- Exposing-core final endpoint viewed as exposing-transport obligations. -/
def toExposingTransportObligations
    (E : TrimmedPresentationExposingCoreFinalEndpoint D) :
    TrimmedPresentationExposingTransportObligations D where
  baseNonterminals := E.finalData.coreData.baseNonterminals
  base_covers := E.finalData.coreData.base_covers
  arities := E.finalData.coreData.arities
  exposingTransport := E.finalData.coreData.exposingTransport
  startEvidence := E.finalData.startEvidence
  splicingConstructor := E.finalData.splicingConstructor
  fanout := E.finalData.fanout
  promise := E.finalData.promise

end TrimmedPresentationExposingCoreFinalEndpoint

namespace TrimmedPresentationSameContextCoreEndpoint

/-- Same-context core endpoint viewed as exposing-transport obligations. -/
def toExposingTransportObligations
    (E : TrimmedPresentationSameContextCoreEndpoint D) :
    TrimmedPresentationExposingTransportObligations D :=
  E.toExposingCoreFinalEndpoint.toExposingTransportObligations

end TrimmedPresentationSameContextCoreEndpoint

end ConversionsFromCoreEndpointsToObligations


section MainTheoremsFromCoreEndpoints

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}
variable {f : Nat}
variable {T : TrimmedOutputTypePresentation G obs}
variable {D : TrimmedPresentationPreCoreData T f}
variable {S : Finset (Word α)}

/-- Stable top-level reachable identification theorem from exposing-core final
endpoint. -/
theorem trimmed_exposing_core_final_endpoint_reachable_identification
    (E : TrimmedPresentationExposingCoreFinalEndpoint D) :
    ∀ Ttxt : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        Ttxt :=
  E.identifies_from_positive_text

/-- Stable top-level prefix-exact theorem from exposing-core final endpoint. -/
theorem trimmed_exposing_core_final_endpoint_prefix_exact
    (E : TrimmedPresentationExposingCoreFinalEndpoint D) :
    ∀ Ttxt : TextFor G.StringLanguage,
      ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
        ReachableSampleStringLanguage (Ttxt.prefixSample n) obs f =
          G.StringLanguage :=
  E.prefix_exact_eventually

/-- Stable top-level positive finite-superset exactness theorem from
exposing-core final endpoint. -/
theorem trimmed_exposing_core_final_endpoint_exact_for_positive_superset
    (E : TrimmedPresentationExposingCoreFinalEndpoint D)
    {K : Finset (Word α)}
    (hEK : (E.sample : Set (Word α)) ⊆ (K : Set (Word α)))
    (hKpos : (K : Set (Word α)) ⊆ G.StringLanguage) :
    ReachableSampleStringLanguage K obs f = G.StringLanguage :=
  E.exact_for_positive_superset hEK hKpos

/-- Stable top-level reachable identification theorem from same-context core
endpoint. -/
theorem trimmed_same_context_core_endpoint_reachable_identification
    (E : TrimmedPresentationSameContextCoreEndpoint D) :
    ∀ Ttxt : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        Ttxt :=
  E.identifies_from_positive_text

/-- Stable top-level prefix-exact theorem from same-context core endpoint. -/
theorem trimmed_same_context_core_endpoint_prefix_exact
    (E : TrimmedPresentationSameContextCoreEndpoint D) :
    ∀ Ttxt : TextFor G.StringLanguage,
      ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
        ReachableSampleStringLanguage (Ttxt.prefixSample n) obs f =
          G.StringLanguage :=
  E.prefix_exact_eventually

/-- Stable top-level positive finite-superset exactness theorem from
same-context core endpoint. -/
theorem trimmed_same_context_core_endpoint_exact_for_positive_superset
    (E : TrimmedPresentationSameContextCoreEndpoint D)
    {K : Finset (Word α)}
    (hEK : (E.sample : Set (Word α)) ⊆ (K : Set (Word α)))
    (hKpos : (K : Set (Word α)) ⊆ G.StringLanguage) :
    ReachableSampleStringLanguage K obs f = G.StringLanguage :=
  E.exact_for_positive_superset hEK hKpos

/-- Stable top-level reachable identification theorem from same-context core
endpoint whose start-word evidence comes from a positive finite sample. -/
theorem trimmed_same_context_core_sample_endpoint_reachable_identification
    (E : TrimmedPresentationSameContextCoreEndpointFromSample D S) :
    ∀ Ttxt : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        Ttxt :=
  E.identifies_from_positive_text

/-- Stable top-level prefix-exact theorem from same-context core endpoint whose
start-word evidence comes from a positive finite sample. -/
theorem trimmed_same_context_core_sample_endpoint_prefix_exact
    (E : TrimmedPresentationSameContextCoreEndpointFromSample D S) :
    ∀ Ttxt : TextFor G.StringLanguage,
      ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
        ReachableSampleStringLanguage (Ttxt.prefixSample n) obs f =
          G.StringLanguage :=
  E.prefix_exact_eventually

end MainTheoremsFromCoreEndpoints

end MCFG
