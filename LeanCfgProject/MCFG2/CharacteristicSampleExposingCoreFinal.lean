/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG2.CharacteristicSampleStartWordEvidence

/-!
# CharacteristicSampleExposingCoreFinal.lean

Sixty-third clean Lean experiment for the fixed-observation MCFG project.

`CharacteristicSampleStartWordEvidence.lean` separated the two remaining
semantic obligations for the characteristic-sample route:

* exposing-context transport;
* positivity of the distinguished start word.

This file gives that separated route a final wrapper:

```lean
TrimmedPresentationExposingCoreFinalData
```

It packages

* core exposing-transport data;
* start-word evidence;
* the named-context splicing constructor;
* the global fanout and fixed-observation substitutability assumptions.

From this package we expose the standard final conclusions:

* characteristic sample;
* exact reconstruction on positive finite supersets;
* eventual prefix-exact reconstruction;
* reachable Gold identification.

No theorem here uses `sorry`.
-/

namespace MCFG

universe u v w

section ExposingCoreFinalData

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}
variable {f : Nat}
variable {T : TrimmedOutputTypePresentation G obs}
variable {D : TrimmedPresentationPreCoreData T f}

/-- Final theorem data for the separated exposing-transport route. -/
structure TrimmedPresentationExposingCoreFinalData
    (D : TrimmedPresentationPreCoreData T f) where
  coreData : TrimmedPresentationExposingTransportCoreData D
  startEvidence : TrimmedPresentationStartWordEvidence D
  splicingConstructor : NamedContextSplicingConstructor α
  fanout : G.FanoutAtMost f
  promise : FixedNamedTupleSubstitutable f obs G.StringLanguage

namespace TrimmedPresentationExposingCoreFinalData

/-- The exposing-transport data recovered from the core data and start-word
evidence. -/
def toExposingTransportData
    (F : TrimmedPresentationExposingCoreFinalData D) :
    TrimmedPresentationExposingTransportData D :=
  F.coreData.withStartWord F.startEvidence

/-- The finite sample produced by the final data. -/
def sample
    (F : TrimmedPresentationExposingCoreFinalData D) :
    Finset (Word α) :=
  F.toExposingTransportData.sample

/-- The produced finite sample is positive. -/
theorem sample_positive
    (F : TrimmedPresentationExposingCoreFinalData D) :
    (F.sample : Set (Word α)) ⊆ G.StringLanguage :=
  F.toExposingTransportData.sample_positive

/-- The produced finite sample contains all required witness words. -/
theorem contains_witnesses
    (F : TrimmedPresentationExposingCoreFinalData D) :
    TrimmedPresentationWitnessWordSet D ⊆
      (F.sample : Set (Word α)) :=
  F.toExposingTransportData.contains_witnesses

/-- Convert to rule-witness transport. -/
def toRuleWitnessTransport
    (F : TrimmedPresentationExposingCoreFinalData D) :
    TrimmedPresentationRuleWitnessTransport D F.coreData.arities :=
  F.coreData.toRuleWitnessTransport F.startEvidence

/-- Convert to grammar-rule transport data. -/
def toGrammarRuleTransportData
    (F : TrimmedPresentationExposingCoreFinalData D) :
    TrimmedPresentationGrammarRuleTransportData D :=
  F.coreData.toGrammarRuleTransportData F.startEvidence

/-- Convert to the rule-transport final wrapper. -/
def toRuleTransportFinalData
    (F : TrimmedPresentationExposingCoreFinalData D) :
    TrimmedPresentationRuleTransportFinalData D :=
  F.toExposingTransportData.toRuleTransportFinalData
    F.splicingConstructor F.fanout F.promise

/-- Convert directly to final reachable data. -/
def toFinalReachableData
    (F : TrimmedPresentationExposingCoreFinalData D) :
    FinalReachableData G F.sample obs f :=
  F.toExposingTransportData.toFinalReachableData
    F.splicingConstructor F.fanout F.promise

/-- The produced finite sample is a characteristic sample for the reachable
learner. -/
theorem characteristic_sample
    (F : TrimmedPresentationExposingCoreFinalData D) :
    CharacteristicSample
      (reachableHypLanguage obs f)
      (reachableSampleLearner (α := α))
      F.sample
      G.StringLanguage :=
  F.toExposingTransportData.characteristic_sample
    F.splicingConstructor F.fanout F.promise

/-- Exact reconstruction for every positive finite superset of the produced
sample. -/
theorem exact_for_positive_superset
    (F : TrimmedPresentationExposingCoreFinalData D)
    {K : Finset (Word α)}
    (hFK : (F.sample : Set (Word α)) ⊆ (K : Set (Word α)))
    (hKpos : (K : Set (Word α)) ⊆ G.StringLanguage) :
    ReachableSampleStringLanguage K obs f = G.StringLanguage :=
  F.toRuleTransportFinalData.exact_for_positive_superset hFK hKpos

/-- Exact reconstruction at a positive-text prefix containing the produced
sample. -/
theorem exact_at_seen_prefix
    (F : TrimmedPresentationExposingCoreFinalData D)
    (Ttxt : TextFor G.StringLanguage)
    {n : Nat}
    (hseen : (F.sample : Set (Word α)) ⊆
      (Ttxt.prefixSample n : Set (Word α))) :
    ReachableSampleStringLanguage (Ttxt.prefixSample n) obs f =
      G.StringLanguage :=
  F.toRuleTransportFinalData.exact_at_seen_prefix Ttxt hseen

/-- Eventual prefix-exact reconstruction from separated exposing-core final
data. -/
theorem prefix_exact_eventually
    (F : TrimmedPresentationExposingCoreFinalData D) :
    ∀ Ttxt : TextFor G.StringLanguage,
      ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
        ReachableSampleStringLanguage (Ttxt.prefixSample n) obs f =
          G.StringLanguage :=
  F.toExposingTransportData.prefix_exact_eventually
    F.splicingConstructor F.fanout F.promise

/-- Reachable Gold identification from separated exposing-core final data. -/
theorem identifies_from_positive_text
    (F : TrimmedPresentationExposingCoreFinalData D) :
    ∀ Ttxt : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        Ttxt :=
  F.toExposingTransportData.identifies_from_positive_text
    F.splicingConstructor F.fanout F.promise

/-- Pointwise eventual correctness on one positive text. -/
theorem eventually_correct_on_text
    (F : TrimmedPresentationExposingCoreFinalData D)
    (Ttxt : TextFor G.StringLanguage) :
    EventuallyCorrectOnText
      (reachableHypLanguage obs f)
      (reachableSampleLearner (α := α))
      Ttxt :=
  F.identifies_from_positive_text Ttxt

end TrimmedPresentationExposingCoreFinalData

end ExposingCoreFinalData


section MainTheoremsFromExposingCoreFinalData

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}
variable {f : Nat}
variable {T : TrimmedOutputTypePresentation G obs}
variable {D : TrimmedPresentationPreCoreData T f}

/-- Stable top-level reachable identification theorem from separated
exposing-core final data. -/
theorem trimmed_exposing_core_final_reachable_identification
    (F : TrimmedPresentationExposingCoreFinalData D) :
    ∀ Ttxt : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        Ttxt :=
  F.identifies_from_positive_text

/-- Stable top-level prefix-exact theorem from separated exposing-core final
data. -/
theorem trimmed_exposing_core_final_reachable_prefix_exact
    (F : TrimmedPresentationExposingCoreFinalData D) :
    ∀ Ttxt : TextFor G.StringLanguage,
      ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
        ReachableSampleStringLanguage (Ttxt.prefixSample n) obs f =
          G.StringLanguage :=
  F.prefix_exact_eventually

/-- Stable top-level finite-superset exactness theorem from separated
exposing-core final data. -/
theorem trimmed_exposing_core_final_exact_for_positive_superset
    (F : TrimmedPresentationExposingCoreFinalData D)
    {K : Finset (Word α)}
    (hFK : (F.sample : Set (Word α)) ⊆ (K : Set (Word α)))
    (hKpos : (K : Set (Word α)) ⊆ G.StringLanguage) :
    ReachableSampleStringLanguage K obs f = G.StringLanguage :=
  F.exact_for_positive_superset hFK hKpos

end MainTheoremsFromExposingCoreFinalData

end MCFG
