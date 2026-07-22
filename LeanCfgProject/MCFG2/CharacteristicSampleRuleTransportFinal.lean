/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG2.CharacteristicSampleRuleWitnessTransport

/-!
# CharacteristicSampleRuleTransportFinal.lean

Fifty-ninth clean Lean experiment for the fixed-observation MCFG project.

`CharacteristicSampleRuleWitnessTransport.lean` isolated the remaining semantic
positivity target for the grammar-rule characteristic sample as

```lean
TrimmedPresentationRuleWitnessTransport
```

and packaged it with a finite base-nonterminal cover as

```lean
TrimmedPresentationGrammarRuleTransportData
```

This file gives that route a final-data wrapper.  It is the stable endpoint for
the current characteristic-sample construction pipeline before proving the
actual witness-transport positivity lemmas.

The route is now:

```text
TrimmedPresentationGrammarRuleTransportData
+
NamedContextSplicingConstructor
+
fanout
+
fixed-observation substitutability
⇒ FinalReachableData
⇒ reachable identification / prefix exactness.
```

No theorem here uses `sorry`.
-/

namespace MCFG

universe u v w

section RuleTransportFinalData

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}
variable {f : Nat}
variable {T : TrimmedOutputTypePresentation G obs}
variable {D : TrimmedPresentationPreCoreData T f}

/-- Final theorem data for the rule-witness-transport route.

This is the current most concrete endpoint of the characteristic-sample
pipeline before proving the semantic transport facts. -/
structure TrimmedPresentationRuleTransportFinalData
    (D : TrimmedPresentationPreCoreData T f) where
  transportData : TrimmedPresentationGrammarRuleTransportData D
  splicingConstructor : NamedContextSplicingConstructor α
  fanout : G.FanoutAtMost f
  promise : FixedNamedTupleSubstitutable f obs G.StringLanguage

namespace TrimmedPresentationRuleTransportFinalData

/-- The finite sample produced by the transport final data. -/
noncomputable def sample
    (F : TrimmedPresentationRuleTransportFinalData D) :
    Finset (Word α) :=
  F.transportData.sample

/-- The produced finite sample is positive. -/
theorem sample_positive
    (F : TrimmedPresentationRuleTransportFinalData D) :
    (F.sample : Set (Word α)) ⊆ G.StringLanguage :=
  F.transportData.sample_positive

/-- The produced finite sample contains all required witness words. -/
theorem contains_witnesses
    (F : TrimmedPresentationRuleTransportFinalData D) :
    TrimmedPresentationWitnessWordSet D ⊆
      (F.sample : Set (Word α)) :=
  F.transportData.contains_witnesses

/-- Convert to reduced grammar-rule data. -/
def toGrammarRuleData
    (F : TrimmedPresentationRuleTransportFinalData D) :
    TrimmedPresentationGrammarRuleData D :=
  F.transportData.toGrammarRuleData

/-- Convert to the grammar-rule builder. -/
def toGrammarRuleBuilder
    (F : TrimmedPresentationRuleTransportFinalData D) :
    TrimmedPresentationGrammarRuleBuilder D :=
  F.toGrammarRuleData.toGrammarRuleBuilder

/-- Convert to componentwise characteristic-sample data. -/
noncomputable def toComponentPackage
    (F : TrimmedPresentationRuleTransportFinalData D) :
    TrimmedPresentationComponentPackage D :=
  F.transportData.toGrammarRuleData.toComponentPackage

/-- Convert to the abstract finite-sample builder. -/
noncomputable def toFiniteSampleBuilder
    (F : TrimmedPresentationRuleTransportFinalData D) :
    TrimmedPresentationFiniteSampleBuilder D :=
  F.transportData.toFiniteSampleBuilder

/-- Convert to a witness-sample package. -/
def toWitnessSample
    (F : TrimmedPresentationRuleTransportFinalData D) :
    TrimmedPresentationWitnessSample D F.sample :=
  F.transportData.toWitnessSample

/-- Convert to a characteristic-sample object. -/
noncomputable def toCharacteristicSample
    (F : TrimmedPresentationRuleTransportFinalData D) :
    TrimmedPresentationCharacteristicSample D :=
  F.transportData.toCharacteristicSample

/-- Convert to final reachable data. -/
noncomputable def toFinalReachableData
    (F : TrimmedPresentationRuleTransportFinalData D) :
    FinalReachableData G F.sample obs f :=
  F.transportData.toFinalReachableData
    F.splicingConstructor F.fanout F.promise

/-- The produced finite sample is a characteristic sample for the reachable
learner. -/
theorem characteristic_sample
    (F : TrimmedPresentationRuleTransportFinalData D) :
    CharacteristicSample
      (reachableHypLanguage obs f)
      (reachableSampleLearner (α := α))
      F.sample
      G.StringLanguage :=
  F.transportData.characteristic_sample
    F.splicingConstructor F.fanout F.promise

/-- Exact reconstruction for every positive finite superset of the produced
sample. -/
theorem exact_for_positive_superset
    (F : TrimmedPresentationRuleTransportFinalData D)
    {K : Finset (Word α)}
    (hFK : (F.sample : Set (Word α)) ⊆ (K : Set (Word α)))
    (hKpos : (K : Set (Word α)) ⊆ G.StringLanguage) :
    ReachableSampleStringLanguage K obs f = G.StringLanguage :=
  F.toWitnessSample.exact_after_mono
    F.splicingConstructor F.fanout F.promise hFK hKpos

/-- Exact reconstruction at a positive-text prefix containing the produced
sample. -/
theorem exact_at_seen_prefix
    (F : TrimmedPresentationRuleTransportFinalData D)
    (Ttxt : TextFor G.StringLanguage)
    {n : Nat}
    (hseen : (F.sample : Set (Word α)) ⊆
      (Ttxt.prefixSample n : Set (Word α))) :
    ReachableSampleStringLanguage (Ttxt.prefixSample n) obs f =
      G.StringLanguage :=
  F.toWitnessSample.exact_at_prefix_via_mono
    F.splicingConstructor F.fanout F.promise Ttxt hseen

/-- Eventual prefix-exact reconstruction from rule-transport final data. -/
theorem prefix_exact_eventually
    (F : TrimmedPresentationRuleTransportFinalData D) :
    ∀ Ttxt : TextFor G.StringLanguage,
      ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
        ReachableSampleStringLanguage (Ttxt.prefixSample n) obs f =
          G.StringLanguage :=
  F.transportData.prefix_exact_eventually
    F.splicingConstructor F.fanout F.promise

/-- Reachable Gold identification from rule-transport final data. -/
theorem identifies_from_positive_text
    (F : TrimmedPresentationRuleTransportFinalData D) :
    ∀ Ttxt : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        Ttxt :=
  F.transportData.identifies_from_positive_text
    F.splicingConstructor F.fanout F.promise

/-- Pointwise eventual correctness on one positive text. -/
theorem eventually_correct_on_text
    (F : TrimmedPresentationRuleTransportFinalData D)
    (Ttxt : TextFor G.StringLanguage) :
    EventuallyCorrectOnText
      (reachableHypLanguage obs f)
      (reachableSampleLearner (α := α))
      Ttxt :=
  F.identifies_from_positive_text Ttxt

end TrimmedPresentationRuleTransportFinalData

end RuleTransportFinalData


section MainTheoremsFromRuleTransportFinalData

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}
variable {f : Nat}
variable {T : TrimmedOutputTypePresentation G obs}
variable {D : TrimmedPresentationPreCoreData T f}

/-- Stable top-level reachable identification theorem from rule-transport final
data. -/
theorem trimmed_rule_transport_final_reachable_identification
    (F : TrimmedPresentationRuleTransportFinalData D) :
    ∀ Ttxt : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        Ttxt :=
  F.identifies_from_positive_text

/-- Stable top-level prefix-exact theorem from rule-transport final data. -/
theorem trimmed_rule_transport_final_reachable_prefix_exact
    (F : TrimmedPresentationRuleTransportFinalData D) :
    ∀ Ttxt : TextFor G.StringLanguage,
      ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
        ReachableSampleStringLanguage (Ttxt.prefixSample n) obs f =
          G.StringLanguage :=
  F.prefix_exact_eventually

/-- Stable top-level finite-superset exactness theorem from rule-transport final
data. -/
theorem trimmed_rule_transport_final_exact_for_positive_superset
    (F : TrimmedPresentationRuleTransportFinalData D)
    {K : Finset (Word α)}
    (hFK : (F.sample : Set (Word α)) ⊆ (K : Set (Word α)))
    (hKpos : (K : Set (Word α)) ⊆ G.StringLanguage) :
    ReachableSampleStringLanguage K obs f = G.StringLanguage :=
  F.exact_for_positive_superset hFK hKpos

end MainTheoremsFromRuleTransportFinalData

end MCFG
