/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG2.CharacteristicSampleTransportInterfaceDiagram

/-!
# CharacteristicSampleAnchorCommonContextFinal.lean

Seventieth clean Lean experiment for the fixed-observation MCFG project.

`CharacteristicSampleAnchorCommonContext.lean` introduced the common-context
route:

```text
common accepting context
+
fixed-observation substitutability
⇒ anchor distributional equivalence
⇒ exposing-context transport
⇒ characteristic sample.
```

`CharacteristicSampleTransportInterfaceDiagram.lean` then recorded the
conversion diagram among the transport interfaces.

This file gives the common-context route its own final-data wrapper.  It stores

* common-context core data;
* start-word evidence;
* a named-context splicing constructor;
* fanout;
* fixed-observation substitutability.

From this package, we expose the standard endpoint theorems:

* characteristic sample;
* exact reconstruction on positive finite supersets;
* prefix-exact eventual reconstruction;
* reachable Gold identification.

No theorem here uses `sorry`.
-/

namespace MCFG

universe u v w

section AnchorCommonContextFinalData

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}
variable {f : Nat}
variable {T : TrimmedOutputTypePresentation G obs}
variable {D : TrimmedPresentationPreCoreData T f}

/-- Final theorem data for the common-context transport route. -/
structure TrimmedPresentationAnchorCommonContextFinalData
    (D : TrimmedPresentationPreCoreData T f) where
  commonData : TrimmedPresentationAnchorCommonContextCoreData D
  startEvidence : TrimmedPresentationStartWordEvidence D
  splicingConstructor : NamedContextSplicingConstructor α
  fanout : G.FanoutAtMost f
  promise : FixedNamedTupleSubstitutable f obs G.StringLanguage

namespace TrimmedPresentationAnchorCommonContextFinalData

/-- Convert to anchor-distributional core data. -/
def toAnchorDistributionCoreData
    (F : TrimmedPresentationAnchorCommonContextFinalData D) :
    TrimmedPresentationAnchorDistributionCoreData D :=
  F.commonData.toAnchorDistributionCoreData F.fanout F.promise

/-- Convert to exposing-transport core data. -/
def toExposingTransportCoreData
    (F : TrimmedPresentationAnchorCommonContextFinalData D) :
    TrimmedPresentationExposingTransportCoreData D :=
  F.commonData.toExposingTransportCoreData F.fanout F.promise

/-- Convert to exposing-common core data. -/
def toExposingCommonCoreData
    (F : TrimmedPresentationAnchorCommonContextFinalData D) :
    TrimmedPresentationExposingCommonCoreData D :=
  F.commonData.toExposingCommonCoreData F.fanout F.promise

/-- Convert to the separated exposing-core final wrapper. -/
def toExposingCoreFinalData
    (F : TrimmedPresentationAnchorCommonContextFinalData D) :
    TrimmedPresentationExposingCoreFinalData D :=
  F.commonData.toExposingCoreFinalData
    F.startEvidence F.splicingConstructor F.fanout F.promise

/-- The finite sample produced by the common-context final data. -/
noncomputable def sample
    (F : TrimmedPresentationAnchorCommonContextFinalData D) :
    Finset (Word α) :=
  F.toExposingCoreFinalData.sample

/-- The produced finite sample is positive. -/
theorem sample_positive
    (F : TrimmedPresentationAnchorCommonContextFinalData D) :
    (F.sample : Set (Word α)) ⊆ G.StringLanguage :=
  F.toExposingCoreFinalData.sample_positive

/-- The produced finite sample contains all required witness words. -/
theorem contains_witnesses
    (F : TrimmedPresentationAnchorCommonContextFinalData D) :
    TrimmedPresentationWitnessWordSet D ⊆
      (F.sample : Set (Word α)) :=
  F.toExposingCoreFinalData.contains_witnesses

/-- Convert to rule-witness transport. -/
def toRuleWitnessTransport
    (F : TrimmedPresentationAnchorCommonContextFinalData D) :
    TrimmedPresentationRuleWitnessTransport D F.commonData.arities :=
  F.toExposingCoreFinalData.toRuleWitnessTransport

/-- Convert to grammar-rule transport data. -/
def toGrammarRuleTransportData
    (F : TrimmedPresentationAnchorCommonContextFinalData D) :
    TrimmedPresentationGrammarRuleTransportData D :=
  F.toExposingCoreFinalData.toGrammarRuleTransportData

/-- Convert to final reachable data. -/
noncomputable def toFinalReachableData
    (F : TrimmedPresentationAnchorCommonContextFinalData D) :
    FinalReachableData G F.sample obs f :=
  F.toExposingCoreFinalData.toFinalReachableData

/-- The produced finite sample is a characteristic sample for the reachable
learner. -/
theorem characteristic_sample
    (F : TrimmedPresentationAnchorCommonContextFinalData D) :
    CharacteristicSample
      (reachableHypLanguage obs f)
      (reachableSampleLearner (α := α))
      F.sample
      G.StringLanguage :=
  F.toExposingCoreFinalData.characteristic_sample

/-- Exact reconstruction for every positive finite superset of the produced
sample. -/
theorem exact_for_positive_superset
    (F : TrimmedPresentationAnchorCommonContextFinalData D)
    {K : Finset (Word α)}
    (hFK : (F.sample : Set (Word α)) ⊆ (K : Set (Word α)))
    (hKpos : (K : Set (Word α)) ⊆ G.StringLanguage) :
    ReachableSampleStringLanguage K obs f = G.StringLanguage :=
  F.toExposingCoreFinalData.exact_for_positive_superset hFK hKpos

/-- Exact reconstruction at a positive-text prefix containing the produced
sample. -/
theorem exact_at_seen_prefix
    (F : TrimmedPresentationAnchorCommonContextFinalData D)
    (Ttxt : TextFor G.StringLanguage)
    {n : Nat}
    (hseen : (F.sample : Set (Word α)) ⊆
      (Ttxt.prefixSample n : Set (Word α))) :
    ReachableSampleStringLanguage (Ttxt.prefixSample n) obs f =
      G.StringLanguage :=
  F.toExposingCoreFinalData.exact_at_seen_prefix Ttxt hseen

/-- Eventual prefix-exact reconstruction from common-context final data. -/
theorem prefix_exact_eventually
    (F : TrimmedPresentationAnchorCommonContextFinalData D) :
    ∀ Ttxt : TextFor G.StringLanguage,
      ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
        ReachableSampleStringLanguage (Ttxt.prefixSample n) obs f =
          G.StringLanguage :=
  F.toExposingCoreFinalData.prefix_exact_eventually

/-- Reachable Gold identification from common-context final data. -/
theorem identifies_from_positive_text
    (F : TrimmedPresentationAnchorCommonContextFinalData D) :
    ∀ Ttxt : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        Ttxt :=
  F.toExposingCoreFinalData.identifies_from_positive_text

/-- Pointwise eventual correctness on one positive text. -/
theorem eventually_correct_on_text
    (F : TrimmedPresentationAnchorCommonContextFinalData D)
    (Ttxt : TextFor G.StringLanguage) :
    EventuallyCorrectOnText
      (reachableHypLanguage obs f)
      (reachableSampleLearner (α := α))
      Ttxt :=
  F.identifies_from_positive_text Ttxt

end TrimmedPresentationAnchorCommonContextFinalData

end AnchorCommonContextFinalData


section AnchorCommonContextFinalFromSample

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}
variable {f : Nat}
variable {T : TrimmedOutputTypePresentation G obs}
variable {D : TrimmedPresentationPreCoreData T f}
variable {S : Finset (Word α)}

namespace TrimmedPresentationAnchorCommonContextCoreData

/-- Build common-context final data using start-word evidence extracted from any
positive finite sample containing the distinguished start word. -/
def toAnchorCommonContextFinalDataOfStartWordSample
    (P : TrimmedPresentationAnchorCommonContextCoreData D)
    (E : TrimmedPresentationStartWordSampleEvidence D S)
    (U : NamedContextSplicingConstructor α)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    TrimmedPresentationAnchorCommonContextFinalData D where
  commonData := P
  startEvidence := E.toStartWordEvidence
  splicingConstructor := U
  fanout := hfan
  promise := hL

/-- Eventual prefix-exact reconstruction through common-context final data
using start-word evidence extracted from a positive finite sample. -/
theorem prefix_exact_eventually_of_startWord_sample_final
    (P : TrimmedPresentationAnchorCommonContextCoreData D)
    (E : TrimmedPresentationStartWordSampleEvidence D S)
    (U : NamedContextSplicingConstructor α)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    ∀ Ttxt : TextFor G.StringLanguage,
      ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
        ReachableSampleStringLanguage (Ttxt.prefixSample n) obs f =
          G.StringLanguage :=
  (P.toAnchorCommonContextFinalDataOfStartWordSample E U hfan hL).prefix_exact_eventually

/-- Reachable Gold identification through common-context final data using
start-word evidence extracted from a positive finite sample. -/
theorem identifies_from_positive_text_of_startWord_sample_final
    (P : TrimmedPresentationAnchorCommonContextCoreData D)
    (E : TrimmedPresentationStartWordSampleEvidence D S)
    (U : NamedContextSplicingConstructor α)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    ∀ Ttxt : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        Ttxt :=
  (P.toAnchorCommonContextFinalDataOfStartWordSample E U hfan hL).identifies_from_positive_text

end TrimmedPresentationAnchorCommonContextCoreData

end AnchorCommonContextFinalFromSample


section MainTheoremsFromAnchorCommonContextFinalData

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}
variable {f : Nat}
variable {T : TrimmedOutputTypePresentation G obs}
variable {D : TrimmedPresentationPreCoreData T f}

/-- Stable top-level reachable identification theorem from common-context final
data. -/
theorem trimmed_anchor_common_context_final_reachable_identification
    (F : TrimmedPresentationAnchorCommonContextFinalData D) :
    ∀ Ttxt : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        Ttxt :=
  F.identifies_from_positive_text

/-- Stable top-level prefix-exact theorem from common-context final data. -/
theorem trimmed_anchor_common_context_final_reachable_prefix_exact
    (F : TrimmedPresentationAnchorCommonContextFinalData D) :
    ∀ Ttxt : TextFor G.StringLanguage,
      ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
        ReachableSampleStringLanguage (Ttxt.prefixSample n) obs f =
          G.StringLanguage :=
  F.prefix_exact_eventually

/-- Stable top-level finite-superset exactness theorem from common-context final
data. -/
theorem trimmed_anchor_common_context_final_exact_for_positive_superset
    (F : TrimmedPresentationAnchorCommonContextFinalData D)
    {K : Finset (Word α)}
    (hFK : (F.sample : Set (Word α)) ⊆ (K : Set (Word α)))
    (hKpos : (K : Set (Word α)) ⊆ G.StringLanguage) :
    ReachableSampleStringLanguage K obs f = G.StringLanguage :=
  F.exact_for_positive_superset hFK hKpos

end MainTheoremsFromAnchorCommonContextFinalData

end MCFG
