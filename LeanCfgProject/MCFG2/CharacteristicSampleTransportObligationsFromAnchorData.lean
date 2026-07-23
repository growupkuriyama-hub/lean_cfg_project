/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG2.CharacteristicSampleTransportObligationsFromCoreData

/-!
# CharacteristicSampleTransportObligationsFromAnchorData.lean

Seventy-ninth clean Lean experiment for the fixed-observation MCFG project.

`CharacteristicSampleTransportObligationsFromCoreData.lean` gave endpoint
wrappers for exposing-core and same-context-core data.  This file gives the
analogous endpoint wrappers for the anchor-based semantic routes:

* `TrimmedPresentationAnchorDistributionCoreData`;
* `TrimmedPresentationAnchorCommonContextCoreData`.

The intended map is:

```text
AnchorCommonContextCoreData
⇒ AnchorDistributionCoreData
⇒ ExposingTransportCoreData
⇒ ExposingCoreFinalData
⇒ FinalReachableData.
```

The common-context route is often the most natural target for the actual
semantic proof, because it asks for one context accepting both the anchor tuple
and a same-type tuple.

No new semantic principle is introduced here.

No theorem here uses `sorry`.
-/

namespace MCFG

universe u v w

section AnchorDistributionCoreEndpoint

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}
variable {f : Nat}
variable {T : TrimmedOutputTypePresentation G obs}

/-- Endpoint wrapper for the anchor-distribution route with compact start-word
evidence. -/
structure TrimmedPresentationAnchorDistributionCoreEndpoint
    (D : TrimmedPresentationPreCoreData T f) where
  coreData : TrimmedPresentationAnchorDistributionCoreData D
  startEvidence : TrimmedPresentationStartWordEvidence D
  splicingConstructor : NamedContextSplicingConstructor α
  fanout : G.FanoutAtMost f
  promise : FixedNamedTupleSubstitutable f obs G.StringLanguage

namespace TrimmedPresentationAnchorDistributionCoreEndpoint

variable {D : TrimmedPresentationPreCoreData T f}

/-- Convert to exposing-transport core data. -/
def toExposingTransportCoreData
    (E : TrimmedPresentationAnchorDistributionCoreEndpoint D) :
    TrimmedPresentationExposingTransportCoreData D :=
  E.coreData.toExposingTransportCoreData

/-- Convert to exposing-transport data. -/
def toExposingTransportData
    (E : TrimmedPresentationAnchorDistributionCoreEndpoint D) :
    TrimmedPresentationExposingTransportData D :=
  E.coreData.toExposingTransportData E.startEvidence

/-- Convert to the separated exposing-core final data. -/
def toExposingCoreFinalData
    (E : TrimmedPresentationAnchorDistributionCoreEndpoint D) :
    TrimmedPresentationExposingCoreFinalData D :=
  E.coreData.toExposingCoreFinalData
    E.startEvidence E.splicingConstructor E.fanout E.promise

/-- Convert to exposing-core final endpoint. -/
def toExposingCoreFinalEndpoint
    (E : TrimmedPresentationAnchorDistributionCoreEndpoint D) :
    TrimmedPresentationExposingCoreFinalEndpoint D where
  finalData := E.toExposingCoreFinalData

/-- Convert to exposing-transport obligations. -/
def toExposingTransportObligations
    (E : TrimmedPresentationAnchorDistributionCoreEndpoint D) :
    TrimmedPresentationExposingTransportObligations D :=
  E.toExposingCoreFinalEndpoint.toExposingTransportObligations

/-- Convert to grammar-rule transport data. -/
def toGrammarRuleTransportData
    (E : TrimmedPresentationAnchorDistributionCoreEndpoint D) :
    TrimmedPresentationGrammarRuleTransportData D :=
  E.coreData.toGrammarRuleTransportData E.startEvidence

/-- Convert to grammar-rule transport endpoint. -/
def toGrammarRuleTransportEndpoint
    (E : TrimmedPresentationAnchorDistributionCoreEndpoint D) :
    TrimmedPresentationGrammarRuleTransportEndpoint D where
  transportData := E.toGrammarRuleTransportData
  splicingConstructor := E.splicingConstructor
  fanout := E.fanout
  promise := E.promise

/-- The finite sample produced by this endpoint. -/
noncomputable def sample
    (E : TrimmedPresentationAnchorDistributionCoreEndpoint D) :
    Finset (Word α) :=
  E.toExposingCoreFinalEndpoint.sample

/-- The finite sample is positive. -/
theorem sample_positive
    (E : TrimmedPresentationAnchorDistributionCoreEndpoint D) :
    (E.sample : Set (Word α)) ⊆ G.StringLanguage :=
  E.toExposingCoreFinalEndpoint.sample_positive

/-- The finite sample contains all required witness words. -/
theorem contains_witnesses
    (E : TrimmedPresentationAnchorDistributionCoreEndpoint D) :
    TrimmedPresentationWitnessWordSet D ⊆
      (E.sample : Set (Word α)) :=
  E.toExposingCoreFinalEndpoint.contains_witnesses

/-- Convert directly to final reachable data. -/
noncomputable def toFinalReachableData
    (E : TrimmedPresentationAnchorDistributionCoreEndpoint D) :
    FinalReachableData G E.sample obs f :=
  E.toExposingCoreFinalEndpoint.toFinalReachableData

/-- The produced finite sample is a characteristic sample for the reachable
learner. -/
theorem characteristic_sample
    (E : TrimmedPresentationAnchorDistributionCoreEndpoint D) :
    CharacteristicSample
      (reachableHypLanguage obs f)
      (reachableSampleLearner (α := α))
      E.sample
      G.StringLanguage :=
  E.toExposingCoreFinalEndpoint.characteristic_sample

/-- Exact reconstruction for every positive finite superset of the produced
sample. -/
theorem exact_for_positive_superset
    (E : TrimmedPresentationAnchorDistributionCoreEndpoint D)
    {K : Finset (Word α)}
    (hEK : (E.sample : Set (Word α)) ⊆ (K : Set (Word α)))
    (hKpos : (K : Set (Word α)) ⊆ G.StringLanguage) :
    ReachableSampleStringLanguage K obs f = G.StringLanguage :=
  E.toExposingCoreFinalEndpoint.exact_for_positive_superset hEK hKpos

/-- Exact reconstruction at a positive-text prefix containing the produced
sample. -/
theorem exact_at_seen_prefix
    (E : TrimmedPresentationAnchorDistributionCoreEndpoint D)
    (Ttxt : TextFor G.StringLanguage)
    {n : Nat}
    (hseen : (E.sample : Set (Word α)) ⊆
      (Ttxt.prefixSample n : Set (Word α))) :
    ReachableSampleStringLanguage (Ttxt.prefixSample n) obs f =
      G.StringLanguage :=
  E.toExposingCoreFinalEndpoint.exact_at_seen_prefix Ttxt hseen

/-- Eventual prefix-exact reconstruction. -/
theorem prefix_exact_eventually
    (E : TrimmedPresentationAnchorDistributionCoreEndpoint D) :
    ∀ Ttxt : TextFor G.StringLanguage,
      ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
        ReachableSampleStringLanguage (Ttxt.prefixSample n) obs f =
          G.StringLanguage :=
  E.toExposingCoreFinalEndpoint.prefix_exact_eventually

/-- Reachable Gold identification. -/
theorem identifies_from_positive_text
    (E : TrimmedPresentationAnchorDistributionCoreEndpoint D) :
    ∀ Ttxt : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        Ttxt :=
  E.toExposingCoreFinalEndpoint.identifies_from_positive_text

/-- Pointwise eventual correctness on one positive text. -/
theorem eventually_correct_on_text
    (E : TrimmedPresentationAnchorDistributionCoreEndpoint D)
    (Ttxt : TextFor G.StringLanguage) :
    EventuallyCorrectOnText
      (reachableHypLanguage obs f)
      (reachableSampleLearner (α := α))
      Ttxt :=
  E.identifies_from_positive_text Ttxt

end TrimmedPresentationAnchorDistributionCoreEndpoint

end AnchorDistributionCoreEndpoint


section AnchorDistributionCoreEndpointFromSample

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}
variable {f : Nat}
variable {T : TrimmedOutputTypePresentation G obs}
variable {D : TrimmedPresentationPreCoreData T f}
variable {S : Finset (Word α)}

/-- Endpoint wrapper for the anchor-distribution route where start-word evidence
comes from a positive finite sample. -/
structure TrimmedPresentationAnchorDistributionCoreEndpointFromSample
    (D : TrimmedPresentationPreCoreData T f)
    (S : Finset (Word α)) where
  coreData : TrimmedPresentationAnchorDistributionCoreData D
  startSampleEvidence : TrimmedPresentationStartWordSampleEvidence D S
  splicingConstructor : NamedContextSplicingConstructor α
  fanout : G.FanoutAtMost f
  promise : FixedNamedTupleSubstitutable f obs G.StringLanguage

namespace TrimmedPresentationAnchorDistributionCoreEndpointFromSample

/-- Extract compact start-word evidence. -/
def startEvidence
    (E : TrimmedPresentationAnchorDistributionCoreEndpointFromSample D S) :
    TrimmedPresentationStartWordEvidence D :=
  E.startSampleEvidence.toStartWordEvidence

/-- Convert to the compact anchor-distribution endpoint. -/
def toAnchorDistributionCoreEndpoint
    (E : TrimmedPresentationAnchorDistributionCoreEndpointFromSample D S) :
    TrimmedPresentationAnchorDistributionCoreEndpoint D where
  coreData := E.coreData
  startEvidence := E.startEvidence
  splicingConstructor := E.splicingConstructor
  fanout := E.fanout
  promise := E.promise

/-- Convert to exposing-core final endpoint. -/
def toExposingCoreFinalEndpoint
    (E : TrimmedPresentationAnchorDistributionCoreEndpointFromSample D S) :
    TrimmedPresentationExposingCoreFinalEndpoint D :=
  E.toAnchorDistributionCoreEndpoint.toExposingCoreFinalEndpoint

/-- The finite sample produced by this endpoint. -/
noncomputable def sample
    (E : TrimmedPresentationAnchorDistributionCoreEndpointFromSample D S) :
    Finset (Word α) :=
  E.toAnchorDistributionCoreEndpoint.sample

/-- The finite sample is positive. -/
theorem sample_positive
    (E : TrimmedPresentationAnchorDistributionCoreEndpointFromSample D S) :
    (E.sample : Set (Word α)) ⊆ G.StringLanguage :=
  E.toAnchorDistributionCoreEndpoint.sample_positive

/-- The auxiliary sample supplies distinguished start-word positivity. -/
theorem startWord_positive
    (E : TrimmedPresentationAnchorDistributionCoreEndpointFromSample D S) :
    D.startWord ∈ G.StringLanguage :=
  E.startSampleEvidence.startWord_positive

/-- The finite sample contains all required witness words. -/
theorem contains_witnesses
    (E : TrimmedPresentationAnchorDistributionCoreEndpointFromSample D S) :
    TrimmedPresentationWitnessWordSet D ⊆
      (E.sample : Set (Word α)) :=
  E.toAnchorDistributionCoreEndpoint.contains_witnesses

/-- Convert directly to final reachable data. -/
noncomputable def toFinalReachableData
    (E : TrimmedPresentationAnchorDistributionCoreEndpointFromSample D S) :
    FinalReachableData G E.sample obs f :=
  E.toAnchorDistributionCoreEndpoint.toFinalReachableData

/-- The produced finite sample is a characteristic sample for the reachable
learner. -/
theorem characteristic_sample
    (E : TrimmedPresentationAnchorDistributionCoreEndpointFromSample D S) :
    CharacteristicSample
      (reachableHypLanguage obs f)
      (reachableSampleLearner (α := α))
      E.sample
      G.StringLanguage :=
  E.toAnchorDistributionCoreEndpoint.characteristic_sample

/-- Exact reconstruction for every positive finite superset of the produced
sample. -/
theorem exact_for_positive_superset
    (E : TrimmedPresentationAnchorDistributionCoreEndpointFromSample D S)
    {K : Finset (Word α)}
    (hEK : (E.sample : Set (Word α)) ⊆ (K : Set (Word α)))
    (hKpos : (K : Set (Word α)) ⊆ G.StringLanguage) :
    ReachableSampleStringLanguage K obs f = G.StringLanguage :=
  E.toAnchorDistributionCoreEndpoint.exact_for_positive_superset hEK hKpos

/-- Eventual prefix-exact reconstruction. -/
theorem prefix_exact_eventually
    (E : TrimmedPresentationAnchorDistributionCoreEndpointFromSample D S) :
    ∀ Ttxt : TextFor G.StringLanguage,
      ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
        ReachableSampleStringLanguage (Ttxt.prefixSample n) obs f =
          G.StringLanguage :=
  E.toAnchorDistributionCoreEndpoint.prefix_exact_eventually

/-- Reachable Gold identification. -/
theorem identifies_from_positive_text
    (E : TrimmedPresentationAnchorDistributionCoreEndpointFromSample D S) :
    ∀ Ttxt : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        Ttxt :=
  E.toAnchorDistributionCoreEndpoint.identifies_from_positive_text

end TrimmedPresentationAnchorDistributionCoreEndpointFromSample

end AnchorDistributionCoreEndpointFromSample


section AnchorCommonContextCoreEndpoint

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}
variable {f : Nat}
variable {T : TrimmedOutputTypePresentation G obs}

/-- Endpoint wrapper for the anchor common-context route with compact start-word
evidence. -/
structure TrimmedPresentationAnchorCommonContextCoreEndpoint
    (D : TrimmedPresentationPreCoreData T f) where
  coreData : TrimmedPresentationAnchorCommonContextCoreData D
  startEvidence : TrimmedPresentationStartWordEvidence D
  splicingConstructor : NamedContextSplicingConstructor α
  fanout : G.FanoutAtMost f
  promise : FixedNamedTupleSubstitutable f obs G.StringLanguage

namespace TrimmedPresentationAnchorCommonContextCoreEndpoint

variable {D : TrimmedPresentationPreCoreData T f}

/-- Convert to anchor-distribution core data. -/
def toAnchorDistributionCoreData
    (E : TrimmedPresentationAnchorCommonContextCoreEndpoint D) :
    TrimmedPresentationAnchorDistributionCoreData D :=
  E.coreData.toAnchorDistributionCoreData E.fanout E.promise

/-- Convert to anchor-distribution endpoint. -/
def toAnchorDistributionCoreEndpoint
    (E : TrimmedPresentationAnchorCommonContextCoreEndpoint D) :
    TrimmedPresentationAnchorDistributionCoreEndpoint D where
  coreData := E.toAnchorDistributionCoreData
  startEvidence := E.startEvidence
  splicingConstructor := E.splicingConstructor
  fanout := E.fanout
  promise := E.promise

/-- Convert to common-context final data. -/
def toAnchorCommonContextFinalData
    (E : TrimmedPresentationAnchorCommonContextCoreEndpoint D) :
    TrimmedPresentationAnchorCommonContextFinalData D where
  commonData := E.coreData
  startEvidence := E.startEvidence
  splicingConstructor := E.splicingConstructor
  fanout := E.fanout
  promise := E.promise

/-- Convert to common-context transport obligations. -/
def toCommonContextTransportObligations
    (E : TrimmedPresentationAnchorCommonContextCoreEndpoint D) :
    TrimmedPresentationCommonContextTransportObligations D where
  commonData := E.coreData
  startEvidence := E.startEvidence
  splicingConstructor := E.splicingConstructor
  fanout := E.fanout
  promise := E.promise

/-- Convert to exposing-transport obligations through the common-context route. -/
def toExposingTransportObligations
    (E : TrimmedPresentationAnchorCommonContextCoreEndpoint D) :
    TrimmedPresentationExposingTransportObligations D :=
  E.toCommonContextTransportObligations.toExposingTransportObligations

/-- Convert to exposing-core final endpoint. -/
def toExposingCoreFinalEndpoint
    (E : TrimmedPresentationAnchorCommonContextCoreEndpoint D) :
    TrimmedPresentationExposingCoreFinalEndpoint D :=
  E.toAnchorDistributionCoreEndpoint.toExposingCoreFinalEndpoint

/-- Convert to grammar-rule transport endpoint. -/
def toGrammarRuleTransportEndpoint
    (E : TrimmedPresentationAnchorCommonContextCoreEndpoint D) :
    TrimmedPresentationGrammarRuleTransportEndpoint D :=
  E.toAnchorDistributionCoreEndpoint.toGrammarRuleTransportEndpoint

/-- The finite sample produced by this endpoint. -/
noncomputable def sample
    (E : TrimmedPresentationAnchorCommonContextCoreEndpoint D) :
    Finset (Word α) :=
  E.toAnchorCommonContextFinalData.sample

/-- The finite sample is positive. -/
theorem sample_positive
    (E : TrimmedPresentationAnchorCommonContextCoreEndpoint D) :
    (E.sample : Set (Word α)) ⊆ G.StringLanguage :=
  E.toAnchorCommonContextFinalData.sample_positive

/-- The finite sample contains all required witness words. -/
theorem contains_witnesses
    (E : TrimmedPresentationAnchorCommonContextCoreEndpoint D) :
    TrimmedPresentationWitnessWordSet D ⊆
      (E.sample : Set (Word α)) :=
  E.toAnchorCommonContextFinalData.contains_witnesses

/-- Convert directly to final reachable data. -/
noncomputable def toFinalReachableData
    (E : TrimmedPresentationAnchorCommonContextCoreEndpoint D) :
    FinalReachableData G E.sample obs f :=
  E.toAnchorCommonContextFinalData.toFinalReachableData

/-- The finite sample is a characteristic sample for the reachable learner. -/
theorem characteristic_sample
    (E : TrimmedPresentationAnchorCommonContextCoreEndpoint D) :
    CharacteristicSample
      (reachableHypLanguage obs f)
      (reachableSampleLearner (α := α))
      E.sample
      G.StringLanguage :=
  E.toAnchorCommonContextFinalData.characteristic_sample

/-- Exact reconstruction for every positive finite superset of the produced
sample. -/
theorem exact_for_positive_superset
    (E : TrimmedPresentationAnchorCommonContextCoreEndpoint D)
    {K : Finset (Word α)}
    (hEK : (E.sample : Set (Word α)) ⊆ (K : Set (Word α)))
    (hKpos : (K : Set (Word α)) ⊆ G.StringLanguage) :
    ReachableSampleStringLanguage K obs f = G.StringLanguage :=
  E.toAnchorCommonContextFinalData.exact_for_positive_superset hEK hKpos

/-- Exact reconstruction at a positive-text prefix containing the produced
sample. -/
theorem exact_at_seen_prefix
    (E : TrimmedPresentationAnchorCommonContextCoreEndpoint D)
    (Ttxt : TextFor G.StringLanguage)
    {n : Nat}
    (hseen : (E.sample : Set (Word α)) ⊆
      (Ttxt.prefixSample n : Set (Word α))) :
    ReachableSampleStringLanguage (Ttxt.prefixSample n) obs f =
      G.StringLanguage :=
  E.toAnchorCommonContextFinalData.exact_at_seen_prefix Ttxt hseen

/-- Eventual prefix-exact reconstruction. -/
theorem prefix_exact_eventually
    (E : TrimmedPresentationAnchorCommonContextCoreEndpoint D) :
    ∀ Ttxt : TextFor G.StringLanguage,
      ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
        ReachableSampleStringLanguage (Ttxt.prefixSample n) obs f =
          G.StringLanguage :=
  E.toAnchorCommonContextFinalData.prefix_exact_eventually

/-- Reachable Gold identification. -/
theorem identifies_from_positive_text
    (E : TrimmedPresentationAnchorCommonContextCoreEndpoint D) :
    ∀ Ttxt : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        Ttxt :=
  E.toAnchorCommonContextFinalData.identifies_from_positive_text

/-- Pointwise eventual correctness on one positive text. -/
theorem eventually_correct_on_text
    (E : TrimmedPresentationAnchorCommonContextCoreEndpoint D)
    (Ttxt : TextFor G.StringLanguage) :
    EventuallyCorrectOnText
      (reachableHypLanguage obs f)
      (reachableSampleLearner (α := α))
      Ttxt :=
  E.identifies_from_positive_text Ttxt

end TrimmedPresentationAnchorCommonContextCoreEndpoint

end AnchorCommonContextCoreEndpoint


section AnchorCommonContextCoreEndpointFromSample

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}
variable {f : Nat}
variable {T : TrimmedOutputTypePresentation G obs}
variable {D : TrimmedPresentationPreCoreData T f}
variable {S : Finset (Word α)}

/-- Endpoint wrapper for the common-context route where start-word evidence
comes from a positive finite sample. -/
structure TrimmedPresentationAnchorCommonContextCoreEndpointFromSample
    (D : TrimmedPresentationPreCoreData T f)
    (S : Finset (Word α)) where
  coreData : TrimmedPresentationAnchorCommonContextCoreData D
  startSampleEvidence : TrimmedPresentationStartWordSampleEvidence D S
  splicingConstructor : NamedContextSplicingConstructor α
  fanout : G.FanoutAtMost f
  promise : FixedNamedTupleSubstitutable f obs G.StringLanguage

namespace TrimmedPresentationAnchorCommonContextCoreEndpointFromSample

/-- Extract compact start-word evidence. -/
def startEvidence
    (E : TrimmedPresentationAnchorCommonContextCoreEndpointFromSample D S) :
    TrimmedPresentationStartWordEvidence D :=
  E.startSampleEvidence.toStartWordEvidence

/-- Convert to compact common-context endpoint. -/
def toAnchorCommonContextCoreEndpoint
    (E : TrimmedPresentationAnchorCommonContextCoreEndpointFromSample D S) :
    TrimmedPresentationAnchorCommonContextCoreEndpoint D where
  coreData := E.coreData
  startEvidence := E.startEvidence
  splicingConstructor := E.splicingConstructor
  fanout := E.fanout
  promise := E.promise

/-- Convert to common-context final data. -/
def toAnchorCommonContextFinalData
    (E : TrimmedPresentationAnchorCommonContextCoreEndpointFromSample D S) :
    TrimmedPresentationAnchorCommonContextFinalData D :=
  E.toAnchorCommonContextCoreEndpoint.toAnchorCommonContextFinalData

/-- Convert to common-context obligations from sample. -/
def toCommonContextTransportObligationsFromSample
    (E : TrimmedPresentationAnchorCommonContextCoreEndpointFromSample D S) :
    TrimmedPresentationCommonContextTransportObligationsFromSample D S where
  commonData := E.coreData
  startSampleEvidence := E.startSampleEvidence
  splicingConstructor := E.splicingConstructor
  fanout := E.fanout
  promise := E.promise

/-- Convert to exposing-transport obligations from sample. -/
def toExposingTransportObligationsFromSample
    (E : TrimmedPresentationAnchorCommonContextCoreEndpointFromSample D S) :
    TrimmedPresentationExposingTransportObligationsFromSample D S :=
  E.toCommonContextTransportObligationsFromSample.toExposingTransportObligationsFromSample

/-- The finite sample produced by this endpoint. -/
noncomputable def sample
    (E : TrimmedPresentationAnchorCommonContextCoreEndpointFromSample D S) :
    Finset (Word α) :=
  E.toAnchorCommonContextCoreEndpoint.sample

/-- The finite sample is positive. -/
theorem sample_positive
    (E : TrimmedPresentationAnchorCommonContextCoreEndpointFromSample D S) :
    (E.sample : Set (Word α)) ⊆ G.StringLanguage :=
  E.toAnchorCommonContextCoreEndpoint.sample_positive

/-- The auxiliary sample supplies distinguished start-word positivity. -/
theorem startWord_positive
    (E : TrimmedPresentationAnchorCommonContextCoreEndpointFromSample D S) :
    D.startWord ∈ G.StringLanguage :=
  E.startSampleEvidence.startWord_positive

/-- The finite sample contains all required witness words. -/
theorem contains_witnesses
    (E : TrimmedPresentationAnchorCommonContextCoreEndpointFromSample D S) :
    TrimmedPresentationWitnessWordSet D ⊆
      (E.sample : Set (Word α)) :=
  E.toAnchorCommonContextCoreEndpoint.contains_witnesses

/-- Convert directly to final reachable data. -/
noncomputable def toFinalReachableData
    (E : TrimmedPresentationAnchorCommonContextCoreEndpointFromSample D S) :
    FinalReachableData G E.sample obs f :=
  E.toAnchorCommonContextCoreEndpoint.toFinalReachableData

/-- The produced finite sample is a characteristic sample for the reachable
learner. -/
theorem characteristic_sample
    (E : TrimmedPresentationAnchorCommonContextCoreEndpointFromSample D S) :
    CharacteristicSample
      (reachableHypLanguage obs f)
      (reachableSampleLearner (α := α))
      E.sample
      G.StringLanguage :=
  E.toAnchorCommonContextCoreEndpoint.characteristic_sample

/-- Exact reconstruction for every positive finite superset of the produced
sample. -/
theorem exact_for_positive_superset
    (E : TrimmedPresentationAnchorCommonContextCoreEndpointFromSample D S)
    {K : Finset (Word α)}
    (hEK : (E.sample : Set (Word α)) ⊆ (K : Set (Word α)))
    (hKpos : (K : Set (Word α)) ⊆ G.StringLanguage) :
    ReachableSampleStringLanguage K obs f = G.StringLanguage :=
  E.toAnchorCommonContextCoreEndpoint.exact_for_positive_superset hEK hKpos

/-- Eventual prefix-exact reconstruction. -/
theorem prefix_exact_eventually
    (E : TrimmedPresentationAnchorCommonContextCoreEndpointFromSample D S) :
    ∀ Ttxt : TextFor G.StringLanguage,
      ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
        ReachableSampleStringLanguage (Ttxt.prefixSample n) obs f =
          G.StringLanguage :=
  E.toAnchorCommonContextCoreEndpoint.prefix_exact_eventually

/-- Reachable Gold identification. -/
theorem identifies_from_positive_text
    (E : TrimmedPresentationAnchorCommonContextCoreEndpointFromSample D S) :
    ∀ Ttxt : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        Ttxt :=
  E.toAnchorCommonContextCoreEndpoint.identifies_from_positive_text

end TrimmedPresentationAnchorCommonContextCoreEndpointFromSample

end AnchorCommonContextCoreEndpointFromSample


section ConversionsFromAnchorEndpointsToExistingObligations

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}
variable {f : Nat}
variable {T : TrimmedOutputTypePresentation G obs}
variable {D : TrimmedPresentationPreCoreData T f}

namespace TrimmedPresentationAnchorCommonContextFinalData

/-- The existing common-context final data can be viewed as a compact
common-context endpoint. -/
def toAnchorCommonContextCoreEndpoint
    (F : TrimmedPresentationAnchorCommonContextFinalData D) :
    TrimmedPresentationAnchorCommonContextCoreEndpoint D where
  coreData := F.commonData
  startEvidence := F.startEvidence
  splicingConstructor := F.splicingConstructor
  fanout := F.fanout
  promise := F.promise

/-- The existing common-context final data can be viewed as an anchor-
distribution endpoint. -/
def toAnchorDistributionCoreEndpoint
    (F : TrimmedPresentationAnchorCommonContextFinalData D) :
    TrimmedPresentationAnchorDistributionCoreEndpoint D :=
  F.toAnchorCommonContextCoreEndpoint.toAnchorDistributionCoreEndpoint

end TrimmedPresentationAnchorCommonContextFinalData

namespace TrimmedPresentationCommonContextTransportObligations

/-- Common-context obligations can be viewed as a compact common-context
endpoint. -/
def toAnchorCommonContextCoreEndpoint
    (O : TrimmedPresentationCommonContextTransportObligations D) :
    TrimmedPresentationAnchorCommonContextCoreEndpoint D where
  coreData := O.commonData
  startEvidence := O.startEvidence
  splicingConstructor := O.splicingConstructor
  fanout := O.fanout
  promise := O.promise

/-- Common-context obligations can be viewed as an anchor-distribution endpoint. -/
def toAnchorDistributionCoreEndpoint
    (O : TrimmedPresentationCommonContextTransportObligations D) :
    TrimmedPresentationAnchorDistributionCoreEndpoint D :=
  O.toAnchorCommonContextCoreEndpoint.toAnchorDistributionCoreEndpoint

end TrimmedPresentationCommonContextTransportObligations

end ConversionsFromAnchorEndpointsToExistingObligations


section MainTheoremsFromAnchorEndpoints

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}
variable {f : Nat}
variable {T : TrimmedOutputTypePresentation G obs}
variable {D : TrimmedPresentationPreCoreData T f}
variable {S : Finset (Word α)}

/-- Stable top-level reachable identification theorem from anchor-distribution
core endpoint. -/
theorem trimmed_anchor_distribution_core_endpoint_reachable_identification
    (E : TrimmedPresentationAnchorDistributionCoreEndpoint D) :
    ∀ Ttxt : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        Ttxt :=
  E.identifies_from_positive_text

/-- Stable top-level prefix-exact theorem from anchor-distribution core
endpoint. -/
theorem trimmed_anchor_distribution_core_endpoint_prefix_exact
    (E : TrimmedPresentationAnchorDistributionCoreEndpoint D) :
    ∀ Ttxt : TextFor G.StringLanguage,
      ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
        ReachableSampleStringLanguage (Ttxt.prefixSample n) obs f =
          G.StringLanguage :=
  E.prefix_exact_eventually

/-- Stable top-level positive finite-superset exactness theorem from
anchor-distribution core endpoint. -/
theorem trimmed_anchor_distribution_core_endpoint_exact_for_positive_superset
    (E : TrimmedPresentationAnchorDistributionCoreEndpoint D)
    {K : Finset (Word α)}
    (hEK : (E.sample : Set (Word α)) ⊆ (K : Set (Word α)))
    (hKpos : (K : Set (Word α)) ⊆ G.StringLanguage) :
    ReachableSampleStringLanguage K obs f = G.StringLanguage :=
  E.exact_for_positive_superset hEK hKpos

/-- Stable top-level reachable identification theorem from anchor-distribution
endpoint whose start-word evidence comes from a positive finite sample. -/
theorem trimmed_anchor_distribution_sample_endpoint_reachable_identification
    (E : TrimmedPresentationAnchorDistributionCoreEndpointFromSample D S) :
    ∀ Ttxt : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        Ttxt :=
  E.identifies_from_positive_text

/-- Stable top-level prefix-exact theorem from anchor-distribution endpoint
whose start-word evidence comes from a positive finite sample. -/
theorem trimmed_anchor_distribution_sample_endpoint_prefix_exact
    (E : TrimmedPresentationAnchorDistributionCoreEndpointFromSample D S) :
    ∀ Ttxt : TextFor G.StringLanguage,
      ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
        ReachableSampleStringLanguage (Ttxt.prefixSample n) obs f =
          G.StringLanguage :=
  E.prefix_exact_eventually

/-- Stable top-level reachable identification theorem from anchor common-context
core endpoint. -/
theorem trimmed_anchor_common_context_core_endpoint_reachable_identification
    (E : TrimmedPresentationAnchorCommonContextCoreEndpoint D) :
    ∀ Ttxt : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        Ttxt :=
  E.identifies_from_positive_text

/-- Stable top-level prefix-exact theorem from anchor common-context core
endpoint. -/
theorem trimmed_anchor_common_context_core_endpoint_prefix_exact
    (E : TrimmedPresentationAnchorCommonContextCoreEndpoint D) :
    ∀ Ttxt : TextFor G.StringLanguage,
      ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
        ReachableSampleStringLanguage (Ttxt.prefixSample n) obs f =
          G.StringLanguage :=
  E.prefix_exact_eventually

/-- Stable top-level positive finite-superset exactness theorem from anchor
common-context core endpoint. -/
theorem trimmed_anchor_common_context_core_endpoint_exact_for_positive_superset
    (E : TrimmedPresentationAnchorCommonContextCoreEndpoint D)
    {K : Finset (Word α)}
    (hEK : (E.sample : Set (Word α)) ⊆ (K : Set (Word α)))
    (hKpos : (K : Set (Word α)) ⊆ G.StringLanguage) :
    ReachableSampleStringLanguage K obs f = G.StringLanguage :=
  E.exact_for_positive_superset hEK hKpos

/-- Stable top-level reachable identification theorem from anchor common-context
endpoint whose start-word evidence comes from a positive finite sample. -/
theorem trimmed_anchor_common_context_sample_endpoint_reachable_identification
    (E : TrimmedPresentationAnchorCommonContextCoreEndpointFromSample D S) :
    ∀ Ttxt : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        Ttxt :=
  E.identifies_from_positive_text

/-- Stable top-level prefix-exact theorem from anchor common-context endpoint
whose start-word evidence comes from a positive finite sample. -/
theorem trimmed_anchor_common_context_sample_endpoint_prefix_exact
    (E : TrimmedPresentationAnchorCommonContextCoreEndpointFromSample D S) :
    ∀ Ttxt : TextFor G.StringLanguage,
      ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
        ReachableSampleStringLanguage (Ttxt.prefixSample n) obs f =
          G.StringLanguage :=
  E.prefix_exact_eventually

end MainTheoremsFromAnchorEndpoints

end MCFG
