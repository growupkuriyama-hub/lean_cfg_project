/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG2.CharacteristicSampleTransportObligations

/-!
# CharacteristicSampleTransportObligationsFromSample.lean

Seventy-second clean Lean experiment for the fixed-observation MCFG project.

`CharacteristicSampleTransportObligations.lean` packaged the two clean
theorem-facing semantic entrances:

* exposing-context transport obligations;
* common-context transport obligations.

Both packages used compact start-word evidence

```lean
TrimmedPresentationStartWordEvidence D
```

as a field.

This file provides variants where the start-word evidence is extracted from any
positive finite sample containing the distinguished start word.  This is often
closer to the intended `CS(G̃₀)` workflow, because the characteristic sample
itself will contain `D.startWord`.

No new mathematical principle is introduced here.  The file only connects the
start-word-from-sample bridge to the final transport-obligation packages.

No theorem here uses `sorry`.
-/

namespace MCFG

universe u v w

section ExposingTransportObligationsFromSample

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}
variable {f : Nat}
variable {T : TrimmedOutputTypePresentation G obs}

/-- Exposing-context transport obligations where the start-word evidence is
obtained from an auxiliary positive finite sample. -/
structure TrimmedPresentationExposingTransportObligationsFromSample
    (D : TrimmedPresentationPreCoreData T f)
    (S : Finset (Word α)) where
  baseNonterminals : Finset N
  base_covers :
    ∀ A : N, A ∈ baseNonterminals

  arities : TrimmedPresentationRuleAritySelectors D
  exposingTransport : TrimmedPresentationExposingContextTransport D
  startSampleEvidence : TrimmedPresentationStartWordSampleEvidence D S

  splicingConstructor : NamedContextSplicingConstructor α
  fanout : G.FanoutAtMost f
  promise : FixedNamedTupleSubstitutable f obs G.StringLanguage

namespace TrimmedPresentationExposingTransportObligationsFromSample

variable {D : TrimmedPresentationPreCoreData T f}
variable {S : Finset (Word α)}

/-- Extract compact start-word evidence from the auxiliary positive sample. -/
def startEvidence
    (O : TrimmedPresentationExposingTransportObligationsFromSample D S) :
    TrimmedPresentationStartWordEvidence D :=
  O.startSampleEvidence.toStartWordEvidence

/-- Convert to the compact exposing-transport obligation package. -/
def toExposingTransportObligations
    (O : TrimmedPresentationExposingTransportObligationsFromSample D S) :
    TrimmedPresentationExposingTransportObligations D where
  baseNonterminals := O.baseNonterminals
  base_covers := O.base_covers
  arities := O.arities
  exposingTransport := O.exposingTransport
  startEvidence := O.startEvidence
  splicingConstructor := O.splicingConstructor
  fanout := O.fanout
  promise := O.promise

/-- Forget the global theorem assumptions and keep only the core exposing
transport data. -/
def toExposingTransportCoreData
    (O : TrimmedPresentationExposingTransportObligationsFromSample D S) :
    TrimmedPresentationExposingTransportCoreData D :=
  O.toExposingTransportObligations.toExposingTransportCoreData

/-- Recover the exposing-transport data package. -/
def toExposingTransportData
    (O : TrimmedPresentationExposingTransportObligationsFromSample D S) :
    TrimmedPresentationExposingTransportData D :=
  O.toExposingTransportObligations.toExposingTransportData

/-- Convert to the separated exposing-core final data. -/
def toExposingCoreFinalData
    (O : TrimmedPresentationExposingTransportObligationsFromSample D S) :
    TrimmedPresentationExposingCoreFinalData D :=
  O.toExposingTransportObligations.toExposingCoreFinalData

/-- The finite sample produced by the resulting exposing-transport obligation
package. -/
noncomputable def sample
    (O : TrimmedPresentationExposingTransportObligationsFromSample D S) :
    Finset (Word α) :=
  O.toExposingTransportObligations.sample

/-- The produced finite sample is positive. -/
theorem sample_positive
    (O : TrimmedPresentationExposingTransportObligationsFromSample D S) :
    (O.sample : Set (Word α)) ⊆ G.StringLanguage :=
  O.toExposingTransportObligations.sample_positive

/-- The auxiliary sample supplies positivity of the distinguished start word. -/
theorem startWord_positive
    (O : TrimmedPresentationExposingTransportObligationsFromSample D S) :
    D.startWord ∈ G.StringLanguage :=
  O.startSampleEvidence.startWord_positive

/-- The produced finite sample contains all required witness words. -/
theorem contains_witnesses
    (O : TrimmedPresentationExposingTransportObligationsFromSample D S) :
    TrimmedPresentationWitnessWordSet D ⊆
      (O.sample : Set (Word α)) :=
  O.toExposingTransportObligations.contains_witnesses

/-- Convert to rule-witness transport. -/
def toRuleWitnessTransport
    (O : TrimmedPresentationExposingTransportObligationsFromSample D S) :
    TrimmedPresentationRuleWitnessTransport D O.arities :=
  O.toExposingTransportObligations.toRuleWitnessTransport

/-- Convert to grammar-rule transport data. -/
def toGrammarRuleTransportData
    (O : TrimmedPresentationExposingTransportObligationsFromSample D S) :
    TrimmedPresentationGrammarRuleTransportData D :=
  O.toExposingTransportObligations.toGrammarRuleTransportData

/-- Convert directly to final reachable data. -/
noncomputable def toFinalReachableData
    (O : TrimmedPresentationExposingTransportObligationsFromSample D S) :
    FinalReachableData G O.sample obs f :=
  O.toExposingTransportObligations.toFinalReachableData

/-- The produced finite sample is a characteristic sample for the reachable
learner. -/
theorem characteristic_sample
    (O : TrimmedPresentationExposingTransportObligationsFromSample D S) :
    CharacteristicSample
      (reachableHypLanguage obs f)
      (reachableSampleLearner (α := α))
      O.sample
      G.StringLanguage :=
  O.toExposingTransportObligations.characteristic_sample

/-- Exact reconstruction for every positive finite superset of the produced
sample. -/
theorem exact_for_positive_superset
    (O : TrimmedPresentationExposingTransportObligationsFromSample D S)
    {K : Finset (Word α)}
    (hOK : (O.sample : Set (Word α)) ⊆ (K : Set (Word α)))
    (hKpos : (K : Set (Word α)) ⊆ G.StringLanguage) :
    ReachableSampleStringLanguage K obs f = G.StringLanguage :=
  O.toExposingTransportObligations.exact_for_positive_superset hOK hKpos

/-- Exact reconstruction at a positive-text prefix containing the produced
sample. -/
theorem exact_at_seen_prefix
    (O : TrimmedPresentationExposingTransportObligationsFromSample D S)
    (Ttxt : TextFor G.StringLanguage)
    {n : Nat}
    (hseen : (O.sample : Set (Word α)) ⊆
      (Ttxt.prefixSample n : Set (Word α))) :
    ReachableSampleStringLanguage (Ttxt.prefixSample n) obs f =
      G.StringLanguage :=
  O.toExposingTransportObligations.exact_at_seen_prefix Ttxt hseen

/-- Eventual prefix-exact reconstruction from exposing-transport obligations
whose start-word evidence is extracted from a positive sample. -/
theorem prefix_exact_eventually
    (O : TrimmedPresentationExposingTransportObligationsFromSample D S) :
    ∀ Ttxt : TextFor G.StringLanguage,
      ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
        ReachableSampleStringLanguage (Ttxt.prefixSample n) obs f =
          G.StringLanguage :=
  O.toExposingTransportObligations.prefix_exact_eventually

/-- Reachable Gold identification from exposing-transport obligations whose
start-word evidence is extracted from a positive sample. -/
theorem identifies_from_positive_text
    (O : TrimmedPresentationExposingTransportObligationsFromSample D S) :
    ∀ Ttxt : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        Ttxt :=
  O.toExposingTransportObligations.identifies_from_positive_text

/-- Pointwise eventual correctness on one positive text. -/
theorem eventually_correct_on_text
    (O : TrimmedPresentationExposingTransportObligationsFromSample D S)
    (Ttxt : TextFor G.StringLanguage) :
    EventuallyCorrectOnText
      (reachableHypLanguage obs f)
      (reachableSampleLearner (α := α))
      Ttxt :=
  O.identifies_from_positive_text Ttxt

end TrimmedPresentationExposingTransportObligationsFromSample

end ExposingTransportObligationsFromSample


section CommonContextTransportObligationsFromSample

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}
variable {f : Nat}
variable {T : TrimmedOutputTypePresentation G obs}

/-- Common-context transport obligations where the start-word evidence is
obtained from an auxiliary positive finite sample. -/
structure TrimmedPresentationCommonContextTransportObligationsFromSample
    (D : TrimmedPresentationPreCoreData T f)
    (S : Finset (Word α)) where
  commonData : TrimmedPresentationAnchorCommonContextCoreData D
  startSampleEvidence : TrimmedPresentationStartWordSampleEvidence D S
  splicingConstructor : NamedContextSplicingConstructor α
  fanout : G.FanoutAtMost f
  promise : FixedNamedTupleSubstitutable f obs G.StringLanguage

namespace TrimmedPresentationCommonContextTransportObligationsFromSample

variable {D : TrimmedPresentationPreCoreData T f}
variable {S : Finset (Word α)}

/-- Extract compact start-word evidence from the auxiliary positive sample. -/
def startEvidence
    (O : TrimmedPresentationCommonContextTransportObligationsFromSample D S) :
    TrimmedPresentationStartWordEvidence D :=
  O.startSampleEvidence.toStartWordEvidence

/-- Convert to the compact common-context obligation package. -/
def toCommonContextTransportObligations
    (O : TrimmedPresentationCommonContextTransportObligationsFromSample D S) :
    TrimmedPresentationCommonContextTransportObligations D where
  commonData := O.commonData
  startEvidence := O.startEvidence
  splicingConstructor := O.splicingConstructor
  fanout := O.fanout
  promise := O.promise

/-- Convert to the common-context final data package. -/
def toAnchorCommonContextFinalData
    (O : TrimmedPresentationCommonContextTransportObligationsFromSample D S) :
    TrimmedPresentationAnchorCommonContextFinalData D :=
  O.toCommonContextTransportObligations.toAnchorCommonContextFinalData

/-- Convert to anchor-distributional core data. -/
def toAnchorDistributionCoreData
    (O : TrimmedPresentationCommonContextTransportObligationsFromSample D S) :
    TrimmedPresentationAnchorDistributionCoreData D :=
  O.toCommonContextTransportObligations.toAnchorDistributionCoreData

/-- Convert to exposing-transport core data. -/
def toExposingTransportCoreData
    (O : TrimmedPresentationCommonContextTransportObligationsFromSample D S) :
    TrimmedPresentationExposingTransportCoreData D :=
  O.toCommonContextTransportObligations.toExposingTransportCoreData

/-- Convert common-context-from-sample obligations to exposing-transport
obligations. -/
def toExposingTransportObligations
    (O : TrimmedPresentationCommonContextTransportObligationsFromSample D S) :
    TrimmedPresentationExposingTransportObligations D :=
  O.toCommonContextTransportObligations.toExposingTransportObligations

/-- Convert common-context-from-sample obligations to exposing-transport
obligations from sample. -/
def toExposingTransportObligationsFromSample
    (O : TrimmedPresentationCommonContextTransportObligationsFromSample D S) :
    TrimmedPresentationExposingTransportObligationsFromSample D S where
  baseNonterminals := O.toExposingTransportCoreData.baseNonterminals
  base_covers := O.toExposingTransportCoreData.base_covers
  arities := O.toExposingTransportCoreData.arities
  exposingTransport := O.toExposingTransportCoreData.exposingTransport
  startSampleEvidence := O.startSampleEvidence
  splicingConstructor := O.splicingConstructor
  fanout := O.fanout
  promise := O.promise

/-- The finite sample produced by the common-context-from-sample obligation
package. -/
noncomputable def sample
    (O : TrimmedPresentationCommonContextTransportObligationsFromSample D S) :
    Finset (Word α) :=
  O.toCommonContextTransportObligations.sample

/-- The produced finite sample is positive. -/
theorem sample_positive
    (O : TrimmedPresentationCommonContextTransportObligationsFromSample D S) :
    (O.sample : Set (Word α)) ⊆ G.StringLanguage :=
  O.toCommonContextTransportObligations.sample_positive

/-- The auxiliary sample supplies positivity of the distinguished start word. -/
theorem startWord_positive
    (O : TrimmedPresentationCommonContextTransportObligationsFromSample D S) :
    D.startWord ∈ G.StringLanguage :=
  O.startSampleEvidence.startWord_positive

/-- The produced finite sample contains all required witness words. -/
theorem contains_witnesses
    (O : TrimmedPresentationCommonContextTransportObligationsFromSample D S) :
    TrimmedPresentationWitnessWordSet D ⊆
      (O.sample : Set (Word α)) :=
  O.toCommonContextTransportObligations.contains_witnesses

/-- Convert to rule-witness transport. -/
def toRuleWitnessTransport
    (O : TrimmedPresentationCommonContextTransportObligationsFromSample D S) :
    TrimmedPresentationRuleWitnessTransport D O.commonData.arities :=
  O.toCommonContextTransportObligations.toRuleWitnessTransport

/-- Convert to grammar-rule transport data. -/
def toGrammarRuleTransportData
    (O : TrimmedPresentationCommonContextTransportObligationsFromSample D S) :
    TrimmedPresentationGrammarRuleTransportData D :=
  O.toCommonContextTransportObligations.toGrammarRuleTransportData

/-- Convert directly to final reachable data. -/
noncomputable def toFinalReachableData
    (O : TrimmedPresentationCommonContextTransportObligationsFromSample D S) :
    FinalReachableData G O.sample obs f :=
  O.toCommonContextTransportObligations.toFinalReachableData

/-- The produced finite sample is a characteristic sample for the reachable
learner. -/
theorem characteristic_sample
    (O : TrimmedPresentationCommonContextTransportObligationsFromSample D S) :
    CharacteristicSample
      (reachableHypLanguage obs f)
      (reachableSampleLearner (α := α))
      O.sample
      G.StringLanguage :=
  O.toCommonContextTransportObligations.characteristic_sample

/-- Exact reconstruction for every positive finite superset of the produced
sample. -/
theorem exact_for_positive_superset
    (O : TrimmedPresentationCommonContextTransportObligationsFromSample D S)
    {K : Finset (Word α)}
    (hOK : (O.sample : Set (Word α)) ⊆ (K : Set (Word α)))
    (hKpos : (K : Set (Word α)) ⊆ G.StringLanguage) :
    ReachableSampleStringLanguage K obs f = G.StringLanguage :=
  O.toCommonContextTransportObligations.exact_for_positive_superset hOK hKpos

/-- Exact reconstruction at a positive-text prefix containing the produced
sample. -/
theorem exact_at_seen_prefix
    (O : TrimmedPresentationCommonContextTransportObligationsFromSample D S)
    (Ttxt : TextFor G.StringLanguage)
    {n : Nat}
    (hseen : (O.sample : Set (Word α)) ⊆
      (Ttxt.prefixSample n : Set (Word α))) :
    ReachableSampleStringLanguage (Ttxt.prefixSample n) obs f =
      G.StringLanguage :=
  O.toCommonContextTransportObligations.exact_at_seen_prefix Ttxt hseen

/-- Eventual prefix-exact reconstruction from common-context obligations whose
start-word evidence is extracted from a positive sample. -/
theorem prefix_exact_eventually
    (O : TrimmedPresentationCommonContextTransportObligationsFromSample D S) :
    ∀ Ttxt : TextFor G.StringLanguage,
      ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
        ReachableSampleStringLanguage (Ttxt.prefixSample n) obs f =
          G.StringLanguage :=
  O.toCommonContextTransportObligations.prefix_exact_eventually

/-- Reachable Gold identification from common-context obligations whose
start-word evidence is extracted from a positive sample. -/
theorem identifies_from_positive_text
    (O : TrimmedPresentationCommonContextTransportObligationsFromSample D S) :
    ∀ Ttxt : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        Ttxt :=
  O.toCommonContextTransportObligations.identifies_from_positive_text

/-- Pointwise eventual correctness on one positive text. -/
theorem eventually_correct_on_text
    (O : TrimmedPresentationCommonContextTransportObligationsFromSample D S)
    (Ttxt : TextFor G.StringLanguage) :
    EventuallyCorrectOnText
      (reachableHypLanguage obs f)
      (reachableSampleLearner (α := α))
      Ttxt :=
  O.identifies_from_positive_text Ttxt

end TrimmedPresentationCommonContextTransportObligationsFromSample

end CommonContextTransportObligationsFromSample


section MainTheoremsFromTransportObligationsFromSample

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}
variable {f : Nat}
variable {T : TrimmedOutputTypePresentation G obs}
variable {D : TrimmedPresentationPreCoreData T f}
variable {S : Finset (Word α)}

/-- Stable top-level reachable identification theorem from exposing-transport
obligations whose start-word evidence comes from a positive finite sample. -/
theorem trimmed_exposing_transport_sample_obligations_reachable_identification
    (O : TrimmedPresentationExposingTransportObligationsFromSample D S) :
    ∀ Ttxt : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        Ttxt :=
  O.identifies_from_positive_text

/-- Stable top-level prefix-exact theorem from exposing-transport obligations
whose start-word evidence comes from a positive finite sample. -/
theorem trimmed_exposing_transport_sample_obligations_reachable_prefix_exact
    (O : TrimmedPresentationExposingTransportObligationsFromSample D S) :
    ∀ Ttxt : TextFor G.StringLanguage,
      ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
        ReachableSampleStringLanguage (Ttxt.prefixSample n) obs f =
          G.StringLanguage :=
  O.prefix_exact_eventually

/-- Stable top-level finite-superset exactness theorem from exposing-transport
obligations whose start-word evidence comes from a positive finite sample. -/
theorem trimmed_exposing_transport_sample_obligations_exact_for_positive_superset
    (O : TrimmedPresentationExposingTransportObligationsFromSample D S)
    {K : Finset (Word α)}
    (hOK : (O.sample : Set (Word α)) ⊆ (K : Set (Word α)))
    (hKpos : (K : Set (Word α)) ⊆ G.StringLanguage) :
    ReachableSampleStringLanguage K obs f = G.StringLanguage :=
  O.exact_for_positive_superset hOK hKpos

/-- Stable top-level reachable identification theorem from common-context
obligations whose start-word evidence comes from a positive finite sample. -/
theorem trimmed_common_context_sample_obligations_reachable_identification
    (O : TrimmedPresentationCommonContextTransportObligationsFromSample D S) :
    ∀ Ttxt : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        Ttxt :=
  O.identifies_from_positive_text

/-- Stable top-level prefix-exact theorem from common-context obligations whose
start-word evidence comes from a positive finite sample. -/
theorem trimmed_common_context_sample_obligations_reachable_prefix_exact
    (O : TrimmedPresentationCommonContextTransportObligationsFromSample D S) :
    ∀ Ttxt : TextFor G.StringLanguage,
      ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
        ReachableSampleStringLanguage (Ttxt.prefixSample n) obs f =
          G.StringLanguage :=
  O.prefix_exact_eventually

/-- Stable top-level finite-superset exactness theorem from common-context
obligations whose start-word evidence comes from a positive finite sample. -/
theorem trimmed_common_context_sample_obligations_exact_for_positive_superset
    (O : TrimmedPresentationCommonContextTransportObligationsFromSample D S)
    {K : Finset (Word α)}
    (hOK : (O.sample : Set (Word α)) ⊆ (K : Set (Word α)))
    (hKpos : (K : Set (Word α)) ⊆ G.StringLanguage) :
    ReachableSampleStringLanguage K obs f = G.StringLanguage :=
  O.exact_for_positive_superset hOK hKpos

end MainTheoremsFromTransportObligationsFromSample

end MCFG
