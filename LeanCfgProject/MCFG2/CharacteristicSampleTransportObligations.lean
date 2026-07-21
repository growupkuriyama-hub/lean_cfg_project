/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG.CharacteristicSampleAnchorCommonContextFinal

/-!
# CharacteristicSampleTransportObligations.lean

Seventy-first clean Lean experiment for the fixed-observation MCFG project.

The CI #558 chain isolated the remaining semantic work into several transport
interfaces.  This file collects the two most useful theorem-facing packages:

* an exposing-context-transport obligation package;
* a common-context-transport obligation package.

Both packages store exactly the data needed to enter the already verified final
routes:

```text
transport obligation
+
start-word evidence
+
NamedContextSplicingConstructor
+
fanout
+
fixed-observation substitutability
⇒ reachable identification / prefix exactness.
```

No new semantic principle is introduced here.  This is a naming and interface
file whose purpose is to make the remaining proof obligations explicit and
compact.

No theorem here uses `sorry`.
-/

namespace MCFG

universe u v w

section ExposingTransportObligations

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}
variable {f : Nat}
variable {T : TrimmedOutputTypePresentation G obs}

/-- The compact theorem-facing obligation package for the exposing-context
transport route.

This is the cleanest current statement of the remaining semantic target:

* finite cover of base nonterminals;
* arity selectors for terminal/start witnesses;
* exposing-context transport;
* start-word evidence;
* named-context splicing;
* fanout and fixed-observation substitutability.
-/
structure TrimmedPresentationExposingTransportObligations
    (D : TrimmedPresentationPreCoreData T f) where
  baseNonterminals : Finset N
  base_covers :
    ∀ A : N, A ∈ baseNonterminals

  arities : TrimmedPresentationRuleAritySelectors D
  exposingTransport : TrimmedPresentationExposingContextTransport D
  startEvidence : TrimmedPresentationStartWordEvidence D

  splicingConstructor : NamedContextSplicingConstructor α
  fanout : G.FanoutAtMost f
  promise : FixedNamedTupleSubstitutable f obs G.StringLanguage

namespace TrimmedPresentationExposingTransportObligations

variable {D : TrimmedPresentationPreCoreData T f}

/-- Forget the global theorem assumptions and keep only the core exposing
transport data. -/
def toExposingTransportCoreData
    (O : TrimmedPresentationExposingTransportObligations D) :
    TrimmedPresentationExposingTransportCoreData D where
  baseNonterminals := O.baseNonterminals
  base_covers := O.base_covers
  arities := O.arities
  exposingTransport := O.exposingTransport

/-- Recover the exposing-transport data package with start-word evidence. -/
def toExposingTransportData
    (O : TrimmedPresentationExposingTransportObligations D) :
    TrimmedPresentationExposingTransportData D :=
  O.toExposingTransportCoreData.withStartWord O.startEvidence

/-- Convert to the separated exposing-core final data. -/
def toExposingCoreFinalData
    (O : TrimmedPresentationExposingTransportObligations D) :
    TrimmedPresentationExposingCoreFinalData D where
  coreData := O.toExposingTransportCoreData
  startEvidence := O.startEvidence
  splicingConstructor := O.splicingConstructor
  fanout := O.fanout
  promise := O.promise

/-- The finite sample produced by the exposing-transport obligation package. -/
def sample
    (O : TrimmedPresentationExposingTransportObligations D) :
    Finset (Word α) :=
  O.toExposingCoreFinalData.sample

/-- The produced finite sample is positive. -/
theorem sample_positive
    (O : TrimmedPresentationExposingTransportObligations D) :
    (O.sample : Set (Word α)) ⊆ G.StringLanguage :=
  O.toExposingCoreFinalData.sample_positive

/-- The produced finite sample contains all required witness words. -/
theorem contains_witnesses
    (O : TrimmedPresentationExposingTransportObligations D) :
    TrimmedPresentationWitnessWordSet D ⊆
      (O.sample : Set (Word α)) :=
  O.toExposingCoreFinalData.contains_witnesses

/-- Convert to rule-witness transport. -/
def toRuleWitnessTransport
    (O : TrimmedPresentationExposingTransportObligations D) :
    TrimmedPresentationRuleWitnessTransport D O.arities :=
  O.toExposingTransportCoreData.toRuleWitnessTransport O.startEvidence

/-- Convert to grammar-rule transport data. -/
def toGrammarRuleTransportData
    (O : TrimmedPresentationExposingTransportObligations D) :
    TrimmedPresentationGrammarRuleTransportData D :=
  O.toExposingTransportCoreData.toGrammarRuleTransportData O.startEvidence

/-- Convert directly to final reachable data. -/
def toFinalReachableData
    (O : TrimmedPresentationExposingTransportObligations D) :
    FinalReachableData G O.sample obs f :=
  O.toExposingCoreFinalData.toFinalReachableData

/-- The produced finite sample is a characteristic sample for the reachable
learner. -/
theorem characteristic_sample
    (O : TrimmedPresentationExposingTransportObligations D) :
    CharacteristicSample
      (reachableHypLanguage obs f)
      (reachableSampleLearner (α := α))
      O.sample
      G.StringLanguage :=
  O.toExposingCoreFinalData.characteristic_sample

/-- Exact reconstruction for every positive finite superset of the produced
sample. -/
theorem exact_for_positive_superset
    (O : TrimmedPresentationExposingTransportObligations D)
    {K : Finset (Word α)}
    (hOK : (O.sample : Set (Word α)) ⊆ (K : Set (Word α)))
    (hKpos : (K : Set (Word α)) ⊆ G.StringLanguage) :
    ReachableSampleStringLanguage K obs f = G.StringLanguage :=
  O.toExposingCoreFinalData.exact_for_positive_superset hOK hKpos

/-- Exact reconstruction at a positive-text prefix containing the produced
sample. -/
theorem exact_at_seen_prefix
    (O : TrimmedPresentationExposingTransportObligations D)
    (Ttxt : TextFor G.StringLanguage)
    {n : Nat}
    (hseen : (O.sample : Set (Word α)) ⊆
      (Ttxt.prefixSample n : Set (Word α))) :
    ReachableSampleStringLanguage (Ttxt.prefixSample n) obs f =
      G.StringLanguage :=
  O.toExposingCoreFinalData.exact_at_seen_prefix Ttxt hseen

/-- Eventual prefix-exact reconstruction from exposing-transport obligations. -/
theorem prefix_exact_eventually
    (O : TrimmedPresentationExposingTransportObligations D) :
    ∀ Ttxt : TextFor G.StringLanguage,
      ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
        ReachableSampleStringLanguage (Ttxt.prefixSample n) obs f =
          G.StringLanguage :=
  O.toExposingCoreFinalData.prefix_exact_eventually

/-- Reachable Gold identification from exposing-transport obligations. -/
theorem identifies_from_positive_text
    (O : TrimmedPresentationExposingTransportObligations D) :
    ∀ Ttxt : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        Ttxt :=
  O.toExposingCoreFinalData.identifies_from_positive_text

/-- Pointwise eventual correctness on one positive text. -/
theorem eventually_correct_on_text
    (O : TrimmedPresentationExposingTransportObligations D)
    (Ttxt : TextFor G.StringLanguage) :
    EventuallyCorrectOnText
      (reachableHypLanguage obs f)
      (reachableSampleLearner (α := α))
      Ttxt :=
  O.identifies_from_positive_text Ttxt

end TrimmedPresentationExposingTransportObligations

end ExposingTransportObligations


section CommonContextTransportObligations

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}
variable {f : Nat}
variable {T : TrimmedOutputTypePresentation G obs}

/-- The compact theorem-facing obligation package for the common-context route.

This is often the most convenient semantic target:

```text
for every base nonterminal A and same-type tuple x,
find one named context accepting both D.anchor A and x.
```

Under fanout and fixed-observation substitutability, this produces anchor
distributional transport and hence exposing-context transport.
-/
structure TrimmedPresentationCommonContextTransportObligations
    (D : TrimmedPresentationPreCoreData T f) where
  commonData : TrimmedPresentationAnchorCommonContextCoreData D
  startEvidence : TrimmedPresentationStartWordEvidence D
  splicingConstructor : NamedContextSplicingConstructor α
  fanout : G.FanoutAtMost f
  promise : FixedNamedTupleSubstitutable f obs G.StringLanguage

namespace TrimmedPresentationCommonContextTransportObligations

variable {D : TrimmedPresentationPreCoreData T f}

/-- Convert to the common-context final data package. -/
def toAnchorCommonContextFinalData
    (O : TrimmedPresentationCommonContextTransportObligations D) :
    TrimmedPresentationAnchorCommonContextFinalData D where
  commonData := O.commonData
  startEvidence := O.startEvidence
  splicingConstructor := O.splicingConstructor
  fanout := O.fanout
  promise := O.promise

/-- Convert to anchor-distributional core data. -/
def toAnchorDistributionCoreData
    (O : TrimmedPresentationCommonContextTransportObligations D) :
    TrimmedPresentationAnchorDistributionCoreData D :=
  O.toAnchorCommonContextFinalData.toAnchorDistributionCoreData

/-- Convert to exposing-transport core data. -/
def toExposingTransportCoreData
    (O : TrimmedPresentationCommonContextTransportObligations D) :
    TrimmedPresentationExposingTransportCoreData D :=
  O.toAnchorCommonContextFinalData.toExposingTransportCoreData

/-- Convert common-context obligations to exposing-transport obligations. -/
def toExposingTransportObligations
    (O : TrimmedPresentationCommonContextTransportObligations D) :
    TrimmedPresentationExposingTransportObligations D where
  baseNonterminals := O.toExposingTransportCoreData.baseNonterminals
  base_covers := O.toExposingTransportCoreData.base_covers
  arities := O.toExposingTransportCoreData.arities
  exposingTransport := O.toExposingTransportCoreData.exposingTransport
  startEvidence := O.startEvidence
  splicingConstructor := O.splicingConstructor
  fanout := O.fanout
  promise := O.promise

/-- The finite sample produced by the common-context obligation package. -/
def sample
    (O : TrimmedPresentationCommonContextTransportObligations D) :
    Finset (Word α) :=
  O.toAnchorCommonContextFinalData.sample

/-- The produced finite sample is positive. -/
theorem sample_positive
    (O : TrimmedPresentationCommonContextTransportObligations D) :
    (O.sample : Set (Word α)) ⊆ G.StringLanguage :=
  O.toAnchorCommonContextFinalData.sample_positive

/-- The produced finite sample contains all required witness words. -/
theorem contains_witnesses
    (O : TrimmedPresentationCommonContextTransportObligations D) :
    TrimmedPresentationWitnessWordSet D ⊆
      (O.sample : Set (Word α)) :=
  O.toAnchorCommonContextFinalData.contains_witnesses

/-- Convert to rule-witness transport. -/
def toRuleWitnessTransport
    (O : TrimmedPresentationCommonContextTransportObligations D) :
    TrimmedPresentationRuleWitnessTransport D O.commonData.arities :=
  O.toAnchorCommonContextFinalData.toRuleWitnessTransport

/-- Convert to grammar-rule transport data. -/
def toGrammarRuleTransportData
    (O : TrimmedPresentationCommonContextTransportObligations D) :
    TrimmedPresentationGrammarRuleTransportData D :=
  O.toAnchorCommonContextFinalData.toGrammarRuleTransportData

/-- Convert directly to final reachable data. -/
def toFinalReachableData
    (O : TrimmedPresentationCommonContextTransportObligations D) :
    FinalReachableData G O.sample obs f :=
  O.toAnchorCommonContextFinalData.toFinalReachableData

/-- The produced finite sample is a characteristic sample for the reachable
learner. -/
theorem characteristic_sample
    (O : TrimmedPresentationCommonContextTransportObligations D) :
    CharacteristicSample
      (reachableHypLanguage obs f)
      (reachableSampleLearner (α := α))
      O.sample
      G.StringLanguage :=
  O.toAnchorCommonContextFinalData.characteristic_sample

/-- Exact reconstruction for every positive finite superset of the produced
sample. -/
theorem exact_for_positive_superset
    (O : TrimmedPresentationCommonContextTransportObligations D)
    {K : Finset (Word α)}
    (hOK : (O.sample : Set (Word α)) ⊆ (K : Set (Word α)))
    (hKpos : (K : Set (Word α)) ⊆ G.StringLanguage) :
    ReachableSampleStringLanguage K obs f = G.StringLanguage :=
  O.toAnchorCommonContextFinalData.exact_for_positive_superset hOK hKpos

/-- Exact reconstruction at a positive-text prefix containing the produced
sample. -/
theorem exact_at_seen_prefix
    (O : TrimmedPresentationCommonContextTransportObligations D)
    (Ttxt : TextFor G.StringLanguage)
    {n : Nat}
    (hseen : (O.sample : Set (Word α)) ⊆
      (Ttxt.prefixSample n : Set (Word α))) :
    ReachableSampleStringLanguage (Ttxt.prefixSample n) obs f =
      G.StringLanguage :=
  O.toAnchorCommonContextFinalData.exact_at_seen_prefix Ttxt hseen

/-- Eventual prefix-exact reconstruction from common-context obligations. -/
theorem prefix_exact_eventually
    (O : TrimmedPresentationCommonContextTransportObligations D) :
    ∀ Ttxt : TextFor G.StringLanguage,
      ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
        ReachableSampleStringLanguage (Ttxt.prefixSample n) obs f =
          G.StringLanguage :=
  O.toAnchorCommonContextFinalData.prefix_exact_eventually

/-- Reachable Gold identification from common-context obligations. -/
theorem identifies_from_positive_text
    (O : TrimmedPresentationCommonContextTransportObligations D) :
    ∀ Ttxt : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        Ttxt :=
  O.toAnchorCommonContextFinalData.identifies_from_positive_text

/-- Pointwise eventual correctness on one positive text. -/
theorem eventually_correct_on_text
    (O : TrimmedPresentationCommonContextTransportObligations D)
    (Ttxt : TextFor G.StringLanguage) :
    EventuallyCorrectOnText
      (reachableHypLanguage obs f)
      (reachableSampleLearner (α := α))
      Ttxt :=
  O.identifies_from_positive_text Ttxt

end TrimmedPresentationCommonContextTransportObligations

end CommonContextTransportObligations


section MainTheoremsFromTransportObligations

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}
variable {f : Nat}
variable {T : TrimmedOutputTypePresentation G obs}
variable {D : TrimmedPresentationPreCoreData T f}

/-- Stable top-level reachable identification theorem from exposing-transport
obligations. -/
theorem trimmed_exposing_transport_obligations_reachable_identification
    (O : TrimmedPresentationExposingTransportObligations D) :
    ∀ Ttxt : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        Ttxt :=
  O.identifies_from_positive_text

/-- Stable top-level prefix-exact theorem from exposing-transport obligations. -/
theorem trimmed_exposing_transport_obligations_reachable_prefix_exact
    (O : TrimmedPresentationExposingTransportObligations D) :
    ∀ Ttxt : TextFor G.StringLanguage,
      ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
        ReachableSampleStringLanguage (Ttxt.prefixSample n) obs f =
          G.StringLanguage :=
  O.prefix_exact_eventually

/-- Stable top-level positive finite-superset exactness theorem from
exposing-transport obligations. -/
theorem trimmed_exposing_transport_obligations_exact_for_positive_superset
    (O : TrimmedPresentationExposingTransportObligations D)
    {K : Finset (Word α)}
    (hOK : (O.sample : Set (Word α)) ⊆ (K : Set (Word α)))
    (hKpos : (K : Set (Word α)) ⊆ G.StringLanguage) :
    ReachableSampleStringLanguage K obs f = G.StringLanguage :=
  O.exact_for_positive_superset hOK hKpos

/-- Stable top-level reachable identification theorem from common-context
obligations. -/
theorem trimmed_common_context_obligations_reachable_identification
    (O : TrimmedPresentationCommonContextTransportObligations D) :
    ∀ Ttxt : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        Ttxt :=
  O.identifies_from_positive_text

/-- Stable top-level prefix-exact theorem from common-context obligations. -/
theorem trimmed_common_context_obligations_reachable_prefix_exact
    (O : TrimmedPresentationCommonContextTransportObligations D) :
    ∀ Ttxt : TextFor G.StringLanguage,
      ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
        ReachableSampleStringLanguage (Ttxt.prefixSample n) obs f =
          G.StringLanguage :=
  O.prefix_exact_eventually

/-- Stable top-level positive finite-superset exactness theorem from
common-context obligations. -/
theorem trimmed_common_context_obligations_exact_for_positive_superset
    (O : TrimmedPresentationCommonContextTransportObligations D)
    {K : Finset (Word α)}
    (hOK : (O.sample : Set (Word α)) ⊆ (K : Set (Word α)))
    (hKpos : (K : Set (Word α)) ⊆ G.StringLanguage) :
    ReachableSampleStringLanguage K obs f = G.StringLanguage :=
  O.exact_for_positive_superset hOK hKpos

end MainTheoremsFromTransportObligations

end MCFG
