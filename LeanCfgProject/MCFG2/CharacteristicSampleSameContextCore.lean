/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG2.CharacteristicSampleStartWordFromSample

/-!
# CharacteristicSampleSameContextCore.lean

Sixty-fifth clean Lean experiment for the fixed-observation MCFG project.

`CharacteristicSampleExposingTransport.lean` weakened the local semantic
transport target from all named contexts to only the exposing contexts
`D.expose A`.

`CharacteristicSampleStartWordEvidence.lean` and
`CharacteristicSampleExposingCoreFinal.lean` then separated the remaining
start-word positivity obligation.

This file reconnects the stronger same-context transport principle to the
separated core route.  It provides a convenient intermediate entrance:

```text
finite base-nonterminal cover
+
arity selectors
+
same-context transport
+
start-word evidence
+
splicing/fanout/substitutability data
⇒ reachable identification.
```

This is useful because later semantic work may prove same-context transport
first, then descend to the sharper exposing-context target.

No theorem here uses `sorry`.
-/

namespace MCFG

universe u v w

section SameContextCoreData

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}
variable {f : Nat}
variable {T : TrimmedOutputTypePresentation G obs}

/-- Core characteristic-sample data using the stronger same-context transport
principle, but without storing start-word positivity. -/
structure TrimmedPresentationSameContextCoreData
    (D : TrimmedPresentationPreCoreData T f) where
  baseNonterminals : Finset N
  base_covers :
    ∀ A : N, A ∈ baseNonterminals

  arities : TrimmedPresentationRuleAritySelectors D
  sameContextTransport : TrimmedPresentationSameContextTransport D

namespace TrimmedPresentationSameContextCoreData

variable {D : TrimmedPresentationPreCoreData T f}

/-- Same-context core data induces exposing-transport core data. -/
def toExposingTransportCoreData
    (P : TrimmedPresentationSameContextCoreData D) :
    TrimmedPresentationExposingTransportCoreData D where
  baseNonterminals := P.baseNonterminals
  base_covers := P.base_covers
  arities := P.arities
  exposingTransport :=
    TrimmedPresentationExposingContextTransport.ofSameContextTransport
      P.sameContextTransport

/-- Same-context core data plus start-word evidence recovers the earlier
same-context transport data package. -/
def toContextTransportData
    (P : TrimmedPresentationSameContextCoreData D)
    (E : TrimmedPresentationStartWordEvidence D) :
    TrimmedPresentationContextTransportData D where
  baseNonterminals := P.baseNonterminals
  base_covers := P.base_covers
  arities := P.arities
  contextTransport := P.sameContextTransport
  startWord_positive := E.startWord_positive

/-- Same-context core data plus start-word evidence recovers the exposing
transport data package. -/
def toExposingTransportData
    (P : TrimmedPresentationSameContextCoreData D)
    (E : TrimmedPresentationStartWordEvidence D) :
    TrimmedPresentationExposingTransportData D :=
  P.toExposingTransportCoreData.withStartWord E

/-- The finite sample produced by same-context core data plus start-word
evidence. -/
def sample
    (P : TrimmedPresentationSameContextCoreData D)
    (E : TrimmedPresentationStartWordEvidence D) :
    Finset (Word α) :=
  (P.toExposingTransportCoreData.sample E)

/-- The produced finite sample is positive. -/
theorem sample_positive
    (P : TrimmedPresentationSameContextCoreData D)
    (E : TrimmedPresentationStartWordEvidence D) :
    (P.sample E : Set (Word α)) ⊆ G.StringLanguage :=
  P.toExposingTransportCoreData.sample_positive E

/-- The produced finite sample contains all required witness words. -/
theorem contains_witnesses
    (P : TrimmedPresentationSameContextCoreData D)
    (E : TrimmedPresentationStartWordEvidence D) :
    TrimmedPresentationWitnessWordSet D ⊆
      (P.sample E : Set (Word α)) :=
  P.toExposingTransportCoreData.contains_witnesses E

/-- Convert to rule-witness transport. -/
def toRuleWitnessTransport
    (P : TrimmedPresentationSameContextCoreData D)
    (E : TrimmedPresentationStartWordEvidence D) :
    TrimmedPresentationRuleWitnessTransport D P.arities :=
  P.toExposingTransportCoreData.toRuleWitnessTransport E

/-- Convert to grammar-rule transport data. -/
def toGrammarRuleTransportData
    (P : TrimmedPresentationSameContextCoreData D)
    (E : TrimmedPresentationStartWordEvidence D) :
    TrimmedPresentationGrammarRuleTransportData D :=
  P.toExposingTransportCoreData.toGrammarRuleTransportData E

/-- Convert to the separated exposing-core final wrapper. -/
def toExposingCoreFinalData
    (P : TrimmedPresentationSameContextCoreData D)
    (E : TrimmedPresentationStartWordEvidence D)
    (U : NamedContextSplicingConstructor α)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    TrimmedPresentationExposingCoreFinalData D where
  coreData := P.toExposingTransportCoreData
  startEvidence := E
  splicingConstructor := U
  fanout := hfan
  promise := hL

/-- Convert directly to final reachable data. -/
def toFinalReachableData
    (P : TrimmedPresentationSameContextCoreData D)
    (E : TrimmedPresentationStartWordEvidence D)
    (U : NamedContextSplicingConstructor α)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    FinalReachableData G (P.sample E) obs f :=
  (P.toExposingCoreFinalData E U hfan hL).toFinalReachableData

/-- The produced sample is a characteristic sample for the reachable learner. -/
theorem characteristic_sample
    (P : TrimmedPresentationSameContextCoreData D)
    (E : TrimmedPresentationStartWordEvidence D)
    (U : NamedContextSplicingConstructor α)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    CharacteristicSample
      (reachableHypLanguage obs f)
      (reachableSampleLearner (α := α))
      (P.sample E)
      G.StringLanguage :=
  (P.toExposingCoreFinalData E U hfan hL).characteristic_sample

/-- Exact reconstruction for every positive finite superset of the produced
sample. -/
theorem exact_for_positive_superset
    (P : TrimmedPresentationSameContextCoreData D)
    (E : TrimmedPresentationStartWordEvidence D)
    (U : NamedContextSplicingConstructor α)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage)
    {K : Finset (Word α)}
    (hPK : (P.sample E : Set (Word α)) ⊆ (K : Set (Word α)))
    (hKpos : (K : Set (Word α)) ⊆ G.StringLanguage) :
    ReachableSampleStringLanguage K obs f = G.StringLanguage :=
  (P.toExposingCoreFinalData E U hfan hL).exact_for_positive_superset
    hPK hKpos

/-- Exact reconstruction at a positive-text prefix containing the produced
sample. -/
theorem exact_at_seen_prefix
    (P : TrimmedPresentationSameContextCoreData D)
    (E : TrimmedPresentationStartWordEvidence D)
    (U : NamedContextSplicingConstructor α)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage)
    (Ttxt : TextFor G.StringLanguage)
    {n : Nat}
    (hseen : (P.sample E : Set (Word α)) ⊆
      (Ttxt.prefixSample n : Set (Word α))) :
    ReachableSampleStringLanguage (Ttxt.prefixSample n) obs f =
      G.StringLanguage :=
  (P.toExposingCoreFinalData E U hfan hL).exact_at_seen_prefix Ttxt hseen

/-- Eventual prefix-exact reconstruction from same-context core data plus
start-word evidence. -/
theorem prefix_exact_eventually
    (P : TrimmedPresentationSameContextCoreData D)
    (E : TrimmedPresentationStartWordEvidence D)
    (U : NamedContextSplicingConstructor α)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    ∀ Ttxt : TextFor G.StringLanguage,
      ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
        ReachableSampleStringLanguage (Ttxt.prefixSample n) obs f =
          G.StringLanguage :=
  (P.toExposingCoreFinalData E U hfan hL).prefix_exact_eventually

/-- Reachable Gold identification from same-context core data plus start-word
evidence. -/
theorem identifies_from_positive_text
    (P : TrimmedPresentationSameContextCoreData D)
    (E : TrimmedPresentationStartWordEvidence D)
    (U : NamedContextSplicingConstructor α)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    ∀ Ttxt : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        Ttxt :=
  (P.toExposingCoreFinalData E U hfan hL).identifies_from_positive_text

end TrimmedPresentationSameContextCoreData

end SameContextCoreData


section SameContextCoreFromSampleEvidence

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}
variable {f : Nat}
variable {T : TrimmedOutputTypePresentation G obs}
variable {D : TrimmedPresentationPreCoreData T f}
variable {S : Finset (Word α)}

namespace TrimmedPresentationSameContextCoreData

/-- Build separated final data using start-word evidence extracted from a
positive finite sample. -/
def toFinalDataOfStartWordSample
    (P : TrimmedPresentationSameContextCoreData D)
    (E : TrimmedPresentationStartWordSampleEvidence D S)
    (U : NamedContextSplicingConstructor α)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    TrimmedPresentationExposingCoreFinalData D :=
  P.toExposingCoreFinalData E.toStartWordEvidence U hfan hL

/-- Eventual prefix-exact reconstruction using same-context core data and
start-word evidence extracted from a positive finite sample. -/
theorem prefix_exact_eventually_of_startWord_sample
    (P : TrimmedPresentationSameContextCoreData D)
    (E : TrimmedPresentationStartWordSampleEvidence D S)
    (U : NamedContextSplicingConstructor α)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    ∀ Ttxt : TextFor G.StringLanguage,
      ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
        ReachableSampleStringLanguage (Ttxt.prefixSample n) obs f =
          G.StringLanguage :=
  (P.toFinalDataOfStartWordSample E U hfan hL).prefix_exact_eventually

/-- Reachable Gold identification using same-context core data and start-word
evidence extracted from a positive finite sample. -/
theorem identifies_from_positive_text_of_startWord_sample
    (P : TrimmedPresentationSameContextCoreData D)
    (E : TrimmedPresentationStartWordSampleEvidence D S)
    (U : NamedContextSplicingConstructor α)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    ∀ Ttxt : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        Ttxt :=
  (P.toFinalDataOfStartWordSample E U hfan hL).identifies_from_positive_text

end TrimmedPresentationSameContextCoreData

end SameContextCoreFromSampleEvidence


section MainTheoremsFromSameContextCoreData

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}
variable {f : Nat}
variable {T : TrimmedOutputTypePresentation G obs}
variable {D : TrimmedPresentationPreCoreData T f}

/-- Stable top-level reachable identification theorem from same-context core
data plus start-word evidence. -/
theorem trimmed_same_context_core_reachable_identification
    (P : TrimmedPresentationSameContextCoreData D)
    (E : TrimmedPresentationStartWordEvidence D)
    (U : NamedContextSplicingConstructor α)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    ∀ Ttxt : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        Ttxt :=
  P.identifies_from_positive_text E U hfan hL

/-- Stable top-level prefix-exact theorem from same-context core data plus
start-word evidence. -/
theorem trimmed_same_context_core_reachable_prefix_exact
    (P : TrimmedPresentationSameContextCoreData D)
    (E : TrimmedPresentationStartWordEvidence D)
    (U : NamedContextSplicingConstructor α)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    ∀ Ttxt : TextFor G.StringLanguage,
      ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
        ReachableSampleStringLanguage (Ttxt.prefixSample n) obs f =
          G.StringLanguage :=
  P.prefix_exact_eventually E U hfan hL

/-- Stable top-level finite-superset exactness theorem from same-context core
data plus start-word evidence. -/
theorem trimmed_same_context_core_exact_for_positive_superset
    (P : TrimmedPresentationSameContextCoreData D)
    (E : TrimmedPresentationStartWordEvidence D)
    (U : NamedContextSplicingConstructor α)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage)
    {K : Finset (Word α)}
    (hPK : (P.sample E : Set (Word α)) ⊆ (K : Set (Word α)))
    (hKpos : (K : Set (Word α)) ⊆ G.StringLanguage) :
    ReachableSampleStringLanguage K obs f = G.StringLanguage :=
  P.exact_for_positive_superset E U hfan hL hPK hKpos

end MainTheoremsFromSameContextCoreData

end MCFG
