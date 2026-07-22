/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG2.CharacteristicSampleAnchorDistributionTransport

/-!
# CharacteristicSampleAnchorCommonContext.lean

Sixty-seventh clean Lean experiment for the fixed-observation MCFG project.

`CharacteristicSampleAnchorDistributionTransport.lean` introduced the semantic
bridge

```text
anchor distributional equivalence
⇒ exposing-context transport
⇒ characteristic sample.
```

This file moves one step closer to the existing substitutability machinery.
It shows how to obtain anchor distributional equivalence from a common
accepting named context.

The key imported lemma is

```lean
fixedNamedDistributionalEquivalent_of_common_context
```

which says that, under fixed-observation substitutability, two tuples of the
same observed type are distributionally equivalent when they are both accepted
by one common named context.

Thus the route is now:

```text
common accepting context for D.anchor A and x
+
same observed type
+
fanout / arity positivity
+
fixed-observation substitutability
⇒ anchor distributional equivalence
⇒ exposing-context transport
⇒ reachable identification.
```

No theorem here uses `sorry`.
-/

namespace MCFG

universe u v w

section AnchorCommonContextEvidence

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}
variable {f : Nat}
variable {T : TrimmedOutputTypePresentation G obs}

/-- A common accepting named context for the anchor tuple of `A` and another
tuple of the same arity. -/
structure TrimmedPresentationAnchorCommonContextEvidence
    (D : TrimmedPresentationPreCoreData T f)
    (A : N)
    (x : Tuple α (G.arity A)) where
  context : NamedSentenceContext α (G.arity A)
  anchor_mem :
    namedFill (G.arity A) context (D.anchor A) ∈
      G.StringLanguage
  target_mem :
    namedFill (G.arity A) context x ∈
      G.StringLanguage

namespace TrimmedPresentationAnchorCommonContextEvidence

variable {D : TrimmedPresentationPreCoreData T f}
variable {A : N} {x : Tuple α (G.arity A)}

/-- A common accepting context yields fixed named distributional equivalence
under the global substitutability promise. -/
theorem toDistributionalEquivalent
    (E : TrimmedPresentationAnchorCommonContextEvidence D A x)
    (hfanA : G.arity A ≤ f)
    (hposA : 0 < G.arity A)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage)
    (htype : tupleType obs (D.anchor A) = tupleType obs x) :
    FixedNamedDistributionalEquivalent
      obs G.StringLanguage (D.anchor A) x :=
  fixedNamedDistributionalEquivalent_of_common_context
    hL hfanA hposA htype E.anchor_mem E.target_mem

end TrimmedPresentationAnchorCommonContextEvidence

end AnchorCommonContextEvidence


section AnchorCommonContextTransport

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}
variable {f : Nat}
variable {T : TrimmedOutputTypePresentation G obs}

/-- Common-context evidence for every anchor tuple and every same-type tuple. -/
structure TrimmedPresentationAnchorCommonContextTransport
    (D : TrimmedPresentationPreCoreData T f) where
  arity_pos :
    ∀ A : N, 0 < G.arity A
  common :
    ∀ (A : N)
      (x : Tuple α (G.arity A)),
        tupleType obs (D.anchor A) = tupleType obs x →
          TrimmedPresentationAnchorCommonContextEvidence D A x

namespace TrimmedPresentationAnchorCommonContextTransport

variable {D : TrimmedPresentationPreCoreData T f}

/-- Common-context transport yields anchor distributional transport under
fanout and fixed-observation substitutability. -/
def toAnchorDistributionTransport
    (H : TrimmedPresentationAnchorCommonContextTransport D)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    TrimmedPresentationAnchorDistributionTransport D where
  equivalent := by
    intro A x htype
    exact (H.common A x htype).toDistributionalEquivalent
      (hfan A) (H.arity_pos A) hL htype

/-- Common-context transport yields exposing-context transport under fanout and
fixed-observation substitutability. -/
def toExposingContextTransport
    (H : TrimmedPresentationAnchorCommonContextTransport D)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    TrimmedPresentationExposingContextTransport D :=
  (H.toAnchorDistributionTransport hfan hL).toExposingContextTransport

/-- Terminal witness positivity obtained through common-context transport. -/
theorem terminal_positive
    (H : TrimmedPresentationAnchorCommonContextTransport D)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage)
    (A : TrimmedPresentationRuleAritySelectors D)
    (ρ : TerminalRule N α)
    (hρ : ρ ∈ G.terminalRules) :
    D.terminalWitnessWord ρ (A.terminal_arity ρ hρ) ∈
      G.StringLanguage :=
  (H.toAnchorDistributionTransport hfan hL).terminal_positive A ρ hρ

/-- Binary witness positivity obtained through common-context transport. -/
theorem binary_positive
    (H : TrimmedPresentationAnchorCommonContextTransport D)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage)
    (ρ : BinaryRule N α G.arity)
    (hρ : ρ ∈ G.binaryRules) :
    D.binaryWitnessWord ρ ∈ G.StringLanguage :=
  (H.toAnchorDistributionTransport hfan hL).binary_positive ρ hρ

/-- Start-rule witness positivity obtained through common-context transport. -/
theorem start_positive
    (H : TrimmedPresentationAnchorCommonContextTransport D)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage)
    (A : TrimmedPresentationRuleAritySelectors D)
    (ρ : StartRule N)
    (hρ : ρ ∈ G.startRules) :
    D.startWitnessWord ρ (A.start_arity ρ hρ) ∈
      G.StringLanguage :=
  (H.toAnchorDistributionTransport hfan hL).start_positive A ρ hρ

end TrimmedPresentationAnchorCommonContextTransport

end AnchorCommonContextTransport


section AnchorCommonContextCoreData

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}
variable {f : Nat}
variable {T : TrimmedOutputTypePresentation G obs}

/-- Core characteristic-sample data using common-context evidence, before
applying fanout and fixed-observation substitutability. -/
structure TrimmedPresentationAnchorCommonContextCoreData
    (D : TrimmedPresentationPreCoreData T f) where
  baseNonterminals : Finset N
  base_covers :
    ∀ A : N, A ∈ baseNonterminals

  arities : TrimmedPresentationRuleAritySelectors D
  commonContext :
    TrimmedPresentationAnchorCommonContextTransport D

namespace TrimmedPresentationAnchorCommonContextCoreData

variable {D : TrimmedPresentationPreCoreData T f}

/-- Convert common-context core data to anchor-distributional core data. -/
def toAnchorDistributionCoreData
    (P : TrimmedPresentationAnchorCommonContextCoreData D)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    TrimmedPresentationAnchorDistributionCoreData D where
  baseNonterminals := P.baseNonterminals
  base_covers := P.base_covers
  arities := P.arities
  anchorDistribution :=
    P.commonContext.toAnchorDistributionTransport hfan hL

/-- Convert common-context core data to exposing-transport core data. -/
def toExposingTransportCoreData
    (P : TrimmedPresentationAnchorCommonContextCoreData D)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    TrimmedPresentationExposingTransportCoreData D :=
  (P.toAnchorDistributionCoreData hfan hL).toExposingTransportCoreData

/-- Convert to grammar-rule transport data after adding start-word evidence,
fanout, and fixed-observation substitutability. -/
def toGrammarRuleTransportData
    (P : TrimmedPresentationAnchorCommonContextCoreData D)
    (E : TrimmedPresentationStartWordEvidence D)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    TrimmedPresentationGrammarRuleTransportData D :=
  (P.toAnchorDistributionCoreData hfan hL).toGrammarRuleTransportData E

/-- The finite sample produced after adding start-word evidence, fanout, and
fixed-observation substitutability. -/
noncomputable def sample
    (P : TrimmedPresentationAnchorCommonContextCoreData D)
    (E : TrimmedPresentationStartWordEvidence D)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    Finset (Word α) :=
  (P.toAnchorDistributionCoreData hfan hL).sample E

/-- The produced finite sample is positive. -/
theorem sample_positive
    (P : TrimmedPresentationAnchorCommonContextCoreData D)
    (E : TrimmedPresentationStartWordEvidence D)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    (P.sample E hfan hL : Set (Word α)) ⊆ G.StringLanguage :=
  (P.toAnchorDistributionCoreData hfan hL).sample_positive E

/-- The produced finite sample contains all required witness words. -/
theorem contains_witnesses
    (P : TrimmedPresentationAnchorCommonContextCoreData D)
    (E : TrimmedPresentationStartWordEvidence D)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    TrimmedPresentationWitnessWordSet D ⊆
      (P.sample E hfan hL : Set (Word α)) :=
  (P.toAnchorDistributionCoreData hfan hL).contains_witnesses E

/-- Convert to the separated exposing-core final wrapper. -/
def toExposingCoreFinalData
    (P : TrimmedPresentationAnchorCommonContextCoreData D)
    (E : TrimmedPresentationStartWordEvidence D)
    (U : NamedContextSplicingConstructor α)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    TrimmedPresentationExposingCoreFinalData D :=
  (P.toAnchorDistributionCoreData hfan hL).toExposingCoreFinalData
    E U hfan hL

/-- Convert directly to final reachable data. -/
noncomputable def toFinalReachableData
    (P : TrimmedPresentationAnchorCommonContextCoreData D)
    (E : TrimmedPresentationStartWordEvidence D)
    (U : NamedContextSplicingConstructor α)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    FinalReachableData G (P.sample E hfan hL) obs f :=
  (P.toExposingCoreFinalData E U hfan hL).toFinalReachableData

/-- The produced sample is a characteristic sample for the reachable learner. -/
theorem characteristic_sample
    (P : TrimmedPresentationAnchorCommonContextCoreData D)
    (E : TrimmedPresentationStartWordEvidence D)
    (U : NamedContextSplicingConstructor α)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    CharacteristicSample
      (reachableHypLanguage obs f)
      (reachableSampleLearner (α := α))
      (P.sample E hfan hL)
      G.StringLanguage :=
  (P.toExposingCoreFinalData E U hfan hL).characteristic_sample

/-- Eventual prefix-exact reconstruction from common-context core data. -/
theorem prefix_exact_eventually
    (P : TrimmedPresentationAnchorCommonContextCoreData D)
    (E : TrimmedPresentationStartWordEvidence D)
    (U : NamedContextSplicingConstructor α)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    ∀ Ttxt : TextFor G.StringLanguage,
      ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
        ReachableSampleStringLanguage (Ttxt.prefixSample n) obs f =
          G.StringLanguage :=
  (P.toExposingCoreFinalData E U hfan hL).prefix_exact_eventually

/-- Reachable Gold identification from common-context core data. -/
theorem identifies_from_positive_text
    (P : TrimmedPresentationAnchorCommonContextCoreData D)
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

end TrimmedPresentationAnchorCommonContextCoreData

end AnchorCommonContextCoreData


section CommonContextCoreFromStartWordSample

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}
variable {f : Nat}
variable {T : TrimmedOutputTypePresentation G obs}
variable {D : TrimmedPresentationPreCoreData T f}
variable {S : Finset (Word α)}

namespace TrimmedPresentationAnchorCommonContextCoreData

/-- Build separated final data using start-word evidence extracted from a
positive finite sample. -/
def toFinalDataOfStartWordSample
    (P : TrimmedPresentationAnchorCommonContextCoreData D)
    (E : TrimmedPresentationStartWordSampleEvidence D S)
    (U : NamedContextSplicingConstructor α)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    TrimmedPresentationExposingCoreFinalData D :=
  P.toExposingCoreFinalData E.toStartWordEvidence U hfan hL

/-- Eventual prefix-exact reconstruction using common-context core data and
start-word evidence extracted from a positive finite sample. -/
theorem prefix_exact_eventually_of_startWord_sample
    (P : TrimmedPresentationAnchorCommonContextCoreData D)
    (E : TrimmedPresentationStartWordSampleEvidence D S)
    (U : NamedContextSplicingConstructor α)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    ∀ Ttxt : TextFor G.StringLanguage,
      ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
        ReachableSampleStringLanguage (Ttxt.prefixSample n) obs f =
          G.StringLanguage :=
  (P.toFinalDataOfStartWordSample E U hfan hL).prefix_exact_eventually

/-- Reachable Gold identification using common-context core data and start-word
evidence extracted from a positive finite sample. -/
theorem identifies_from_positive_text_of_startWord_sample
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
  (P.toFinalDataOfStartWordSample E U hfan hL).identifies_from_positive_text

end TrimmedPresentationAnchorCommonContextCoreData

end CommonContextCoreFromStartWordSample


section MainTheoremsFromAnchorCommonContextCoreData

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}
variable {f : Nat}
variable {T : TrimmedOutputTypePresentation G obs}
variable {D : TrimmedPresentationPreCoreData T f}

/-- Stable top-level reachable identification theorem from common-context core
data plus start-word evidence. -/
theorem trimmed_anchor_common_context_core_reachable_identification
    (P : TrimmedPresentationAnchorCommonContextCoreData D)
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

/-- Stable top-level prefix-exact theorem from common-context core data plus
start-word evidence. -/
theorem trimmed_anchor_common_context_core_reachable_prefix_exact
    (P : TrimmedPresentationAnchorCommonContextCoreData D)
    (E : TrimmedPresentationStartWordEvidence D)
    (U : NamedContextSplicingConstructor α)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    ∀ Ttxt : TextFor G.StringLanguage,
      ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
        ReachableSampleStringLanguage (Ttxt.prefixSample n) obs f =
          G.StringLanguage :=
  P.prefix_exact_eventually E U hfan hL

end MainTheoremsFromAnchorCommonContextCoreData

end MCFG
