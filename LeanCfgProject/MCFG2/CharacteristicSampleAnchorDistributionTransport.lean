/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG2.CharacteristicSampleSameContextCore

/-!
# CharacteristicSampleAnchorDistributionTransport.lean

Sixty-sixth clean Lean experiment for the fixed-observation MCFG project.

The previous files isolated the remaining semantic obligation as exposing
context transport:

```lean
TrimmedPresentationExposingContextTransport
```

This file introduces a distributional-equivalence version of that obligation.

For each base nonterminal `A`, it is enough to know that every tuple with the
same observed type as the anchor tuple `D.anchor A` is distributionally
equivalent to that anchor tuple.  Then the exposing context `D.expose A`, which
already accepts the anchor tuple, also accepts the new tuple.

This is a useful bridge toward the existing distributional-equivalence
machinery:

```text
anchor distributional equivalence
⇒ exposing-context transport
⇒ rule-witness transport
⇒ characteristic sample
⇒ reachable identification.
```

No theorem here uses `sorry`.
-/

namespace MCFG

universe u v w

section AnchorDistributionTransport

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}
variable {f : Nat}
variable {T : TrimmedOutputTypePresentation G obs}

/-- Distributional transport from each anchor tuple to every tuple of the same
observed type at the same arity.

This is stronger than exposing-context transport, but closer to the
distributional-equivalence lemmas already present in the development. -/
structure TrimmedPresentationAnchorDistributionTransport
    (D : TrimmedPresentationPreCoreData T f) where
  equivalent :
    ∀ (A : N)
      (x : Tuple α (G.arity A)),
        tupleType obs (D.anchor A) = tupleType obs x →
          FixedNamedDistributionalEquivalent
            obs G.StringLanguage (D.anchor A) x

namespace TrimmedPresentationAnchorDistributionTransport

variable {D : TrimmedPresentationPreCoreData T f}

/-- Distributional equivalence transports acceptance of the exposing context
from the anchor tuple to any tuple with the same observed type. -/
theorem exposing_accepts
    (H : TrimmedPresentationAnchorDistributionTransport D)
    (A : N)
    (x : Tuple α (G.arity A))
    (htype : tupleType obs (D.anchor A) = tupleType obs x) :
    namedFill (G.arity A) (D.expose A) x ∈ G.StringLanguage := by
  exact (H.equivalent A x htype).namedFill_mem_right
    (c := D.expose A)
    (D.anchorWitnessWord_mem_target A)

/-- Anchor distributional transport implies exposing-context transport. -/
def toExposingContextTransport
    (H : TrimmedPresentationAnchorDistributionTransport D) :
    TrimmedPresentationExposingContextTransport D where
  transport := H.exposing_accepts

/-- Terminal witness positivity follows through the induced exposing-context
transport. -/
theorem terminal_positive
    (H : TrimmedPresentationAnchorDistributionTransport D)
    (A : TrimmedPresentationRuleAritySelectors D)
    (ρ : TerminalRule N α)
    (hρ : ρ ∈ G.terminalRules) :
    D.terminalWitnessWord ρ (A.terminal_arity ρ hρ) ∈
      G.StringLanguage :=
  H.toExposingContextTransport.terminal_positive A ρ hρ

/-- Binary witness positivity follows through the induced exposing-context
transport. -/
theorem binary_positive
    (H : TrimmedPresentationAnchorDistributionTransport D)
    (ρ : BinaryRule N α G.arity)
    (hρ : ρ ∈ G.binaryRules) :
    D.binaryWitnessWord ρ ∈ G.StringLanguage :=
  H.toExposingContextTransport.binary_positive ρ hρ

/-- Start-rule witness positivity follows through the induced exposing-context
transport. -/
theorem start_positive
    (H : TrimmedPresentationAnchorDistributionTransport D)
    (A : TrimmedPresentationRuleAritySelectors D)
    (ρ : StartRule N)
    (hρ : ρ ∈ G.startRules) :
    D.startWitnessWord ρ (A.start_arity ρ hρ) ∈
      G.StringLanguage :=
  H.toExposingContextTransport.start_positive A ρ hρ

/-- Build rule-witness transport from anchor distributional transport and
start-word evidence. -/
def toRuleWitnessTransport
    (H : TrimmedPresentationAnchorDistributionTransport D)
    (A : TrimmedPresentationRuleAritySelectors D)
    (E : TrimmedPresentationStartWordEvidence D) :
    TrimmedPresentationRuleWitnessTransport D A :=
  H.toExposingContextTransport.toRuleWitnessTransport
    A E.startWord_positive

end TrimmedPresentationAnchorDistributionTransport

end AnchorDistributionTransport


section AnchorDistributionCoreData

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}
variable {f : Nat}
variable {T : TrimmedOutputTypePresentation G obs}

/-- Core characteristic-sample data using anchor distributional transport,
without storing start-word positivity. -/
structure TrimmedPresentationAnchorDistributionCoreData
    (D : TrimmedPresentationPreCoreData T f) where
  baseNonterminals : Finset N
  base_covers :
    ∀ A : N, A ∈ baseNonterminals

  arities : TrimmedPresentationRuleAritySelectors D
  anchorDistribution :
    TrimmedPresentationAnchorDistributionTransport D

namespace TrimmedPresentationAnchorDistributionCoreData

variable {D : TrimmedPresentationPreCoreData T f}

/-- Anchor distributional core data induces exposing-transport core data. -/
def toExposingTransportCoreData
    (P : TrimmedPresentationAnchorDistributionCoreData D) :
    TrimmedPresentationExposingTransportCoreData D where
  baseNonterminals := P.baseNonterminals
  base_covers := P.base_covers
  arities := P.arities
  exposingTransport := P.anchorDistribution.toExposingContextTransport

/-- Anchor distributional core data plus start-word evidence recovers exposing
transport data. -/
def toExposingTransportData
    (P : TrimmedPresentationAnchorDistributionCoreData D)
    (E : TrimmedPresentationStartWordEvidence D) :
    TrimmedPresentationExposingTransportData D :=
  P.toExposingTransportCoreData.withStartWord E

/-- Convert to rule-witness transport. -/
def toRuleWitnessTransport
    (P : TrimmedPresentationAnchorDistributionCoreData D)
    (E : TrimmedPresentationStartWordEvidence D) :
    TrimmedPresentationRuleWitnessTransport D P.arities :=
  P.anchorDistribution.toRuleWitnessTransport P.arities E

/-- Convert to grammar-rule transport data. -/
def toGrammarRuleTransportData
    (P : TrimmedPresentationAnchorDistributionCoreData D)
    (E : TrimmedPresentationStartWordEvidence D) :
    TrimmedPresentationGrammarRuleTransportData D :=
  P.toExposingTransportCoreData.toGrammarRuleTransportData E

/-- The finite sample produced by anchor distributional core data plus
start-word evidence. -/
noncomputable def sample
    (P : TrimmedPresentationAnchorDistributionCoreData D)
    (E : TrimmedPresentationStartWordEvidence D) :
    Finset (Word α) :=
  P.toExposingTransportCoreData.sample E

/-- The produced finite sample is positive. -/
theorem sample_positive
    (P : TrimmedPresentationAnchorDistributionCoreData D)
    (E : TrimmedPresentationStartWordEvidence D) :
    (P.sample E : Set (Word α)) ⊆ G.StringLanguage :=
  P.toExposingTransportCoreData.sample_positive E

/-- The produced finite sample contains all required witness words. -/
theorem contains_witnesses
    (P : TrimmedPresentationAnchorDistributionCoreData D)
    (E : TrimmedPresentationStartWordEvidence D) :
    TrimmedPresentationWitnessWordSet D ⊆
      (P.sample E : Set (Word α)) :=
  P.toExposingTransportCoreData.contains_witnesses E

/-- Convert to the separated exposing-core final wrapper. -/
def toExposingCoreFinalData
    (P : TrimmedPresentationAnchorDistributionCoreData D)
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
noncomputable def toFinalReachableData
    (P : TrimmedPresentationAnchorDistributionCoreData D)
    (E : TrimmedPresentationStartWordEvidence D)
    (U : NamedContextSplicingConstructor α)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    FinalReachableData G (P.sample E) obs f :=
  (P.toExposingCoreFinalData E U hfan hL).toFinalReachableData

/-- The produced sample is a characteristic sample for the reachable learner. -/
theorem characteristic_sample
    (P : TrimmedPresentationAnchorDistributionCoreData D)
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
    (P : TrimmedPresentationAnchorDistributionCoreData D)
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

/-- Eventual prefix-exact reconstruction from anchor distributional core data
plus start-word evidence. -/
theorem prefix_exact_eventually
    (P : TrimmedPresentationAnchorDistributionCoreData D)
    (E : TrimmedPresentationStartWordEvidence D)
    (U : NamedContextSplicingConstructor α)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    ∀ Ttxt : TextFor G.StringLanguage,
      ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
        ReachableSampleStringLanguage (Ttxt.prefixSample n) obs f =
          G.StringLanguage :=
  (P.toExposingCoreFinalData E U hfan hL).prefix_exact_eventually

/-- Reachable Gold identification from anchor distributional core data plus
start-word evidence. -/
theorem identifies_from_positive_text
    (P : TrimmedPresentationAnchorDistributionCoreData D)
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

end TrimmedPresentationAnchorDistributionCoreData

end AnchorDistributionCoreData


section AnchorDistributionCoreFromSampleEvidence

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}
variable {f : Nat}
variable {T : TrimmedOutputTypePresentation G obs}
variable {D : TrimmedPresentationPreCoreData T f}
variable {S : Finset (Word α)}

namespace TrimmedPresentationAnchorDistributionCoreData

/-- Build separated final data using start-word evidence extracted from a
positive finite sample. -/
def toFinalDataOfStartWordSample
    (P : TrimmedPresentationAnchorDistributionCoreData D)
    (E : TrimmedPresentationStartWordSampleEvidence D S)
    (U : NamedContextSplicingConstructor α)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    TrimmedPresentationExposingCoreFinalData D :=
  P.toExposingCoreFinalData E.toStartWordEvidence U hfan hL

/-- Eventual prefix-exact reconstruction using anchor distributional core data
and start-word evidence extracted from a positive finite sample. -/
theorem prefix_exact_eventually_of_startWord_sample
    (P : TrimmedPresentationAnchorDistributionCoreData D)
    (E : TrimmedPresentationStartWordSampleEvidence D S)
    (U : NamedContextSplicingConstructor α)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    ∀ Ttxt : TextFor G.StringLanguage,
      ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
        ReachableSampleStringLanguage (Ttxt.prefixSample n) obs f =
          G.StringLanguage :=
  (P.toFinalDataOfStartWordSample E U hfan hL).prefix_exact_eventually

/-- Reachable Gold identification using anchor distributional core data and
start-word evidence extracted from a positive finite sample. -/
theorem identifies_from_positive_text_of_startWord_sample
    (P : TrimmedPresentationAnchorDistributionCoreData D)
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

end TrimmedPresentationAnchorDistributionCoreData

end AnchorDistributionCoreFromSampleEvidence


section MainTheoremsFromAnchorDistributionCoreData

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}
variable {f : Nat}
variable {T : TrimmedOutputTypePresentation G obs}
variable {D : TrimmedPresentationPreCoreData T f}

/-- Stable top-level reachable identification theorem from anchor
distributional core data plus start-word evidence. -/
theorem trimmed_anchor_distribution_core_reachable_identification
    (P : TrimmedPresentationAnchorDistributionCoreData D)
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

/-- Stable top-level prefix-exact theorem from anchor distributional core data
plus start-word evidence. -/
theorem trimmed_anchor_distribution_core_reachable_prefix_exact
    (P : TrimmedPresentationAnchorDistributionCoreData D)
    (E : TrimmedPresentationStartWordEvidence D)
    (U : NamedContextSplicingConstructor α)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    ∀ Ttxt : TextFor G.StringLanguage,
      ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
        ReachableSampleStringLanguage (Ttxt.prefixSample n) obs f =
          G.StringLanguage :=
  P.prefix_exact_eventually E U hfan hL

/-- Stable top-level finite-superset exactness theorem from anchor
distributional core data plus start-word evidence. -/
theorem trimmed_anchor_distribution_core_exact_for_positive_superset
    (P : TrimmedPresentationAnchorDistributionCoreData D)
    (E : TrimmedPresentationStartWordEvidence D)
    (U : NamedContextSplicingConstructor α)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage)
    {K : Finset (Word α)}
    (hPK : (P.sample E : Set (Word α)) ⊆ (K : Set (Word α)))
    (hKpos : (K : Set (Word α)) ⊆ G.StringLanguage) :
    ReachableSampleStringLanguage K obs f = G.StringLanguage :=
  P.exact_for_positive_superset E U hfan hL hPK hKpos

end MainTheoremsFromAnchorDistributionCoreData

end MCFG
