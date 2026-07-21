/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG2.CharacteristicSampleExposingTransport

/-!
# CharacteristicSampleStartWordEvidence.lean

Sixty-second clean Lean experiment for the fixed-observation MCFG project.

`CharacteristicSampleExposingTransport.lean` reduced the semantic target for
rule-witness positivity to exposing-context transport, but the distinguished
start word still appears as a separate positivity assumption.

This file separates that start-word assumption into its own small interface:

```lean
TrimmedPresentationStartWordEvidence
```

and introduces a core version of exposing-transport data that does not store
the start-word positivity field.  Combining the core data with start-word
evidence recovers the previous `TrimmedPresentationExposingTransportData`.

This keeps the remaining proof obligations cleanly separated:

* exposing-context transport for terminal/binary/start witness words;
* positivity of the distinguished start word.

No theorem here uses `sorry`.
-/

namespace MCFG

universe u v w

section StartWordEvidence

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}
variable {f : Nat}
variable {T : TrimmedOutputTypePresentation G obs}

/-- Evidence that the distinguished start word stored in a trimmed pre-core is
positive for the target grammar language. -/
structure TrimmedPresentationStartWordEvidence
    (D : TrimmedPresentationPreCoreData T f) where
  mem_target :
    D.startWord ∈ G.StringLanguage

namespace TrimmedPresentationStartWordEvidence

variable {D : TrimmedPresentationPreCoreData T f}

/-- Coerce the evidence to the proposition it stores. -/
theorem startWord_positive
    (E : TrimmedPresentationStartWordEvidence D) :
    D.startWord ∈ G.StringLanguage :=
  E.mem_target

end TrimmedPresentationStartWordEvidence

end StartWordEvidence


section ExposingTransportCoreData

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}
variable {f : Nat}
variable {T : TrimmedOutputTypePresentation G obs}

/-- Exposing-transport data without the distinguished start-word positivity
field. -/
structure TrimmedPresentationExposingTransportCoreData
    (D : TrimmedPresentationPreCoreData T f) where
  baseNonterminals : Finset N
  base_covers :
    ∀ A : N, A ∈ baseNonterminals

  arities : TrimmedPresentationRuleAritySelectors D
  exposingTransport : TrimmedPresentationExposingContextTransport D

namespace TrimmedPresentationExposingTransportCoreData

variable {D : TrimmedPresentationPreCoreData T f}

/-- Combine core exposing-transport data with start-word evidence to recover the
previous exposing-transport package. -/
def withStartWord
    (P : TrimmedPresentationExposingTransportCoreData D)
    (E : TrimmedPresentationStartWordEvidence D) :
    TrimmedPresentationExposingTransportData D where
  baseNonterminals := P.baseNonterminals
  base_covers := P.base_covers
  arities := P.arities
  exposingTransport := P.exposingTransport
  startWord_positive := E.startWord_positive

/-- Convert the core data plus start-word evidence to rule-witness transport. -/
def toRuleWitnessTransport
    (P : TrimmedPresentationExposingTransportCoreData D)
    (E : TrimmedPresentationStartWordEvidence D) :
    TrimmedPresentationRuleWitnessTransport D P.arities :=
  (P.withStartWord E).toRuleWitnessTransport

/-- Convert the core data plus start-word evidence to grammar-rule transport
data. -/
def toGrammarRuleTransportData
    (P : TrimmedPresentationExposingTransportCoreData D)
    (E : TrimmedPresentationStartWordEvidence D) :
    TrimmedPresentationGrammarRuleTransportData D :=
  (P.withStartWord E).toGrammarRuleTransportData

/-- The finite sample produced by the core data plus start-word evidence. -/
def sample
    (P : TrimmedPresentationExposingTransportCoreData D)
    (E : TrimmedPresentationStartWordEvidence D) :
    Finset (Word α) :=
  (P.withStartWord E).sample

/-- The produced sample is positive. -/
theorem sample_positive
    (P : TrimmedPresentationExposingTransportCoreData D)
    (E : TrimmedPresentationStartWordEvidence D) :
    (P.sample E : Set (Word α)) ⊆ G.StringLanguage :=
  (P.withStartWord E).sample_positive

/-- The produced sample contains all required witness words. -/
theorem contains_witnesses
    (P : TrimmedPresentationExposingTransportCoreData D)
    (E : TrimmedPresentationStartWordEvidence D) :
    TrimmedPresentationWitnessWordSet D ⊆
      (P.sample E : Set (Word α)) :=
  (P.withStartWord E).contains_witnesses

/-- Convert to final reachable data after adding start-word evidence and the
remaining global assumptions. -/
def toFinalReachableData
    (P : TrimmedPresentationExposingTransportCoreData D)
    (E : TrimmedPresentationStartWordEvidence D)
    (U : NamedContextSplicingConstructor α)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    FinalReachableData G (P.sample E) obs f :=
  (P.withStartWord E).toFinalReachableData U hfan hL

/-- The produced sample is a characteristic sample for the reachable learner. -/
theorem characteristic_sample
    (P : TrimmedPresentationExposingTransportCoreData D)
    (E : TrimmedPresentationStartWordEvidence D)
    (U : NamedContextSplicingConstructor α)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    CharacteristicSample
      (reachableHypLanguage obs f)
      (reachableSampleLearner (α := α))
      (P.sample E)
      G.StringLanguage :=
  (P.withStartWord E).characteristic_sample U hfan hL

/-- Eventual prefix-exact reconstruction from core exposing-transport data plus
start-word evidence. -/
theorem prefix_exact_eventually
    (P : TrimmedPresentationExposingTransportCoreData D)
    (E : TrimmedPresentationStartWordEvidence D)
    (U : NamedContextSplicingConstructor α)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    ∀ Ttxt : TextFor G.StringLanguage,
      ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
        ReachableSampleStringLanguage (Ttxt.prefixSample n) obs f =
          G.StringLanguage :=
  (P.withStartWord E).prefix_exact_eventually U hfan hL

/-- Reachable Gold identification from core exposing-transport data plus
start-word evidence. -/
theorem identifies_from_positive_text
    (P : TrimmedPresentationExposingTransportCoreData D)
    (E : TrimmedPresentationStartWordEvidence D)
    (U : NamedContextSplicingConstructor α)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    ∀ Ttxt : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        Ttxt :=
  (P.withStartWord E).identifies_from_positive_text U hfan hL

end TrimmedPresentationExposingTransportCoreData

end ExposingTransportCoreData


section MainTheoremsFromExposingTransportCoreData

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}
variable {f : Nat}
variable {T : TrimmedOutputTypePresentation G obs}
variable {D : TrimmedPresentationPreCoreData T f}

/-- Stable top-level reachable identification theorem from core exposing
transport data plus start-word evidence. -/
theorem trimmed_exposing_core_reachable_identification
    (P : TrimmedPresentationExposingTransportCoreData D)
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

/-- Stable top-level prefix-exact theorem from core exposing transport data plus
start-word evidence. -/
theorem trimmed_exposing_core_reachable_prefix_exact
    (P : TrimmedPresentationExposingTransportCoreData D)
    (E : TrimmedPresentationStartWordEvidence D)
    (U : NamedContextSplicingConstructor α)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    ∀ Ttxt : TextFor G.StringLanguage,
      ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
        ReachableSampleStringLanguage (Ttxt.prefixSample n) obs f =
          G.StringLanguage :=
  P.prefix_exact_eventually E U hfan hL

end MainTheoremsFromExposingTransportCoreData

end MCFG
