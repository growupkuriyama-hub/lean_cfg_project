/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG.CharacteristicSampleSemanticTransportTargetLevels

/-!
# CharacteristicSampleSameContextTransportTargets.lean

Eighty-fourth clean Lean experiment for the fixed-observation MCFG project.

The preceding files introduced targets based on anchor common-context transport
and exposing-context transport.  This file adds the stronger same-context
transport target at the grammar-rule-builder level.

The new target has the shape:

```text
GrammarRuleBuilder
+ SameContextTransport
+ splicing/fanout/promise
⇒ reachable identification.
```

The same-context transport assumption is stronger than exposing-context
transport, but it is useful as a debugging and proof-search target: once it is
available, the already-verified same-context core route gives the final
reachable identification theorem.

No new semantic principle is introduced here.  This file only assembles the
existing same-context core interface using the finite cover and arity selectors
from the grammar-rule builder.

No theorem here uses `sorry`.
-/

namespace MCFG

universe u v w

section GrammarBuilderSameContextTransportTarget

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}
variable {f : Nat}
variable {T : TrimmedOutputTypePresentation G obs}

/-- Grammar-rule-builder target using the stronger same-context transport
assumption. -/
structure TrimmedPresentationGrammarBuilderSameContextTransportTarget
    (D : TrimmedPresentationPreCoreData T f) where
  builder : TrimmedPresentationGrammarRuleBuilder D
  sameContextTransport : TrimmedPresentationSameContextTransport D
  splicingConstructor : NamedContextSplicingConstructor α
  fanout : G.FanoutAtMost f
  promise : FixedNamedTupleSubstitutable f obs G.StringLanguage

namespace TrimmedPresentationGrammarBuilderSameContextTransportTarget

variable {D : TrimmedPresentationPreCoreData T f}

/-- Arity selectors inherited from the grammar-rule builder. -/
def arities
    (C : TrimmedPresentationGrammarBuilderSameContextTransportTarget D) :
    TrimmedPresentationRuleAritySelectors D where
  terminal_arity := C.builder.terminal_arity
  start_arity := C.builder.start_arity

/-- Build same-context core data from the builder's finite cover and arity
selectors. -/
def toSameContextCoreData
    (C : TrimmedPresentationGrammarBuilderSameContextTransportTarget D) :
    TrimmedPresentationSameContextCoreData D where
  baseNonterminals := C.builder.baseNonterminals
  base_covers := C.builder.base_covers
  arities := C.arities
  sameContextTransport := C.sameContextTransport

/-- The start-word evidence supplied by the grammar-rule builder route. -/
def startEvidence
    (C : TrimmedPresentationGrammarBuilderSameContextTransportTarget D) :
    TrimmedPresentationStartWordEvidence D :=
  C.builder.toGrammarRuleData.startWord_positive

/-- Convert to the same-context core endpoint. -/
def toSameContextCoreEndpoint
    (C : TrimmedPresentationGrammarBuilderSameContextTransportTarget D) :
    TrimmedPresentationSameContextCoreEndpoint D where
  coreData := C.toSameContextCoreData
  startEvidence := C.startEvidence
  splicingConstructor := C.splicingConstructor
  fanout := C.fanout
  promise := C.promise

/-- Convert to exposing-core final endpoint through the same-context route. -/
def toExposingCoreFinalEndpoint
    (C : TrimmedPresentationGrammarBuilderSameContextTransportTarget D) :
    TrimmedPresentationExposingCoreFinalEndpoint D :=
  C.toSameContextCoreEndpoint.toExposingCoreFinalEndpoint

/-- Convert to exposing-transport obligations through the same-context route. -/
def toExposingTransportObligations
    (C : TrimmedPresentationGrammarBuilderSameContextTransportTarget D) :
    TrimmedPresentationExposingTransportObligations D :=
  C.toSameContextCoreEndpoint.toExposingTransportObligations

/-- Convert to grammar-rule transport endpoint. -/
def toGrammarRuleTransportEndpoint
    (C : TrimmedPresentationGrammarBuilderSameContextTransportTarget D) :
    TrimmedPresentationGrammarRuleTransportEndpoint D :=
  C.toSameContextCoreEndpoint.toGrammarRuleTransportEndpoint

/-- Convert to rule-transport endpoint. -/
def toRuleTransportEndpoint
    (C : TrimmedPresentationGrammarBuilderSameContextTransportTarget D) :
    TrimmedPresentationRuleTransportEndpoint D :=
  C.toSameContextCoreEndpoint.toRuleTransportEndpoint

/-- The finite sample produced by the same-context target. -/
def sample
    (C : TrimmedPresentationGrammarBuilderSameContextTransportTarget D) :
    Finset (Word α) :=
  C.toSameContextCoreEndpoint.sample

/-- The finite sample is positive. -/
theorem sample_positive
    (C : TrimmedPresentationGrammarBuilderSameContextTransportTarget D) :
    (C.sample : Set (Word α)) ⊆ G.StringLanguage :=
  C.toSameContextCoreEndpoint.sample_positive

/-- The finite sample contains all required witness words. -/
theorem contains_witnesses
    (C : TrimmedPresentationGrammarBuilderSameContextTransportTarget D) :
    TrimmedPresentationWitnessWordSet D ⊆
      (C.sample : Set (Word α)) :=
  C.toSameContextCoreEndpoint.contains_witnesses

/-- Convert directly to final reachable data. -/
def toFinalReachableData
    (C : TrimmedPresentationGrammarBuilderSameContextTransportTarget D) :
    FinalReachableData G C.sample obs f :=
  C.toSameContextCoreEndpoint.toFinalReachableData

/-- The produced sample is a characteristic sample for the reachable learner. -/
theorem characteristic_sample
    (C : TrimmedPresentationGrammarBuilderSameContextTransportTarget D) :
    CharacteristicSample
      (reachableHypLanguage obs f)
      (reachableSampleLearner (α := α))
      C.sample
      G.StringLanguage :=
  C.toSameContextCoreEndpoint.characteristic_sample

/-- Exact reconstruction for every positive finite superset of the produced
sample. -/
theorem exact_for_positive_superset
    (C : TrimmedPresentationGrammarBuilderSameContextTransportTarget D)
    {K : Finset (Word α)}
    (hCK : (C.sample : Set (Word α)) ⊆ (K : Set (Word α)))
    (hKpos : (K : Set (Word α)) ⊆ G.StringLanguage) :
    ReachableSampleStringLanguage K obs f = G.StringLanguage :=
  C.toSameContextCoreEndpoint.exact_for_positive_superset hCK hKpos

/-- Exact reconstruction at a positive-text prefix containing the produced
sample. -/
theorem exact_at_seen_prefix
    (C : TrimmedPresentationGrammarBuilderSameContextTransportTarget D)
    (Ttxt : TextFor G.StringLanguage)
    {n : Nat}
    (hseen : (C.sample : Set (Word α)) ⊆
      (Ttxt.prefixSample n : Set (Word α))) :
    ReachableSampleStringLanguage (Ttxt.prefixSample n) obs f =
      G.StringLanguage :=
  C.toSameContextCoreEndpoint.exact_at_seen_prefix Ttxt hseen

/-- Eventual prefix-exact reconstruction. -/
theorem prefix_exact_eventually
    (C : TrimmedPresentationGrammarBuilderSameContextTransportTarget D) :
    ∀ Ttxt : TextFor G.StringLanguage,
      ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
        ReachableSampleStringLanguage (Ttxt.prefixSample n) obs f =
          G.StringLanguage :=
  C.toSameContextCoreEndpoint.prefix_exact_eventually

/-- Reachable Gold identification. -/
theorem identifies_from_positive_text
    (C : TrimmedPresentationGrammarBuilderSameContextTransportTarget D) :
    ∀ Ttxt : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        Ttxt :=
  C.toSameContextCoreEndpoint.identifies_from_positive_text

/-- Pointwise eventual correctness on one positive text. -/
theorem eventually_correct_on_text
    (C : TrimmedPresentationGrammarBuilderSameContextTransportTarget D)
    (Ttxt : TextFor G.StringLanguage) :
    EventuallyCorrectOnText
      (reachableHypLanguage obs f)
      (reachableSampleLearner (α := α))
      Ttxt :=
  C.identifies_from_positive_text Ttxt

end TrimmedPresentationGrammarBuilderSameContextTransportTarget

end GrammarBuilderSameContextTransportTarget


section MainTheoremsFromSameContextTransportTarget

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}
variable {f : Nat}
variable {T : TrimmedOutputTypePresentation G obs}
variable {D : TrimmedPresentationPreCoreData T f}

/-- Stable theorem name for the grammar-builder + same-context transport
target. -/
theorem trimmed_grammar_builder_same_context_transport_target_reachable_identification
    (C : TrimmedPresentationGrammarBuilderSameContextTransportTarget D) :
    ∀ Ttxt : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        Ttxt :=
  C.identifies_from_positive_text

/-- Prefix-exact theorem for the grammar-builder + same-context transport
target. -/
theorem trimmed_grammar_builder_same_context_transport_target_prefix_exact
    (C : TrimmedPresentationGrammarBuilderSameContextTransportTarget D) :
    ∀ Ttxt : TextFor G.StringLanguage,
      ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
        ReachableSampleStringLanguage (Ttxt.prefixSample n) obs f =
          G.StringLanguage :=
  C.prefix_exact_eventually

/-- Positive finite-superset exactness theorem for the grammar-builder +
same-context transport target. -/
theorem trimmed_grammar_builder_same_context_transport_target_exact_for_positive_superset
    (C : TrimmedPresentationGrammarBuilderSameContextTransportTarget D)
    {K : Finset (Word α)}
    (hCK : (C.sample : Set (Word α)) ⊆ (K : Set (Word α)))
    (hKpos : (K : Set (Word α)) ⊆ G.StringLanguage) :
    ReachableSampleStringLanguage K obs f = G.StringLanguage :=
  C.exact_for_positive_superset hCK hKpos

end MainTheoremsFromSameContextTransportTarget

end MCFG
