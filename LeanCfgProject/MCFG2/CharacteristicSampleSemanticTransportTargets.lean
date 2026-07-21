/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG.CharacteristicSampleSemanticConstructionTargetLevels

/-!
# CharacteristicSampleSemanticTransportTargets.lean

Eighty-second clean Lean experiment for the fixed-observation MCFG project.

The previous files named semantic construction targets using already-packaged
core data such as

```lean
TrimmedPresentationAnchorCommonContextCoreData D
```

This file moves one step closer to the actual construction.  It gives target
records where the finite-cover and arity information is supplied by the
`TrimmedPresentationGrammarRuleBuilder`, while the semantic part is supplied
only as transport evidence:

* `TrimmedPresentationAnchorCommonContextTransport D`;
* `TrimmedPresentationExposingContextTransport D`.

Thus the common-context target now has the shape:

```text
GrammarRuleBuilder
+ AnchorCommonContextTransport
+ splicing/fanout/promise
⇒ reachable identification.
```

and the exposing target has the shape:

```text
GrammarRuleBuilder
+ ExposingContextTransport
+ splicing/fanout/promise
⇒ reachable identification.
```

No new semantic theorem is proved here; this file only assembles previously
verified interfaces into more convenient construction targets.

No theorem here uses `sorry`.
-/

namespace MCFG

universe u v w

section GrammarBuilderCommonTransportTarget

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}
variable {f : Nat}
variable {T : TrimmedOutputTypePresentation G obs}

/-- A semantic construction target where the sample data come from a
grammar-rule builder and the semantic transport is supplied as anchor
common-context transport.

This removes the need to separately provide a full
`TrimmedPresentationAnchorCommonContextCoreData`: the finite cover and arity
selectors are inherited from the builder. -/
structure TrimmedPresentationGrammarBuilderCommonTransportTarget
    (D : TrimmedPresentationPreCoreData T f) where
  builder : TrimmedPresentationGrammarRuleBuilder D
  commonTransport : TrimmedPresentationAnchorCommonContextTransport D
  splicingConstructor : NamedContextSplicingConstructor α
  fanout : G.FanoutAtMost f
  promise : FixedNamedTupleSubstitutable f obs G.StringLanguage

namespace TrimmedPresentationGrammarBuilderCommonTransportTarget

variable {D : TrimmedPresentationPreCoreData T f}

/-- Arity selectors inherited from the grammar-rule builder. -/
def arities
    (C : TrimmedPresentationGrammarBuilderCommonTransportTarget D) :
    TrimmedPresentationRuleAritySelectors D where
  terminal_arity := C.builder.terminal_arity
  start_arity := C.builder.start_arity

/-- Build anchor common-context core data from the builder's finite cover and
arity selectors. -/
def toAnchorCommonContextCoreData
    (C : TrimmedPresentationGrammarBuilderCommonTransportTarget D) :
    TrimmedPresentationAnchorCommonContextCoreData D where
  baseNonterminals := C.builder.baseNonterminals
  base_covers := C.builder.base_covers
  arities := C.arities
  commonTransport := C.commonTransport

/-- Convert to the already-established grammar-builder common-context target. -/
def toGrammarBuilderCommonContextTarget
    (C : TrimmedPresentationGrammarBuilderCommonTransportTarget D) :
    TrimmedPresentationGrammarBuilderCommonContextTarget D where
  builder := C.builder
  commonData := C.toAnchorCommonContextCoreData
  splicingConstructor := C.splicingConstructor
  fanout := C.fanout
  promise := C.promise

/-- Convert to the anchor common-context endpoint. -/
def toAnchorCommonContextCoreEndpoint
    (C : TrimmedPresentationGrammarBuilderCommonTransportTarget D) :
    TrimmedPresentationAnchorCommonContextCoreEndpoint D where
  coreData := C.toAnchorCommonContextCoreData
  startEvidence := C.builder.toGrammarRuleData.startWord_positive
  splicingConstructor := C.splicingConstructor
  fanout := C.fanout
  promise := C.promise

/-- Convert to common-context transport obligations. -/
def toCommonContextTransportObligations
    (C : TrimmedPresentationGrammarBuilderCommonTransportTarget D) :
    TrimmedPresentationCommonContextTransportObligations D :=
  C.toGrammarBuilderCommonContextTarget.toCommonContextTransportObligations

/-- Convert to exposing-transport obligations through the common-context route. -/
def toExposingTransportObligations
    (C : TrimmedPresentationGrammarBuilderCommonTransportTarget D) :
    TrimmedPresentationExposingTransportObligations D :=
  C.toGrammarBuilderCommonContextTarget.toExposingTransportObligations

/-- The finite sample produced by the target. -/
def sample
    (C : TrimmedPresentationGrammarBuilderCommonTransportTarget D) :
    Finset (Word α) :=
  C.toGrammarBuilderCommonContextTarget.sample

/-- The finite sample is positive. -/
theorem sample_positive
    (C : TrimmedPresentationGrammarBuilderCommonTransportTarget D) :
    (C.sample : Set (Word α)) ⊆ G.StringLanguage :=
  C.toGrammarBuilderCommonContextTarget.sample_positive

/-- The finite sample contains all required witness words. -/
theorem contains_witnesses
    (C : TrimmedPresentationGrammarBuilderCommonTransportTarget D) :
    TrimmedPresentationWitnessWordSet D ⊆
      (C.sample : Set (Word α)) :=
  C.toGrammarBuilderCommonContextTarget.contains_witnesses

/-- Convert directly to final reachable data. -/
def toFinalReachableData
    (C : TrimmedPresentationGrammarBuilderCommonTransportTarget D) :
    FinalReachableData G C.sample obs f :=
  C.toGrammarBuilderCommonContextTarget.toFinalReachableData

/-- The produced sample is a characteristic sample for the reachable learner. -/
theorem characteristic_sample
    (C : TrimmedPresentationGrammarBuilderCommonTransportTarget D) :
    CharacteristicSample
      (reachableHypLanguage obs f)
      (reachableSampleLearner (α := α))
      C.sample
      G.StringLanguage :=
  C.toGrammarBuilderCommonContextTarget.characteristic_sample

/-- Exact reconstruction for every positive finite superset of the produced
sample. -/
theorem exact_for_positive_superset
    (C : TrimmedPresentationGrammarBuilderCommonTransportTarget D)
    {K : Finset (Word α)}
    (hCK : (C.sample : Set (Word α)) ⊆ (K : Set (Word α)))
    (hKpos : (K : Set (Word α)) ⊆ G.StringLanguage) :
    ReachableSampleStringLanguage K obs f = G.StringLanguage :=
  C.toGrammarBuilderCommonContextTarget.exact_for_positive_superset hCK hKpos

/-- Eventual prefix-exact reconstruction. -/
theorem prefix_exact_eventually
    (C : TrimmedPresentationGrammarBuilderCommonTransportTarget D) :
    ∀ Ttxt : TextFor G.StringLanguage,
      ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
        ReachableSampleStringLanguage (Ttxt.prefixSample n) obs f =
          G.StringLanguage :=
  C.toGrammarBuilderCommonContextTarget.prefix_exact_eventually

/-- Reachable Gold identification. -/
theorem identifies_from_positive_text
    (C : TrimmedPresentationGrammarBuilderCommonTransportTarget D) :
    ∀ Ttxt : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        Ttxt :=
  C.toGrammarBuilderCommonContextTarget.identifies_from_positive_text

/-- Pointwise eventual correctness on one positive text. -/
theorem eventually_correct_on_text
    (C : TrimmedPresentationGrammarBuilderCommonTransportTarget D)
    (Ttxt : TextFor G.StringLanguage) :
    EventuallyCorrectOnText
      (reachableHypLanguage obs f)
      (reachableSampleLearner (α := α))
      Ttxt :=
  C.identifies_from_positive_text Ttxt

end TrimmedPresentationGrammarBuilderCommonTransportTarget

end GrammarBuilderCommonTransportTarget


section GrammarBuilderExposingTransportTarget

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}
variable {f : Nat}
variable {T : TrimmedOutputTypePresentation G obs}

/-- A semantic construction target where the sample data come from a
grammar-rule builder and the semantic transport is supplied directly as
exposing-context transport. -/
structure TrimmedPresentationGrammarBuilderExposingTransportTarget
    (D : TrimmedPresentationPreCoreData T f) where
  builder : TrimmedPresentationGrammarRuleBuilder D
  exposingTransport : TrimmedPresentationExposingContextTransport D
  splicingConstructor : NamedContextSplicingConstructor α
  fanout : G.FanoutAtMost f
  promise : FixedNamedTupleSubstitutable f obs G.StringLanguage

namespace TrimmedPresentationGrammarBuilderExposingTransportTarget

variable {D : TrimmedPresentationPreCoreData T f}

/-- Convert to the already-established grammar-builder exposing target. -/
def toGrammarBuilderExposingTarget
    (C : TrimmedPresentationGrammarBuilderExposingTransportTarget D) :
    TrimmedPresentationGrammarBuilderExposingTarget D where
  builder := C.builder
  exposingTransport := C.exposingTransport
  splicingConstructor := C.splicingConstructor
  fanout := C.fanout
  promise := C.promise

/-- Convert to exposing-transport obligations. -/
def toExposingTransportObligations
    (C : TrimmedPresentationGrammarBuilderExposingTransportTarget D) :
    TrimmedPresentationExposingTransportObligations D :=
  C.toGrammarBuilderExposingTarget.toExposingTransportObligations

/-- Convert to grammar-rule transport endpoint. -/
def toGrammarRuleTransportEndpoint
    (C : TrimmedPresentationGrammarBuilderExposingTransportTarget D) :
    TrimmedPresentationGrammarRuleTransportEndpoint D :=
  C.toGrammarBuilderExposingTarget.toGrammarRuleTransportEndpoint

/-- The finite sample produced by the target. -/
def sample
    (C : TrimmedPresentationGrammarBuilderExposingTransportTarget D) :
    Finset (Word α) :=
  C.toGrammarBuilderExposingTarget.sample

/-- The finite sample is positive. -/
theorem sample_positive
    (C : TrimmedPresentationGrammarBuilderExposingTransportTarget D) :
    (C.sample : Set (Word α)) ⊆ G.StringLanguage :=
  C.toGrammarBuilderExposingTarget.sample_positive

/-- The finite sample contains all required witness words. -/
theorem contains_witnesses
    (C : TrimmedPresentationGrammarBuilderExposingTransportTarget D) :
    TrimmedPresentationWitnessWordSet D ⊆
      (C.sample : Set (Word α)) :=
  C.toGrammarBuilderExposingTarget.contains_witnesses

/-- Convert directly to final reachable data. -/
def toFinalReachableData
    (C : TrimmedPresentationGrammarBuilderExposingTransportTarget D) :
    FinalReachableData G C.sample obs f :=
  C.toGrammarBuilderExposingTarget.toFinalReachableData

/-- The produced sample is a characteristic sample for the reachable learner. -/
theorem characteristic_sample
    (C : TrimmedPresentationGrammarBuilderExposingTransportTarget D) :
    CharacteristicSample
      (reachableHypLanguage obs f)
      (reachableSampleLearner (α := α))
      C.sample
      G.StringLanguage :=
  C.toGrammarBuilderExposingTarget.characteristic_sample

/-- Exact reconstruction for every positive finite superset of the produced
sample. -/
theorem exact_for_positive_superset
    (C : TrimmedPresentationGrammarBuilderExposingTransportTarget D)
    {K : Finset (Word α)}
    (hCK : (C.sample : Set (Word α)) ⊆ (K : Set (Word α)))
    (hKpos : (K : Set (Word α)) ⊆ G.StringLanguage) :
    ReachableSampleStringLanguage K obs f = G.StringLanguage :=
  C.toGrammarBuilderExposingTarget.exact_for_positive_superset hCK hKpos

/-- Eventual prefix-exact reconstruction. -/
theorem prefix_exact_eventually
    (C : TrimmedPresentationGrammarBuilderExposingTransportTarget D) :
    ∀ Ttxt : TextFor G.StringLanguage,
      ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
        ReachableSampleStringLanguage (Ttxt.prefixSample n) obs f =
          G.StringLanguage :=
  C.toGrammarBuilderExposingTarget.prefix_exact_eventually

/-- Reachable Gold identification. -/
theorem identifies_from_positive_text
    (C : TrimmedPresentationGrammarBuilderExposingTransportTarget D) :
    ∀ Ttxt : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        Ttxt :=
  C.toGrammarBuilderExposingTarget.identifies_from_positive_text

/-- Pointwise eventual correctness on one positive text. -/
theorem eventually_correct_on_text
    (C : TrimmedPresentationGrammarBuilderExposingTransportTarget D)
    (Ttxt : TextFor G.StringLanguage) :
    EventuallyCorrectOnText
      (reachableHypLanguage obs f)
      (reachableSampleLearner (α := α))
      Ttxt :=
  C.identifies_from_positive_text Ttxt

end TrimmedPresentationGrammarBuilderExposingTransportTarget

end GrammarBuilderExposingTransportTarget


section MainTheoremsFromSemanticTransportTargets

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}
variable {f : Nat}
variable {T : TrimmedOutputTypePresentation G obs}
variable {D : TrimmedPresentationPreCoreData T f}

/-- Stable theorem name for the grammar-builder + anchor common-context
transport target. -/
theorem trimmed_grammar_builder_common_transport_target_reachable_identification
    (C : TrimmedPresentationGrammarBuilderCommonTransportTarget D) :
    ∀ Ttxt : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        Ttxt :=
  C.identifies_from_positive_text

/-- Prefix-exact theorem for the grammar-builder + anchor common-context
transport target. -/
theorem trimmed_grammar_builder_common_transport_target_prefix_exact
    (C : TrimmedPresentationGrammarBuilderCommonTransportTarget D) :
    ∀ Ttxt : TextFor G.StringLanguage,
      ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
        ReachableSampleStringLanguage (Ttxt.prefixSample n) obs f =
          G.StringLanguage :=
  C.prefix_exact_eventually

/-- Positive finite-superset exactness theorem for the grammar-builder + anchor
common-context transport target. -/
theorem trimmed_grammar_builder_common_transport_target_exact_for_positive_superset
    (C : TrimmedPresentationGrammarBuilderCommonTransportTarget D)
    {K : Finset (Word α)}
    (hCK : (C.sample : Set (Word α)) ⊆ (K : Set (Word α)))
    (hKpos : (K : Set (Word α)) ⊆ G.StringLanguage) :
    ReachableSampleStringLanguage K obs f = G.StringLanguage :=
  C.exact_for_positive_superset hCK hKpos

/-- Stable theorem name for the grammar-builder + exposing-context transport
target. -/
theorem trimmed_grammar_builder_exposing_transport_target_reachable_identification
    (C : TrimmedPresentationGrammarBuilderExposingTransportTarget D) :
    ∀ Ttxt : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        Ttxt :=
  C.identifies_from_positive_text

/-- Prefix-exact theorem for the grammar-builder + exposing-context transport
target. -/
theorem trimmed_grammar_builder_exposing_transport_target_prefix_exact
    (C : TrimmedPresentationGrammarBuilderExposingTransportTarget D) :
    ∀ Ttxt : TextFor G.StringLanguage,
      ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
        ReachableSampleStringLanguage (Ttxt.prefixSample n) obs f =
          G.StringLanguage :=
  C.prefix_exact_eventually

/-- Positive finite-superset exactness theorem for the grammar-builder +
exposing-context transport target. -/
theorem trimmed_grammar_builder_exposing_transport_target_exact_for_positive_superset
    (C : TrimmedPresentationGrammarBuilderExposingTransportTarget D)
    {K : Finset (Word α)}
    (hCK : (C.sample : Set (Word α)) ⊆ (K : Set (Word α)))
    (hKpos : (K : Set (Word α)) ⊆ G.StringLanguage) :
    ReachableSampleStringLanguage K obs f = G.StringLanguage :=
  C.exact_for_positive_superset hCK hKpos

end MainTheoremsFromSemanticTransportTargets

end MCFG
