/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG2.CharacteristicSampleAnchorCommonContext

/-!
# CharacteristicSampleExposingAsCommonContext.lean

Sixty-eighth clean Lean experiment for the fixed-observation MCFG project.

`CharacteristicSampleAnchorCommonContext.lean` introduced a route through a
common accepting named context.

This file records the safest way to supply such common contexts: use the
exposing context itself.

If we already know exposing-context transport,

```lean
TrimmedPresentationExposingContextTransport D
```

then for every base nonterminal `A` and same-type tuple `x`, the context

```lean
D.expose A
```

accepts both `D.anchor A` and `x`.  Hence it is a common accepting context and
can feed the common-context route.

The file therefore gives a reversible-looking bridge between the sharper
exposing-transport interface and the common-context/distributional route.

No theorem here uses `sorry`.
-/

namespace MCFG

universe u v w

section ExposingAsCommonContext

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}
variable {f : Nat}
variable {T : TrimmedOutputTypePresentation G obs}

/-- Exposing-context transport together with positivity of all relevant arities.

The arity positivity is only needed to use the existing
`fixedNamedDistributionalEquivalent_of_common_context` bridge. -/
structure TrimmedPresentationExposingAsCommonContext
    (D : TrimmedPresentationPreCoreData T f) where
  arity_pos :
    ∀ A : N, 0 < G.arity A
  exposingTransport :
    TrimmedPresentationExposingContextTransport D

namespace TrimmedPresentationExposingAsCommonContext

variable {D : TrimmedPresentationPreCoreData T f}

/-- The exposing context itself is a common accepting context. -/
def commonEvidence
    (E : TrimmedPresentationExposingAsCommonContext D)
    (A : N)
    (x : Tuple α (G.arity A))
    (htype : tupleType obs (D.anchor A) = tupleType obs x) :
    TrimmedPresentationAnchorCommonContextEvidence D A x where
  context := D.expose A
  anchor_mem := D.anchorWitnessWord_mem_target A
  target_mem := E.exposingTransport.accepts_of_type_eq A x htype

/-- Exposing-context transport supplies common-context transport by using
`D.expose A` as the common accepting context. -/
def toAnchorCommonContextTransport
    (E : TrimmedPresentationExposingAsCommonContext D) :
    TrimmedPresentationAnchorCommonContextTransport D where
  arity_pos := E.arity_pos
  common := E.commonEvidence

/-- Under fanout and fixed-observation substitutability, exposing-context
transport also supplies anchor distributional transport through the common
context route. -/
def toAnchorDistributionTransport
    (E : TrimmedPresentationExposingAsCommonContext D)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    TrimmedPresentationAnchorDistributionTransport D :=
  E.toAnchorCommonContextTransport.toAnchorDistributionTransport hfan hL

/-- The induced distributional route still yields exposing-context transport. -/
def toExposingContextTransportViaCommon
    (E : TrimmedPresentationExposingAsCommonContext D)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    TrimmedPresentationExposingContextTransport D :=
  E.toAnchorCommonContextTransport.toExposingContextTransport hfan hL

/-- Terminal witness positivity through the common-context route. -/
theorem terminal_positive_via_common
    (E : TrimmedPresentationExposingAsCommonContext D)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage)
    (A : TrimmedPresentationRuleAritySelectors D)
    (ρ : TerminalRule N α)
    (hρ : ρ ∈ G.terminalRules) :
    D.terminalWitnessWord ρ (A.terminal_arity ρ hρ) ∈
      G.StringLanguage :=
  E.toAnchorCommonContextTransport.terminal_positive hfan hL A ρ hρ

/-- Binary witness positivity through the common-context route. -/
theorem binary_positive_via_common
    (E : TrimmedPresentationExposingAsCommonContext D)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage)
    (ρ : BinaryRule N α G.arity)
    (hρ : ρ ∈ G.binaryRules) :
    D.binaryWitnessWord ρ ∈ G.StringLanguage :=
  E.toAnchorCommonContextTransport.binary_positive hfan hL ρ hρ

/-- Start-rule witness positivity through the common-context route. -/
theorem start_positive_via_common
    (E : TrimmedPresentationExposingAsCommonContext D)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage)
    (A : TrimmedPresentationRuleAritySelectors D)
    (ρ : StartRule N)
    (hρ : ρ ∈ G.startRules) :
    D.startWitnessWord ρ (A.start_arity ρ hρ) ∈
      G.StringLanguage :=
  E.toAnchorCommonContextTransport.start_positive hfan hL A ρ hρ

end TrimmedPresentationExposingAsCommonContext

end ExposingAsCommonContext


section ExposingCoreAsCommonContext

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}
variable {f : Nat}
variable {T : TrimmedOutputTypePresentation G obs}

/-- Core exposing-transport data plus arity positivity, viewed as common-context
core data. -/
structure TrimmedPresentationExposingCommonCoreData
    (D : TrimmedPresentationPreCoreData T f) where
  coreData : TrimmedPresentationExposingTransportCoreData D
  arity_pos :
    ∀ A : N, 0 < G.arity A

namespace TrimmedPresentationExposingCommonCoreData

variable {D : TrimmedPresentationPreCoreData T f}

/-- Exposing core data supplies the compact exposing-as-common package. -/
def toExposingAsCommonContext
    (P : TrimmedPresentationExposingCommonCoreData D) :
    TrimmedPresentationExposingAsCommonContext D where
  arity_pos := P.arity_pos
  exposingTransport := P.coreData.exposingTransport

/-- Convert to common-context core data by taking `D.expose A` as the common
context. -/
def toAnchorCommonContextCoreData
    (P : TrimmedPresentationExposingCommonCoreData D) :
    TrimmedPresentationAnchorCommonContextCoreData D where
  baseNonterminals := P.coreData.baseNonterminals
  base_covers := P.coreData.base_covers
  arities := P.coreData.arities
  commonContext := P.toExposingAsCommonContext.toAnchorCommonContextTransport

/-- Convert to anchor-distributional core data after adding fanout and
fixed-observation substitutability. -/
def toAnchorDistributionCoreData
    (P : TrimmedPresentationExposingCommonCoreData D)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    TrimmedPresentationAnchorDistributionCoreData D :=
  P.toAnchorCommonContextCoreData.toAnchorDistributionCoreData hfan hL

/-- Recover the original exposing-transport core data. -/
def toExposingTransportCoreData
    (P : TrimmedPresentationExposingCommonCoreData D) :
    TrimmedPresentationExposingTransportCoreData D :=
  P.coreData

/-- The finite sample produced after adding start-word evidence. -/
def sample
    (P : TrimmedPresentationExposingCommonCoreData D)
    (E : TrimmedPresentationStartWordEvidence D) :
    Finset (Word α) :=
  P.coreData.sample E

/-- The produced finite sample is positive. -/
theorem sample_positive
    (P : TrimmedPresentationExposingCommonCoreData D)
    (E : TrimmedPresentationStartWordEvidence D) :
    (P.sample E : Set (Word α)) ⊆ G.StringLanguage :=
  P.coreData.sample_positive E

/-- The produced finite sample contains all required witness words. -/
theorem contains_witnesses
    (P : TrimmedPresentationExposingCommonCoreData D)
    (E : TrimmedPresentationStartWordEvidence D) :
    TrimmedPresentationWitnessWordSet D ⊆
      (P.sample E : Set (Word α)) :=
  P.coreData.contains_witnesses E

/-- Convert to the separated exposing-core final wrapper. -/
def toExposingCoreFinalData
    (P : TrimmedPresentationExposingCommonCoreData D)
    (E : TrimmedPresentationStartWordEvidence D)
    (U : NamedContextSplicingConstructor α)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    TrimmedPresentationExposingCoreFinalData D where
  coreData := P.coreData
  startEvidence := E
  splicingConstructor := U
  fanout := hfan
  promise := hL

/-- Convert directly to final reachable data. -/
def toFinalReachableData
    (P : TrimmedPresentationExposingCommonCoreData D)
    (E : TrimmedPresentationStartWordEvidence D)
    (U : NamedContextSplicingConstructor α)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    FinalReachableData G (P.sample E) obs f :=
  (P.toExposingCoreFinalData E U hfan hL).toFinalReachableData

/-- The produced sample is a characteristic sample for the reachable learner. -/
theorem characteristic_sample
    (P : TrimmedPresentationExposingCommonCoreData D)
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

/-- Eventual prefix-exact reconstruction from exposing-as-common core data. -/
theorem prefix_exact_eventually
    (P : TrimmedPresentationExposingCommonCoreData D)
    (E : TrimmedPresentationStartWordEvidence D)
    (U : NamedContextSplicingConstructor α)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    ∀ Ttxt : TextFor G.StringLanguage,
      ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
        ReachableSampleStringLanguage (Ttxt.prefixSample n) obs f =
          G.StringLanguage :=
  (P.toExposingCoreFinalData E U hfan hL).prefix_exact_eventually

/-- Reachable Gold identification from exposing-as-common core data. -/
theorem identifies_from_positive_text
    (P : TrimmedPresentationExposingCommonCoreData D)
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

end TrimmedPresentationExposingCommonCoreData

end ExposingCoreAsCommonContext


section MainTheoremsFromExposingAsCommonContext

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}
variable {f : Nat}
variable {T : TrimmedOutputTypePresentation G obs}
variable {D : TrimmedPresentationPreCoreData T f}

/-- Stable top-level reachable identification theorem from exposing-as-common
core data plus start-word evidence. -/
theorem trimmed_exposing_common_core_reachable_identification
    (P : TrimmedPresentationExposingCommonCoreData D)
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

/-- Stable top-level prefix-exact theorem from exposing-as-common core data plus
start-word evidence. -/
theorem trimmed_exposing_common_core_reachable_prefix_exact
    (P : TrimmedPresentationExposingCommonCoreData D)
    (E : TrimmedPresentationStartWordEvidence D)
    (U : NamedContextSplicingConstructor α)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    ∀ Ttxt : TextFor G.StringLanguage,
      ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
        ReachableSampleStringLanguage (Ttxt.prefixSample n) obs f =
          G.StringLanguage :=
  P.prefix_exact_eventually E U hfan hL

end MainTheoremsFromExposingAsCommonContext

end MCFG
