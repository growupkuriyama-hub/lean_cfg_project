/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG2.CharacteristicSampleContextTransport

/-!
# CharacteristicSampleExposingTransport.lean

Sixty-first clean Lean experiment for the fixed-observation MCFG project.

`CharacteristicSampleContextTransport.lean` introduced a strong local transport
principle:

```text
same named context
+
same observation type
+
acceptance of one tuple
⇒ acceptance of the other tuple.
```

For the characteristic-sample construction we do not need such a principle for
all named contexts.  We only need it for the exposing contexts already stored
in the trimmed-presentation pre-core:

```lean
D.expose A
```

This file introduces that weaker interface:

```lean
TrimmedPresentationExposingContextTransport
```

and proves that it is sufficient to build
`TrimmedPresentationRuleWitnessTransport`, hence the full rule-transport final
route.

No theorem here uses `sorry`.
-/

namespace MCFG

universe u v w

section ExposingContextTransport

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}
variable {f : Nat}
variable {T : TrimmedOutputTypePresentation G obs}

/-- Transport only for the exposing contexts of a trimmed-presentation
pre-core.

For every base nonterminal `A`, if a tuple has the same observed type as the
anchor of `A`, then the exposing context of `A` also accepts that tuple. -/
structure TrimmedPresentationExposingContextTransport
    (D : TrimmedPresentationPreCoreData T f) where
  transport :
    ∀ (A : N)
      (x : Tuple α (G.arity A)),
        tupleType obs (D.anchor A) = tupleType obs x →
        namedFill (G.arity A) (D.expose A) x ∈ G.StringLanguage

namespace TrimmedPresentationExposingContextTransport

variable {D : TrimmedPresentationPreCoreData T f}

/-- Same-context transport implies exposing-context transport. -/
def ofSameContextTransport
    (C : TrimmedPresentationSameContextTransport D) :
    TrimmedPresentationExposingContextTransport D where
  transport := by
    intro A x htype
    exact C.transport
      (D.expose A)
      (D.anchor A)
      x
      htype
      (D.anchorWitnessWord_mem_target A)

/-- Direct accessor for acceptance in the exposing context. -/
theorem accepts_of_type_eq
    (E : TrimmedPresentationExposingContextTransport D)
    (A : N)
    (x : Tuple α (G.arity A))
    (htype : tupleType obs (D.anchor A) = tupleType obs x) :
    namedFill (G.arity A) (D.expose A) x ∈ G.StringLanguage :=
  E.transport A x htype

/-- Terminal witness positivity follows from exposing-context transport and the
terminal type equality stored in the pre-core. -/
theorem terminal_positive
    (E : TrimmedPresentationExposingContextTransport D)
    (A : TrimmedPresentationRuleAritySelectors D)
    (ρ : TerminalRule N α)
    (hρ : ρ ∈ G.terminalRules) :
    D.terminalWitnessWord ρ (A.terminal_arity ρ hρ) ∈
      G.StringLanguage :=
  E.transport
    ρ.lhs
    (castTuple (A.terminal_arity ρ hρ).symm ρ.outputTuple)
    (D.terminal_type ρ hρ (A.terminal_arity ρ hρ))

/-- Binary witness positivity follows from exposing-context transport and the
binary type equality stored in the pre-core. -/
theorem binary_positive
    (E : TrimmedPresentationExposingContextTransport D)
    (ρ : BinaryRule N α G.arity)
    (hρ : ρ ∈ G.binaryRules) :
    D.binaryWitnessWord ρ ∈ G.StringLanguage :=
  E.transport
    ρ.lhs
    (ρ.apply (D.anchor ρ.left) (D.anchor ρ.right))
    (D.binary_type ρ hρ)

/-- Start-rule witness positivity follows from exposing-context transport and
the start type equality stored in the pre-core. -/
theorem start_positive
    (E : TrimmedPresentationExposingContextTransport D)
    (A : TrimmedPresentationRuleAritySelectors D)
    (ρ : StartRule N)
    (hρ : ρ ∈ G.startRules) :
    D.startWitnessWord ρ (A.start_arity ρ hρ) ∈
      G.StringLanguage :=
  E.transport
    G.start
    (castTuple (A.start_arity ρ hρ) (D.anchor ρ.child))
    (D.start_type ρ hρ (A.start_arity ρ hρ))

/-- Build the remaining rule-witness transport package from exposing-context
transport and positivity of the distinguished start word. -/
def toRuleWitnessTransport
    (E : TrimmedPresentationExposingContextTransport D)
    (A : TrimmedPresentationRuleAritySelectors D)
    (hstart : D.startWord ∈ G.StringLanguage) :
    TrimmedPresentationRuleWitnessTransport D A where
  terminal_positive := E.terminal_positive A
  binary_positive := E.binary_positive
  start_positive := E.start_positive A
  startWord_positive := hstart

end TrimmedPresentationExposingContextTransport

end ExposingContextTransport


section ExposingTransportData

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}
variable {f : Nat}
variable {T : TrimmedOutputTypePresentation G obs}

/-- Data for the characteristic-sample route using transport only for the
trimmed exposing contexts. -/
structure TrimmedPresentationExposingTransportData
    (D : TrimmedPresentationPreCoreData T f) where
  baseNonterminals : Finset N
  base_covers :
    ∀ A : N, A ∈ baseNonterminals

  arities : TrimmedPresentationRuleAritySelectors D
  exposingTransport : TrimmedPresentationExposingContextTransport D
  startWord_positive :
    D.startWord ∈ G.StringLanguage

namespace TrimmedPresentationExposingTransportData

variable {D : TrimmedPresentationPreCoreData T f}

/-- Convert exposing-context transport data to the rule-witness transport
package. -/
def toRuleWitnessTransport
    (P : TrimmedPresentationExposingTransportData D) :
    TrimmedPresentationRuleWitnessTransport D P.arities :=
  P.exposingTransport.toRuleWitnessTransport P.arities P.startWord_positive

/-- Convert exposing-context transport data to grammar-rule transport data. -/
def toGrammarRuleTransportData
    (P : TrimmedPresentationExposingTransportData D) :
    TrimmedPresentationGrammarRuleTransportData D where
  baseNonterminals := P.baseNonterminals
  base_covers := P.base_covers
  arities := P.arities
  transport := P.toRuleWitnessTransport

/-- Build exposing-context transport data from the stronger same-context
transport data. -/
def ofContextTransportData
    (P : TrimmedPresentationContextTransportData D) :
    TrimmedPresentationExposingTransportData D where
  baseNonterminals := P.baseNonterminals
  base_covers := P.base_covers
  arities := P.arities
  exposingTransport :=
    TrimmedPresentationExposingContextTransport.ofSameContextTransport
      P.contextTransport
  startWord_positive := P.startWord_positive

/-- The finite sample produced by exposing-context transport data. -/
def sample
    (P : TrimmedPresentationExposingTransportData D) :
    Finset (Word α) :=
  P.toGrammarRuleTransportData.sample

/-- The produced sample is positive. -/
theorem sample_positive
    (P : TrimmedPresentationExposingTransportData D) :
    (P.sample : Set (Word α)) ⊆ G.StringLanguage :=
  P.toGrammarRuleTransportData.sample_positive

/-- The produced sample contains all required witness words. -/
theorem contains_witnesses
    (P : TrimmedPresentationExposingTransportData D) :
    TrimmedPresentationWitnessWordSet D ⊆
      (P.sample : Set (Word α)) :=
  P.toGrammarRuleTransportData.contains_witnesses

/-- Convert to the final rule-transport wrapper after adding the remaining
splicing constructor and global assumptions. -/
def toRuleTransportFinalData
    (P : TrimmedPresentationExposingTransportData D)
    (U : NamedContextSplicingConstructor α)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    TrimmedPresentationRuleTransportFinalData D where
  transportData := P.toGrammarRuleTransportData
  splicingConstructor := U
  fanout := hfan
  promise := hL

/-- Convert directly to final reachable data. -/
def toFinalReachableData
    (P : TrimmedPresentationExposingTransportData D)
    (U : NamedContextSplicingConstructor α)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    FinalReachableData G P.sample obs f :=
  (P.toRuleTransportFinalData U hfan hL).toFinalReachableData

/-- The produced sample is a characteristic sample for the reachable learner. -/
theorem characteristic_sample
    (P : TrimmedPresentationExposingTransportData D)
    (U : NamedContextSplicingConstructor α)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    CharacteristicSample
      (reachableHypLanguage obs f)
      (reachableSampleLearner (α := α))
      P.sample
      G.StringLanguage :=
  (P.toRuleTransportFinalData U hfan hL).characteristic_sample

/-- Eventual prefix-exact reconstruction from exposing-context transport data. -/
theorem prefix_exact_eventually
    (P : TrimmedPresentationExposingTransportData D)
    (U : NamedContextSplicingConstructor α)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    ∀ Ttxt : TextFor G.StringLanguage,
      ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
        ReachableSampleStringLanguage (Ttxt.prefixSample n) obs f =
          G.StringLanguage :=
  (P.toRuleTransportFinalData U hfan hL).prefix_exact_eventually

/-- Reachable Gold identification from exposing-context transport data. -/
theorem identifies_from_positive_text
    (P : TrimmedPresentationExposingTransportData D)
    (U : NamedContextSplicingConstructor α)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    ∀ Ttxt : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        Ttxt :=
  (P.toRuleTransportFinalData U hfan hL).identifies_from_positive_text

end TrimmedPresentationExposingTransportData

end ExposingTransportData


section MainTheoremsFromExposingTransportData

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}
variable {f : Nat}
variable {T : TrimmedOutputTypePresentation G obs}
variable {D : TrimmedPresentationPreCoreData T f}

/-- Stable top-level reachable identification theorem from exposing-context
transport data. -/
theorem trimmed_exposing_transport_reachable_identification
    (P : TrimmedPresentationExposingTransportData D)
    (U : NamedContextSplicingConstructor α)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    ∀ Ttxt : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        Ttxt :=
  P.identifies_from_positive_text U hfan hL

/-- Stable top-level prefix-exact theorem from exposing-context transport data. -/
theorem trimmed_exposing_transport_reachable_prefix_exact
    (P : TrimmedPresentationExposingTransportData D)
    (U : NamedContextSplicingConstructor α)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    ∀ Ttxt : TextFor G.StringLanguage,
      ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
        ReachableSampleStringLanguage (Ttxt.prefixSample n) obs f =
          G.StringLanguage :=
  P.prefix_exact_eventually U hfan hL

end MainTheoremsFromExposingTransportData

end MCFG
