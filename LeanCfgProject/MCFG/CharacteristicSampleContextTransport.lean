/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG.CharacteristicSampleRuleTransportFinal

/-!
# CharacteristicSampleContextTransport.lean

Sixtieth clean Lean experiment for the fixed-observation MCFG project.

`CharacteristicSampleRuleWitnessTransport.lean` isolated the remaining
positivity target for terminal, binary, and start witness words.

This file proves that target from a more local semantic transport principle:

```text
same named context
+
same observation type
+
the context accepts one tuple
⇒ the same context accepts the other tuple.
```

This principle is intentionally stronger than the current global
substitutability promise.  It is a useful intermediate target: later files can
try to prove it for the exposing contexts coming from the trimmed presentation,
or replace it by a more precise exposure-validity statement.

From this local context transport, we build:

```lean
TrimmedPresentationRuleWitnessTransport
```

and therefore the full rule-transport final theorem route.

No theorem here uses `sorry`.
-/

namespace MCFG

universe u v w

section SameContextTransport

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}
variable {f : Nat}
variable {T : TrimmedOutputTypePresentation G obs}

/-- Local same-context transport for the exposing contexts used by a
trimmed-presentation pre-core.

Given two tuples of the same observed type, if a named context accepts one of
them, then it accepts the other. -/
structure TrimmedPresentationSameContextTransport
    (D : TrimmedPresentationPreCoreData T f) where
  transport :
    ∀ {d : Nat}
      (c : NamedSentenceContext α d)
      (x y : Tuple α d),
        tupleType obs x = tupleType obs y →
        namedFill d c x ∈ G.StringLanguage →
        namedFill d c y ∈ G.StringLanguage

namespace TrimmedPresentationSameContextTransport

variable {D : TrimmedPresentationPreCoreData T f}

/-- Transport acceptance across a fixed exposing context. -/
theorem accepts_of_type_eq
    (C : TrimmedPresentationSameContextTransport D)
    {d : Nat}
    (c : NamedSentenceContext α d)
    (x y : Tuple α d)
    (htype : tupleType obs x = tupleType obs y)
    (hx : namedFill d c x ∈ G.StringLanguage) :
    namedFill d c y ∈ G.StringLanguage :=
  C.transport c x y htype hx

/-- Terminal witness positivity follows from same-context transport and the
terminal type equality stored in the pre-core. -/
theorem terminal_positive
    (C : TrimmedPresentationSameContextTransport D)
    (A : TrimmedPresentationRuleAritySelectors D)
    (ρ : TerminalRule N α)
    (hρ : ρ ∈ G.terminalRules) :
    D.terminalWitnessWord ρ (A.terminal_arity ρ hρ) ∈
      G.StringLanguage := by
  exact C.transport
    (D.expose ρ.lhs)
    (D.anchor ρ.lhs)
    (castTuple (A.terminal_arity ρ hρ).symm ρ.outputTuple)
    (D.terminal_type ρ hρ (A.terminal_arity ρ hρ))
    (D.anchorWitnessWord_mem_target ρ.lhs)

/-- Binary witness positivity follows from same-context transport and the
binary type equality stored in the pre-core. -/
theorem binary_positive
    (C : TrimmedPresentationSameContextTransport D)
    (ρ : BinaryRule N α G.arity)
    (hρ : ρ ∈ G.binaryRules) :
    D.binaryWitnessWord ρ ∈ G.StringLanguage := by
  exact C.transport
    (D.expose ρ.lhs)
    (D.anchor ρ.lhs)
    (ρ.apply (D.anchor ρ.left) (D.anchor ρ.right))
    (D.binary_type ρ hρ)
    (D.anchorWitnessWord_mem_target ρ.lhs)

/-- Start-rule witness positivity follows from same-context transport and the
start type equality stored in the pre-core. -/
theorem start_positive
    (C : TrimmedPresentationSameContextTransport D)
    (A : TrimmedPresentationRuleAritySelectors D)
    (ρ : StartRule N)
    (hρ : ρ ∈ G.startRules) :
    D.startWitnessWord ρ (A.start_arity ρ hρ) ∈
      G.StringLanguage := by
  exact C.transport
    (D.expose G.start)
    (D.anchor G.start)
    (castTuple (A.start_arity ρ hρ) (D.anchor ρ.child))
    (D.start_type ρ hρ (A.start_arity ρ hρ))
    (D.anchorWitnessWord_mem_target G.start)

/-- Build the remaining rule-witness transport package from same-context
transport and positivity of the distinguished start word. -/
def toRuleWitnessTransport
    (C : TrimmedPresentationSameContextTransport D)
    (A : TrimmedPresentationRuleAritySelectors D)
    (hstart : D.startWord ∈ G.StringLanguage) :
    TrimmedPresentationRuleWitnessTransport D A where
  terminal_positive := C.terminal_positive A
  binary_positive := C.binary_positive
  start_positive := C.start_positive A
  startWord_positive := hstart

end TrimmedPresentationSameContextTransport

end SameContextTransport


section ContextTransportData

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}
variable {f : Nat}
variable {T : TrimmedOutputTypePresentation G obs}

/-- Data for the characteristic-sample route using local same-context
transport. -/
structure TrimmedPresentationContextTransportData
    (D : TrimmedPresentationPreCoreData T f) where
  baseNonterminals : Finset N
  base_covers :
    ∀ A : N, A ∈ baseNonterminals

  arities : TrimmedPresentationRuleAritySelectors D
  contextTransport : TrimmedPresentationSameContextTransport D
  startWord_positive :
    D.startWord ∈ G.StringLanguage

namespace TrimmedPresentationContextTransportData

variable {D : TrimmedPresentationPreCoreData T f}

/-- Convert same-context-transport data to the rule-witness transport package. -/
def toRuleWitnessTransport
    (P : TrimmedPresentationContextTransportData D) :
    TrimmedPresentationRuleWitnessTransport D P.arities :=
  P.contextTransport.toRuleWitnessTransport P.arities P.startWord_positive

/-- Convert same-context-transport data to the grammar-rule transport data. -/
def toGrammarRuleTransportData
    (P : TrimmedPresentationContextTransportData D) :
    TrimmedPresentationGrammarRuleTransportData D where
  baseNonterminals := P.baseNonterminals
  base_covers := P.base_covers
  arities := P.arities
  transport := P.toRuleWitnessTransport

/-- The finite sample produced by same-context-transport data. -/
def sample
    (P : TrimmedPresentationContextTransportData D) :
    Finset (Word α) :=
  P.toGrammarRuleTransportData.sample

/-- The produced sample is positive. -/
theorem sample_positive
    (P : TrimmedPresentationContextTransportData D) :
    (P.sample : Set (Word α)) ⊆ G.StringLanguage :=
  P.toGrammarRuleTransportData.sample_positive

/-- The produced sample contains all required witness words. -/
theorem contains_witnesses
    (P : TrimmedPresentationContextTransportData D) :
    TrimmedPresentationWitnessWordSet D ⊆
      (P.sample : Set (Word α)) :=
  P.toGrammarRuleTransportData.contains_witnesses

/-- Convert to the final rule-transport wrapper after adding the remaining
splicing constructor and global assumptions. -/
def toRuleTransportFinalData
    (P : TrimmedPresentationContextTransportData D)
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
    (P : TrimmedPresentationContextTransportData D)
    (U : NamedContextSplicingConstructor α)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    FinalReachableData G P.sample obs f :=
  (P.toRuleTransportFinalData U hfan hL).toFinalReachableData

/-- The produced sample is a characteristic sample for the reachable learner. -/
theorem characteristic_sample
    (P : TrimmedPresentationContextTransportData D)
    (U : NamedContextSplicingConstructor α)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    CharacteristicSample
      (reachableHypLanguage obs f)
      (reachableSampleLearner (α := α))
      P.sample
      G.StringLanguage :=
  (P.toRuleTransportFinalData U hfan hL).characteristic_sample

/-- Eventual prefix-exact reconstruction from same-context-transport data. -/
theorem prefix_exact_eventually
    (P : TrimmedPresentationContextTransportData D)
    (U : NamedContextSplicingConstructor α)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    ∀ Ttxt : TextFor G.StringLanguage,
      ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
        ReachableSampleStringLanguage (Ttxt.prefixSample n) obs f =
          G.StringLanguage :=
  (P.toRuleTransportFinalData U hfan hL).prefix_exact_eventually

/-- Reachable Gold identification from same-context-transport data. -/
theorem identifies_from_positive_text
    (P : TrimmedPresentationContextTransportData D)
    (U : NamedContextSplicingConstructor α)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    ∀ Ttxt : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        Ttxt :=
  (P.toRuleTransportFinalData U hfan hL).identifies_from_positive_text

end TrimmedPresentationContextTransportData

end ContextTransportData


section MainTheoremsFromContextTransportData

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}
variable {f : Nat}
variable {T : TrimmedOutputTypePresentation G obs}
variable {D : TrimmedPresentationPreCoreData T f}

/-- Stable top-level reachable identification theorem from same-context
transport data. -/
theorem trimmed_context_transport_reachable_identification
    (P : TrimmedPresentationContextTransportData D)
    (U : NamedContextSplicingConstructor α)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    ∀ Ttxt : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        Ttxt :=
  P.identifies_from_positive_text U hfan hL

/-- Stable top-level prefix-exact theorem from same-context transport data. -/
theorem trimmed_context_transport_reachable_prefix_exact
    (P : TrimmedPresentationContextTransportData D)
    (U : NamedContextSplicingConstructor α)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    ∀ Ttxt : TextFor G.StringLanguage,
      ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
        ReachableSampleStringLanguage (Ttxt.prefixSample n) obs f =
          G.StringLanguage :=
  P.prefix_exact_eventually U hfan hL

end MainTheoremsFromContextTransportData

end MCFG
