/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG2.CharacteristicSampleGrammarRulePositivity

/-!
# CharacteristicSampleRuleWitnessTransport.lean

Fifty-eighth clean Lean experiment for the fixed-observation MCFG project.

`CharacteristicSampleGrammarRulePositivity.lean` reduced the positivity
requirements for the grammar-rule characteristic sample: anchor witness
positivity is automatic from `TrimmedPresentationPreCoreData`, while terminal,
binary, start, and distinguished start-word positivity remain explicit.

This file isolates those remaining semantic positivity facts as a single
transport target:

```lean
TrimmedPresentationRuleWitnessTransport
```

The intended future proof is:

```text
type equalities in the pre-core
+
exposing-context acceptance
+
fixed-observation substitutability
⇒ terminal/binary/start witness words are positive.
```

For now, this file packages that target and connects it to the already verified
grammar-rule-data route.

No theorem here uses `sorry`.
-/

namespace MCFG

universe u v w

section RuleWitnessTransport

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}
variable {f : Nat}
variable {T : TrimmedOutputTypePresentation G obs}

/-- Chosen arity proofs needed to form terminal and start witness words. -/
structure TrimmedPresentationRuleAritySelectors
    (D : TrimmedPresentationPreCoreData T f) where
  terminal_arity :
    ∀ (ρ : TerminalRule N α),
      ρ ∈ G.terminalRules →
        G.arity ρ.lhs = 1

  start_arity :
    ∀ (ρ : StartRule N),
      ρ ∈ G.startRules →
        G.arity ρ.child = G.arity G.start

/-- The remaining semantic positivity facts needed after anchor positivity has
been discharged by the trimmed pre-core itself. -/
structure TrimmedPresentationRuleWitnessTransport
    (D : TrimmedPresentationPreCoreData T f)
    (A : TrimmedPresentationRuleAritySelectors D) where
  terminal_positive :
    ∀ (ρ : TerminalRule N α)
      (hρ : ρ ∈ G.terminalRules),
        D.terminalWitnessWord ρ (A.terminal_arity ρ hρ) ∈
          G.StringLanguage

  binary_positive :
    ∀ (ρ : BinaryRule N α G.arity),
      ρ ∈ G.binaryRules →
        D.binaryWitnessWord ρ ∈ G.StringLanguage

  start_positive :
    ∀ (ρ : StartRule N)
      (hρ : ρ ∈ G.startRules),
        D.startWitnessWord ρ (A.start_arity ρ hρ) ∈
          G.StringLanguage

  startWord_positive :
    D.startWord ∈ G.StringLanguage

namespace TrimmedPresentationRuleWitnessTransport

variable {D : TrimmedPresentationPreCoreData T f}
variable {A : TrimmedPresentationRuleAritySelectors D}

/-- Terminal witness positivity accessor. -/
theorem terminal_mem_target
    (P : TrimmedPresentationRuleWitnessTransport D A)
    (ρ : TerminalRule N α)
    (hρ : ρ ∈ G.terminalRules) :
    D.terminalWitnessWord ρ (A.terminal_arity ρ hρ) ∈
      G.StringLanguage :=
  P.terminal_positive ρ hρ

/-- Binary witness positivity accessor. -/
theorem binary_mem_target
    (P : TrimmedPresentationRuleWitnessTransport D A)
    (ρ : BinaryRule N α G.arity)
    (hρ : ρ ∈ G.binaryRules) :
    D.binaryWitnessWord ρ ∈ G.StringLanguage :=
  P.binary_positive ρ hρ

/-- Start witness positivity accessor. -/
theorem start_mem_target
    (P : TrimmedPresentationRuleWitnessTransport D A)
    (ρ : StartRule N)
    (hρ : ρ ∈ G.startRules) :
    D.startWitnessWord ρ (A.start_arity ρ hρ) ∈
      G.StringLanguage :=
  P.start_positive ρ hρ

end TrimmedPresentationRuleWitnessTransport

end RuleWitnessTransport


section GrammarRuleDataFromTransport

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}
variable {f : Nat}
variable {T : TrimmedOutputTypePresentation G obs}

/-- Grammar-rule data built from a finite base-nonterminal cover, arity
selectors, and the remaining semantic witness-transport facts. -/
structure TrimmedPresentationGrammarRuleTransportData
    (D : TrimmedPresentationPreCoreData T f) where
  baseNonterminals : Finset N
  base_covers :
    ∀ A : N, A ∈ baseNonterminals

  arities : TrimmedPresentationRuleAritySelectors D
  transport : TrimmedPresentationRuleWitnessTransport D arities

namespace TrimmedPresentationGrammarRuleTransportData

variable {D : TrimmedPresentationPreCoreData T f}

/-- Convert the transport-oriented package to reduced grammar-rule data. -/
def toGrammarRuleData
    (P : TrimmedPresentationGrammarRuleTransportData D) :
    TrimmedPresentationGrammarRuleData D where
  baseNonterminals := P.baseNonterminals
  base_covers := P.base_covers
  terminal_arity := P.arities.terminal_arity
  start_arity := P.arities.start_arity
  terminal_positive := P.transport.terminal_positive
  binary_positive := P.transport.binary_positive
  start_positive := P.transport.start_positive
  startWord_positive := P.transport.startWord_positive

/-- The finite sample produced by the transport-oriented package. -/
noncomputable def sample
    (P : TrimmedPresentationGrammarRuleTransportData D) :
    Finset (Word α) :=
  P.toGrammarRuleData.sample

/-- The produced sample is positive. -/
theorem sample_positive
    (P : TrimmedPresentationGrammarRuleTransportData D) :
    (P.sample : Set (Word α)) ⊆ G.StringLanguage :=
  P.toGrammarRuleData.sample_positive

/-- The produced sample contains all required witness words. -/
theorem contains_witnesses
    (P : TrimmedPresentationGrammarRuleTransportData D) :
    TrimmedPresentationWitnessWordSet D ⊆
      (P.sample : Set (Word α)) :=
  P.toGrammarRuleData.contains_witnesses

/-- Convert to the abstract finite-sample builder. -/
noncomputable def toFiniteSampleBuilder
    (P : TrimmedPresentationGrammarRuleTransportData D) :
    TrimmedPresentationFiniteSampleBuilder D :=
  P.toGrammarRuleData.toFiniteSampleBuilder

/-- Convert to a witness-sample package. -/
def toWitnessSample
    (P : TrimmedPresentationGrammarRuleTransportData D) :
    TrimmedPresentationWitnessSample D P.sample :=
  P.toGrammarRuleData.toWitnessSample

/-- Convert to a characteristic-sample object. -/
noncomputable def toCharacteristicSample
    (P : TrimmedPresentationGrammarRuleTransportData D) :
    TrimmedPresentationCharacteristicSample D :=
  P.toGrammarRuleData.toCharacteristicSample

/-- Convert to final reachable data after adding the remaining splicing
constructor and global assumptions. -/
noncomputable def toFinalReachableData
    (P : TrimmedPresentationGrammarRuleTransportData D)
    (U : NamedContextSplicingConstructor α)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    FinalReachableData G P.sample obs f :=
  P.toGrammarRuleData.toFinalReachableData U hfan hL

/-- The produced sample is a characteristic sample for the reachable learner. -/
theorem characteristic_sample
    (P : TrimmedPresentationGrammarRuleTransportData D)
    (U : NamedContextSplicingConstructor α)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    CharacteristicSample
      (reachableHypLanguage obs f)
      (reachableSampleLearner (α := α))
      P.sample
      G.StringLanguage :=
  P.toGrammarRuleData.characteristic_sample U hfan hL

/-- Eventual prefix-exact reconstruction from transport-oriented grammar-rule
data. -/
theorem prefix_exact_eventually
    (P : TrimmedPresentationGrammarRuleTransportData D)
    (U : NamedContextSplicingConstructor α)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    ∀ Ttxt : TextFor G.StringLanguage,
      ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
        ReachableSampleStringLanguage (Ttxt.prefixSample n) obs f =
          G.StringLanguage :=
  P.toGrammarRuleData.prefix_exact_eventually U hfan hL

/-- Reachable Gold identification from transport-oriented grammar-rule data. -/
theorem identifies_from_positive_text
    (P : TrimmedPresentationGrammarRuleTransportData D)
    (U : NamedContextSplicingConstructor α)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    ∀ Ttxt : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        Ttxt :=
  P.toGrammarRuleData.identifies_from_positive_text U hfan hL

end TrimmedPresentationGrammarRuleTransportData

end GrammarRuleDataFromTransport


section MainTheoremsFromRuleWitnessTransport

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}
variable {f : Nat}
variable {T : TrimmedOutputTypePresentation G obs}
variable {D : TrimmedPresentationPreCoreData T f}

/-- Stable top-level reachable identification theorem from the witness-transport
package. -/
theorem trimmed_rule_transport_reachable_identification
    (P : TrimmedPresentationGrammarRuleTransportData D)
    (U : NamedContextSplicingConstructor α)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    ∀ Ttxt : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        Ttxt :=
  P.identifies_from_positive_text U hfan hL

/-- Stable top-level prefix-exact theorem from the witness-transport package. -/
theorem trimmed_rule_transport_reachable_prefix_exact
    (P : TrimmedPresentationGrammarRuleTransportData D)
    (U : NamedContextSplicingConstructor α)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    ∀ Ttxt : TextFor G.StringLanguage,
      ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
        ReachableSampleStringLanguage (Ttxt.prefixSample n) obs f =
          G.StringLanguage :=
  P.prefix_exact_eventually U hfan hL

end MainTheoremsFromRuleWitnessTransport

end MCFG
