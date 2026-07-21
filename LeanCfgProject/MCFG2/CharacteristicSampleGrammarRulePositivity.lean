/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG.CharacteristicSampleGrammarRuleBuilder

/-!
# CharacteristicSampleGrammarRulePositivity.lean

Fifty-seventh clean Lean experiment for the fixed-observation MCFG project.

`CharacteristicSampleGrammarRuleBuilder.lean` built the characteristic-sample
route from the grammar's own finite rule sets, but it still asked for
positivity of anchor witness words as an explicit field.

This file removes that redundant anchor-positivity assumption.

For a `TrimmedPresentationPreCoreData D`, anchor witness words are already
positive: they are the exposed anchor words, and `D` carries the corresponding
acceptance fact.  The remaining positivity data is therefore only for:

* terminal-rule witness words;
* binary-rule witness words;
* start-rule witness words;
* the distinguished start word.

Together with a finite cover of base nonterminals and arity selectors for
terminal/start rules, this data builds the previous
`TrimmedPresentationGrammarRuleBuilder`.

No theorem here uses `sorry`.
-/

namespace MCFG

universe u v w

section GrammarRulePositivityData

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}
variable {f : Nat}
variable {T : TrimmedOutputTypePresentation G obs}

/-- Reduced grammar-rule characteristic-sample data.

Anchor witness positivity is not a field here, because it follows from the
exposing-context facts already present in `TrimmedPresentationPreCoreData`. -/
structure TrimmedPresentationGrammarRuleData
    (D : TrimmedPresentationPreCoreData T f) where
  baseNonterminals : Finset N
  base_covers :
    ∀ A : N, A ∈ baseNonterminals

  terminal_arity :
    ∀ (ρ : TerminalRule N α),
      ρ ∈ G.terminalRules →
        G.arity ρ.lhs = 1

  start_arity :
    ∀ (ρ : StartRule N),
      ρ ∈ G.startRules →
        G.arity ρ.child = G.arity G.start

  terminal_positive :
    ∀ (ρ : TerminalRule N α)
      (hρ : ρ ∈ G.terminalRules),
        D.terminalWitnessWord ρ (terminal_arity ρ hρ) ∈
          G.StringLanguage

  binary_positive :
    ∀ (ρ : BinaryRule N α G.arity),
      ρ ∈ G.binaryRules →
        D.binaryWitnessWord ρ ∈ G.StringLanguage

  start_positive :
    ∀ (ρ : StartRule N)
      (hρ : ρ ∈ G.startRules),
        D.startWitnessWord ρ (start_arity ρ hρ) ∈
          G.StringLanguage

  startWord_positive :
    D.startWord ∈ G.StringLanguage

namespace TrimmedPresentationGrammarRuleData

variable {D : TrimmedPresentationPreCoreData T f}

/-- Anchor witness positivity follows from the trimmed-presentation pre-core. -/
theorem anchor_positive
    (P : TrimmedPresentationGrammarRuleData D)
    (A : N)
    (_hA : A ∈ P.baseNonterminals) :
    D.anchorWitnessWord A ∈ G.StringLanguage :=
  D.anchorWitnessWord_mem_target A

/-- Build the previous grammar-rule builder by filling the anchor positivity
field automatically. -/
def toGrammarRuleBuilder
    (P : TrimmedPresentationGrammarRuleData D) :
    TrimmedPresentationGrammarRuleBuilder D where
  baseNonterminals := P.baseNonterminals
  base_covers := P.base_covers
  terminal_arity := P.terminal_arity
  start_arity := P.start_arity
  anchor_positive := P.anchor_positive
  terminal_positive := P.terminal_positive
  binary_positive := P.binary_positive
  start_positive := P.start_positive
  startWord_positive := P.startWord_positive

/-- The finite sample produced by the reduced grammar-rule data. -/
def sample
    (P : TrimmedPresentationGrammarRuleData D) :
    Finset (Word α) :=
  P.toGrammarRuleBuilder.sample

/-- The produced sample is positive. -/
theorem sample_positive
    (P : TrimmedPresentationGrammarRuleData D) :
    (P.sample : Set (Word α)) ⊆ G.StringLanguage :=
  P.toGrammarRuleBuilder.sample_positive

/-- The produced sample contains all required witness words. -/
theorem contains_witnesses
    (P : TrimmedPresentationGrammarRuleData D) :
    TrimmedPresentationWitnessWordSet D ⊆
      (P.sample : Set (Word α)) :=
  P.toGrammarRuleBuilder.contains_witnesses

/-- Convert to the component package. -/
def toComponentPackage
    (P : TrimmedPresentationGrammarRuleData D) :
    TrimmedPresentationComponentPackage D :=
  P.toGrammarRuleBuilder.toComponentPackage

/-- Convert to the abstract finite-sample builder. -/
def toFiniteSampleBuilder
    (P : TrimmedPresentationGrammarRuleData D) :
    TrimmedPresentationFiniteSampleBuilder D :=
  P.toGrammarRuleBuilder.toFiniteSampleBuilder

/-- Convert to a witness-sample package. -/
def toWitnessSample
    (P : TrimmedPresentationGrammarRuleData D) :
    TrimmedPresentationWitnessSample D P.sample :=
  P.toGrammarRuleBuilder.toWitnessSample

/-- Convert to a characteristic-sample object. -/
def toCharacteristicSample
    (P : TrimmedPresentationGrammarRuleData D) :
    TrimmedPresentationCharacteristicSample D :=
  P.toGrammarRuleBuilder.toCharacteristicSample

/-- Convert to final reachable data after adding the remaining splicing
constructor and global assumptions. -/
def toFinalReachableData
    (P : TrimmedPresentationGrammarRuleData D)
    (U : NamedContextSplicingConstructor α)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    FinalReachableData G P.sample obs f :=
  P.toGrammarRuleBuilder.toFinalReachableData U hfan hL

/-- The produced sample is a characteristic sample for the reachable learner. -/
theorem characteristic_sample
    (P : TrimmedPresentationGrammarRuleData D)
    (U : NamedContextSplicingConstructor α)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    CharacteristicSample
      (reachableHypLanguage obs f)
      (reachableSampleLearner (α := α))
      P.sample
      G.StringLanguage :=
  P.toGrammarRuleBuilder.characteristic_sample U hfan hL

/-- Eventual prefix-exact reconstruction from the reduced grammar-rule data. -/
theorem prefix_exact_eventually
    (P : TrimmedPresentationGrammarRuleData D)
    (U : NamedContextSplicingConstructor α)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    ∀ Ttxt : TextFor G.StringLanguage,
      ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
        ReachableSampleStringLanguage (Ttxt.prefixSample n) obs f =
          G.StringLanguage :=
  P.toGrammarRuleBuilder.prefix_exact_eventually U hfan hL

/-- Reachable Gold identification from the reduced grammar-rule data. -/
theorem identifies_from_positive_text
    (P : TrimmedPresentationGrammarRuleData D)
    (U : NamedContextSplicingConstructor α)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    ∀ Ttxt : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        Ttxt :=
  P.toGrammarRuleBuilder.identifies_from_positive_text U hfan hL

end TrimmedPresentationGrammarRuleData

end GrammarRulePositivityData


section MainTheoremsFromGrammarRuleData

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}
variable {f : Nat}
variable {T : TrimmedOutputTypePresentation G obs}
variable {D : TrimmedPresentationPreCoreData T f}

/-- Stable top-level reachable identification theorem from reduced
grammar-rule data. -/
theorem trimmed_grammar_rule_data_reachable_identification
    (P : TrimmedPresentationGrammarRuleData D)
    (U : NamedContextSplicingConstructor α)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    ∀ Ttxt : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        Ttxt :=
  P.identifies_from_positive_text U hfan hL

/-- Stable top-level prefix-exact theorem from reduced grammar-rule data. -/
theorem trimmed_grammar_rule_data_reachable_prefix_exact
    (P : TrimmedPresentationGrammarRuleData D)
    (U : NamedContextSplicingConstructor α)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    ∀ Ttxt : TextFor G.StringLanguage,
      ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
        ReachableSampleStringLanguage (Ttxt.prefixSample n) obs f =
          G.StringLanguage :=
  P.prefix_exact_eventually U hfan hL

end MainTheoremsFromGrammarRuleData

end MCFG
