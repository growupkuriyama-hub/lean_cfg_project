/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG2.CharacteristicSampleRuleCoverage

/-!
# CharacteristicSampleGrammarRuleBuilder.lean

Fifty-sixth clean Lean experiment for the fixed-observation MCFG project.

`CharacteristicSampleRuleCoverage.lean` packaged finite rule coverage and
positivity data abstractly.

This file moves one step closer to the concrete `CS(G̃₀)` construction.  It
uses the grammar's own finite rule sets

* `G.terminalRules`,
* `G.binaryRules`,
* `G.startRules`

to build the terminal, binary, and start witness components.

For anchor witnesses we still require an explicit finite cover of the base
nonterminal type, because `N` need not be finite globally.

For terminal and start witnesses, the witness word requires an arity proof.
This file stores canonical choices of those arity proofs and uses proof
irrelevance to cover any other proof of the same arity statement.

No theorem here uses `sorry`.
-/

namespace MCFG

universe u v w

section GrammarRuleBuilder

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}
variable {f : Nat}
variable {T : TrimmedOutputTypePresentation G obs}

/-- Builder data using the grammar's own finite rule sets.

The only finite cover not supplied directly by the grammar is the cover of base
nonterminals needed for anchor witnesses. -/
structure TrimmedPresentationGrammarRuleBuilder
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

  anchor_positive :
    ∀ A : N, A ∈ baseNonterminals →
      D.anchorWitnessWord A ∈ G.StringLanguage

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

namespace TrimmedPresentationGrammarRuleBuilder

variable {D : TrimmedPresentationPreCoreData T f}

/-- Anchor sample obtained from the finite base-nonterminal cover. -/
def anchorSample
    (B : TrimmedPresentationGrammarRuleBuilder D) :
    Finset (Word α) :=
  B.baseNonterminals.image (fun A => D.anchorWitnessWord A)

/-- Terminal sample obtained from the grammar's terminal rules. -/
def terminalSample
    (B : TrimmedPresentationGrammarRuleBuilder D) :
    Finset (Word α) :=
  G.terminalRules.attach.image
    (fun i => D.terminalWitnessWord i.val
      (B.terminal_arity i.val i.property))

/-- Binary sample obtained from the grammar's binary rules. -/
def binarySample
    (B : TrimmedPresentationGrammarRuleBuilder D) :
    Finset (Word α) :=
  G.binaryRules.image (fun ρ => D.binaryWitnessWord ρ)

/-- Start sample obtained from the grammar's start rules. -/
def startSample
    (B : TrimmedPresentationGrammarRuleBuilder D) :
    Finset (Word α) :=
  G.startRules.attach.image
    (fun i => D.startWitnessWord i.val
      (B.start_arity i.val i.property))

/-- Anchor sample positivity. -/
theorem anchorSample_positive
    (B : TrimmedPresentationGrammarRuleBuilder D) :
    (B.anchorSample : Set (Word α)) ⊆ G.StringLanguage := by
  intro word hword
  rcases Finset.mem_image.mp hword with ⟨A, hA, hEq⟩
  rw [← hEq]
  exact B.anchor_positive A hA

/-- Terminal sample positivity. -/
theorem terminalSample_positive
    (B : TrimmedPresentationGrammarRuleBuilder D) :
    (B.terminalSample : Set (Word α)) ⊆ G.StringLanguage := by
  intro word hword
  unfold terminalSample at hword
  rcases Finset.mem_image.mp hword with ⟨i, _hi, hEq⟩
  rw [← hEq]
  exact B.terminal_positive i.val i.property

/-- Binary sample positivity. -/
theorem binarySample_positive
    (B : TrimmedPresentationGrammarRuleBuilder D) :
    (B.binarySample : Set (Word α)) ⊆ G.StringLanguage := by
  intro word hword
  unfold binarySample at hword
  rcases Finset.mem_image.mp hword with ⟨ρ, hρ, hEq⟩
  rw [← hEq]
  exact B.binary_positive ρ (by simpa using hρ)

/-- Start sample positivity. -/
theorem startSample_positive
    (B : TrimmedPresentationGrammarRuleBuilder D) :
    (B.startSample : Set (Word α)) ⊆ G.StringLanguage := by
  intro word hword
  unfold startSample at hword
  rcases Finset.mem_image.mp hword with ⟨i, _hi, hEq⟩
  rw [← hEq]
  exact B.start_positive i.val i.property

/-- The anchor sample covers every anchor witness word. -/
theorem anchor_covers_sample
    (B : TrimmedPresentationGrammarRuleBuilder D)
    (A : N) :
    D.anchorWitnessWord A ∈ B.anchorSample :=
  Finset.mem_image.mpr ⟨A, B.base_covers A, rfl⟩

/-- The terminal sample covers every terminal witness word.

The stored arity proof and the requested arity proof are equal by proof
irrelevance. -/
theorem terminal_covers_sample
    (B : TrimmedPresentationGrammarRuleBuilder D)
    (ρ : TerminalRule N α)
    (hρ : ρ ∈ G.terminalRules)
    (hwt : G.arity ρ.lhs = 1) :
    D.terminalWitnessWord ρ hwt ∈ B.terminalSample := by
  have hp : B.terminal_arity ρ hρ = hwt := Subsingleton.elim _ _
  unfold terminalSample
  refine Finset.mem_image.mpr ?_
  refine ⟨⟨ρ, hρ⟩, ?_, ?_⟩
  · simp
  · simpa only [hp]

/-- The binary sample covers every binary witness word. -/
theorem binary_covers_sample
    (B : TrimmedPresentationGrammarRuleBuilder D)
    (ρ : BinaryRule N α G.arity)
    (hρ : ρ ∈ G.binaryRules) :
    D.binaryWitnessWord ρ ∈ B.binarySample := by
  unfold binarySample
  refine Finset.mem_image.mpr ?_
  exact ⟨ρ, by simpa using hρ, rfl⟩

/-- The start sample covers every start witness word.

The stored arity proof and the requested arity proof are equal by proof
irrelevance. -/
theorem start_covers_sample
    (B : TrimmedPresentationGrammarRuleBuilder D)
    (ρ : StartRule N)
    (hρ : ρ ∈ G.startRules)
    (hwt : G.arity ρ.child = G.arity G.start) :
    D.startWitnessWord ρ hwt ∈ B.startSample := by
  classical
  have hp : B.start_arity ρ hρ = hwt := Subsingleton.elim _ _
  unfold startSample
  refine Finset.mem_image.mpr ?_
  refine ⟨⟨ρ, hρ⟩, ?_, ?_⟩
  · simp
  · simpa only [hp]

/-- Convert the grammar-rule builder to the component package. -/
def toComponentPackage
    (B : TrimmedPresentationGrammarRuleBuilder D) :
    TrimmedPresentationComponentPackage D where
  anchor :=
    { sample := B.anchorSample
      covers := B.anchor_covers_sample
      positive := B.anchorSample_positive }
  terminal :=
    { sample := B.terminalSample
      covers := B.terminal_covers_sample
      positive := B.terminalSample_positive }
  binary :=
    { sample := B.binarySample
      covers := B.binary_covers_sample
      positive := B.binarySample_positive }
  start :=
    { sample := B.startSample
      covers := B.start_covers_sample
      positive := B.startSample_positive }
  startWord_positive := B.startWord_positive

/-- The finite sample produced by the grammar-rule builder. -/
def sample
    (B : TrimmedPresentationGrammarRuleBuilder D) :
    Finset (Word α) :=
  B.toComponentPackage.sample

/-- The produced sample is positive. -/
theorem sample_positive
    (B : TrimmedPresentationGrammarRuleBuilder D) :
    (B.sample : Set (Word α)) ⊆ G.StringLanguage :=
  B.toComponentPackage.sample_positive

/-- The produced sample contains all required witness words. -/
theorem contains_witnesses
    (B : TrimmedPresentationGrammarRuleBuilder D) :
    TrimmedPresentationWitnessWordSet D ⊆
      (B.sample : Set (Word α)) :=
  B.toComponentPackage.contains_witnesses

/-- Convert to the abstract finite-sample builder. -/
def toFiniteSampleBuilder
    (B : TrimmedPresentationGrammarRuleBuilder D) :
    TrimmedPresentationFiniteSampleBuilder D :=
  B.toComponentPackage.toFiniteSampleBuilder

/-- Convert to a witness-sample package. -/
def toWitnessSample
    (B : TrimmedPresentationGrammarRuleBuilder D) :
    TrimmedPresentationWitnessSample D B.sample :=
  B.toComponentPackage.toWitnessSample

/-- Convert to a characteristic-sample object. -/
def toCharacteristicSample
    (B : TrimmedPresentationGrammarRuleBuilder D) :
    TrimmedPresentationCharacteristicSample D :=
  B.toComponentPackage.toCharacteristicSample

/-- Convert to final reachable data after adding the remaining splicing
constructor and global assumptions. -/
def toFinalReachableData
    (B : TrimmedPresentationGrammarRuleBuilder D)
    (U : NamedContextSplicingConstructor α)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    FinalReachableData G B.sample obs f :=
  B.toComponentPackage.toFinalReachableData U hfan hL

/-- The produced sample is a characteristic sample for the reachable learner. -/
theorem characteristic_sample
    (B : TrimmedPresentationGrammarRuleBuilder D)
    (U : NamedContextSplicingConstructor α)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    CharacteristicSample
      (reachableHypLanguage obs f)
      (reachableSampleLearner (α := α))
      B.sample
      G.StringLanguage :=
  B.toComponentPackage.characteristic_sample U hfan hL

/-- Eventual prefix-exact reconstruction from the grammar-rule builder. -/
theorem prefix_exact_eventually
    (B : TrimmedPresentationGrammarRuleBuilder D)
    (U : NamedContextSplicingConstructor α)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    ∀ Ttxt : TextFor G.StringLanguage,
      ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
        ReachableSampleStringLanguage (Ttxt.prefixSample n) obs f =
          G.StringLanguage :=
  B.toComponentPackage.prefix_exact_eventually U hfan hL

/-- Reachable Gold identification from the grammar-rule builder. -/
theorem identifies_from_positive_text
    (B : TrimmedPresentationGrammarRuleBuilder D)
    (U : NamedContextSplicingConstructor α)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    ∀ Ttxt : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        Ttxt :=
  B.toComponentPackage.identifies_from_positive_text U hfan hL

end TrimmedPresentationGrammarRuleBuilder

end GrammarRuleBuilder


section MainTheoremsFromGrammarRuleBuilder

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}
variable {f : Nat}
variable {T : TrimmedOutputTypePresentation G obs}
variable {D : TrimmedPresentationPreCoreData T f}

/-- Stable top-level reachable identification theorem from the grammar-rule
builder. -/
theorem trimmed_grammar_rule_builder_reachable_identification
    (B : TrimmedPresentationGrammarRuleBuilder D)
    (U : NamedContextSplicingConstructor α)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    ∀ Ttxt : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        Ttxt :=
  B.identifies_from_positive_text U hfan hL

/-- Stable top-level prefix-exact theorem from the grammar-rule builder. -/
theorem trimmed_grammar_rule_builder_reachable_prefix_exact
    (B : TrimmedPresentationGrammarRuleBuilder D)
    (U : NamedContextSplicingConstructor α)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    ∀ Ttxt : TextFor G.StringLanguage,
      ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
        ReachableSampleStringLanguage (Ttxt.prefixSample n) obs f =
          G.StringLanguage :=
  B.prefix_exact_eventually U hfan hL

end MainTheoremsFromGrammarRuleBuilder

end MCFG
