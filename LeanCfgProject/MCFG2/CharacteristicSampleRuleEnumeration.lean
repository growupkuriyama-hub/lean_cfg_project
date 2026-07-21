/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG2.CharacteristicSampleComponentEnumeration

/-!
# CharacteristicSampleRuleEnumeration.lean

Fifty-fourth clean Lean experiment for the fixed-observation MCFG project.

`CharacteristicSampleComponentEnumeration.lean` introduced a general indexed
enumeration interface:

```text
finite indices
→ witness word function
→ image finite set
→ component package.
```

This file specializes that idea to the grammar data that will eventually
produce `CS(G̃₀)`:

* finite base-nonterminal indices for anchor witnesses;
* finite terminal-rule/arity indices for terminal witnesses;
* finite binary-rule indices for binary witnesses;
* finite start-rule/arity indices for start witnesses.

The file still does not construct those finite index sets from `G̃₀`; it fixes
the exact Lean interface that such a construction should satisfy.

No theorem here uses `sorry`.
-/

namespace MCFG

universe u v w

section RuleIndexTypes

variable {N : Type v} {α : Type u}
variable (G : WorkingMCFG N α)

/-- A terminal rule together with the arity proof needed to form its witness
word. -/
structure TerminalWitnessIndex where
  rule : TerminalRule N α
  rule_mem : rule ∈ G.terminalRules
  arity_eq : G.arity rule.lhs = 1

/-- A start rule together with the arity proof needed to form its witness word. -/
structure StartWitnessIndex where
  rule : StartRule N
  rule_mem : rule ∈ G.startRules
  arity_eq : G.arity rule.child = G.arity G.start

end RuleIndexTypes


section RuleEnumerations

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}
variable {f : Nat}
variable {T : TrimmedOutputTypePresentation G obs}

/-- Finite enumeration of base nonterminals used for anchor witnesses. -/
structure AnchorRuleEnumeration
    (D : TrimmedPresentationPreCoreData T f) where
  nonterminals : Finset N
  covers :
    ∀ A : N, A ∈ nonterminals
  positive :
    ∀ A : N, A ∈ nonterminals →
      D.anchorWitnessWord A ∈ G.StringLanguage

/-- Finite enumeration of terminal-rule witnesses. -/
structure TerminalRuleWitnessEnumeration
    (D : TrimmedPresentationPreCoreData T f) where
  indices : Finset (TerminalWitnessIndex G)
  covers :
    ∀ (ρ : TerminalRule N α),
      ρ ∈ G.terminalRules →
      ∀ hwt : G.arity ρ.lhs = 1,
        ∃ i : TerminalWitnessIndex G, i ∈ indices ∧
          D.terminalWitnessWord i.rule i.arity_eq =
            D.terminalWitnessWord ρ hwt
  positive :
    ∀ i : TerminalWitnessIndex G, i ∈ indices →
      D.terminalWitnessWord i.rule i.arity_eq ∈ G.StringLanguage

/-- Finite enumeration of binary-rule witnesses. -/
structure BinaryRuleWitnessEnumeration
    (D : TrimmedPresentationPreCoreData T f) where
  rules : Finset (BinaryRule N α G.arity)
  covers :
    ∀ (ρ : BinaryRule N α G.arity),
      ρ ∈ G.binaryRules →
        ρ ∈ rules
  positive :
    ∀ ρ : BinaryRule N α G.arity, ρ ∈ rules →
      D.binaryWitnessWord ρ ∈ G.StringLanguage

/-- Finite enumeration of start-rule witnesses. -/
structure StartRuleWitnessEnumeration
    (D : TrimmedPresentationPreCoreData T f) where
  indices : Finset (StartWitnessIndex G)
  covers :
    ∀ (ρ : StartRule N),
      ρ ∈ G.startRules →
      ∀ hwt : G.arity ρ.child = G.arity G.start,
        ∃ i : StartWitnessIndex G, i ∈ indices ∧
          D.startWitnessWord i.rule i.arity_eq =
            D.startWitnessWord ρ hwt
  positive :
    ∀ i : StartWitnessIndex G, i ∈ indices →
      D.startWitnessWord i.rule i.arity_eq ∈ G.StringLanguage

namespace AnchorRuleEnumeration

variable {D : TrimmedPresentationPreCoreData T f}

/-- The finite anchor sample produced by the base-nonterminal enumeration. -/
def sample
    (E : AnchorRuleEnumeration D) : Finset (Word α) :=
  E.nonterminals.image (fun A => D.anchorWitnessWord A)

/-- The anchor sample is positive. -/
theorem sample_positive
    (E : AnchorRuleEnumeration D) :
    (E.sample : Set (Word α)) ⊆ G.StringLanguage := by
  intro word hword
  rcases Finset.mem_image.mp hword with ⟨A, hA, hEq⟩
  rw [← hEq]
  exact E.positive A hA

/-- The anchor sample covers every anchor witness word. -/
theorem covers_sample
    (E : AnchorRuleEnumeration D)
    (A : N) :
    D.anchorWitnessWord A ∈ E.sample := by
  exact Finset.mem_image.mpr
    ⟨A, E.covers A, rfl⟩

/-- Convert to an anchor witness component. -/
def toComponent
    (E : AnchorRuleEnumeration D) :
    AnchorWitnessComponent D where
  sample := E.sample
  covers := E.covers_sample
  positive := E.sample_positive

end AnchorRuleEnumeration

namespace TerminalRuleWitnessEnumeration

variable {D : TrimmedPresentationPreCoreData T f}

/-- The finite terminal sample produced by the terminal-rule enumeration. -/
def sample
    (E : TerminalRuleWitnessEnumeration D) : Finset (Word α) :=
  E.indices.image (fun i =>
    D.terminalWitnessWord i.rule i.arity_eq)

/-- The terminal sample is positive. -/
theorem sample_positive
    (E : TerminalRuleWitnessEnumeration D) :
    (E.sample : Set (Word α)) ⊆ G.StringLanguage := by
  intro word hword
  rcases Finset.mem_image.mp hword with ⟨i, hi, hEq⟩
  rw [← hEq]
  exact E.positive i hi

/-- The terminal sample covers every terminal witness word. -/
theorem covers_sample
    (E : TerminalRuleWitnessEnumeration D)
    (ρ : TerminalRule N α)
    (hρ : ρ ∈ G.terminalRules)
    (hwt : G.arity ρ.lhs = 1) :
    D.terminalWitnessWord ρ hwt ∈ E.sample := by
  rcases E.covers ρ hρ hwt with ⟨i, hi, hEq⟩
  exact Finset.mem_image.mpr ⟨i, hi, hEq⟩

/-- Convert to a terminal witness component. -/
def toComponent
    (E : TerminalRuleWitnessEnumeration D) :
    TerminalWitnessComponent D where
  sample := E.sample
  covers := E.covers_sample
  positive := E.sample_positive

end TerminalRuleWitnessEnumeration

namespace BinaryRuleWitnessEnumeration

variable {D : TrimmedPresentationPreCoreData T f}

/-- The finite binary sample produced by the binary-rule enumeration. -/
def sample
    (E : BinaryRuleWitnessEnumeration D) : Finset (Word α) :=
  E.rules.image (fun ρ => D.binaryWitnessWord ρ)

/-- The binary sample is positive. -/
theorem sample_positive
    (E : BinaryRuleWitnessEnumeration D) :
    (E.sample : Set (Word α)) ⊆ G.StringLanguage := by
  intro word hword
  rcases Finset.mem_image.mp hword with ⟨ρ, hρ, hEq⟩
  rw [← hEq]
  exact E.positive ρ hρ

/-- The binary sample covers every binary witness word. -/
theorem covers_sample
    (E : BinaryRuleWitnessEnumeration D)
    (ρ : BinaryRule N α G.arity)
    (hρ : ρ ∈ G.binaryRules) :
    D.binaryWitnessWord ρ ∈ E.sample := by
  exact Finset.mem_image.mpr
    ⟨ρ, E.covers ρ hρ, rfl⟩

/-- Convert to a binary witness component. -/
def toComponent
    (E : BinaryRuleWitnessEnumeration D) :
    BinaryWitnessComponent D where
  sample := E.sample
  covers := E.covers_sample
  positive := E.sample_positive

end BinaryRuleWitnessEnumeration

namespace StartRuleWitnessEnumeration

variable {D : TrimmedPresentationPreCoreData T f}

/-- The finite start sample produced by the start-rule enumeration. -/
def sample
    (E : StartRuleWitnessEnumeration D) : Finset (Word α) :=
  E.indices.image (fun i =>
    D.startWitnessWord i.rule i.arity_eq)

/-- The start sample is positive. -/
theorem sample_positive
    (E : StartRuleWitnessEnumeration D) :
    (E.sample : Set (Word α)) ⊆ G.StringLanguage := by
  intro word hword
  rcases Finset.mem_image.mp hword with ⟨i, hi, hEq⟩
  rw [← hEq]
  exact E.positive i hi

/-- The start sample covers every start witness word. -/
theorem covers_sample
    (E : StartRuleWitnessEnumeration D)
    (ρ : StartRule N)
    (hρ : ρ ∈ G.startRules)
    (hwt : G.arity ρ.child = G.arity G.start) :
    D.startWitnessWord ρ hwt ∈ E.sample := by
  rcases E.covers ρ hρ hwt with ⟨i, hi, hEq⟩
  exact Finset.mem_image.mpr ⟨i, hi, hEq⟩

/-- Convert to a start witness component. -/
def toComponent
    (E : StartRuleWitnessEnumeration D) :
    StartWitnessComponent D where
  sample := E.sample
  covers := E.covers_sample
  positive := E.sample_positive

end StartRuleWitnessEnumeration

end RuleEnumerations


section RuleEnumerationPackage

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}
variable {f : Nat}
variable {T : TrimmedOutputTypePresentation G obs}

/-- Rule-indexed enumeration package for the presentation-relative
characteristic sample. -/
structure TrimmedPresentationRuleEnumeration
    (D : TrimmedPresentationPreCoreData T f) where
  anchor : AnchorRuleEnumeration D
  terminal : TerminalRuleWitnessEnumeration D
  binary : BinaryRuleWitnessEnumeration D
  start : StartRuleWitnessEnumeration D
  startWord_positive :
    D.startWord ∈ G.StringLanguage

namespace TrimmedPresentationRuleEnumeration

variable {D : TrimmedPresentationPreCoreData T f}

/-- Convert rule-indexed enumerations to componentwise characteristic-sample
data. -/
def toComponentPackage
    (E : TrimmedPresentationRuleEnumeration D) :
    TrimmedPresentationComponentPackage D where
  anchor := E.anchor.toComponent
  terminal := E.terminal.toComponent
  binary := E.binary.toComponent
  start := E.start.toComponent
  startWord_positive := E.startWord_positive

/-- The finite sample produced by the rule-indexed enumeration. -/
def sample
    (E : TrimmedPresentationRuleEnumeration D) : Finset (Word α) :=
  E.toComponentPackage.sample

/-- The produced sample is positive. -/
theorem sample_positive
    (E : TrimmedPresentationRuleEnumeration D) :
    (E.sample : Set (Word α)) ⊆ G.StringLanguage :=
  E.toComponentPackage.sample_positive

/-- The produced sample contains all required witness words. -/
theorem contains_witnesses
    (E : TrimmedPresentationRuleEnumeration D) :
    TrimmedPresentationWitnessWordSet D ⊆
      (E.sample : Set (Word α)) :=
  E.toComponentPackage.contains_witnesses

/-- Convert to the abstract finite-sample builder. -/
def toFiniteSampleBuilder
    (E : TrimmedPresentationRuleEnumeration D) :
    TrimmedPresentationFiniteSampleBuilder D :=
  E.toComponentPackage.toFiniteSampleBuilder

/-- Convert to a witness-sample package. -/
def toWitnessSample
    (E : TrimmedPresentationRuleEnumeration D) :
    TrimmedPresentationWitnessSample D E.sample :=
  E.toComponentPackage.toWitnessSample

/-- Convert to a characteristic-sample object. -/
def toCharacteristicSample
    (E : TrimmedPresentationRuleEnumeration D) :
    TrimmedPresentationCharacteristicSample D :=
  E.toComponentPackage.toCharacteristicSample

/-- Convert to final reachable data after adding the remaining splicing
constructor and global assumptions. -/
def toFinalReachableData
    (E : TrimmedPresentationRuleEnumeration D)
    (U : NamedContextSplicingConstructor α)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    FinalReachableData G E.sample obs f :=
  E.toComponentPackage.toFinalReachableData U hfan hL

/-- Eventual prefix-exact reconstruction from rule-indexed enumerations. -/
theorem prefix_exact_eventually
    (E : TrimmedPresentationRuleEnumeration D)
    (U : NamedContextSplicingConstructor α)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    ∀ Ttxt : TextFor G.StringLanguage,
      ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
        ReachableSampleStringLanguage (Ttxt.prefixSample n) obs f =
          G.StringLanguage :=
  E.toComponentPackage.prefix_exact_eventually U hfan hL

/-- Reachable Gold identification from rule-indexed enumerations. -/
theorem identifies_from_positive_text
    (E : TrimmedPresentationRuleEnumeration D)
    (U : NamedContextSplicingConstructor α)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    ∀ Ttxt : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        Ttxt :=
  E.toComponentPackage.identifies_from_positive_text U hfan hL

/-- The produced sample is a characteristic sample for the reachable learner. -/
theorem characteristic_sample
    (E : TrimmedPresentationRuleEnumeration D)
    (U : NamedContextSplicingConstructor α)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    CharacteristicSample
      (reachableHypLanguage obs f)
      (reachableSampleLearner (α := α))
      E.sample
      G.StringLanguage :=
  E.toComponentPackage.characteristic_sample U hfan hL

end TrimmedPresentationRuleEnumeration

end RuleEnumerationPackage


section MainTheoremsFromRuleEnumeration

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}
variable {f : Nat}
variable {T : TrimmedOutputTypePresentation G obs}
variable {D : TrimmedPresentationPreCoreData T f}

/-- Stable top-level reachable identification theorem from rule-indexed
enumerations. -/
theorem trimmed_rule_enumeration_reachable_identification
    (E : TrimmedPresentationRuleEnumeration D)
    (U : NamedContextSplicingConstructor α)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    ∀ Ttxt : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        Ttxt :=
  E.identifies_from_positive_text U hfan hL

/-- Stable top-level prefix-exact theorem from rule-indexed enumerations. -/
theorem trimmed_rule_enumeration_reachable_prefix_exact
    (E : TrimmedPresentationRuleEnumeration D)
    (U : NamedContextSplicingConstructor α)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    ∀ Ttxt : TextFor G.StringLanguage,
      ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
        ReachableSampleStringLanguage (Ttxt.prefixSample n) obs f =
          G.StringLanguage :=
  E.prefix_exact_eventually U hfan hL

end MainTheoremsFromRuleEnumeration

end MCFG
