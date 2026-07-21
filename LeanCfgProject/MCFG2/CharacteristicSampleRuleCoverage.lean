/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG.CharacteristicSampleRuleEnumeration

/-!
# CharacteristicSampleRuleCoverage.lean

Fifty-fifth clean Lean experiment for the fixed-observation MCFG project.

`CharacteristicSampleRuleEnumeration.lean` introduced rule-indexed
enumerations for the future presentation-relative characteristic sample.

This file separates the data used to build those enumerations into two layers:

* finite coverage data;
* positivity data for the witness words selected by that coverage.

This is closer to the eventual construction of `CS(G̃₀)`: first choose finite
sets covering the relevant nonterminals and rules, then prove the corresponding
witness words are positive, then obtain the already verified rule-enumeration
route to reachable identification.

No theorem here uses `sorry`.
-/

namespace MCFG

universe u v w

section RuleCoverageData

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}
variable {f : Nat}
variable {T : TrimmedOutputTypePresentation G obs}

/-- Finite coverage of all base nonterminals needed for anchor witness words. -/
structure AnchorRuleCoverage
    (D : TrimmedPresentationPreCoreData T f) where
  nonterminals : Finset N
  covers :
    ∀ A : N, A ∈ nonterminals

/-- Positivity of the anchor witness words selected by an anchor coverage. -/
structure AnchorRulePositivity
    (D : TrimmedPresentationPreCoreData T f)
    (C : AnchorRuleCoverage D) where
  positive :
    ∀ A : N, A ∈ C.nonterminals →
      D.anchorWitnessWord A ∈ G.StringLanguage

/-- Finite coverage of all terminal-rule witness words. -/
structure TerminalRuleCoverage
    (D : TrimmedPresentationPreCoreData T f) where
  indices : Finset (TerminalWitnessIndex G)
  covers :
    ∀ (ρ : TerminalRule N α),
      ρ ∈ G.terminalRules →
      ∀ hwt : G.arity ρ.lhs = 1,
        ∃ i : TerminalWitnessIndex G, i ∈ indices ∧
          D.terminalWitnessWord i.rule i.arity_eq =
            D.terminalWitnessWord ρ hwt

/-- Positivity of terminal witness words selected by a terminal-rule coverage. -/
structure TerminalRulePositivity
    (D : TrimmedPresentationPreCoreData T f)
    (C : TerminalRuleCoverage D) where
  positive :
    ∀ i : TerminalWitnessIndex G, i ∈ C.indices →
      D.terminalWitnessWord i.rule i.arity_eq ∈ G.StringLanguage

/-- Finite coverage of all binary-rule witness words. -/
structure BinaryRuleCoverage
    (D : TrimmedPresentationPreCoreData T f) where
  rules : Finset (BinaryRule N α G.arity)
  covers :
    ∀ (ρ : BinaryRule N α G.arity),
      ρ ∈ G.binaryRules →
        ρ ∈ rules

/-- Positivity of binary witness words selected by a binary-rule coverage. -/
structure BinaryRulePositivity
    (D : TrimmedPresentationPreCoreData T f)
    (C : BinaryRuleCoverage D) where
  positive :
    ∀ ρ : BinaryRule N α G.arity, ρ ∈ C.rules →
      D.binaryWitnessWord ρ ∈ G.StringLanguage

/-- Finite coverage of all start-rule witness words. -/
structure StartRuleCoverage
    (D : TrimmedPresentationPreCoreData T f) where
  indices : Finset (StartWitnessIndex G)
  covers :
    ∀ (ρ : StartRule N),
      ρ ∈ G.startRules →
      ∀ hwt : G.arity ρ.child = G.arity G.start,
        ∃ i : StartWitnessIndex G, i ∈ indices ∧
          D.startWitnessWord i.rule i.arity_eq =
            D.startWitnessWord ρ hwt

/-- Positivity of start-rule witness words selected by a start-rule coverage. -/
structure StartRulePositivity
    (D : TrimmedPresentationPreCoreData T f)
    (C : StartRuleCoverage D) where
  positive :
    ∀ i : StartWitnessIndex G, i ∈ C.indices →
      D.startWitnessWord i.rule i.arity_eq ∈ G.StringLanguage

namespace AnchorRuleCoverage

variable {D : TrimmedPresentationPreCoreData T f}

/-- Build the rule-enumeration object for anchor witnesses from coverage and
positivity. -/
def toEnumeration
    (C : AnchorRuleCoverage D)
    (P : AnchorRulePositivity D C) :
    AnchorRuleEnumeration D where
  nonterminals := C.nonterminals
  covers := C.covers
  positive := P.positive

/-- Every covered anchor witness word is positive. -/
theorem witness_mem_target
    (C : AnchorRuleCoverage D)
    (P : AnchorRulePositivity D C)
    (A : N) :
    D.anchorWitnessWord A ∈ G.StringLanguage :=
  P.positive A (C.covers A)

end AnchorRuleCoverage

namespace TerminalRuleCoverage

variable {D : TrimmedPresentationPreCoreData T f}

/-- Build the rule-enumeration object for terminal witnesses from coverage and
positivity. -/
def toEnumeration
    (C : TerminalRuleCoverage D)
    (P : TerminalRulePositivity D C) :
    TerminalRuleWitnessEnumeration D where
  indices := C.indices
  covers := C.covers
  positive := P.positive

/-- Every covered terminal witness word is positive. -/
theorem witness_mem_target
    (C : TerminalRuleCoverage D)
    (P : TerminalRulePositivity D C)
    (ρ : TerminalRule N α)
    (hρ : ρ ∈ G.terminalRules)
    (hwt : G.arity ρ.lhs = 1) :
    D.terminalWitnessWord ρ hwt ∈ G.StringLanguage := by
  rcases C.covers ρ hρ hwt with ⟨i, hi, hEq⟩
  rw [← hEq]
  exact P.positive i hi

end TerminalRuleCoverage

namespace BinaryRuleCoverage

variable {D : TrimmedPresentationPreCoreData T f}

/-- Build the rule-enumeration object for binary witnesses from coverage and
positivity. -/
def toEnumeration
    (C : BinaryRuleCoverage D)
    (P : BinaryRulePositivity D C) :
    BinaryRuleWitnessEnumeration D where
  rules := C.rules
  covers := C.covers
  positive := P.positive

/-- Every covered binary witness word is positive. -/
theorem witness_mem_target
    (C : BinaryRuleCoverage D)
    (P : BinaryRulePositivity D C)
    (ρ : BinaryRule N α G.arity)
    (hρ : ρ ∈ G.binaryRules) :
    D.binaryWitnessWord ρ ∈ G.StringLanguage :=
  P.positive ρ (C.covers ρ hρ)

end BinaryRuleCoverage

namespace StartRuleCoverage

variable {D : TrimmedPresentationPreCoreData T f}

/-- Build the rule-enumeration object for start-rule witnesses from coverage and
positivity. -/
def toEnumeration
    (C : StartRuleCoverage D)
    (P : StartRulePositivity D C) :
    StartRuleWitnessEnumeration D where
  indices := C.indices
  covers := C.covers
  positive := P.positive

/-- Every covered start-rule witness word is positive. -/
theorem witness_mem_target
    (C : StartRuleCoverage D)
    (P : StartRulePositivity D C)
    (ρ : StartRule N)
    (hρ : ρ ∈ G.startRules)
    (hwt : G.arity ρ.child = G.arity G.start) :
    D.startWitnessWord ρ hwt ∈ G.StringLanguage := by
  rcases C.covers ρ hρ hwt with ⟨i, hi, hEq⟩
  rw [← hEq]
  exact P.positive i hi

end StartRuleCoverage

end RuleCoverageData


section RuleCoveragePackage

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}
variable {f : Nat}
variable {T : TrimmedOutputTypePresentation G obs}

/-- Coverage-and-positivity package for rule-indexed characteristic sample
enumerations. -/
structure TrimmedPresentationRuleCoveragePackage
    (D : TrimmedPresentationPreCoreData T f) where
  anchorCoverage : AnchorRuleCoverage D
  anchorPositive : AnchorRulePositivity D anchorCoverage

  terminalCoverage : TerminalRuleCoverage D
  terminalPositive : TerminalRulePositivity D terminalCoverage

  binaryCoverage : BinaryRuleCoverage D
  binaryPositive : BinaryRulePositivity D binaryCoverage

  startCoverage : StartRuleCoverage D
  startPositive : StartRulePositivity D startCoverage

  startWord_positive :
    D.startWord ∈ G.StringLanguage

namespace TrimmedPresentationRuleCoveragePackage

variable {D : TrimmedPresentationPreCoreData T f}

/-- Convert coverage-and-positivity data to rule-indexed enumerations. -/
def toRuleEnumeration
    (P : TrimmedPresentationRuleCoveragePackage D) :
    TrimmedPresentationRuleEnumeration D where
  anchor := P.anchorCoverage.toEnumeration P.anchorPositive
  terminal := P.terminalCoverage.toEnumeration P.terminalPositive
  binary := P.binaryCoverage.toEnumeration P.binaryPositive
  start := P.startCoverage.toEnumeration P.startPositive
  startWord_positive := P.startWord_positive

/-- Convert coverage-and-positivity data to componentwise characteristic-sample
data. -/
def toComponentPackage
    (P : TrimmedPresentationRuleCoveragePackage D) :
    TrimmedPresentationComponentPackage D :=
  P.toRuleEnumeration.toComponentPackage

/-- The finite sample produced by the coverage package. -/
def sample
    (P : TrimmedPresentationRuleCoveragePackage D) :
    Finset (Word α) :=
  P.toRuleEnumeration.sample

/-- The produced sample is positive. -/
theorem sample_positive
    (P : TrimmedPresentationRuleCoveragePackage D) :
    (P.sample : Set (Word α)) ⊆ G.StringLanguage :=
  P.toRuleEnumeration.sample_positive

/-- The produced sample contains all required witness words. -/
theorem contains_witnesses
    (P : TrimmedPresentationRuleCoveragePackage D) :
    TrimmedPresentationWitnessWordSet D ⊆
      (P.sample : Set (Word α)) :=
  P.toRuleEnumeration.contains_witnesses

/-- Convert to the abstract finite-sample builder. -/
def toFiniteSampleBuilder
    (P : TrimmedPresentationRuleCoveragePackage D) :
    TrimmedPresentationFiniteSampleBuilder D :=
  P.toRuleEnumeration.toFiniteSampleBuilder

/-- Convert to a witness-sample package. -/
def toWitnessSample
    (P : TrimmedPresentationRuleCoveragePackage D) :
    TrimmedPresentationWitnessSample D P.sample :=
  P.toRuleEnumeration.toWitnessSample

/-- Convert to a characteristic-sample object. -/
def toCharacteristicSample
    (P : TrimmedPresentationRuleCoveragePackage D) :
    TrimmedPresentationCharacteristicSample D :=
  P.toRuleEnumeration.toCharacteristicSample

/-- Convert to final reachable data after adding the remaining splicing
constructor and global assumptions. -/
def toFinalReachableData
    (P : TrimmedPresentationRuleCoveragePackage D)
    (U : NamedContextSplicingConstructor α)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    FinalReachableData G P.sample obs f :=
  P.toRuleEnumeration.toFinalReachableData U hfan hL

/-- The produced sample is a characteristic sample for the reachable learner. -/
theorem characteristic_sample
    (P : TrimmedPresentationRuleCoveragePackage D)
    (U : NamedContextSplicingConstructor α)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    CharacteristicSample
      (reachableHypLanguage obs f)
      (reachableSampleLearner (α := α))
      P.sample
      G.StringLanguage :=
  P.toRuleEnumeration.characteristic_sample U hfan hL

/-- Eventual prefix-exact reconstruction from the rule-coverage package. -/
theorem prefix_exact_eventually
    (P : TrimmedPresentationRuleCoveragePackage D)
    (U : NamedContextSplicingConstructor α)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    ∀ Ttxt : TextFor G.StringLanguage,
      ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
        ReachableSampleStringLanguage (Ttxt.prefixSample n) obs f =
          G.StringLanguage :=
  P.toRuleEnumeration.prefix_exact_eventually U hfan hL

/-- Reachable Gold identification from the rule-coverage package. -/
theorem identifies_from_positive_text
    (P : TrimmedPresentationRuleCoveragePackage D)
    (U : NamedContextSplicingConstructor α)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    ∀ Ttxt : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        Ttxt :=
  P.toRuleEnumeration.identifies_from_positive_text U hfan hL

end TrimmedPresentationRuleCoveragePackage

end RuleCoveragePackage


section MainTheoremsFromRuleCoverage

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}
variable {f : Nat}
variable {T : TrimmedOutputTypePresentation G obs}
variable {D : TrimmedPresentationPreCoreData T f}

/-- Stable top-level reachable identification theorem from rule coverage and
positivity data. -/
theorem trimmed_rule_coverage_reachable_identification
    (P : TrimmedPresentationRuleCoveragePackage D)
    (U : NamedContextSplicingConstructor α)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    ∀ Ttxt : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        Ttxt :=
  P.identifies_from_positive_text U hfan hL

/-- Stable top-level prefix-exact theorem from rule coverage and positivity
data. -/
theorem trimmed_rule_coverage_reachable_prefix_exact
    (P : TrimmedPresentationRuleCoveragePackage D)
    (U : NamedContextSplicingConstructor α)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    ∀ Ttxt : TextFor G.StringLanguage,
      ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
        ReachableSampleStringLanguage (Ttxt.prefixSample n) obs f =
          G.StringLanguage :=
  P.prefix_exact_eventually U hfan hL

end MainTheoremsFromRuleCoverage

end MCFG
