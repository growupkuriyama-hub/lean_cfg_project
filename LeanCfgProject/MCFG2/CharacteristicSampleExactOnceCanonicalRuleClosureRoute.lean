/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG.CharacteristicSampleExactOnceSuccessfulRuleRealizationRoute

/-!
# CharacteristicSampleExactOnceCanonicalRuleClosureRoute.lean

The preceding successful-rule-realization route still asks the caller to choose
one present typed terminal, binary, and start rule for every original grammar
rule, and then prove that the chosen typed rule erases to that original rule.

This file removes those choices.

For a selected base-representative family `R`, the typed rule instances are
canonical:

* a terminal rule is decorated by its grammar-membership and arity proof;
* a binary rule is decorated by the transported output types of the selected
  left and right representatives;
* a start rule is decorated by the transported output type of the selected
  child representative and its start-arity proof.

A `SuccessfulOccurrenceRepresentativeCanonicalRuleClosure R` says only that
these canonical typed rules occur in the finite presentation and that their
typed endpoints agree with the selected representatives.  From this closure
property and `BasicWorkingConditions`, the entire
`SuccessfulOccurrenceRepresentativeRuleRealization R` object is constructed
automatically.

The already verified route then yields the trimmed pre-core, finite positive
characteristic sample, exact reconstruction, eventual prefix exactness, and
Gold identification.

No arbitrary typed-rule choice, rule-erasure equality, unrestricted named
context splicing constructor, or unconditional exposing transport is used.
-/

namespace MCFG

universe u v w

section CanonicalTypedRules

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}
variable {S : SuccessfulOccurrenceCompletePresentation G obs}

namespace SuccessfulOccurrenceBaseRepresentativeSelection

/-- The canonical typed terminal instance of an original terminal rule. -/
def canonicalTerminalRule
    (R : SuccessfulOccurrenceBaseRepresentativeSelection S)
    (ρ : TerminalRule N α)
    (hρ : ρ ∈ G.terminalRules)
    (hwt : G.arity ρ.lhs = 1) :
    TypedTerminalRule G where
  baseRule := ρ
  inGrammar := hρ
  wellTyped := hwt

@[simp] theorem canonicalTerminalRule_baseRule
    (R : SuccessfulOccurrenceBaseRepresentativeSelection S)
    (ρ : TerminalRule N α)
    (hρ : ρ ∈ G.terminalRules)
    (hwt : G.arity ρ.lhs = 1) :
    (R.canonicalTerminalRule ρ hρ hwt).baseRule = ρ :=
  rfl

/-- The canonical typed binary instance uses the transported output types of
the selected child representatives. -/
def canonicalBinaryRule
    (R : SuccessfulOccurrenceBaseRepresentativeSelection S)
    (ρ : BinaryRule N α G.arity)
    (hρ : ρ ∈ G.binaryRules) :
    TypedBinaryRule G M where
  baseRule := ρ
  inGrammar := hρ
  leftOut := R.transportedOutput ρ.left
  rightOut := R.transportedOutput ρ.right

@[simp] theorem canonicalBinaryRule_baseRule
    (R : SuccessfulOccurrenceBaseRepresentativeSelection S)
    (ρ : BinaryRule N α G.arity)
    (hρ : ρ ∈ G.binaryRules) :
    (R.canonicalBinaryRule ρ hρ).baseRule = ρ :=
  rfl

@[simp] theorem canonicalBinaryRule_leftOut
    (R : SuccessfulOccurrenceBaseRepresentativeSelection S)
    (ρ : BinaryRule N α G.arity)
    (hρ : ρ ∈ G.binaryRules) :
    (R.canonicalBinaryRule ρ hρ).leftOut =
      R.transportedOutput ρ.left :=
  rfl

@[simp] theorem canonicalBinaryRule_rightOut
    (R : SuccessfulOccurrenceBaseRepresentativeSelection S)
    (ρ : BinaryRule N α G.arity)
    (hρ : ρ ∈ G.binaryRules) :
    (R.canonicalBinaryRule ρ hρ).rightOut =
      R.transportedOutput ρ.right :=
  rfl

/-- The canonical typed start instance uses the transported output type of the
selected child representative. -/
def canonicalStartRule
    (R : SuccessfulOccurrenceBaseRepresentativeSelection S)
    (ρ : StartRule N)
    (hρ : ρ ∈ G.startRules)
    (hwt : G.arity ρ.child = G.arity G.start) :
    TypedStartRule G M where
  baseRule := ρ
  inGrammar := hρ
  wellTyped := hwt
  childOut := R.transportedOutput ρ.child

@[simp] theorem canonicalStartRule_baseRule
    (R : SuccessfulOccurrenceBaseRepresentativeSelection S)
    (ρ : StartRule N)
    (hρ : ρ ∈ G.startRules)
    (hwt : G.arity ρ.child = G.arity G.start) :
    (R.canonicalStartRule ρ hρ hwt).baseRule = ρ :=
  rfl

@[simp] theorem canonicalStartRule_childOut
    (R : SuccessfulOccurrenceBaseRepresentativeSelection S)
    (ρ : StartRule N)
    (hρ : ρ ∈ G.startRules)
    (hwt : G.arity ρ.child = G.arity G.start) :
    (R.canonicalStartRule ρ hρ hwt).childOut =
      R.transportedOutput ρ.child :=
  rfl

end SuccessfulOccurrenceBaseRepresentativeSelection

end CanonicalTypedRules


section CanonicalRuleClosure

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}
variable {S : SuccessfulOccurrenceCompletePresentation G obs}

/-- Closure of the successful finite presentation under the canonical typed
instances determined by the selected representative outputs.

Unlike `SuccessfulOccurrenceRepresentativeRuleRealization`, this structure
does not choose arbitrary typed rules and does not carry separate proofs that
their base rules are the intended original rules. -/
structure SuccessfulOccurrenceRepresentativeCanonicalRuleClosure
    (R : SuccessfulOccurrenceBaseRepresentativeSelection S) where

  terminal_mem :
    ∀ (ρ : TerminalRule N α)
      (hρ : ρ ∈ G.terminalRules)
      (hwt : G.arity ρ.lhs = 1),
      S.completePresentation.presentation.HasTerminalRule
        (R.canonicalTerminalRule ρ hρ hwt)

  terminal_lhs_rep :
    ∀ (ρ : TerminalRule N α)
      (hρ : ρ ∈ G.terminalRules)
      (hwt : G.arity ρ.lhs = 1),
      (R.rep ρ.lhs).node =
        (R.canonicalTerminalRule ρ hρ hwt).lhs obs

  binary_mem :
    ∀ (ρ : BinaryRule N α G.arity)
      (hρ : ρ ∈ G.binaryRules),
      S.completePresentation.presentation.HasBinaryRule
        (R.canonicalBinaryRule ρ hρ)

  binary_left_rep :
    ∀ (ρ : BinaryRule N α G.arity)
      (hρ : ρ ∈ G.binaryRules),
      (R.rep ρ.left).node =
        (R.canonicalBinaryRule ρ hρ).left

  binary_right_rep :
    ∀ (ρ : BinaryRule N α G.arity)
      (hρ : ρ ∈ G.binaryRules),
      (R.rep ρ.right).node =
        (R.canonicalBinaryRule ρ hρ).right

  binary_lhs_rep :
    ∀ (ρ : BinaryRule N α G.arity)
      (hρ : ρ ∈ G.binaryRules),
      (R.rep ρ.lhs).node =
        (R.canonicalBinaryRule ρ hρ).lhs obs

  start_mem :
    ∀ (ρ : StartRule N)
      (hρ : ρ ∈ G.startRules)
      (hwt : G.arity ρ.child = G.arity G.start),
      S.completePresentation.presentation.HasStartRule
        (R.canonicalStartRule ρ hρ hwt)

  start_child_rep :
    ∀ (ρ : StartRule N)
      (hρ : ρ ∈ G.startRules)
      (hwt : G.arity ρ.child = G.arity G.start),
      (R.rep ρ.child).node =
        (R.canonicalStartRule ρ hρ hwt).child

  start_parent_rep :
    ∀ (ρ : StartRule N)
      (hρ : ρ ∈ G.startRules)
      (hwt : G.arity ρ.child = G.arity G.start),
      (R.rep G.start).node =
        (R.canonicalStartRule ρ hρ hwt).parent

namespace SuccessfulOccurrenceRepresentativeCanonicalRuleClosure

variable {R : SuccessfulOccurrenceBaseRepresentativeSelection S}

/-- Recover the previous explicit rule-realization object from canonical rule
closure and the grammar's ordinary working side conditions. -/
def toRuleRealization
    (Q : SuccessfulOccurrenceRepresentativeCanonicalRuleClosure R)
    (hworking : G.BasicWorkingConditions) :
    SuccessfulOccurrenceRepresentativeRuleRealization R where

  terminalTypedRule := by
    intro ρ hρ
    exact R.canonicalTerminalRule ρ hρ
      (hworking.2.2.1 ρ hρ)

  terminalTypedRule_mem := by
    intro ρ hρ
    exact Q.terminal_mem ρ hρ
      (hworking.2.2.1 ρ hρ)

  terminalTypedRule_base := by
    intro ρ hρ
    rfl

  terminal_lhs_rep := by
    intro ρ hρ
    exact Q.terminal_lhs_rep ρ hρ
      (hworking.2.2.1 ρ hρ)

  binaryTypedRule := by
    intro ρ hρ
    exact R.canonicalBinaryRule ρ hρ

  binaryTypedRule_mem := by
    intro ρ hρ
    exact Q.binary_mem ρ hρ

  binaryTypedRule_base := by
    intro ρ hρ
    rfl

  binary_left_rep := by
    intro ρ hρ
    exact Q.binary_left_rep ρ hρ

  binary_right_rep := by
    intro ρ hρ
    exact Q.binary_right_rep ρ hρ

  binary_lhs_rep := by
    intro ρ hρ
    exact Q.binary_lhs_rep ρ hρ

  startTypedRule := by
    intro ρ hρ
    exact R.canonicalStartRule ρ hρ
      (hworking.2.1 ρ hρ)

  startTypedRule_mem := by
    intro ρ hρ
    exact Q.start_mem ρ hρ
      (hworking.2.1 ρ hρ)

  startTypedRule_base := by
    intro ρ hρ
    rfl

  start_child_rep := by
    intro ρ hρ
    exact Q.start_child_rep ρ hρ
      (hworking.2.1 ρ hρ)

  start_parent_rep := by
    intro ρ hρ
    exact Q.start_parent_rep ρ hρ
      (hworking.2.1 ρ hρ)

/-- Canonical closure automatically implies the output-compatibility equations
needed by the trimmed pre-core. -/
def toOutputCompatibility
    (Q : SuccessfulOccurrenceRepresentativeCanonicalRuleClosure R)
    (hworking : G.BasicWorkingConditions) :
    SuccessfulOccurrenceRepresentativeOutputCompatibility R :=
  (Q.toRuleRealization hworking).toOutputCompatibility

end SuccessfulOccurrenceRepresentativeCanonicalRuleClosure

end CanonicalRuleClosure


section CanonicalClosedConstruction

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]

/-- A successful complete typed presentation, a base-representative selection,
and closure under the canonical typed rule instances generated by that
selection. -/
structure SuccessfulOccurrenceCanonicalRuleClosedPreCoreConstruction
    (G : WorkingMCFG N α)
    (obs : α → M) where

  presentation :
    SuccessfulOccurrenceCompletePresentation G obs

  representatives :
    SuccessfulOccurrenceBaseRepresentativeSelection presentation

  canonicalClosure :
    SuccessfulOccurrenceRepresentativeCanonicalRuleClosure representatives

namespace SuccessfulOccurrenceCanonicalRuleClosedPreCoreConstruction

/-- Construct the preceding explicit typed-rule-realization package. -/
def toRuleRealizedPreCoreConstruction
    {G : WorkingMCFG N α}
    {obs : α → M}
    (C : SuccessfulOccurrenceCanonicalRuleClosedPreCoreConstruction G obs)
    (hworking : G.BasicWorkingConditions) :
    SuccessfulOccurrenceRuleRealizedPreCoreConstruction G obs where
  presentation := C.presentation
  representatives := C.representatives
  ruleRealization :=
    C.canonicalClosure.toRuleRealization hworking

/-- Construct the output-compatible pre-core package directly. -/
def toPreCoreConstruction
    {G : WorkingMCFG N α}
    {obs : α → M}
    (C : SuccessfulOccurrenceCanonicalRuleClosedPreCoreConstruction G obs)
    (hworking : G.BasicWorkingConditions) :
    SuccessfulOccurrencePreCoreConstruction G obs :=
  (C.toRuleRealizedPreCoreConstruction hworking).toPreCoreConstruction

/-- Construct the trimmed presentation pre-core. -/
def toPreCoreData
    {G : WorkingMCFG N α}
    {obs : α → M}
    {f : Nat}
    (C : SuccessfulOccurrenceCanonicalRuleClosedPreCoreConstruction G obs)
    (hworking : G.BasicWorkingConditions) :
    TrimmedPresentationPreCoreData
      (C.toPreCoreConstruction hworking).trimmedPresentation f :=
  (C.toPreCoreConstruction hworking).toPreCoreData hworking

/-- Construct the successful occurrence data used by the exact-once
characteristic-sample route. -/
def toSuccessfulOccurrenceData
    {G : WorkingMCFG N α}
    {obs : α → M}
    {f : Nat}
    (C : SuccessfulOccurrenceCanonicalRuleClosedPreCoreConstruction G obs)
    (hworking : G.BasicWorkingConditions) :
    TrimmedPresentationSuccessfulOccurrenceData
      (C.toPreCoreData (f := f) hworking) :=
  (C.toPreCoreConstruction hworking).
    toSuccessfulOccurrenceData hworking

end SuccessfulOccurrenceCanonicalRuleClosedPreCoreConstruction

end CanonicalClosedConstruction


section FiniteCanonicalClosedRoute

variable {N : Type v} {α : Type u} {M : Type w}
variable [Finite N]
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}
variable {f : Nat}

namespace SuccessfulOccurrenceCanonicalRuleClosedPreCoreConstruction

/-- Concrete finite characteristic sample produced from canonical typed-rule
closure. -/
noncomputable def finiteSample
    (C : SuccessfulOccurrenceCanonicalRuleClosedPreCoreConstruction G obs)
    (hworking : G.ExactWorkingConditions) :
    Finset (Word α) :=
  (C.toRuleRealizedPreCoreConstruction hworking.basic).
    finiteSample (f := f) hworking

/-- The canonical-closure sample is positive. -/
theorem finiteSample_positive
    (C : SuccessfulOccurrenceCanonicalRuleClosedPreCoreConstruction G obs)
    (hworking : G.ExactWorkingConditions) :
    (C.finiteSample (f := f) hworking : Set (Word α)) ⊆
      G.StringLanguage :=
  (C.toRuleRealizedPreCoreConstruction hworking.basic).
    finiteSample_positive (f := f) hworking

/-- Exact reconstruction on every positive finite superset of the generated
sample. -/
theorem exact_for_positive_superset
    (C : SuccessfulOccurrenceCanonicalRuleClosedPreCoreConstruction G obs)
    (hworking : G.ExactWorkingConditions)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage)
    {K : Finset (Word α)}
    (hCK :
      (C.finiteSample (f := f) hworking : Set (Word α)) ⊆
        (K : Set (Word α)))
    (hKpos : (K : Set (Word α)) ⊆ G.StringLanguage) :
    ReachableSampleStringLanguage K obs f =
      G.StringLanguage :=
  (C.toRuleRealizedPreCoreConstruction hworking.basic).
    exact_for_positive_superset
      (f := f) hworking hfan hL hCK hKpos

/-- Eventual prefix-exact reconstruction from canonical typed-rule closure. -/
theorem exact_prefix_reconstruction
    (C : SuccessfulOccurrenceCanonicalRuleClosedPreCoreConstruction G obs)
    (hworking : G.ExactWorkingConditions)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    ∀ Ttxt : TextFor G.StringLanguage,
      ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
        ReachableSampleStringLanguage (Ttxt.prefixSample n) obs f =
          G.StringLanguage :=
  (C.toRuleRealizedPreCoreConstruction hworking.basic).
    exact_prefix_reconstruction
      (f := f) hworking hfan hL

/-- Gold identification from canonical typed-rule closure. -/
theorem identifies_from_positive_text
    (C : SuccessfulOccurrenceCanonicalRuleClosedPreCoreConstruction G obs)
    (hworking : G.ExactWorkingConditions)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    ∀ Ttxt : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        Ttxt :=
  (C.toRuleRealizedPreCoreConstruction hworking.basic).
    identifies_from_positive_text
      (f := f) hworking hfan hL

/-- Paper-facing identification theorem from a successful complete
presentation closed under the canonical typed rules determined by its selected
representatives. -/
theorem exact_working_paper_main_theorem
    (C : SuccessfulOccurrenceCanonicalRuleClosedPreCoreConstruction G obs)
    (hworking : G.ExactWorkingConditions)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    PaperConstructiveIdentificationConclusion G obs :=
  (C.toRuleRealizedPreCoreConstruction hworking.basic).
    exact_working_paper_main_theorem
      (f := f) hworking hfan hL

/-- Full characteristic-sample, prefix-exact, and Gold-identification package
from canonical typed-rule closure. -/
theorem exact_working_paper_conclusion_package
    (C : SuccessfulOccurrenceCanonicalRuleClosedPreCoreConstruction G obs)
    (hworking : G.ExactWorkingConditions)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    PaperConstructiveLearningConclusionPackage G obs :=
  (C.toRuleRealizedPreCoreConstruction hworking.basic).
    exact_working_paper_conclusion_package
      (f := f) hworking hfan hL

end SuccessfulOccurrenceCanonicalRuleClosedPreCoreConstruction

end FiniteCanonicalClosedRoute


section CanonicalClosedTopLevel

variable {N : Type v} {α : Type u} {M : Type w}
variable [Finite N]
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}
variable {f : Nat}

/-- Stable paper-facing endpoint from canonical typed-rule closure. -/
theorem trimmed_successful_canonical_rule_closure_exact_working_main_theorem
    (C : SuccessfulOccurrenceCanonicalRuleClosedPreCoreConstruction G obs)
    (hworking : G.ExactWorkingConditions)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    PaperConstructiveIdentificationConclusion G obs :=
  C.exact_working_paper_main_theorem
    (f := f) hworking hfan hL

/-- Stable full conclusion package from canonical typed-rule closure. -/
theorem trimmed_successful_canonical_rule_closure_exact_working_conclusion_package
    (C : SuccessfulOccurrenceCanonicalRuleClosedPreCoreConstruction G obs)
    (hworking : G.ExactWorkingConditions)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    PaperConstructiveLearningConclusionPackage G obs :=
  C.exact_working_paper_conclusion_package
    (f := f) hworking hfan hL

end CanonicalClosedTopLevel

end MCFG
