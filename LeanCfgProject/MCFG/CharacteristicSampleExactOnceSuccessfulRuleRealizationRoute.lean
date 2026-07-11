/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG.CharacteristicSampleExactOnceSuccessfulPresentationRoute

/-!
# CharacteristicSampleExactOnceSuccessfulRuleRealizationRoute.lean

`CharacteristicSampleExactOnceSuccessfulPresentationRoute.lean` reduces the
remaining pre-core construction to a complete typed presentation, successful
typed occurrences, a base-representative selection, and three rule-level
output-type equations.

This file replaces those output equations by more concrete presentation data.

For every original terminal, binary, and start rule, it selects an actual typed
rule present in the finite output-type presentation.  The chosen base
representatives are required to coincide with the typed rule's endpoints:

* a terminal representative is the typed terminal lhs;
* binary representatives are the typed left child, right child, and lhs;
* a start child representative is the typed start child, and the selected
  grammar-start representative is its transported parent output type.

The three output-compatibility equations are then derived automatically from
these endpoint equalities.  The already verified successful-presentation route
constructs the pre-core, finite positive characteristic sample, exact
reconstruction, and Gold identification.

No unrestricted named-context splicing constructor, unconditional exposing
transport, `sorry`, `admit`, or `axiom` is used.
-/

namespace MCFG

universe u v w

section TypedStartParents

variable {N : Type v} {α : Type u} {M : Type w}

/-- The output-typed grammar-start nonterminal associated with a typed start
rule. -/
def TypedStartRule.parent
    {G : WorkingMCFG N α}
    (σ : TypedStartRule G M) :
    TypedNonterminal G M where
  base := G.start
  out := castTuple σ.wellTyped σ.childOut

@[simp] theorem TypedStartRule.parent_base
    {G : WorkingMCFG N α}
    (σ : TypedStartRule G M) :
    σ.parent.base = G.start :=
  rfl

@[simp] theorem TypedStartRule.parent_out
    {G : WorkingMCFG N α}
    (σ : TypedStartRule G M) :
    σ.parent.out = castTuple σ.wellTyped σ.childOut :=
  rfl

end TypedStartParents


section TransportedRepresentativeOutputs

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}
variable {S : SuccessfulOccurrenceCompletePresentation G obs}

namespace SuccessfulOccurrenceBaseRepresentativeSelection

/-- If the selected representative node is identified with a typed
nonterminal `X`, its transported output is the output of `X`, transported along
the corresponding base equality.

This lemma removes all dependence on the particular proof stored in
`rep_base_eq`; proof irrelevance identifies it with the base equality supplied
by `X`. -/
theorem transportedOutput_eq_of_node_eq
    (R : SuccessfulOccurrenceBaseRepresentativeSelection S)
    (A : N)
    (X : TypedNonterminal G M)
    (hbase : X.base = A)
    (hnode : (R.rep A).node = X) :
    R.transportedOutput A =
      castTuple (congrArg G.arity hbase) X.out := by
  cases hnode
  unfold transportedOutput repArityEq
  have hp :
      R.rep_base_eq A = hbase :=
    Subsingleton.elim _ _
  cases hp
  rfl

/-- Special case when the typed node has definitionally the selected base
nonterminal. -/
theorem transportedOutput_eq_of_node_eq_rfl
    (R : SuccessfulOccurrenceBaseRepresentativeSelection S)
    (A : N)
    (X : TypedNonterminal G M)
    (hbase : X.base = A)
    (hnode : (R.rep A).node = X)
    (hbaseRfl :
      congrArg G.arity hbase =
        (rfl : G.arity A = G.arity A)) :
    R.transportedOutput A = X.out := by
  rw [R.transportedOutput_eq_of_node_eq A X hbase hnode]
  rw [hbaseRfl]
  rfl

end SuccessfulOccurrenceBaseRepresentativeSelection

end TransportedRepresentativeOutputs


section RuleRealizationData

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}
variable {S : SuccessfulOccurrenceCompletePresentation G obs}

/-- Concrete realization of every original grammar rule by a typed rule that
is actually present in the finite presentation.

The endpoint equalities say that the base representatives selected for the
pre-core are precisely the endpoints of the realizing typed rules. -/
structure SuccessfulOccurrenceRepresentativeRuleRealization
    (R : SuccessfulOccurrenceBaseRepresentativeSelection S) where

  terminalTypedRule :
    ∀ (ρ : TerminalRule N α),
      ρ ∈ G.terminalRules →
        TypedTerminalRule G

  terminalTypedRule_mem :
    ∀ (ρ : TerminalRule N α)
      (hρ : ρ ∈ G.terminalRules),
      S.completePresentation.presentation.HasTerminalRule
        (terminalTypedRule ρ hρ)

  terminalTypedRule_base :
    ∀ (ρ : TerminalRule N α)
      (hρ : ρ ∈ G.terminalRules),
      (terminalTypedRule ρ hρ).baseRule = ρ

  terminal_lhs_rep :
    ∀ (ρ : TerminalRule N α)
      (hρ : ρ ∈ G.terminalRules),
      (R.rep ρ.lhs).node =
        (terminalTypedRule ρ hρ).lhs obs

  binaryTypedRule :
    ∀ (ρ : BinaryRule N α G.arity),
      ρ ∈ G.binaryRules →
        TypedBinaryRule G M

  binaryTypedRule_mem :
    ∀ (ρ : BinaryRule N α G.arity)
      (hρ : ρ ∈ G.binaryRules),
      S.completePresentation.presentation.HasBinaryRule
        (binaryTypedRule ρ hρ)

  binaryTypedRule_base :
    ∀ (ρ : BinaryRule N α G.arity)
      (hρ : ρ ∈ G.binaryRules),
      (binaryTypedRule ρ hρ).baseRule = ρ

  binary_left_rep :
    ∀ (ρ : BinaryRule N α G.arity)
      (hρ : ρ ∈ G.binaryRules),
      (R.rep ρ.left).node =
        (binaryTypedRule ρ hρ).left

  binary_right_rep :
    ∀ (ρ : BinaryRule N α G.arity)
      (hρ : ρ ∈ G.binaryRules),
      (R.rep ρ.right).node =
        (binaryTypedRule ρ hρ).right

  binary_lhs_rep :
    ∀ (ρ : BinaryRule N α G.arity)
      (hρ : ρ ∈ G.binaryRules),
      (R.rep ρ.lhs).node =
        (binaryTypedRule ρ hρ).lhs obs

  startTypedRule :
    ∀ (ρ : StartRule N),
      ρ ∈ G.startRules →
        TypedStartRule G M

  startTypedRule_mem :
    ∀ (ρ : StartRule N)
      (hρ : ρ ∈ G.startRules),
      S.completePresentation.presentation.HasStartRule
        (startTypedRule ρ hρ)

  startTypedRule_base :
    ∀ (ρ : StartRule N)
      (hρ : ρ ∈ G.startRules),
      (startTypedRule ρ hρ).baseRule = ρ

  start_child_rep :
    ∀ (ρ : StartRule N)
      (hρ : ρ ∈ G.startRules),
      (R.rep ρ.child).node =
        (startTypedRule ρ hρ).child

  start_parent_rep :
    ∀ (ρ : StartRule N)
      (hρ : ρ ∈ G.startRules),
      (R.rep G.start).node =
        (startTypedRule ρ hρ).parent

namespace SuccessfulOccurrenceRepresentativeRuleRealization

variable
  {R : SuccessfulOccurrenceBaseRepresentativeSelection S}

/-- The realizing typed terminal rule is genuinely present. -/
theorem terminal_present
    (Q : SuccessfulOccurrenceRepresentativeRuleRealization R)
    (ρ : TerminalRule N α)
    (hρ : ρ ∈ G.terminalRules) :
    S.completePresentation.presentation.HasTerminalRule
      (Q.terminalTypedRule ρ hρ) :=
  Q.terminalTypedRule_mem ρ hρ

/-- The realizing typed binary rule is genuinely present. -/
theorem binary_present
    (Q : SuccessfulOccurrenceRepresentativeRuleRealization R)
    (ρ : BinaryRule N α G.arity)
    (hρ : ρ ∈ G.binaryRules) :
    S.completePresentation.presentation.HasBinaryRule
      (Q.binaryTypedRule ρ hρ) :=
  Q.binaryTypedRule_mem ρ hρ

/-- The realizing typed start rule is genuinely present. -/
theorem start_present
    (Q : SuccessfulOccurrenceRepresentativeRuleRealization R)
    (ρ : StartRule N)
    (hρ : ρ ∈ G.startRules) :
    S.completePresentation.presentation.HasStartRule
      (Q.startTypedRule ρ hρ) :=
  Q.startTypedRule_mem ρ hρ

/-- Typed-rule realization implies the terminal representative output
equation. -/
theorem terminal_output
    (Q : SuccessfulOccurrenceRepresentativeRuleRealization R)
    (ρ : TerminalRule N α)
    (hρ : ρ ∈ G.terminalRules)
    (hwt : G.arity ρ.lhs = 1) :
    R.transportedOutput ρ.lhs =
      tupleType obs
        (castTuple hwt.symm ρ.outputTuple) := by
  let τ := Q.terminalTypedRule ρ hρ
  have hbase : τ.baseRule = ρ :=
    Q.terminalTypedRule_base ρ hρ
  have hlhs :
      (R.rep ρ.lhs).node = τ.lhs obs :=
    Q.terminal_lhs_rep ρ hρ
  cases hbase
  have hout :
      R.transportedOutput τ.baseRule.lhs =
        (τ.lhs obs).out := by
    simpa using
      R.transportedOutput_eq_of_node_eq
        τ.baseRule.lhs
        (τ.lhs obs)
        rfl
        hlhs
  calc
    R.transportedOutput τ.baseRule.lhs =
        (τ.lhs obs).out :=
      hout
    _ =
        tupleType obs
          (castTuple hwt.symm τ.baseRule.outputTuple) := by
      have hp : hwt = τ.wellTyped :=
        Subsingleton.elim _ _
      cases hp
      exact (τ.cast_outputTuple_matches_lhs obs).symm

/-- Typed-rule realization implies the binary representative output equation. -/
theorem binary_output
    (Q : SuccessfulOccurrenceRepresentativeRuleRealization R)
    (ρ : BinaryRule N α G.arity)
    (hρ : ρ ∈ G.binaryRules) :
    R.transportedOutput ρ.lhs =
      BinaryRule.outputType obs ρ
        (R.transportedOutput ρ.left)
        (R.transportedOutput ρ.right) := by
  let τ := Q.binaryTypedRule ρ hρ
  have hbase : τ.baseRule = ρ :=
    Q.binaryTypedRule_base ρ hρ
  have hleft :
      (R.rep ρ.left).node = τ.left :=
    Q.binary_left_rep ρ hρ
  have hright :
      (R.rep ρ.right).node = τ.right :=
    Q.binary_right_rep ρ hρ
  have hlhs :
      (R.rep ρ.lhs).node = τ.lhs obs :=
    Q.binary_lhs_rep ρ hρ
  cases hbase
  have houtLeft :
      R.transportedOutput τ.baseRule.left =
        τ.leftOut := by
    simpa [TypedBinaryRule.left] using
      R.transportedOutput_eq_of_node_eq
        τ.baseRule.left
        τ.left
        rfl
        hleft
  have houtRight :
      R.transportedOutput τ.baseRule.right =
        τ.rightOut := by
    simpa [TypedBinaryRule.right] using
      R.transportedOutput_eq_of_node_eq
        τ.baseRule.right
        τ.right
        rfl
        hright
  have houtLhs :
      R.transportedOutput τ.baseRule.lhs =
        BinaryRule.outputType obs τ.baseRule
          τ.leftOut τ.rightOut := by
    simpa [TypedBinaryRule.lhs] using
      R.transportedOutput_eq_of_node_eq
        τ.baseRule.lhs
        (τ.lhs obs)
        rfl
        hlhs
  calc
    R.transportedOutput τ.baseRule.lhs =
        BinaryRule.outputType obs τ.baseRule
          τ.leftOut τ.rightOut :=
      houtLhs
    _ =
        BinaryRule.outputType obs τ.baseRule
          (R.transportedOutput τ.baseRule.left)
          (R.transportedOutput τ.baseRule.right) := by
      rw [houtLeft, houtRight]

/-- Typed-rule realization implies the start representative output equation. -/
theorem start_output
    (Q : SuccessfulOccurrenceRepresentativeRuleRealization R)
    (ρ : StartRule N)
    (hρ : ρ ∈ G.startRules)
    (hwt : G.arity ρ.child = G.arity G.start) :
    R.transportedOutput G.start =
      castTuple hwt
        (R.transportedOutput ρ.child) := by
  let σ := Q.startTypedRule ρ hρ
  have hbase : σ.baseRule = ρ :=
    Q.startTypedRule_base ρ hρ
  have hchild :
      (R.rep ρ.child).node = σ.child :=
    Q.start_child_rep ρ hρ
  have hparent :
      (R.rep G.start).node = σ.parent :=
    Q.start_parent_rep ρ hρ
  cases hbase
  have houtChild :
      R.transportedOutput σ.baseRule.child =
        σ.childOut := by
    simpa [TypedStartRule.child] using
      R.transportedOutput_eq_of_node_eq
        σ.baseRule.child
        σ.child
        rfl
        hchild
  have houtParent :
      R.transportedOutput G.start =
        castTuple σ.wellTyped σ.childOut := by
    simpa [TypedStartRule.parent] using
      R.transportedOutput_eq_of_node_eq
        G.start
        σ.parent
        rfl
        hparent
  calc
    R.transportedOutput G.start =
        castTuple σ.wellTyped σ.childOut :=
      houtParent
    _ =
        castTuple hwt
          (R.transportedOutput σ.baseRule.child) := by
      rw [houtChild]
      have hp : hwt = σ.wellTyped :=
        Subsingleton.elim _ _
      cases hp
      rfl

/-- All three output-compatibility obligations are consequences of concrete
typed-rule realization. -/
def toOutputCompatibility
    (Q : SuccessfulOccurrenceRepresentativeRuleRealization R) :
    SuccessfulOccurrenceRepresentativeOutputCompatibility R where
  terminal_output := Q.terminal_output
  binary_output := Q.binary_output
  start_output := Q.start_output

end SuccessfulOccurrenceRepresentativeRuleRealization

end RuleRealizationData


section RuleRealizedPreCoreConstruction

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]

/-- A successful complete typed presentation with base representatives and
concrete present typed rules realizing every original grammar rule. -/
structure SuccessfulOccurrenceRuleRealizedPreCoreConstruction
    (G : WorkingMCFG N α)
    (obs : α → M) where

  presentation :
    SuccessfulOccurrenceCompletePresentation G obs

  representatives :
    SuccessfulOccurrenceBaseRepresentativeSelection presentation

  ruleRealization :
    SuccessfulOccurrenceRepresentativeRuleRealization representatives

namespace SuccessfulOccurrenceRuleRealizedPreCoreConstruction

/-- Forget concrete typed-rule witnesses and recover the output-compatible
pre-core construction from the previous file. -/
def toPreCoreConstruction
    {G : WorkingMCFG N α}
    {obs : α → M}
    (C : SuccessfulOccurrenceRuleRealizedPreCoreConstruction G obs) :
    SuccessfulOccurrencePreCoreConstruction G obs where
  presentation := C.presentation
  representatives := C.representatives
  compatibility := C.ruleRealization.toOutputCompatibility

/-- Construct the trimmed presentation and pre-core from concrete typed-rule
realization. -/
def toPreCoreData
    {G : WorkingMCFG N α}
    {obs : α → M}
    {f : Nat}
    (C : SuccessfulOccurrenceRuleRealizedPreCoreConstruction G obs)
    (hworking : G.BasicWorkingConditions) :
    TrimmedPresentationPreCoreData
      C.toPreCoreConstruction.trimmedPresentation f :=
  C.toPreCoreConstruction.toPreCoreData hworking

/-- Construct the base-indexed successful occurrence data. -/
def toSuccessfulOccurrenceData
    {G : WorkingMCFG N α}
    {obs : α → M}
    {f : Nat}
    (C : SuccessfulOccurrenceRuleRealizedPreCoreConstruction G obs)
    (hworking : G.BasicWorkingConditions) :
    TrimmedPresentationSuccessfulOccurrenceData
      (C.toPreCoreData (f := f) hworking) :=
  C.toPreCoreConstruction.toSuccessfulOccurrenceData hworking

end SuccessfulOccurrenceRuleRealizedPreCoreConstruction

end RuleRealizedPreCoreConstruction


section FiniteRuleRealizedRoute

variable {N : Type v} {α : Type u} {M : Type w}
variable [Finite N]
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}
variable {f : Nat}

namespace SuccessfulOccurrenceRuleRealizedPreCoreConstruction

/-- The finite characteristic-sample candidate generated from present typed
rules and successful occurrences. -/
noncomputable def finiteSample
    (C : SuccessfulOccurrenceRuleRealizedPreCoreConstruction G obs)
    (hworking : G.ExactWorkingConditions) :
    Finset (Word α) :=
  C.toPreCoreConstruction.finiteSample
    (f := f) hworking

/-- The generated sample is positive. -/
theorem finiteSample_positive
    (C : SuccessfulOccurrenceRuleRealizedPreCoreConstruction G obs)
    (hworking : G.ExactWorkingConditions) :
    (C.finiteSample (f := f) hworking : Set (Word α)) ⊆
      G.StringLanguage :=
  C.toPreCoreConstruction.finiteSample_positive
    (f := f) hworking

/-- Exact reconstruction on every positive finite superset of the generated
sample. -/
theorem exact_for_positive_superset
    (C : SuccessfulOccurrenceRuleRealizedPreCoreConstruction G obs)
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
  C.toPreCoreConstruction.exact_for_positive_superset
    (f := f) hworking hfan hL hCK hKpos

/-- Eventual prefix-exact reconstruction. -/
theorem exact_prefix_reconstruction
    (C : SuccessfulOccurrenceRuleRealizedPreCoreConstruction G obs)
    (hworking : G.ExactWorkingConditions)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    ∀ Ttxt : TextFor G.StringLanguage,
      ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
        ReachableSampleStringLanguage (Ttxt.prefixSample n) obs f =
          G.StringLanguage :=
  C.toPreCoreConstruction.exact_prefix_reconstruction
    (f := f) hworking hfan hL

/-- Gold identification from concrete present typed-rule realization. -/
theorem identifies_from_positive_text
    (C : SuccessfulOccurrenceRuleRealizedPreCoreConstruction G obs)
    (hworking : G.ExactWorkingConditions)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    ∀ Ttxt : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        Ttxt :=
  C.toPreCoreConstruction.identifies_from_positive_text
    (f := f) hworking hfan hL

/-- Paper-facing identification theorem from successful occurrences and
present typed rules realizing all original rules. -/
theorem exact_working_paper_main_theorem
    (C : SuccessfulOccurrenceRuleRealizedPreCoreConstruction G obs)
    (hworking : G.ExactWorkingConditions)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    PaperConstructiveIdentificationConclusion G obs :=
  C.toPreCoreConstruction.exact_working_paper_main_theorem
    (f := f) hworking hfan hL

/-- Full characteristic-sample, prefix-exact, and Gold-identification package
from concrete typed-rule realization. -/
theorem exact_working_paper_conclusion_package
    (C : SuccessfulOccurrenceRuleRealizedPreCoreConstruction G obs)
    (hworking : G.ExactWorkingConditions)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    PaperConstructiveLearningConclusionPackage G obs :=
  C.toPreCoreConstruction.exact_working_paper_conclusion_package
    (f := f) hworking hfan hL

end SuccessfulOccurrenceRuleRealizedPreCoreConstruction

end FiniteRuleRealizedRoute


section RuleRealizedTopLevel

variable {N : Type v} {α : Type u} {M : Type w}
variable [Finite N]
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}
variable {f : Nat}

/-- Stable paper-facing endpoint from explicit successful occurrences and
actual present typed rules realizing every original grammar rule. -/
theorem trimmed_successful_rule_realization_exact_working_main_theorem
    (C : SuccessfulOccurrenceRuleRealizedPreCoreConstruction G obs)
    (hworking : G.ExactWorkingConditions)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    PaperConstructiveIdentificationConclusion G obs :=
  C.exact_working_paper_main_theorem
    (f := f) hworking hfan hL

/-- Stable full conclusion package from explicit successful occurrences and
present typed-rule realization. -/
theorem trimmed_successful_rule_realization_exact_working_conclusion_package
    (C : SuccessfulOccurrenceRuleRealizedPreCoreConstruction G obs)
    (hworking : G.ExactWorkingConditions)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    PaperConstructiveLearningConclusionPackage G obs :=
  C.exact_working_paper_conclusion_package
    (f := f) hworking hfan hL

end RuleRealizedTopLevel

end MCFG
