import LeanCfgProject.MCFG.FI_v2_1_CanonicalRuleListSpecificationGold

/-!
# FI v2.1 Lean experiment: canonical rule-list counting summary

This fifty-sixth layer records the elementary size information carried by a
canonical learner grammar package.

The previous layers isolate the rule-list specification: finite refined rule
lists cover all ordinary output-type rule refinements and are supported by the
canonical finite-monoid rule-enumeration plan.  This file adds a small counting
API around those lists.  It is intentionally modest: no complexity bound is
claimed yet.  The purpose is to make the finite listed data, its ordinary base
rule counts, and its refined rule counts available through stable names for
later size and polynomial-data statements.
-/

namespace FIv21

universe u v w

noncomputable section

section CanonicalRuleListCounting

variable {N : Type w} {α : Type u}
variable [DecidableEq α]
variable {M : Type v} [Monoid M] [Fintype M]

namespace CanonicalLearnerGrammarPackage

/-- Ordinary terminal-rule count in the canonical finite-monoid enumeration
plan associated with the package. -/
def ordinaryTerminalRuleCount
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (P : CanonicalLearnerGrammarPackage G obs K) : Nat :=
  P.ruleEnumerationPlan.terminalRuleCount

/-- Ordinary binary-rule count in the canonical finite-monoid enumeration plan. -/
def ordinaryBinaryRuleCount
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (P : CanonicalLearnerGrammarPackage G obs K) : Nat :=
  P.ruleEnumerationPlan.binaryRuleCount

/-- Ordinary start-rule count in the canonical finite-monoid enumeration plan. -/
def ordinaryStartRuleCount
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (P : CanonicalLearnerGrammarPackage G obs K) : Nat :=
  P.ruleEnumerationPlan.startRuleCount

/-- Total ordinary-rule count seen by the canonical finite-monoid plan. -/
def ordinaryRuleCount
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (P : CanonicalLearnerGrammarPackage G obs K) : Nat :=
  P.ordinaryTerminalRuleCount +
  P.ordinaryBinaryRuleCount +
  P.ordinaryStartRuleCount

/-- Output-type count at arity `d` in the package's finite enumeration plan. -/
def planOutputTypeCount
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (P : CanonicalLearnerGrammarPackage G obs K) (d : Nat) : Nat :=
  P.ruleEnumerationPlan.outputTypeCount d

/-- Binary child-type choice count for an ordinary binary rule. -/
def planBinaryTypeChoiceCount
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (P : CanonicalLearnerGrammarPackage G obs K)
    (ρ : BinaryRule N α G.arity) : Nat :=
  P.ruleEnumerationPlan.binaryTypeChoiceCount ρ

/-- Start child-type choice count for an ordinary start rule. -/
def planStartTypeChoiceCount
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (P : CanonicalLearnerGrammarPackage G obs K)
    (ρ : StartRule N) : Nat :=
  P.ruleEnumerationPlan.startTypeChoiceCount ρ

/-- The refined terminal-rule count is literally the length of the listed
refined terminal-rule list. -/
theorem refinedTerminalRuleCount_eq_length
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (P : CanonicalLearnerGrammarPackage G obs K) :
    P.refinedTerminalRuleCount = P.finiteRefinedGrammar.terminalRules.length := by
  rfl

/-- The refined binary-rule count is the length of the listed refined binary
rule list. -/
theorem refinedBinaryRuleCount_eq_length
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (P : CanonicalLearnerGrammarPackage G obs K) :
    P.refinedBinaryRuleCount = P.finiteRefinedGrammar.binaryRules.length := by
  rfl

/-- The refined start-rule count is the length of the listed refined start-rule
list. -/
theorem refinedStartRuleCount_eq_length
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (P : CanonicalLearnerGrammarPackage G obs K) :
    P.refinedStartRuleCount = P.finiteRefinedGrammar.startRules.length := by
  rfl

/-- The total refined-rule count is the sum of the three listed refined-rule
counts. -/
theorem refinedRuleCount_eq_sum
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (P : CanonicalLearnerGrammarPackage G obs K) :
    P.refinedRuleCount =
      P.refinedTerminalRuleCount +
      P.refinedBinaryRuleCount +
      P.refinedStartRuleCount := by
  rfl

/-- The ordinary rule count is the sum of the ordinary rule counts in the
canonical plan. -/
theorem ordinaryRuleCount_eq_sum
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (P : CanonicalLearnerGrammarPackage G obs K) :
    P.ordinaryRuleCount =
      P.ordinaryTerminalRuleCount +
      P.ordinaryBinaryRuleCount +
      P.ordinaryStartRuleCount := by
  rfl

end CanonicalLearnerGrammarPackage

/-- Counting and finite-rule-list summary attached to a canonical learner
grammar package.

This keeps the size information separate from the semantic exactness
certificates.  Future complexity layers can extend this structure with actual
upper bounds without changing the earlier exactness API. -/
structure CanonicalRuleListCountingSpecification
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (P : CanonicalLearnerGrammarPackage G obs K) where
  ruleLists : CanonicalRuleListSpecification P
  terminalCount_eq :
    P.refinedTerminalRuleCount = P.finiteRefinedGrammar.terminalRules.length
  binaryCount_eq :
    P.refinedBinaryRuleCount = P.finiteRefinedGrammar.binaryRules.length
  startCount_eq :
    P.refinedStartRuleCount = P.finiteRefinedGrammar.startRules.length
  totalCount_eq :
    P.refinedRuleCount =
      P.refinedTerminalRuleCount +
      P.refinedBinaryRuleCount +
      P.refinedStartRuleCount
  ordinaryTotal_eq :
    P.ordinaryRuleCount =
      P.ordinaryTerminalRuleCount +
      P.ordinaryBinaryRuleCount +
      P.ordinaryStartRuleCount

namespace CanonicalRuleListCountingSpecification

/-- Every canonical learner grammar package carries the counting summary. -/
def ofPackage
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (P : CanonicalLearnerGrammarPackage G obs K) :
    CanonicalRuleListCountingSpecification P :=
  { ruleLists := CanonicalRuleListSpecification.ofPackage P
    terminalCount_eq := P.refinedTerminalRuleCount_eq_length
    binaryCount_eq := P.refinedBinaryRuleCount_eq_length
    startCount_eq := P.refinedStartRuleCount_eq_length
    totalCount_eq := P.refinedRuleCount_eq_sum
    ordinaryTotal_eq := P.ordinaryRuleCount_eq_sum }

/-- Forget the counting summary to the underlying rule-list specification. -/
def toRuleListSpecification
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {P : CanonicalLearnerGrammarPackage G obs K}
    (S : CanonicalRuleListCountingSpecification P) :
    CanonicalRuleListSpecification P :=
  S.ruleLists

/-- Rule-list coverage inherited from the underlying specification. -/
theorem refinedRuleLists_coverAll
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {P : CanonicalLearnerGrammarPackage G obs K}
    (S : CanonicalRuleListCountingSpecification P) :
    P.finiteRefinedGrammar.CoversAllOrdinaryRuleRefinements := by
  exact S.ruleLists.coversAll

/-- Rule-list plan support inherited from the underlying specification. -/
theorem refinedRuleLists_supportedByPlan
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {P : CanonicalLearnerGrammarPackage G obs K}
    (S : CanonicalRuleListCountingSpecification P) :
    P.finiteRefinedGrammar.AllRulesSupportedByPlan P.ruleEnumerationPlan := by
  exact S.ruleLists.supportedByPlan

/-- Terminal refined-rule count exposed by the counting summary. -/
theorem terminal_count_eq_length
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {P : CanonicalLearnerGrammarPackage G obs K}
    (S : CanonicalRuleListCountingSpecification P) :
    P.refinedTerminalRuleCount = P.finiteRefinedGrammar.terminalRules.length := by
  exact S.terminalCount_eq

/-- Binary refined-rule count exposed by the counting summary. -/
theorem binary_count_eq_length
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {P : CanonicalLearnerGrammarPackage G obs K}
    (S : CanonicalRuleListCountingSpecification P) :
    P.refinedBinaryRuleCount = P.finiteRefinedGrammar.binaryRules.length := by
  exact S.binaryCount_eq

/-- Start refined-rule count exposed by the counting summary. -/
theorem start_count_eq_length
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {P : CanonicalLearnerGrammarPackage G obs K}
    (S : CanonicalRuleListCountingSpecification P) :
    P.refinedStartRuleCount = P.finiteRefinedGrammar.startRules.length := by
  exact S.startCount_eq

/-- Total refined-rule count exposed by the counting summary. -/
theorem total_count_eq_sum
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {P : CanonicalLearnerGrammarPackage G obs K}
    (S : CanonicalRuleListCountingSpecification P) :
    P.refinedRuleCount =
      P.refinedTerminalRuleCount +
      P.refinedBinaryRuleCount +
      P.refinedStartRuleCount := by
  exact S.totalCount_eq

end CanonicalRuleListCountingSpecification

end CanonicalRuleListCounting

end

end FIv21
