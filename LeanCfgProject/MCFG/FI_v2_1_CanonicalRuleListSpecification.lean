import LeanCfgProject.MCFG.FI_v2_1_CanonicalLearnerGrammarGold

/-!
# FI v2.1 Lean experiment: canonical rule-list specification

This fifty-third layer records the rule-list obligations carried by a canonical
learner grammar package.

The previous files packaged extracted sample data, learner-side word semantics,
and Gold-style wrappers.  This file isolates the refined-rule-list component of
such a package: the finite refined grammar listed by the concrete enumeration,
its canonical finite-monoid rule-enumeration plan, and the two key facts needed
from rule lists:

* the lists cover all ordinary output-type rule refinements; and
* every listed refined rule is supported by the canonical finite-monoid plan.

No new rule-generation algorithm is implemented here.  The point is to expose a
small API that a future `List.bind` implementation of concrete rule lists can
instantiate directly.
-/

namespace FIv21

universe u v w

noncomputable section

section CanonicalRuleListSpecification

variable {N : Type w} {α : Type u}
variable [DecidableEq α]
variable {M : Type v} [Monoid M] [Fintype M]

namespace CanonicalLearnerGrammarPackage

/-- The canonical finite-monoid rule-enumeration plan associated with a package. -/
def ruleEnumerationPlan
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (_P : CanonicalLearnerGrammarPackage G obs K) :
    FiniteRuleEnumerationPlan G obs :=
  FiniteRuleEnumerationPlan.ofFintype G obs

/-- The finite output-type refined grammar listed by the package. -/
def finiteRefinedGrammar
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (P : CanonicalLearnerGrammarPackage G obs K) :
    FiniteOutputTypeRefinedGrammar G obs :=
  FintypeConcreteRuleEnumeration.grammar P.data.concreteRules

/-- Number of refined terminal rules listed by the package. -/
def refinedTerminalRuleCount
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (P : CanonicalLearnerGrammarPackage G obs K) : Nat :=
  P.finiteRefinedGrammar.terminalRuleCount

/-- Number of refined binary rules listed by the package. -/
def refinedBinaryRuleCount
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (P : CanonicalLearnerGrammarPackage G obs K) : Nat :=
  P.finiteRefinedGrammar.binaryRuleCount

/-- Number of refined start rules listed by the package. -/
def refinedStartRuleCount
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (P : CanonicalLearnerGrammarPackage G obs K) : Nat :=
  P.finiteRefinedGrammar.startRuleCount

/-- Total number of refined rules listed by the package. -/
def refinedRuleCount
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (P : CanonicalLearnerGrammarPackage G obs K) : Nat :=
  P.finiteRefinedGrammar.ruleCount

/-- The package's concrete refined-rule lists cover all ordinary output-type
rule refinements. -/
theorem refinedRuleLists_coverAll
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (P : CanonicalLearnerGrammarPackage G obs K) :
    P.finiteRefinedGrammar.CoversAllOrdinaryRuleRefinements := by
  exact P.data.concreteRules.concrete.coversAll

/-- All listed refined rules are supported by the canonical finite-monoid
rule-enumeration plan. -/
theorem refinedRuleLists_supportedByPlan
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (P : CanonicalLearnerGrammarPackage G obs K) :
    P.finiteRefinedGrammar.AllRulesSupportedByPlan P.ruleEnumerationPlan := by
  exact FintypeConcreteRuleEnumeration.allRulesSupportedByPlan P.data.concreteRules

/-- A listed refined terminal rule is supported by the package's finite plan. -/
theorem listed_refinedTerminal_supported
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (P : CanonicalLearnerGrammarPackage G obs K)
    (ρ : RefinedTerminalRule G obs)
    (hρ : ρ ∈ P.finiteRefinedGrammar.terminalRules) :
    P.ruleEnumerationPlan.SupportsRefinedTerminalRule ρ := by
  exact P.refinedRuleLists_supportedByPlan.1 ρ hρ

/-- A listed refined binary rule is supported by the package's finite plan. -/
theorem listed_refinedBinary_supported
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (P : CanonicalLearnerGrammarPackage G obs K)
    (ρ : RefinedBinaryRule G obs)
    (hρ : ρ ∈ P.finiteRefinedGrammar.binaryRules) :
    P.ruleEnumerationPlan.SupportsRefinedBinaryRule ρ := by
  exact P.refinedRuleLists_supportedByPlan.2.1 ρ hρ

/-- A listed refined start rule is supported by the package's finite plan. -/
theorem listed_refinedStart_supported
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (P : CanonicalLearnerGrammarPackage G obs K)
    (ρ : RefinedStartRule G obs)
    (hρ : ρ ∈ P.finiteRefinedGrammar.startRules) :
    P.ruleEnumerationPlan.SupportsRefinedStartRule ρ := by
  exact P.refinedRuleLists_supportedByPlan.2.2 ρ hρ

end CanonicalLearnerGrammarPackage

/-- Rule-list specification automatically carried by a canonical learner grammar
package.

This is separated as a structure so that later files can ask explicitly for the
rule-list portion of the canonical learner interface without unpacking the
whole package. -/
structure CanonicalRuleListSpecification
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (P : CanonicalLearnerGrammarPackage G obs K) where
  coversAll : P.finiteRefinedGrammar.CoversAllOrdinaryRuleRefinements
  supportedByPlan :
    P.finiteRefinedGrammar.AllRulesSupportedByPlan P.ruleEnumerationPlan

namespace CanonicalRuleListSpecification

/-- Every canonical learner grammar package has the rule-list specification. -/
def ofPackage
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (P : CanonicalLearnerGrammarPackage G obs K) :
    CanonicalRuleListSpecification P :=
  { coversAll := P.refinedRuleLists_coverAll
    supportedByPlan := P.refinedRuleLists_supportedByPlan }

/-- Terminal-rule support supplied by a rule-list specification. -/
theorem listed_terminal_supported
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {P : CanonicalLearnerGrammarPackage G obs K}
    (S : CanonicalRuleListSpecification P)
    (ρ : RefinedTerminalRule G obs)
    (hρ : ρ ∈ P.finiteRefinedGrammar.terminalRules) :
    P.ruleEnumerationPlan.SupportsRefinedTerminalRule ρ := by
  exact S.supportedByPlan.1 ρ hρ

/-- Binary-rule support supplied by a rule-list specification. -/
theorem listed_binary_supported
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {P : CanonicalLearnerGrammarPackage G obs K}
    (S : CanonicalRuleListSpecification P)
    (ρ : RefinedBinaryRule G obs)
    (hρ : ρ ∈ P.finiteRefinedGrammar.binaryRules) :
    P.ruleEnumerationPlan.SupportsRefinedBinaryRule ρ := by
  exact S.supportedByPlan.2.1 ρ hρ

/-- Start-rule support supplied by a rule-list specification. -/
theorem listed_start_supported
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {P : CanonicalLearnerGrammarPackage G obs K}
    (S : CanonicalRuleListSpecification P)
    (ρ : RefinedStartRule G obs)
    (hρ : ρ ∈ P.finiteRefinedGrammar.startRules) :
    P.ruleEnumerationPlan.SupportsRefinedStartRule ρ := by
  exact S.supportedByPlan.2.2 ρ hρ

end CanonicalRuleListSpecification

end CanonicalRuleListSpecification

end

end FIv21
