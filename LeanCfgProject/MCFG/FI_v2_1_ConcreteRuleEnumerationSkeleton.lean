import LeanCfgProject.MCFG.FI_v2_1_FintypeRuleEnumerationPlan

/-!
# FI v2.1 Lean experiment: concrete refined-rule enumeration skeleton

This twenty-sixth layer is the bridge between the abstract finite rule-
enumeration plan and a later concrete list-producing algorithm.

The preceding layer built a finite plan from two finite ingredients:
ordinary base-rule lists and output-type-vector lists.  This file records the
support properties that any concrete refined-rule list automatically has with
respect to such a plan.  It does not yet construct the nested `List.bind`
products of refined rules; instead it isolates the correctness interface for
those products.
-/

namespace FIv21

universe u v w

section ConcreteRuleEnumerationSkeleton

variable {N : Type w} {α : Type u}
variable {M : Type v} [Monoid M]

namespace FiniteRuleEnumerationPlan

/-- A refined terminal rule is supported by a finite rule-enumeration plan when
its underlying ordinary rule is supported by the plan's base-rule component. -/
def SupportsRefinedTerminalRule
    {G : WorkingMCFG N α} {obs : α → M}
    (P : FiniteRuleEnumerationPlan G obs)
    (ρ : RefinedTerminalRule G obs) : Prop :=
  P.baseRules.SupportsTerminalRule ρ.rule

/-- A refined binary rule is supported by a finite rule-enumeration plan when
its underlying ordinary rule is supported and both child output-type vectors are
listed by the plan. -/
def SupportsRefinedBinaryRule
    {G : WorkingMCFG N α} {obs : α → M}
    (P : FiniteRuleEnumerationPlan G obs)
    (ρ : RefinedBinaryRule G obs) : Prop :=
  P.baseRules.SupportsBinaryRule ρ.rule ∧
  P.outputTypes.SupportsRefinedBinaryRule ρ

/-- A refined start rule is supported by a finite rule-enumeration plan when its
underlying ordinary start rule is supported and its child output-type vector is
listed by the plan. -/
def SupportsRefinedStartRule
    {G : WorkingMCFG N α} {obs : α → M}
    (P : FiniteRuleEnumerationPlan G obs)
    (ρ : RefinedStartRule G obs) : Prop :=
  P.baseRules.SupportsStartRule ρ.rule ∧
  P.outputTypes.SupportsRefinedStartRule ρ

/-- Every packaged refined terminal rule whose ordinary rule belongs to the base
grammar is supported by any complete finite plan for that grammar. -/
theorem supports_refinedTerminalRule
    {G : WorkingMCFG N α} {obs : α → M}
    (P : FiniteRuleEnumerationPlan G obs)
    (ρ : RefinedTerminalRule G obs) :
    P.SupportsRefinedTerminalRule ρ := by
  exact P.supports_terminal_rule ρ.rule ρ.mem

/-- Every packaged refined binary rule is supported by any complete finite plan
for the base grammar. -/
theorem supports_refinedBinaryRule
    {G : WorkingMCFG N α} {obs : α → M}
    (P : FiniteRuleEnumerationPlan G obs)
    (ρ : RefinedBinaryRule G obs) :
    P.SupportsRefinedBinaryRule ρ := by
  constructor
  · exact P.supports_binary_rule ρ.rule ρ.mem
  · exact P.outputTypes.supports_refinedBinaryRule ρ

/-- Every packaged refined start rule is supported by any complete finite plan
for the base grammar. -/
theorem supports_refinedStartRule
    {G : WorkingMCFG N α} {obs : α → M}
    (P : FiniteRuleEnumerationPlan G obs)
    (ρ : RefinedStartRule G obs) :
    P.SupportsRefinedStartRule ρ := by
  constructor
  · exact P.supports_start_rule ρ.rule ρ.mem
  · exact P.outputTypes.supports_refinedStartRule ρ

end FiniteRuleEnumerationPlan

namespace FiniteOutputTypeRefinedGrammar

/-- All listed refined rules of a finite refined grammar are supported by a
finite rule-enumeration plan. -/
def AllRulesSupportedByPlan
    {G : WorkingMCFG N α} {obs : α → M}
    (FG : FiniteOutputTypeRefinedGrammar G obs)
    (P : FiniteRuleEnumerationPlan G obs) : Prop :=
  (∀ ρ : RefinedTerminalRule G obs,
      ρ ∈ FG.terminalRules → P.SupportsRefinedTerminalRule ρ) ∧
  (∀ ρ : RefinedBinaryRule G obs,
      ρ ∈ FG.binaryRules → P.SupportsRefinedBinaryRule ρ) ∧
  (∀ ρ : RefinedStartRule G obs,
      ρ ∈ FG.startRules → P.SupportsRefinedStartRule ρ)

/-- Any finite refined grammar whose rules are packaged with membership
certificates is supported by any complete finite plan for the same base grammar.
This records that the remaining hard part is not support soundness, but proving
that the concrete lists cover all desired refinements. -/
theorem allRulesSupportedByPlan
    {G : WorkingMCFG N α} {obs : α → M}
    (FG : FiniteOutputTypeRefinedGrammar G obs)
    (P : FiniteRuleEnumerationPlan G obs) :
    FG.AllRulesSupportedByPlan P := by
  constructor
  · intro ρ hρ
    exact P.supports_refinedTerminalRule ρ
  constructor
  · intro ρ hρ
    exact P.supports_refinedBinaryRule ρ
  · intro ρ hρ
    exact P.supports_refinedStartRule ρ

/-- Terminal-rule support for a listed refined terminal rule. -/
theorem listed_terminal_supported_by_plan
    {G : WorkingMCFG N α} {obs : α → M}
    (FG : FiniteOutputTypeRefinedGrammar G obs)
    (P : FiniteRuleEnumerationPlan G obs)
    (ρ : RefinedTerminalRule G obs)
    (hρ : ρ ∈ FG.terminalRules) :
    P.SupportsRefinedTerminalRule ρ := by
  exact (FG.allRulesSupportedByPlan P).1 ρ hρ

/-- Binary-rule support for a listed refined binary rule. -/
theorem listed_binary_supported_by_plan
    {G : WorkingMCFG N α} {obs : α → M}
    (FG : FiniteOutputTypeRefinedGrammar G obs)
    (P : FiniteRuleEnumerationPlan G obs)
    (ρ : RefinedBinaryRule G obs)
    (hρ : ρ ∈ FG.binaryRules) :
    P.SupportsRefinedBinaryRule ρ := by
  exact (FG.allRulesSupportedByPlan P).2.1 ρ hρ

/-- Start-rule support for a listed refined start rule. -/
theorem listed_start_supported_by_plan
    {G : WorkingMCFG N α} {obs : α → M}
    (FG : FiniteOutputTypeRefinedGrammar G obs)
    (P : FiniteRuleEnumerationPlan G obs)
    (ρ : RefinedStartRule G obs)
    (hρ : ρ ∈ FG.startRules) :
    P.SupportsRefinedStartRule ρ := by
  exact (FG.allRulesSupportedByPlan P).2.2 ρ hρ

end FiniteOutputTypeRefinedGrammar

end ConcreteRuleEnumerationSkeleton

end FIv21
