import LeanCfgProject.MCFG.FI_v2_1_FiniteRuleEnumerationPlan

/-!
# FI v2.1 Lean experiment: rule-enumeration plans from finite monoids

This twenty-fifth layer specializes finite rule-enumeration plans to the
finite-monoid setting.  The base grammar already supplies finite ordinary rule
lists, and `[Fintype M]` supplies complete finite output-type lists.  Bundling
these gives the finite plan from which the output-type refined rule lists are
intended to be produced.
-/

namespace FIv21

universe u v w

section FintypeRuleEnumerationPlan

variable {N : Type w} {α : Type u}
variable {M : Type v} [Monoid M] [Fintype M]

namespace FiniteRuleEnumerationPlan

/-- The canonical finite rule-enumeration plan associated with a finite
observation monoid. -/
noncomputable def ofFintype
    (G : WorkingMCFG N α) (obs : α → M) :
    FiniteRuleEnumerationPlan G obs :=
  { baseRules := FiniteBaseRuleSupport.canonical G
    outputTypes := OutputTypeEnumeration.ofFintype M }

/-- The canonical finite plan supports every ordinary terminal rule. -/
theorem ofFintype_supports_terminal_rule
    (G : WorkingMCFG N α) (obs : α → M)
    (ρ : TerminalRule N α) (hρ : ρ ∈ G.terminalRules) :
    (FiniteRuleEnumerationPlan.ofFintype G obs).baseRules.SupportsTerminalRule ρ := by
  exact (FiniteRuleEnumerationPlan.ofFintype G obs).supports_terminal_rule ρ hρ

/-- The canonical finite plan supports every ordinary binary rule. -/
theorem ofFintype_supports_binary_rule
    (G : WorkingMCFG N α) (obs : α → M)
    (ρ : BinaryRule N α G.arity) (hρ : ρ ∈ G.binaryRules) :
    (FiniteRuleEnumerationPlan.ofFintype G obs).baseRules.SupportsBinaryRule ρ := by
  exact (FiniteRuleEnumerationPlan.ofFintype G obs).supports_binary_rule ρ hρ

/-- The canonical finite plan supports every ordinary start rule. -/
theorem ofFintype_supports_start_rule
    (G : WorkingMCFG N α) (obs : α → M)
    (ρ : StartRule N) (hρ : ρ ∈ G.startRules) :
    (FiniteRuleEnumerationPlan.ofFintype G obs).baseRules.SupportsStartRule ρ := by
  exact (FiniteRuleEnumerationPlan.ofFintype G obs).supports_start_rule ρ hρ

/-- The canonical finite plan lists every output-type vector. -/
theorem ofFintype_lists_output_type
    (G : WorkingMCFG N α) (obs : α → M)
    {d : Nat} (ty : Fin d → M) :
    ty ∈ (FiniteRuleEnumerationPlan.ofFintype G obs).outputTypes.types d := by
  exact OutputTypeEnumeration.ofFintype_complete (M := M) ty

/-- The canonical finite plan supports every binary-rule output-type choice. -/
theorem ofFintype_supports_binary_type_choices
    (G : WorkingMCFG N α) (obs : α → M)
    (ρ : BinaryRule N α G.arity)
    (leftTy : Fin (G.arity ρ.left) → M)
    (rightTy : Fin (G.arity ρ.right) → M) :
    leftTy ∈ (FiniteRuleEnumerationPlan.ofFintype G obs).outputTypes.types
      (G.arity ρ.left) ∧
    rightTy ∈ (FiniteRuleEnumerationPlan.ofFintype G obs).outputTypes.types
      (G.arity ρ.right) := by
  exact (FiniteRuleEnumerationPlan.ofFintype G obs).supports_binary_type_choices
    ρ leftTy rightTy

/-- The canonical finite plan supports every start-rule output-type choice. -/
theorem ofFintype_supports_start_type_choice
    (G : WorkingMCFG N α) (obs : α → M)
    (ρ : StartRule N)
    (childTy : Fin (G.arity ρ.child) → M) :
    childTy ∈ (FiniteRuleEnumerationPlan.ofFintype G obs).outputTypes.types
      (G.arity ρ.child) := by
  exact (FiniteRuleEnumerationPlan.ofFintype G obs).supports_start_type_choice
    ρ childTy

end FiniteRuleEnumerationPlan

end FintypeRuleEnumerationPlan

end FIv21
