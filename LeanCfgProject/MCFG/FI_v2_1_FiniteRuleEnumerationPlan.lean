import LeanCfgProject.MCFG.FI_v2_1_FiniteBaseRuleSupport

/-!
# FI v2.1 Lean experiment: finite rule-enumeration plan

This twenty-fourth layer combines the two finite ingredients needed by the
output-type refined grammar construction:

* finite support for the ordinary base rules, and
* finite enumeration of output-type vectors.

The file still does not compute the nested list products of refined rules.
Instead, it records the exact finite plan from which those products are built
and proves that every ordinary rule refinement requested by the paper is
supported by the plan.
-/

namespace FIv21

universe u v w

section FiniteRuleEnumerationPlan

variable {N : Type w} {α : Type u}
variable {M : Type v} [Monoid M]

/-- A finite plan for enumerating all output-type refinements of the ordinary
rules of a working grammar. -/
structure FiniteRuleEnumerationPlan
    (G : WorkingMCFG N α) (obs : α → M) where
  baseRules : FiniteBaseRuleSupport G
  outputTypes : OutputTypeEnumeration M

namespace FiniteRuleEnumerationPlan

/-- The ordinary terminal-rule support size. -/
def terminalRuleCount
    {G : WorkingMCFG N α} {obs : α → M}
    (P : FiniteRuleEnumerationPlan G obs) : Nat :=
  P.baseRules.terminalRuleCount

/-- The ordinary binary-rule support size. -/
def binaryRuleCount
    {G : WorkingMCFG N α} {obs : α → M}
    (P : FiniteRuleEnumerationPlan G obs) : Nat :=
  P.baseRules.binaryRuleCount

/-- The ordinary start-rule support size. -/
def startRuleCount
    {G : WorkingMCFG N α} {obs : α → M}
    (P : FiniteRuleEnumerationPlan G obs) : Nat :=
  P.baseRules.startRuleCount

/-- Number of output-type vectors listed at arity `d` by the plan. -/
def outputTypeCount
    {G : WorkingMCFG N α} {obs : α → M}
    (P : FiniteRuleEnumerationPlan G obs) (d : Nat) : Nat :=
  P.outputTypes.typeCount d

/-- The number of output-type choices associated with a binary rule in the
plan.  This is the product of the left and right child type-vector counts. -/
def binaryTypeChoiceCount
    {G : WorkingMCFG N α} {obs : α → M}
    (P : FiniteRuleEnumerationPlan G obs)
    (ρ : BinaryRule N α G.arity) : Nat :=
  P.outputTypeCount (G.arity ρ.left) *
  P.outputTypeCount (G.arity ρ.right)

/-- The number of output-type choices associated with a start rule in the
plan. -/
def startTypeChoiceCount
    {G : WorkingMCFG N α} {obs : α → M}
    (P : FiniteRuleEnumerationPlan G obs)
    (ρ : StartRule N) : Nat :=
  P.outputTypeCount (G.arity ρ.child)

/-- Every ordinary terminal rule listed by the grammar is supported by the
base-rule component of the plan. -/
theorem supports_terminal_rule
    {G : WorkingMCFG N α} {obs : α → M}
    (P : FiniteRuleEnumerationPlan G obs)
    (ρ : TerminalRule N α) (hρ : ρ ∈ G.terminalRules) :
    P.baseRules.SupportsTerminalRule ρ :=
  P.baseRules.supports_terminal_of_mem ρ hρ

/-- Every ordinary binary rule listed by the grammar is supported by the
base-rule component of the plan. -/
theorem supports_binary_rule
    {G : WorkingMCFG N α} {obs : α → M}
    (P : FiniteRuleEnumerationPlan G obs)
    (ρ : BinaryRule N α G.arity) (hρ : ρ ∈ G.binaryRules) :
    P.baseRules.SupportsBinaryRule ρ :=
  P.baseRules.supports_binary_of_mem ρ hρ

/-- Every ordinary start rule listed by the grammar is supported by the
base-rule component of the plan. -/
theorem supports_start_rule
    {G : WorkingMCFG N α} {obs : α → M}
    (P : FiniteRuleEnumerationPlan G obs)
    (ρ : StartRule N) (hρ : ρ ∈ G.startRules) :
    P.baseRules.SupportsStartRule ρ :=
  P.baseRules.supports_start_of_mem ρ hρ

/-- Every output-type vector is listed by the output-type component of the
plan. -/
theorem lists_output_type
    {G : WorkingMCFG N α} {obs : α → M}
    (P : FiniteRuleEnumerationPlan G obs)
    {d : Nat} (ty : Fin d → M) :
    ty ∈ P.outputTypes.types d :=
  P.outputTypes.complete ty

/-- The child output-type choices of any binary-rule refinement are supported
by the plan. -/
theorem supports_binary_type_choices
    {G : WorkingMCFG N α} {obs : α → M}
    (P : FiniteRuleEnumerationPlan G obs)
    (ρ : BinaryRule N α G.arity)
    (leftTy : Fin (G.arity ρ.left) → M)
    (rightTy : Fin (G.arity ρ.right) → M) :
    leftTy ∈ P.outputTypes.types (G.arity ρ.left) ∧
    rightTy ∈ P.outputTypes.types (G.arity ρ.right) := by
  constructor
  · exact P.outputTypes.complete leftTy
  · exact P.outputTypes.complete rightTy

/-- The parent output type of a binary-rule refinement is listed by the plan. -/
theorem lists_binary_parent_outputType
    {G : WorkingMCFG N α} {obs : α → M}
    (P : FiniteRuleEnumerationPlan G obs)
    (ρ : BinaryRule N α G.arity)
    (leftTy : Fin (G.arity ρ.left) → M)
    (rightTy : Fin (G.arity ρ.right) → M) :
    ρ.outputType obs leftTy rightTy ∈
      P.outputTypes.types (G.arity ρ.lhs) :=
  P.outputTypes.lists_binary_parent_outputType ρ leftTy rightTy

/-- The child output-type choice of any start-rule refinement is supported by
the plan. -/
theorem supports_start_type_choice
    {G : WorkingMCFG N α} {obs : α → M}
    (P : FiniteRuleEnumerationPlan G obs)
    (ρ : StartRule N)
    (childTy : Fin (G.arity ρ.child) → M) :
    childTy ∈ P.outputTypes.types (G.arity ρ.child) :=
  P.outputTypes.complete childTy

/-- The transported parent output type of a start-rule refinement is listed by
the plan. -/
theorem lists_start_parent_outputType
    {G : WorkingMCFG N α} {obs : α → M}
    (P : FiniteRuleEnumerationPlan G obs)
    (ρ : StartRule N) (hwt : ρ.WellTyped G)
    (childTy : Fin (G.arity ρ.child) → M) :
    castOutputType hwt childTy ∈ P.outputTypes.types (G.arity G.start) :=
  P.outputTypes.lists_start_parent_outputType ρ hwt childTy

end FiniteRuleEnumerationPlan

end FiniteRuleEnumerationPlan

end FIv21
