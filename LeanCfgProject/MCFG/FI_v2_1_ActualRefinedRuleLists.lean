import LeanCfgProject.MCFG.FI_v2_1_MainTheoremGold

/-!
# FI v2.1 Lean experiment: actual refined rule lists

This file starts the vertical construction that was intentionally postponed in
previous layers.  The earlier files introduced finite rule-enumeration plans and
certificate interfaces.  Here we actually build the refined terminal, binary,
and start rule lists by mapping and binding over the finite ordinary rule lists
and the finite output-type lists supplied by the plan.

The construction is still relative to the ordinary well-typedness side
conditions for terminal and start rules, because those proofs are needed to
package refined terminal and start rules.  Binary rules need no additional
well-typedness proof in the current syntax: their dependent arities are already
part of the rule type.
-/

namespace FIv21

universe u v w

section ActualRefinedRuleLists

variable {N : Type w} {α : Type u}
variable {M : Type v} [Monoid M]

/-- The actual finite list of refined terminal rules.

For each listed ordinary terminal rule, the grammar-side well-typedness
condition supplies the proof needed by `RefinedTerminalRule`. -/
def actualRefinedTerminalRules
    {G : WorkingMCFG N α} {obs : α → M}
    (P : FiniteRuleEnumerationPlan G obs)
    (hTerm : G.TerminalRulesWellTyped) :
    List (RefinedTerminalRule G obs) :=
  G.terminalRules.attach.map fun ρ =>
    { rule := ρ.val
      mem := ρ.property
      wellTyped := hTerm ρ.val ρ.property }

/-- The actual finite list of refined binary rules.

For each ordinary binary rule and each pair of listed child output-type vectors,
we add the corresponding packaged refined binary rule. -/
def actualRefinedBinaryRules
    {G : WorkingMCFG N α} {obs : α → M}
    (P : FiniteRuleEnumerationPlan G obs) :
    List (RefinedBinaryRule G obs) :=
  (G.binaryRules.attach).flatMap fun ρ =>
    (P.outputTypes.types (G.arity ρ.val.left)).flatMap fun leftTy =>
      (P.outputTypes.types (G.arity ρ.val.right)).map fun rightTy =>
        { rule := ρ.val
          mem := ρ.property
          leftTy := leftTy
          rightTy := rightTy }

/-- The actual finite list of refined start rules.

For each ordinary start rule and each listed child output-type vector, we add
the corresponding packaged refined start rule. -/
def actualRefinedStartRules
    {G : WorkingMCFG N α} {obs : α → M}
    (P : FiniteRuleEnumerationPlan G obs)
    (hStart : G.StartRulesWellTyped) :
    List (RefinedStartRule G obs) :=
  (G.startRules.attach).flatMap fun ρ =>
    (P.outputTypes.types (G.arity ρ.val.child)).map fun childTy =>
      { rule := ρ.val
        mem := ρ.property
        wellTyped := hStart ρ.val ρ.property
        childTy := childTy }

/-- Every ordinary terminal-rule refinement occurs in the actual terminal list. -/
theorem mem_actualRefinedTerminalRules
    {G : WorkingMCFG N α} {obs : α → M}
    (P : FiniteRuleEnumerationPlan G obs)
    (hTerm : G.TerminalRulesWellTyped)
    (ρ : TerminalRule N α) (hρ : ρ ∈ G.terminalRules)
    (hwt : ρ.WellTyped G.arity) :
    ({ rule := ρ
       mem := hρ
       wellTyped := hwt } : RefinedTerminalRule G obs) ∈
      actualRefinedTerminalRules P hTerm := by
  classical
  apply List.mem_map.mpr
  refine ⟨⟨ρ, hρ⟩, ?_, ?_⟩
  · simp
  · dsimp [actualRefinedTerminalRules]

/-- Every ordinary binary-rule refinement occurs in the actual binary list. -/
theorem mem_actualRefinedBinaryRules
    {G : WorkingMCFG N α} {obs : α → M}
    (P : FiniteRuleEnumerationPlan G obs)
    (ρ : BinaryRule N α G.arity) (hρ : ρ ∈ G.binaryRules)
    (leftTy : Fin (G.arity ρ.left) → M)
    (rightTy : Fin (G.arity ρ.right) → M) :
    ({ rule := ρ
       mem := hρ
       leftTy := leftTy
       rightTy := rightTy } : RefinedBinaryRule G obs) ∈
      actualRefinedBinaryRules P := by
  classical
  apply List.mem_flatMap.mpr
  refine ⟨⟨ρ, hρ⟩, ?_, ?_⟩
  · simp
  · apply List.mem_flatMap.mpr
    refine ⟨leftTy, P.outputTypes.complete leftTy, ?_⟩
    apply List.mem_map.mpr
    refine ⟨rightTy, P.outputTypes.complete rightTy, ?_⟩
    rfl

/-- Every ordinary start-rule refinement occurs in the actual start list. -/
theorem mem_actualRefinedStartRules
    {G : WorkingMCFG N α} {obs : α → M}
    (P : FiniteRuleEnumerationPlan G obs)
    (hStart : G.StartRulesWellTyped)
    (ρ : StartRule N) (hρ : ρ ∈ G.startRules)
    (hwt : ρ.WellTyped G)
    (childTy : Fin (G.arity ρ.child) → M) :
    ({ rule := ρ
       mem := hρ
       wellTyped := hwt
       childTy := childTy } : RefinedStartRule G obs) ∈
      actualRefinedStartRules P hStart := by
  classical
  apply List.mem_flatMap.mpr
  refine ⟨⟨ρ, hρ⟩, ?_, ?_⟩
  · simp
  · apply List.mem_map.mpr
    refine ⟨childTy, P.outputTypes.complete childTy, ?_⟩
    dsimp [actualRefinedStartRules]

/-- The finite refined grammar actually generated from a finite plan. -/
def actualFiniteOutputTypeRefinedGrammar
    {G : WorkingMCFG N α} {obs : α → M}
    (P : FiniteRuleEnumerationPlan G obs)
    (hTerm : G.TerminalRulesWellTyped)
    (hStart : G.StartRulesWellTyped) :
    FiniteOutputTypeRefinedGrammar G obs :=
  { terminalRules := actualRefinedTerminalRules P hTerm
    binaryRules := actualRefinedBinaryRules P
    startRules := actualRefinedStartRules P hStart }

/-- The actual refined-rule lists cover all ordinary output-type refinements. -/
theorem actualFiniteOutputTypeRefinedGrammar_coversAll
    {G : WorkingMCFG N α} {obs : α → M}
    (P : FiniteRuleEnumerationPlan G obs)
    (hTerm : G.TerminalRulesWellTyped)
    (hStart : G.StartRulesWellTyped) :
    (actualFiniteOutputTypeRefinedGrammar P hTerm hStart).CoversAllOrdinaryRuleRefinements := by
  constructor
  · intro ρ hρ hwt
    exact mem_actualRefinedTerminalRules P hTerm ρ hρ hwt
  constructor
  · intro ρ hρ leftTy rightTy
    exact mem_actualRefinedBinaryRules P ρ hρ leftTy rightTy
  · intro ρ hρ hwt childTy
    exact mem_actualRefinedStartRules P hStart ρ hρ hwt childTy

/-- The actual refined-rule lists packaged as the concrete enumeration
certificate required by previous layers. -/
def actualConcreteRefinedRuleEnumeration
    {G : WorkingMCFG N α} {obs : α → M}
    (P : FiniteRuleEnumerationPlan G obs)
    (hTerm : G.TerminalRulesWellTyped)
    (hStart : G.StartRulesWellTyped) :
    ConcreteRefinedRuleEnumeration P :=
  { grammar := actualFiniteOutputTypeRefinedGrammar P hTerm hStart
    coversAll := actualFiniteOutputTypeRefinedGrammar_coversAll P hTerm hStart }

/-- The actual refined-rule enumeration is supported by its finite plan. -/
theorem actualConcreteRefinedRuleEnumeration_supportedByPlan
    {G : WorkingMCFG N α} {obs : α → M}
    (P : FiniteRuleEnumerationPlan G obs)
    (hTerm : G.TerminalRulesWellTyped)
    (hStart : G.StartRulesWellTyped) :
    (actualConcreteRefinedRuleEnumeration P hTerm hStart).grammar.AllRulesSupportedByPlan P := by
  exact (actualConcreteRefinedRuleEnumeration P hTerm hStart).allRulesSupportedByPlan

end ActualRefinedRuleLists

end FIv21
