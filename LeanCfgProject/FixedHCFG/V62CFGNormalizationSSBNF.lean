import LeanCfgProject.FixedHCFG.V62CFGNormalizationUnitStart
import LeanCfgProject.FixedHCFG.V62CFGNormalizationTrim

namespace LeanCfgProject
namespace FixedHCFG

/-!
# Structural SSBNF endpoint for the executable v62 normalization

The normalization pipeline accumulates several simple invariants in separate
modules. This file packages exactly the structural combination used by the
manuscript definition of start-separated binary normal form:

* the start symbol never occurs on a right-hand side;
* every start rule is either a single-nonterminal rule or epsilon;
* non-start rules are nonempty and non-unit;
* every right-hand side has length at most two; and
* every right-hand side of length two is terminal-free.

Those conditions force every non-start production to be either A -> a or
A -> B C.
-/

/-- The permitted shape of productions whose source is the distinguished start. -/
def V62CFGStartRuleForm {T : Type*} (g : ContextFreeGrammar T) : Prop :=
  ∀ r ∈ g.rules, r.input = g.initial →
    r.output = [] ∨
      ∃ A : g.NT, r.output = [Symbol.nonterminal A]

/-- Manuscript structural SSBNF predicate on a concrete mathlib CFG. -/
def V62CFGSSBNF {T : Type*} (g : ContextFreeGrammar T) : Prop :=
  V62CFGStartSeparated g ∧
  V62CFGStartRuleForm g ∧
  ∀ r ∈ g.rules, r.input ≠ g.initial →
    (∃ a : T, r.output = [Symbol.terminal a]) ∨
      ∃ B C : g.NT,
        r.output = [Symbol.nonterminal B, Symbol.nonterminal C]

/--
The elementary structural invariants accumulated by the normalization imply
the exact SSBNF rule shapes.
-/
theorem v62_ssbnf_of_structural_invariants
    {T : Type} {g : ContextFreeGrammar T}
    (hSep : V62CFGStartSeparated g)
    (hStart : V62CFGStartRuleForm g)
    (hEps : V62CFGNoNonStartEpsilon g)
    (hUnit : V62CFGNoNonStartUnitRules g)
    (hTwo : V62CFGRHSAtMostTwo g)
    (hIso : V62CFGTerminalsIsolated g) :
    V62CFGSSBNF g := by
  refine ⟨hSep, hStart, ?_⟩
  intro r hr hNonStart
  have hNonempty : r.output ≠ [] := by
    intro hnil
    exact hNonStart (hEps r hr hnil)
  have hlen := hTwo r hr
  cases hout : r.output with
  | nil =>
      exact (hNonempty hout).elim
  | cons x xs =>
      cases xs with
      | nil =>
          cases x with
          | terminal a =>
              exact Or.inl ⟨a, hout⟩
          | nonterminal A =>
              have hIsUnit : V62CFGIsUnitRule r := ⟨A, hout⟩
              exact (hUnit r hr hNonStart hIsUnit).elim
      | cons y ys =>
          cases ys with
          | nil =>
              have hlenTwo : 2 ≤ r.output.length := by
                simp [hout]
              cases x with
              | terminal a =>
                  have hNoTerm := hIso r hr hlenTwo a
                  exact (hNoTerm (by simp [hout])).elim
              | nonterminal B =>
                  cases y with
                  | terminal a =>
                      have hNoTerm := hIso r hr hlenTwo a
                      exact (hNoTerm (by simp [hout])).elim
                  | nonterminal C =>
                      exact Or.inr ⟨B, C, hout⟩
          | cons z zs =>
              rw [hout] at hlen
              simp at hlen

/-- Useful-rule trimming preserves the start-rule shape predicate. -/
theorem v62_trim_preserves_start_rule_form
    {T : Type} {g : ContextFreeGrammar T}
    (h : V62CFGStartRuleForm g) :
    V62CFGStartRuleForm (v62UsefulTrimGrammar g) := by
  intro r hr hinput
  exact h r (v62_trim_rule_mem_old hr) hinput

/-- Useful-rule trimming preserves absence of non-start unit productions. -/
theorem v62_trim_preserves_no_nonstart_unit_rules
    {T : Type} {g : ContextFreeGrammar T}
    (h : V62CFGNoNonStartUnitRules g) :
    V62CFGNoNonStartUnitRules (v62UsefulTrimGrammar g) := by
  intro r hr hinput
  exact h r (v62_trim_rule_mem_old hr) hinput

/-- Any already-SSBNF grammar stays SSBNF after useful-rule trimming. -/
theorem v62_trim_preserves_ssbnf
    {T : Type} {g : ContextFreeGrammar T}
    (h : V62CFGSSBNF g) :
    V62CFGSSBNF (v62UsefulTrimGrammar g) := by
  rcases h with ⟨hSep, hStart, hRules⟩
  refine ⟨
    v62_trim_preserves_start_separated hSep,
    v62_trim_preserves_start_rule_form hStart,
    ?_⟩
  intro r hr hNonStart
  exact hRules r (v62_trim_rule_mem_old hr) hNonStart

end FixedHCFG
end LeanCfgProject
