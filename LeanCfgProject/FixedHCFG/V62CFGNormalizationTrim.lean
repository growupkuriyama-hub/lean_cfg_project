import LeanCfgProject.FixedHCFG.V62CFGNormalizationSize

namespace LeanCfgProject
namespace FixedHCFG

/-!
# Executable useless-symbol trimming stage for the v62 normalization

Mathlib's CFG representation allows a nonterminal type larger than the finite
support actually mentioned by the grammar.  For the manuscript's final
"reduced" grammar, the relevant finite notion is therefore active support:
symbols occurring at the start or in installed productions.

This file introduces the standard useful-symbol filter.  A nonterminal is
useful when it is both reachable from the start and productive.  The trimmed
grammar keeps only rules whose input and every RHS nonterminal are useful.
Because this is a literal subgrammar, it cannot introduce new terminal words,
its rule set only shrinks, and every universal structural invariant already
proved for the pre-trim grammar is preserved automatically.

The converse language inclusion and the proof that every active symbol of the
trimmed grammar is useful *in the trimmed grammar itself* are the semantic
completion of this final normalization stage.
-/

/-- A nonterminal is reachable if it occurs in some sentential form from the start. -/
def V62CFGReachableNT {T : Type*} (g : ContextFreeGrammar T)
    (A : g.NT) : Prop :=
  ∃ p s : List (Symbol T g.NT),
    g.Derives [Symbol.nonterminal g.initial]
      (p ++ [Symbol.nonterminal A] ++ s)

/-- Standard usefulness: reachable and productive. -/
def V62CFGUsefulNT {T : Type*} (g : ContextFreeGrammar T)
    (A : g.NT) : Prop :=
  V62CFGReachableNT g A ∧ V62CFGProductive g A

/-- A rule is useful when its input and every RHS nonterminal are useful. -/
def V62CFGRuleUseful {T : Type*} (g : ContextFreeGrammar T)
    (r : ContextFreeRule T g.NT) : Prop :=
  V62CFGUsefulNT g r.input ∧
    ∀ A : g.NT, Symbol.nonterminal A ∈ r.output → V62CFGUsefulNT g A

/-- Filter the finite production set to useful rules, keeping the old NT type. -/
@[reducible] noncomputable def v62UsefulTrimGrammar {T : Type}
    (g : ContextFreeGrammar T) : ContextFreeGrammar T := by
  classical
  exact
    { NT := g.NT
      initial := g.initial
      rules := g.rules.filter (V62CFGRuleUseful g) }

/-- Every trimmed rule is an old rule. -/
theorem v62_trim_rule_mem_old
    {T : Type} {g : ContextFreeGrammar T}
    {r : ContextFreeRule T g.NT}
    (hr : r ∈ (v62UsefulTrimGrammar g).rules) :
    r ∈ g.rules := by
  classical
  exact (Finset.mem_filter.mp hr).1

/-- Every trimmed rule satisfies the usefulness predicate used by the filter. -/
theorem v62_trim_rule_useful
    {T : Type} {g : ContextFreeGrammar T}
    {r : ContextFreeRule T g.NT}
    (hr : r ∈ (v62UsefulTrimGrammar g).rules) :
    V62CFGRuleUseful g r := by
  classical
  exact (Finset.mem_filter.mp hr).2

/-- Trimming can only decrease the number of productions. -/
theorem v62_trim_rule_card_le
    {T : Type} (g : ContextFreeGrammar T) :
    (v62UsefulTrimGrammar g).rules.card ≤ g.rules.card := by
  classical
  exact Finset.card_filter_le _ _

/-- Every one-step rewrite of the trimmed grammar is an old one-step rewrite. -/
theorem v62_trim_produces_simulates
    {T : Type} {g : ContextFreeGrammar T}
    {u v : List (Symbol T g.NT)}
    (h : (v62UsefulTrimGrammar g).Produces u v) :
    g.Produces u v := by
  rcases h with ⟨r, hr, hrew⟩
  exact ⟨r, v62_trim_rule_mem_old hr, hrew⟩

/-- Every trimmed derivation is an old derivation. -/
theorem v62_trim_derives_simulates
    {T : Type} {g : ContextFreeGrammar T}
    {u v : List (Symbol T g.NT)}
    (h : (v62UsefulTrimGrammar g).Derives u v) :
    g.Derives u v := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ last ih =>
      exact ih.trans_produces (v62_trim_produces_simulates last)

/-- Useless-symbol trimming introduces no new terminal word. -/
theorem v62_trim_language_subset
    {T : Type} (g : ContextFreeGrammar T) :
    ∀ w : List T,
      w ∈ (v62UsefulTrimGrammar g).language → w ∈ g.language := by
  intro w hw
  rw [ContextFreeGrammar.mem_language_iff] at hw ⊢
  exact v62_trim_derives_simulates hw

/-- A convenient generic predicate for absence of unit productions. -/
def V62CFGNoUnitRules {T : Type*} (g : ContextFreeGrammar T) : Prop :=
  ∀ r ∈ g.rules, ¬ V62CFGIsUnitRule r

/-- Unit elimination establishes the generic no-unit invariant. -/
theorem v62_unit_elimination_no_unit_rules'
    {T : Type} (g : ContextFreeGrammar T) :
    V62CFGNoUnitRules (v62UnitEliminationGrammar g) :=
  v62_unit_elimination_no_unit_rules g

/-- Any subgrammar obtained by useful trimming preserves start separation. -/
theorem v62_trim_preserves_start_separated
    {T : Type} {g : ContextFreeGrammar T}
    (h : V62CFGStartSeparated g) :
    V62CFGStartSeparated (v62UsefulTrimGrammar g) := by
  intro r hr
  exact h r (v62_trim_rule_mem_old hr)

/-- Useful trimming preserves the RHS-length-at-most-two invariant. -/
theorem v62_trim_preserves_rhs_at_most_two
    {T : Type} {g : ContextFreeGrammar T}
    (h : V62CFGRHSAtMostTwo g) :
    V62CFGRHSAtMostTwo (v62UsefulTrimGrammar g) := by
  intro r hr
  exact h r (v62_trim_rule_mem_old hr)

/-- Useful trimming preserves terminal isolation. -/
theorem v62_trim_preserves_terminals_isolated
    {T : Type} {g : ContextFreeGrammar T}
    (h : V62CFGTerminalsIsolated g) :
    V62CFGTerminalsIsolated (v62UsefulTrimGrammar g) := by
  intro r hr hlen a
  exact h r (v62_trim_rule_mem_old hr) hlen a

/-- Useful trimming preserves the absence of non-start epsilon productions. -/
theorem v62_trim_preserves_no_nonstart_epsilon
    {T : Type} {g : ContextFreeGrammar T}
    (h : V62CFGNoNonStartEpsilon g) :
    V62CFGNoNonStartEpsilon (v62UsefulTrimGrammar g) := by
  intro r hr hout
  exact h r (v62_trim_rule_mem_old hr) hout

/-- Useful trimming preserves the absence of unit productions. -/
theorem v62_trim_preserves_no_unit_rules
    {T : Type} {g : ContextFreeGrammar T}
    (h : V62CFGNoUnitRules g) :
    V62CFGNoUnitRules (v62UsefulTrimGrammar g) := by
  intro r hr
  exact h r (v62_trim_rule_mem_old hr)

end FixedHCFG
end LeanCfgProject
