import LeanCfgProject.FixedHCFG.V62CFGNormalizationNullableReverse

namespace LeanCfgProject
namespace FixedHCFG

/-!
# Executable unit-rule elimination for the v62 normalization

After non-start lambda elimination, the manuscript takes unit closure and
copies each reachable non-unit production back to the source of the unit
chain.  This file implements that construction directly on mathlib's finite
rule set.

Only nonterminals that actually occur in the finite grammar representation are
enumerated.  For each such source `A` and each installed non-unit rule
`B -> alpha`, we install `A -> alpha` exactly when `B` is reachable from
`A` by unit rules.  Hence all unit rules disappear in one finite step.
-/

/-- Extract the nonterminal carried by a grammar symbol, if any. -/
def v62NonterminalOfSymbol {T N : Type*} : Symbol T N → Option N
  | .terminal _ => none
  | .nonterminal A => some A

/-- Nonterminals mentioned by one production, including its input. -/
noncomputable def v62RuleNonterminals {T N : Type*}
    (r : ContextFreeRule T N) : Finset N := by
  classical
  exact insert r.input
    (r.output.filterMap v62NonterminalOfSymbol).toFinset

/-- Finite support of nonterminals occurring in the grammar representation. -/
noncomputable def v62GrammarNonterminals {T : Type*}
    (g : ContextFreeGrammar T) : Finset g.NT := by
  classical
  exact insert g.initial (g.rules.biUnion v62RuleNonterminals)

/-- One unit-production edge `A -> B`. -/
def V62CFGUnitStep {T : Type*} (g : ContextFreeGrammar T)
    (A B : g.NT) : Prop :=
  ∃ r ∈ g.rules,
    r.input = A ∧ r.output = [Symbol.nonterminal B]

/-- Reflexive-transitive unit reachability. -/
def V62CFGUnitReach {T : Type*} (g : ContextFreeGrammar T)
    (A B : g.NT) : Prop :=
  Relation.ReflTransGen (V62CFGUnitStep g) A B

/-- A rule is a unit production precisely when its RHS is one nonterminal. -/
def V62CFGIsUnitRule {T N : Type*}
    (r : ContextFreeRule T N) : Prop :=
  ∃ B : N, r.output = [Symbol.nonterminal B]

/-- Copy a production while replacing only its input nonterminal. -/
def v62CopyRuleInput {T N : Type*} (A : N)
    (r : ContextFreeRule T N) : ContextFreeRule T N :=
  { input := A, output := r.output }

/-- Finite rule set obtained by unit closure and deletion of unit rules. -/
noncomputable def v62UnitEliminationRules {T : Type}
    (g : ContextFreeGrammar T) : Finset (ContextFreeRule T g.NT) := by
  classical
  exact (v62GrammarNonterminals g).biUnion fun A =>
    (g.rules.filter fun r =>
      ¬ V62CFGIsUnitRule r ∧ V62CFGUnitReach g A r.input).image
        (v62CopyRuleInput A)

/-- Executable grammar after unit-rule elimination. -/
@[reducible] noncomputable def v62UnitEliminationGrammar {T : Type}
    (g : ContextFreeGrammar T) : ContextFreeGrammar T := by
  classical
  exact
    { NT := g.NT
      initial := g.initial
      rules := v62UnitEliminationRules g }

/-- Copying an input preserves the RHS literally. -/
@[simp] theorem v62_copy_rule_input_output
    {T N : Type*} (A : N) (r : ContextFreeRule T N) :
    (v62CopyRuleInput A r).output = r.output := rfl

/-- Every installed copied rule has a non-unit source production. -/
theorem v62_unit_elimination_rule_source
    {T : Type} {g : ContextFreeGrammar T}
    {q : ContextFreeRule T g.NT}
    (hq : q ∈ (v62UnitEliminationGrammar g).rules) :
    ∃ A ∈ v62GrammarNonterminals g,
      ∃ r ∈ g.rules,
        ¬ V62CFGIsUnitRule r ∧
        V62CFGUnitReach g A r.input ∧
        q = v62CopyRuleInput A r := by
  classical
  change q ∈ v62UnitEliminationRules g at hq
  unfold v62UnitEliminationRules at hq
  rcases Finset.mem_biUnion.mp hq with ⟨A, hA, hqA⟩
  rcases Finset.mem_image.mp hqA with ⟨r, hrFilter, hrq⟩
  have hr : r ∈ g.rules := (Finset.mem_filter.mp hrFilter).1
  have hprops := (Finset.mem_filter.mp hrFilter).2
  exact ⟨A, hA, r, hr, hprops.1, hprops.2, hrq.symm⟩

/-- The transformed grammar contains no unit production. -/
theorem v62_unit_elimination_no_unit_rules
    {T : Type} (g : ContextFreeGrammar T) :
    ∀ q ∈ (v62UnitEliminationGrammar g).rules,
      ¬ V62CFGIsUnitRule q := by
  intro q hq
  rcases v62_unit_elimination_rule_source hq with
    ⟨A, hA, r, hr, hNonunit, hReach, rfl⟩
  simpa [V62CFGIsUnitRule, v62CopyRuleInput] using hNonunit

/-- Unit closure copies at most `|V_active| * |P|` productions. -/
theorem v62_unit_elimination_rule_card_le
    {T : Type} (g : ContextFreeGrammar T) :
    (v62UnitEliminationGrammar g).rules.card ≤
      (v62GrammarNonterminals g).card * g.rules.card := by
  classical
  change (v62UnitEliminationRules g).card ≤
    (v62GrammarNonterminals g).card * g.rules.card
  unfold v62UnitEliminationRules
  calc
    _ ≤ ∑ A ∈ v62GrammarNonterminals g,
          ((g.rules.filter fun r =>
            ¬ V62CFGIsUnitRule r ∧
              V62CFGUnitReach g A r.input).image
                (v62CopyRuleInput A)).card := Finset.card_biUnion_le
    _ ≤ ∑ _A ∈ v62GrammarNonterminals g, g.rules.card := by
      apply Finset.sum_le_sum
      intro A hA
      exact Finset.card_image_le.trans Finset.card_filter_le
    _ = (v62GrammarNonterminals g).card * g.rules.card := by
      simp [Nat.mul_comm]

end FixedHCFG
end LeanCfgProject
