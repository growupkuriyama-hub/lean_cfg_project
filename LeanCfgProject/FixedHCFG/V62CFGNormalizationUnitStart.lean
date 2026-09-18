import LeanCfgProject.FixedHCFG.V62CFGNormalizationUnitReverse

namespace LeanCfgProject
namespace FixedHCFG

/-!
# Start-preserving unit elimination for manuscript SSBNF

SSBNF keeps the separated start rules S0 -> A (and optionally
S0 -> lambda) while eliminating unit productions only away from the start.
The earlier executable unit-elimination module removes every unit rule and is
useful as a generic closure construction, but the manuscript normalization
needs this start-preserving variant.

For the distinguished start source we therefore keep its installed rules
literally.  For every other active source A, we copy each unit-reachable
non-unit production back to A.  This removes all non-start unit rules while
retaining the start interface required by SSBNF.
-/

/-- Finite rule set for unit elimination away from the separated start symbol. -/
noncomputable def v62StartPreservingUnitRules {T : Type}
    (g : ContextFreeGrammar T) : Finset (ContextFreeRule T g.NT) := by
  classical
  exact
    (g.rules.filter fun r => r.input = g.initial) ∪
      ((v62GrammarNonterminals g).erase g.initial).biUnion fun A =>
        (g.rules.filter fun r =>
          ¬ V62CFGIsUnitRule r ∧ V62CFGUnitReach g A r.input).image
            (v62CopyRuleInput A)

/-- Executable unit elimination that leaves all start rules untouched. -/
@[reducible] noncomputable def v62StartPreservingUnitGrammar {T : Type}
    (g : ContextFreeGrammar T) : ContextFreeGrammar T := by
  classical
  exact
    { NT := g.NT
      initial := g.initial
      rules := v62StartPreservingUnitRules g }

/--
Every transformed rule is either an unchanged old start rule or a copied
non-unit rule attached to a non-start active source.
-/
theorem v62_start_unit_rule_source
    {T : Type} {g : ContextFreeGrammar T}
    {q : ContextFreeRule T g.NT}
    (hq : q ∈ (v62StartPreservingUnitGrammar g).rules) :
    (q ∈ g.rules ∧ q.input = g.initial) ∨
      ∃ A ∈ v62GrammarNonterminals g,
        A ≠ g.initial ∧
        ∃ r ∈ g.rules,
          ¬ V62CFGIsUnitRule r ∧
          V62CFGUnitReach g A r.input ∧
          q = v62CopyRuleInput A r := by
  classical
  change q ∈ v62StartPreservingUnitRules g at hq
  unfold v62StartPreservingUnitRules at hq
  rw [Finset.mem_union] at hq
  rcases hq with hStart | hCopy
  · have hs := Finset.mem_filter.mp hStart
    exact Or.inl ⟨hs.1, hs.2⟩
  · rcases Finset.mem_biUnion.mp hCopy with ⟨A, hAerase, hqA⟩
    have hAactive : A ∈ v62GrammarNonterminals g :=
      (Finset.mem_erase.mp hAerase).2
    have hAne : A ≠ g.initial :=
      (Finset.mem_erase.mp hAerase).1
    rcases Finset.mem_image.mp hqA with ⟨r, hrFilter, hrq⟩
    have hr := (Finset.mem_filter.mp hrFilter).1
    have hp := (Finset.mem_filter.mp hrFilter).2
    exact Or.inr
      ⟨A, hAactive, hAne, r, hr, hp.1, hp.2, hrq.symm⟩

/-- Generic invariant: no unit production is allowed away from the start. -/
def V62CFGNoNonStartUnitRules {T : Type*}
    (g : ContextFreeGrammar T) : Prop :=
  ∀ r ∈ g.rules, r.input ≠ g.initial → ¬ V62CFGIsUnitRule r

/-- The start-preserving closure removes every non-start unit production. -/
theorem v62_start_unit_elimination_no_nonstart_units
    {T : Type} (g : ContextFreeGrammar T) :
    V62CFGNoNonStartUnitRules (v62StartPreservingUnitGrammar g) := by
  intro q hq hqNonStart
  rcases v62_start_unit_rule_source hq with hStart | hCopy
  · exact (hqNonStart hStart.2).elim
  · rcases hCopy with
      ⟨A, hAactive, hAne, r, hr, hNonunit, hReach, hqeq⟩
    subst q
    simpa [V62CFGIsUnitRule, v62CopyRuleInput] using hNonunit

/-- Every transformed start rule is literally an old start rule. -/
theorem v62_start_unit_start_rule_old
    {T : Type} {g : ContextFreeGrammar T}
    {q : ContextFreeRule T g.NT}
    (hq : q ∈ (v62StartPreservingUnitGrammar g).rules)
    (hinput : q.input = g.initial) :
    q ∈ g.rules := by
  rcases v62_start_unit_rule_source hq with hStart | hCopy
  · exact hStart.1
  · rcases hCopy with
      ⟨A, hAactive, hAne, r, hr, hNonunit, hReach, hqeq⟩
    subst q
    have : A = g.initial := by simpa [v62CopyRuleInput] using hinput
    exact (hAne this).elim

/-- Every installed transformed rule is derivable in the old grammar. -/
theorem v62_start_unit_rule_derives_old
    {T : Type} {g : ContextFreeGrammar T}
    {q : ContextFreeRule T g.NT}
    (hq : q ∈ (v62StartPreservingUnitGrammar g).rules) :
    g.Derives [Symbol.nonterminal q.input] q.output := by
  rcases v62_start_unit_rule_source hq with hStart | hCopy
  · exact (show g.Produces
      [Symbol.nonterminal q.input] q.output from
        ⟨q, hStart.1, ContextFreeRule.Rewrites.input_output⟩).single
  · rcases hCopy with
      ⟨A, hAactive, hAne, r, hr, hNonunit, hReach, hqeq⟩
    subst q
    have hchain := v62_unit_reach_derives hReach
    have hprod :
        g.Produces [Symbol.nonterminal r.input] r.output :=
      ⟨r, hr, ContextFreeRule.Rewrites.input_output⟩
    exact hchain.trans_produces hprod

/-- One transformed contextual rewrite is simulated by an old derivation. -/
theorem v62_start_unit_produces_simulates
    {T : Type} {g : ContextFreeGrammar T}
    {u v : List (Symbol T g.NT)}
    (h : (v62StartPreservingUnitGrammar g).Produces u v) :
    g.Derives u v := by
  rcases h with ⟨q, hq, hrew⟩
  have hlocal := v62_start_unit_rule_derives_old hq
  rcases hrew.exists_parts with ⟨p, s, hu, hv⟩
  have hctx := (hlocal.append_left p).append_right s
  simpa [hu, hv, List.append_assoc] using hctx

/-- Every transformed derivation is simulated by an old derivation. -/
theorem v62_start_unit_derives_simulates
    {T : Type} {g : ContextFreeGrammar T}
    {u v : List (Symbol T g.NT)}
    (h : (v62StartPreservingUnitGrammar g).Derives u v) :
    g.Derives u v := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ last ih =>
      exact ih.trans (v62_start_unit_produces_simulates last)

/-- Start-preserving unit elimination introduces no new terminal word. -/
theorem v62_start_unit_language_subset
    {T : Type} (g : ContextFreeGrammar T) :
    ∀ w : List T,
      w ∈ (v62StartPreservingUnitGrammar g).language → w ∈ g.language := by
  intro w hw
  rw [ContextFreeGrammar.mem_language_iff] at hw ⊢
  exact v62_start_unit_derives_simulates hw

/-- The start-preserving unit stage has a quadratic finite-rule envelope. -/
theorem v62_start_unit_rule_card_le
    {T : Type} (g : ContextFreeGrammar T) :
    (v62StartPreservingUnitGrammar g).rules.card ≤
      (v62GrammarNonterminals g).card * g.rules.card + g.rules.card := by
  classical
  change (v62StartPreservingUnitRules g).card ≤
    (v62GrammarNonterminals g).card * g.rules.card + g.rules.card
  unfold v62StartPreservingUnitRules
  calc
    _ ≤
        (g.rules.filter fun r => r.input = g.initial).card +
          (((v62GrammarNonterminals g).erase g.initial).biUnion fun A =>
            (g.rules.filter fun r =>
              ¬ V62CFGIsUnitRule r ∧
                V62CFGUnitReach g A r.input).image
                  (v62CopyRuleInput A)).card :=
      Finset.card_union_le _ _
    _ ≤ g.rules.card +
        ((v62GrammarNonterminals g).erase g.initial).card *
          g.rules.card := by
      apply Nat.add_le_add
      · exact Finset.card_filter_le _ _
      · calc
          _ ≤ ∑ A ∈ (v62GrammarNonterminals g).erase g.initial,
                ((g.rules.filter fun r =>
                  ¬ V62CFGIsUnitRule r ∧
                    V62CFGUnitReach g A r.input).image
                      (v62CopyRuleInput A)).card :=
                Finset.card_biUnion_le
          _ ≤ ∑ _A ∈ (v62GrammarNonterminals g).erase g.initial,
                g.rules.card := by
                apply Finset.sum_le_sum
                intro A hA
                exact Finset.card_image_le.trans
                  (Finset.card_filter_le g.rules
                    (fun r => ¬ V62CFGIsUnitRule r ∧
                      V62CFGUnitReach g A r.input))
          _ =
              ((v62GrammarNonterminals g).erase g.initial).card *
                g.rules.card := by
                simp [Nat.mul_comm]
    _ ≤ g.rules.card +
        (v62GrammarNonterminals g).card * g.rules.card := by
      apply Nat.add_le_add_left
      have hcard :
          ((v62GrammarNonterminals g).erase g.initial).card ≤
            (v62GrammarNonterminals g).card :=
        Finset.card_erase_le
      exact Nat.mul_le_mul_right g.rules.card hcard
    _ = (v62GrammarNonterminals g).card * g.rules.card +
        g.rules.card := by omega

end FixedHCFG
end LeanCfgProject
