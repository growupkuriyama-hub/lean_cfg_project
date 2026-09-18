import LeanCfgProject.FixedHCFG.V62CFGNormalizationUnit

namespace LeanCfgProject
namespace FixedHCFG

/-!
# Reverse semantics for executable unit-rule elimination

A copied rule `A -> alpha` records a unit chain `A =>* B` followed by an old
non-unit rule `B -> alpha`.  Hence every transformed step is simulated by an
old derivation, and the unit-elimination stage cannot introduce terminal
words.
-/

/-- One unit edge is one old grammar derivation step. -/
theorem v62_unit_step_derives
    {T : Type} {g : ContextFreeGrammar T}
    {A B : g.NT}
    (h : V62CFGUnitStep g A B) :
    g.Derives [Symbol.nonterminal A] [Symbol.nonterminal B] := by
  rcases h with ⟨r, hr, hinput, houtput⟩
  have hp : g.Produces
      [Symbol.nonterminal A] [Symbol.nonterminal B] := by
    refine ⟨r, hr, ?_⟩
    simpa [hinput, houtput] using
      (ContextFreeRule.Rewrites.input_output (r := r))
  exact hp.single

/-- A reflexive-transitive unit chain is an old grammar derivation. -/
theorem v62_unit_reach_derives
    {T : Type} {g : ContextFreeGrammar T}
    {A B : g.NT}
    (h : V62CFGUnitReach g A B) :
    g.Derives [Symbol.nonterminal A] [Symbol.nonterminal B] := by
  unfold V62CFGUnitReach at h
  induction h with
  | refl =>
      exact Relation.ReflTransGen.refl
  | tail _ hstep ih =>
      exact ih.trans (v62_unit_step_derives hstep)

/-- Every installed copied rule is derivable in the old grammar. -/
theorem v62_unit_elimination_rule_derives_old
    {T : Type} {g : ContextFreeGrammar T}
    {q : ContextFreeRule T g.NT}
    (hq : q ∈ (v62UnitEliminationGrammar g).rules) :
    g.Derives [Symbol.nonterminal q.input] q.output := by
  rcases v62_unit_elimination_rule_source hq with
    ⟨A, hA, r, hr, hNonunit, hReach, hqeq⟩
  subst q
  have hchain := v62_unit_reach_derives hReach
  have hprod :
      g.Produces [Symbol.nonterminal r.input] r.output :=
    ⟨r, hr, ContextFreeRule.Rewrites.input_output⟩
  exact hchain.trans_produces hprod

/-- One transformed rewrite is simulated by an old multi-step derivation. -/
theorem v62_unit_elimination_produces_simulates
    {T : Type} {g : ContextFreeGrammar T}
    {u v : List (Symbol T g.NT)}
    (h : (v62UnitEliminationGrammar g).Produces u v) :
    g.Derives u v := by
  rcases h with ⟨q, hq, hrew⟩
  have hlocal := v62_unit_elimination_rule_derives_old hq
  rcases hrew.exists_parts with ⟨p, s, hu, hv⟩
  have hctx := (hlocal.append_left p).append_right s
  simpa [hu, hv, List.append_assoc] using hctx

/-- Every transformed derivation is simulated by an old derivation. -/
theorem v62_unit_elimination_derives_simulates
    {T : Type} {g : ContextFreeGrammar T}
    {u v : List (Symbol T g.NT)}
    (h : (v62UnitEliminationGrammar g).Derives u v) :
    g.Derives u v := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ last ih =>
      exact ih.trans (v62_unit_elimination_produces_simulates last)

/-- Unit elimination introduces no new terminal word. -/
theorem v62_unit_elimination_language_subset
    {T : Type} (g : ContextFreeGrammar T) :
    ∀ w : List T,
      w ∈ (v62UnitEliminationGrammar g).language →
        w ∈ g.language := by
  intro w hw
  rw [ContextFreeGrammar.mem_language_iff] at hw ⊢
  exact v62_unit_elimination_derives_simulates hw

end FixedHCFG
end LeanCfgProject
