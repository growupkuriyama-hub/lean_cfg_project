import LeanCfgProject.FixedHCFG.V62CFGNormalizationNullable

namespace LeanCfgProject
namespace FixedHCFG

/-!
# Reverse simulation for executable non-start lambda elimination

Every transformed rule is semantically available in the old grammar.  Original
nonempty rules are old one-step rewrites.  A generated unit rule from
`A -> B C` is simulated by that old binary step followed by a nullable child
deriving the empty word.  The reintroduced start epsilon rule is justified
directly by old start nullability.

Consequently the lambda-elimination stage introduces no new terminal words.
-/

/-- One nullable-elimination variant is derivable in the old grammar. -/
theorem v62_nullable_variant_derives_old
    {T : Type} {g : ContextFreeGrammar T}
    {r q : ContextFreeRule T g.NT}
    (hr : r ∈ g.rules)
    (hq : q ∈ v62NullableVariants g r) :
    g.Derives [Symbol.nonterminal q.input] q.output := by
  classical
  unfold v62NullableVariants at hq
  split at hq
  · simp at hq
  · rename_i h0
    cases hout : r.output with
    | nil => exact (h0 hout).elim
    | cons x xs =>
        cases xs with
        | nil =>
            simp [hout] at hq
            subst q
            exact (show g.Produces
              [Symbol.nonterminal r.input] r.output from
                ⟨r, hr, ContextFreeRule.Rewrites.input_output⟩).single
        | cons y ys =>
            cases ys with
            | cons z zs =>
                simp [hout] at hq
                subst q
                exact (show g.Produces
                  [Symbol.nonterminal r.input] r.output from
                    ⟨r, hr, ContextFreeRule.Rewrites.input_output⟩).single
            | nil =>
                cases x with
                | terminal a =>
                    simp [hout] at hq
                    subst q
                    exact (show g.Produces
                      [Symbol.nonterminal r.input] r.output from
                        ⟨r, hr, ContextFreeRule.Rewrites.input_output⟩).single
                | nonterminal B =>
                    cases y with
                    | terminal a =>
                        simp [hout] at hq
                        subst q
                        exact (show g.Produces
                          [Symbol.nonterminal r.input] r.output from
                            ⟨r, hr,
                              ContextFreeRule.Rewrites.input_output⟩).single
                    | nonterminal C =>
                        have hfirst :
                            g.Derives
                              [Symbol.nonterminal r.input]
                              [Symbol.nonterminal B,
                                Symbol.nonterminal C] := by
                          exact (show g.Produces
                            [Symbol.nonterminal r.input]
                            [Symbol.nonterminal B,
                              Symbol.nonterminal C] from
                              ⟨r, hr, by
                                simpa [hout] using
                                  (ContextFreeRule.Rewrites.input_output
                                    (r := r))⟩).single
                        by_cases hB : V62CFGNullable g B
                        · have hB' :
                              g.Derives [Symbol.nonterminal B] [] := hB
                          have hdropB :
                              g.Derives
                                [Symbol.nonterminal B,
                                  Symbol.nonterminal C]
                                [Symbol.nonterminal C] := by
                            simpa using
                              hB'.append_right [Symbol.nonterminal C]
                          by_cases hC : V62CFGNullable g C
                          · have hC' :
                                g.Derives [Symbol.nonterminal C] [] := hC
                            have hdropC :
                                g.Derives
                                  [Symbol.nonterminal B,
                                    Symbol.nonterminal C]
                                  [Symbol.nonterminal B] := by
                              simpa using
                                hC'.append_left [Symbol.nonterminal B]
                            simp [hout, hB, hC] at hq
                            rcases hq with rfl | rfl | rfl
                            · exact hfirst
                            · exact hfirst.trans hdropB
                            · exact hfirst.trans hdropC
                          · simp [hout, hB, hC] at hq
                            rcases hq with rfl | rfl
                            · exact hfirst
                            · exact hfirst.trans hdropB
                        · by_cases hC : V62CFGNullable g C
                          · have hC' :
                                g.Derives [Symbol.nonterminal C] [] := hC
                            have hdropC :
                                g.Derives
                                  [Symbol.nonterminal B,
                                    Symbol.nonterminal C]
                                  [Symbol.nonterminal B] := by
                              simpa using
                                hC'.append_left [Symbol.nonterminal B]
                            simp [hout, hB, hC] at hq
                            rcases hq with rfl | rfl
                            · exact hfirst
                            · exact hfirst.trans hdropC
                          · simp [hout, hB, hC] at hq
                            subst q
                            exact hfirst

/-- Every installed transformed rule is derivable in the old grammar. -/
theorem v62_nullable_elimination_rule_derives_old
    {T : Type} {g : ContextFreeGrammar T}
    {q : ContextFreeRule T g.NT}
    (hq : q ∈ (v62NullableEliminationGrammar g).rules) :
    g.Derives [Symbol.nonterminal q.input] q.output := by
  classical
  change q ∈
      g.rules.biUnion (fun r => (v62NullableVariants g r).toFinset) ∪
        (if V62CFGNullable g g.initial
          then {v62StartEpsilonRule g}
          else ∅) at hq
  rw [Finset.mem_union] at hq
  rcases hq with hOld | hStart
  · rcases Finset.mem_biUnion.mp hOld with ⟨r, hr, hqr⟩
    apply v62_nullable_variant_derives_old hr
    simpa only [List.mem_toFinset] using hqr
  · by_cases hNull : V62CFGNullable g g.initial
    · have hEq : q = v62StartEpsilonRule g := by
        simpa [hNull] using hStart
      subst q
      change g.Derives [Symbol.nonterminal g.initial] []
      exact hNull
    · simp [hNull] at hStart

/-- A transformed one-step rewrite is simulated by an old multi-step derivation. -/
theorem v62_nullable_elimination_produces_simulates
    {T : Type} {g : ContextFreeGrammar T}
    {u v : List (Symbol T g.NT)}
    (h : (v62NullableEliminationGrammar g).Produces u v) :
    g.Derives u v := by
  rcases h with ⟨q, hq, hrew⟩
  have hlocal := v62_nullable_elimination_rule_derives_old hq
  rcases hrew.exists_parts with ⟨p, s, hu, hv⟩
  have hctx := (hlocal.append_left p).append_right s
  simpa [hu, hv, List.append_assoc] using hctx

/-- Every transformed derivation is simulated by an old derivation. -/
theorem v62_nullable_elimination_derives_simulates
    {T : Type} {g : ContextFreeGrammar T}
    {u v : List (Symbol T g.NT)}
    (h : (v62NullableEliminationGrammar g).Derives u v) :
    g.Derives u v := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ last ih =>
      exact ih.trans (v62_nullable_elimination_produces_simulates last)

/-- Non-start lambda elimination introduces no new terminal word. -/
theorem v62_nullable_elimination_language_subset
    {T : Type} (g : ContextFreeGrammar T) :
    ∀ w : List T,
      w ∈ (v62NullableEliminationGrammar g).language →
        w ∈ g.language := by
  intro w hw
  rw [ContextFreeGrammar.mem_language_iff] at hw ⊢
  exact v62_nullable_elimination_derives_simulates hw

end FixedHCFG
end LeanCfgProject
