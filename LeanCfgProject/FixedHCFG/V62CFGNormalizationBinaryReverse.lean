import LeanCfgProject.FixedHCFG.V62CFGNormalizationBinaryProjection

namespace LeanCfgProject
namespace FixedHCFG

/-!
# Reverse semantic simulation for executable v62 binarization

The suffix-expansion map from `V62CFGNormalizationBinaryProjection` turns each
helper-chain production into an identity and each primary transformed
production into its original CFG production.  This file lifts that local fact
through rewrite contexts and arbitrary derivations, proving that binarization
introduces no terminal words.
-/

@[simp] theorem v62_binarize_project_word_append
    {T N : Type*}
    (u v : List (Symbol T
      (Sum N (ContextFreeRule T N × Nat)))) :
    v62BinarizeProjectWord (u ++ v) =
      v62BinarizeProjectWord u ++ v62BinarizeProjectWord v := by
  simp [v62BinarizeProjectWord, List.flatMap_append]

/-- If a transformed rule is projection-invisible, so is any contextual rewrite by it. -/
theorem v62_binarize_project_rewrites_eq
    {T N : Type*}
    {q : ContextFreeRule T
      (Sum N (ContextFreeRule T N × Nat))}
    {u v : List (Symbol T
      (Sum N (ContextFreeRule T N × Nat)))}
    (hrew : q.Rewrites u v)
    (hmid :
      v62BinarizeProjectWord [Symbol.nonterminal q.input] =
        v62BinarizeProjectWord q.output) :
    v62BinarizeProjectWord u = v62BinarizeProjectWord v := by
  rcases hrew.exists_parts with ⟨p, s, hu, hv⟩
  rw [hu, hv]
  simp only [v62_binarize_project_word_append]
  rw [hmid]

/--
If a transformed rule projects to an old production, any contextual rewrite
projects to the corresponding old rewrite.
-/
theorem v62_binarize_project_rewrites_old
    {T N : Type*}
    {r : ContextFreeRule T N}
    {q : ContextFreeRule T
      (Sum N (ContextFreeRule T N × Nat))}
    {u v : List (Symbol T
      (Sum N (ContextFreeRule T N × Nat)))}
    (hrew : q.Rewrites u v)
    (hinput :
      v62BinarizeProjectWord [Symbol.nonterminal q.input] =
        [Symbol.nonterminal r.input])
    (houtput : v62BinarizeProjectWord q.output = r.output) :
    r.Rewrites (v62BinarizeProjectWord u)
      (v62BinarizeProjectWord v) := by
  rcases hrew.exists_parts with ⟨p, s, hu, hv⟩
  rw [ContextFreeRule.rewrites_iff]
  refine ⟨v62BinarizeProjectWord p, v62BinarizeProjectWord s, ?_, ?_⟩
  · rw [hu]
    simp only [v62_binarize_project_word_append]
    rw [hinput]
  · rw [hv]
    simp only [v62_binarize_project_word_append]
    rw [houtput]

/--
A single binarized step projects either to an identity helper step or to one
production of the old grammar.
-/
theorem v62_project_binarized_produces
    {T : Type} {g : ContextFreeGrammar T}
    {u v : List (Symbol T
      (Sum g.NT (ContextFreeRule T g.NT × Nat)))}
    (h : (v62BinarizedGrammar g).Produces u v) :
    v62BinarizeProjectWord u = v62BinarizeProjectWord v ∨
      g.Produces (v62BinarizeProjectWord u)
        (v62BinarizeProjectWord v) := by
  classical
  rcases h with ⟨q, hq, hrew⟩
  change q ∈ g.rules.biUnion
    (fun r => (v62BinarizeRulesFor r).toFinset) at hq
  rcases Finset.mem_biUnion.mp hq with ⟨r, hr, hqr⟩
  have hlist : q ∈ v62BinarizeRulesFor r := by
    simpa only [List.mem_toFinset] using hqr
  cases h0 : r.output with
  | nil =>
      simp [v62BinarizeRulesFor, h0] at hlist
      subst q
      right
      refine ⟨r, hr, ?_⟩
      apply v62_binarize_project_rewrites_old hrew
      · rfl
      · simpa [h0] using
          (v62_binarize_project_lift_word r.output)
  | cons x xs =>
      cases xs with
      | nil =>
          simp [v62BinarizeRulesFor, h0] at hlist
          subst q
          right
          refine ⟨r, hr, ?_⟩
          apply v62_binarize_project_rewrites_old hrew
          · rfl
          · simpa [h0] using
          (v62_binarize_project_lift_word r.output)
      | cons y ys =>
          cases ys with
          | nil =>
              simp [v62BinarizeRulesFor, h0] at hlist
              subst q
              right
              refine ⟨r, hr, ?_⟩
              apply v62_binarize_project_rewrites_old hrew
              · rfl
              · simpa [h0] using
          (v62_binarize_project_lift_word r.output)
          | cons z zs =>
              simp only [v62BinarizeRulesFor, h0, List.mem_cons] at hlist
              rcases hlist with hfirst | htail
              · subst q
                right
                refine ⟨r, hr, ?_⟩
                apply v62_binarize_project_rewrites_old hrew
                · rfl
                · simpa [v62BinarizeProjectWord, h0]
              · left
                apply v62_binarize_project_rewrites_eq hrew
                exact v62_binarize_tail_rule_projects_eq
                  (r := r) (i := 0) (u := y :: z :: zs) (q := q)
                  (by simpa [h0]) htail

/-- Every binarized derivation projects to an old derivation. -/
theorem v62_project_binarized_derives
    {T : Type} {g : ContextFreeGrammar T}
    {u v : List (Symbol T
      (Sum g.NT (ContextFreeRule T g.NT × Nat)))}
    (h : (v62BinarizedGrammar g).Derives u v) :
    g.Derives (v62BinarizeProjectWord u)
      (v62BinarizeProjectWord v) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ last ih =>
      rcases v62_project_binarized_produces last with heq | hstep
      · simpa [heq] using ih
      · exact ih.trans_produces hstep

/-- Binarization introduces no new terminal word. -/
theorem v62_binarization_language_subset
    {T : Type} (g : ContextFreeGrammar T) :
    ∀ w : List T,
      w ∈ (v62BinarizedGrammar g).language → w ∈ g.language := by
  intro w hw
  rw [ContextFreeGrammar.mem_language_iff] at hw ⊢
  have hp := v62_project_binarized_derives hw
  rw [v62_binarize_project_terminal_word] at hp
  simpa [v62BinarizeProjectWord, v62BinarizeProjectSymbol] using hp

/-- Long-rule binarization preserves the generated language exactly. -/
theorem v62_binarization_language_eq
    {T : Type} (g : ContextFreeGrammar T) :
    (v62BinarizedGrammar g).language = g.language := by
  apply Set.ext
  intro w
  constructor
  · exact v62_binarization_language_subset g w
  · exact v62_language_subset_binarization g w

end FixedHCFG
end LeanCfgProject
