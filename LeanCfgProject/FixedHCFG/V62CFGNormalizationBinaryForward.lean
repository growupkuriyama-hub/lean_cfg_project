import LeanCfgProject.FixedHCFG.V62CFGNormalizationBinary

namespace LeanCfgProject
namespace FixedHCFG

/-!
# Forward simulation for executable v62 binarization

The structural binarization file builds the chain grammar and proves that every
new RHS has length at most two.  Here we verify the semantic direction needed
to show that binarization does not lose old derivations.

The central lemma executes a helper chain from its current helper nonterminal
to the plainly lifted remaining suffix.  Applying that lemma after the first
rule of each transformed production simulates one old CFG step; induction then
simulates arbitrary derivations and generated terminal words.
-/

/-- A rule generated from an old rule is present in the binarized grammar. -/
theorem v62_binarized_rule_mem
    {T : Type} {g : ContextFreeGrammar T}
    {r : ContextFreeRule T g.NT}
    (hr : r ∈ g.rules)
    {q : ContextFreeRule T
      (Sum g.NT (ContextFreeRule T g.NT × Nat))}
    (hq : q ∈ v62BinarizeRulesFor r) :
    q ∈ (v62BinarizedGrammar g).rules := by
  classical
  change q ∈ g.rules.biUnion
    (fun s => (v62BinarizeRulesFor s).toFinset)
  exact Finset.mem_biUnion.mpr
    ⟨r, hr, by simpa only [List.mem_toFinset] using hq⟩

/--
Execute an arbitrary well-installed helper chain.  The membership hypothesis
is deliberately local: later calls instantiate it with the tail-rule sublist
belonging to one concrete old production.
-/
theorem v62_binarize_tail_derives
    {T : Type} (g : ContextFreeGrammar T)
    (r : ContextFreeRule T g.NT) (i : Nat)
    (u : List (Symbol T g.NT))
    (hmem : ∀ q, q ∈ v62BinarizeTailRules r i u →
      q ∈ (v62BinarizedGrammar g).rules)
    (hlen : 2 ≤ u.length) :
    (v62BinarizedGrammar g).Derives
      [v62BinarizeHelperSymbol r i]
      (u.map v62BinarizeLiftSymbol) := by
  induction u generalizing i with
  | nil =>
      simp at hlen
  | cons x xs ih =>
      cases xs with
      | nil =>
          simp at hlen
      | cons y ys =>
          cases ys with
          | nil =>
              have hstep :
                  (v62BinarizedGrammar g).Produces
                    [v62BinarizeHelperSymbol r i]
                    [v62BinarizeLiftSymbol x,
                      v62BinarizeLiftSymbol y] := by
                refine ⟨
                  { input := Sum.inr (r, i)
                    output := [v62BinarizeLiftSymbol x,
                      v62BinarizeLiftSymbol y] }, ?_, ?_⟩
                · apply hmem
                  simp [v62BinarizeTailRules]
                · simpa [v62BinarizeHelperSymbol] using
                    (ContextFreeRule.Rewrites.input_output
                      (r :=
                        { input := Sum.inr (r, i)
                          output := [v62BinarizeLiftSymbol x,
                            v62BinarizeLiftSymbol y] }))
              simpa using hstep.single
          | cons z zs =>
              have hstep :
                  (v62BinarizedGrammar g).Produces
                    [v62BinarizeHelperSymbol r i]
                    [v62BinarizeLiftSymbol x,
                      v62BinarizeHelperSymbol r (i + 1)] := by
                refine ⟨
                  { input := Sum.inr (r, i)
                    output := [v62BinarizeLiftSymbol x,
                      v62BinarizeHelperSymbol r (i + 1)] }, ?_, ?_⟩
                · apply hmem
                  simp [v62BinarizeTailRules]
                · simpa [v62BinarizeHelperSymbol] using
                    (ContextFreeRule.Rewrites.input_output
                      (r :=
                        { input := Sum.inr (r, i)
                          output := [v62BinarizeLiftSymbol x,
                            v62BinarizeHelperSymbol r (i + 1)] }))
              have hmemTail : ∀ q,
                  q ∈ v62BinarizeTailRules r (i + 1) (y :: z :: zs) →
                    q ∈ (v62BinarizedGrammar g).rules := by
                intro q hq
                apply hmem q
                simp only [v62BinarizeTailRules, List.mem_cons]
                exact Or.inr hq
              have hrest := ih (i := i + 1) hmemTail (by simp)
              have hall := hstep.single.trans
                (hrest.append_left [v62BinarizeLiftSymbol x])
              simpa using hall

/-- One old CFG step is simulated by a derivation of the binarized grammar. -/
theorem v62_binarization_simulates_produces
    {T : Type} {g : ContextFreeGrammar T}
    {u v : List (Symbol T g.NT)}
    (h : g.Produces u v) :
    (v62BinarizedGrammar g).Derives
      (u.map v62BinarizeLiftSymbol)
      (v.map v62BinarizeLiftSymbol) := by
  classical
  rcases h with ⟨r, hr, hrew⟩
  rcases hrew.exists_parts with ⟨p, s, hu, hv⟩
  cases h0 : r.output with
  | nil =>
      have hstep :
          (v62BinarizedGrammar g).Produces
            (u.map v62BinarizeLiftSymbol)
            (v.map v62BinarizeLiftSymbol) := by
        refine ⟨
          { input := Sum.inl r.input
            output := r.output.map v62BinarizeLiftSymbol }, ?_, ?_⟩
        · apply v62_binarized_rule_mem hr
          simp [v62BinarizeRulesFor, h0]
        · rw [ContextFreeRule.rewrites_iff]
          refine ⟨p.map v62BinarizeLiftSymbol,
            s.map v62BinarizeLiftSymbol, ?_, ?_⟩
          · rw [hu]
            simp [List.map_append, v62BinarizeLiftSymbol]
          · rw [hv]
            simp [List.map_append]
      exact hstep.single
  | cons x xs =>
      cases xs with
      | nil =>
          have hstep :
              (v62BinarizedGrammar g).Produces
                (u.map v62BinarizeLiftSymbol)
                (v.map v62BinarizeLiftSymbol) := by
            refine ⟨
              { input := Sum.inl r.input
                output := r.output.map v62BinarizeLiftSymbol }, ?_, ?_⟩
            · apply v62_binarized_rule_mem hr
              simp [v62BinarizeRulesFor, h0]
            · rw [ContextFreeRule.rewrites_iff]
              refine ⟨p.map v62BinarizeLiftSymbol,
                s.map v62BinarizeLiftSymbol, ?_, ?_⟩
              · rw [hu]
                simp [List.map_append, v62BinarizeLiftSymbol]
              · rw [hv]
                simp [List.map_append]
          exact hstep.single
      | cons y ys =>
          cases ys with
          | nil =>
              have hstep :
                  (v62BinarizedGrammar g).Produces
                    (u.map v62BinarizeLiftSymbol)
                    (v.map v62BinarizeLiftSymbol) := by
                refine ⟨
                  { input := Sum.inl r.input
                    output := r.output.map v62BinarizeLiftSymbol }, ?_, ?_⟩
                · apply v62_binarized_rule_mem hr
                  simp [v62BinarizeRulesFor, h0]
                · rw [ContextFreeRule.rewrites_iff]
                  refine ⟨p.map v62BinarizeLiftSymbol,
                    s.map v62BinarizeLiftSymbol, ?_, ?_⟩
                  · rw [hu]
                    simp [List.map_append, v62BinarizeLiftSymbol]
                  · rw [hv]
                    simp [List.map_append]
              exact hstep.single
          | cons z zs =>
              have hfirst :
                  (v62BinarizedGrammar g).Produces
                    (u.map v62BinarizeLiftSymbol)
                    (p.map v62BinarizeLiftSymbol ++
                      [v62BinarizeLiftSymbol x,
                        v62BinarizeHelperSymbol r 0] ++
                      s.map v62BinarizeLiftSymbol) := by
                refine ⟨
                  { input := Sum.inl r.input
                    output := [v62BinarizeLiftSymbol x,
                      v62BinarizeHelperSymbol r 0] }, ?_, ?_⟩
                · apply v62_binarized_rule_mem hr
                  simp [v62BinarizeRulesFor, h0]
                · rw [ContextFreeRule.rewrites_iff]
                  refine ⟨p.map v62BinarizeLiftSymbol,
                    s.map v62BinarizeLiftSymbol, ?_, rfl⟩
                  rw [hu]
                  simp [List.map_append, v62BinarizeLiftSymbol]
              have htailMem : ∀ q,
                  q ∈ v62BinarizeTailRules r 0 (y :: z :: zs) →
                    q ∈ (v62BinarizedGrammar g).rules := by
                intro q hq
                apply v62_binarized_rule_mem hr
                simp only [v62BinarizeRulesFor, h0, List.mem_cons]
                exact Or.inr hq
              have htail := v62_binarize_tail_derives
                g r 0 (y :: z :: zs) htailMem (by simp)
              have hmiddle :=
                (htail.append_left [v62BinarizeLiftSymbol x]).append_left
                  (p.map v62BinarizeLiftSymbol)
              have hcontext := hmiddle.append_right
                (s.map v62BinarizeLiftSymbol)
              have hall := hfirst.single.trans hcontext
              rw [hv]
              simpa [h0, List.map_append, List.append_assoc] using hall

/-- Every old derivation is simulated after binarization. -/
theorem v62_binarization_simulates_derives
    {T : Type} {g : ContextFreeGrammar T}
    {u v : List (Symbol T g.NT)}
    (h : g.Derives u v) :
    (v62BinarizedGrammar g).Derives
      (u.map v62BinarizeLiftSymbol)
      (v.map v62BinarizeLiftSymbol) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ last ih =>
      exact ih.trans (v62_binarization_simulates_produces last)

/-- Lifting a terminal word changes only the nonterminal type. -/
@[simp] theorem v62_binarize_lift_terminal_word
    {T : Type} {g : ContextFreeGrammar T} (w : List T) :
    (w.map (@Symbol.terminal T g.NT)).map v62BinarizeLiftSymbol =
      w.map (@Symbol.terminal T
        (Sum g.NT (ContextFreeRule T g.NT × Nat))) := by
  induction w with
  | nil => rfl
  | cons a w ih => simp [v62BinarizeLiftSymbol, ih]

/-- Binarization does not lose any old generated word. -/
theorem v62_language_subset_binarization
    {T : Type} (g : ContextFreeGrammar T) :
    ∀ w : List T, w ∈ g.language → w ∈ (v62BinarizedGrammar g).language := by
  intro w hw
  rw [ContextFreeGrammar.mem_language_iff] at hw ⊢
  have hSim := v62_binarization_simulates_derives hw
  change (v62BinarizedGrammar g).Derives
    [Symbol.nonterminal (Sum.inl g.initial)]
    (w.map (@Symbol.terminal T
      (Sum g.NT (ContextFreeRule T g.NT × Nat))))
  rw [← v62_binarize_lift_terminal_word (g := g) w]
  simpa only [List.map_cons, List.map_nil, v62BinarizeLiftSymbol] using hSim

end FixedHCFG
end LeanCfgProject
