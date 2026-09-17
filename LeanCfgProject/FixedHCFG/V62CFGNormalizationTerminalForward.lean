import LeanCfgProject.FixedHCFG.V62CFGNormalizationTerminal

namespace LeanCfgProject
namespace FixedHCFG

/-!
# Forward simulation for v62 terminal isolation

`V62CFGNormalizationTerminal` constructs the terminal-isolated grammar and
proves the reverse projection.  This file supplies the other semantic
inclusion.  The only extra work is to expand, one by one, the helper
nonterminals `T_a` introduced in a long right-hand side.

Together with the reverse projection this closes language preservation for the
terminal-isolation stage.  Thickness bookkeeping is kept separate: old
nonterminals inherit their old short yields, while helper nonterminals have a
one-letter yield.
-/

/-- A terminal occurring in a rule RHS belongs to that rule's terminal set. -/
theorem v62_terminal_mem_ruleTerminals
    {T N : Type*} {r : ContextFreeRule T N} {a : T}
    (ha : Symbol.terminal a ∈ r.output) :
    a ∈ v62RuleTerminals r := by
  classical
  unfold v62RuleTerminals
  simp only [List.mem_toFinset, List.mem_filterMap]
  exact ⟨Symbol.terminal a, ha, rfl⟩

/-- A terminal occurring in a grammar rule belongs to the global helper set. -/
theorem v62_terminal_mem_grammarTerminals_of_rule
    {T : Type} {g : ContextFreeGrammar T}
    {r : ContextFreeRule T g.NT} {a : T}
    (hr : r ∈ g.rules)
    (ha : Symbol.terminal a ∈ r.output) :
    a ∈ v62GrammarTerminals g := by
  classical
  unfold v62GrammarTerminals
  exact Finset.mem_biUnion.mpr
    ⟨r, hr, v62_terminal_mem_ruleTerminals ha⟩

/-- Every helper symbol has its intended one-step expansion `T_a -> a`. -/
theorem v62_terminal_helper_produces
    {T : Type} (g : ContextFreeGrammar T)
    {a : T} (ha : a ∈ v62GrammarTerminals g) :
    (v62TerminalIsolationGrammar g).Produces
      [Symbol.nonterminal (Sum.inr a)]
      [Symbol.terminal a] := by
  classical
  refine ⟨v62TerminalHelperRule a, ?_, ?_⟩
  · change v62TerminalHelperRule a ∈
      g.rules.image v62IsolateRule ∪
        (v62GrammarTerminals g).image v62TerminalHelperRule
    exact Finset.mem_union_right _
      (Finset.mem_image.mpr ⟨a, ha, rfl⟩)
  · exact ContextFreeRule.Rewrites.input_output

/--
Expand every helper nonterminal in a long isolated RHS.  The hypothesis says
that every terminal represented in the old RHS has a helper rule in the
transformed grammar.
-/
theorem v62_isolate_long_derives_terminal_lift
    {T : Type} (g : ContextFreeGrammar T)
    (u : List (Symbol T g.NT))
    (hterm : ∀ a : T, Symbol.terminal a ∈ u →
      a ∈ v62GrammarTerminals g) :
    (v62TerminalIsolationGrammar g).Derives
      (u.map v62IsolateLongSymbol)
      (u.map v62TerminalLiftSymbol) := by
  induction u with
  | nil =>
      exact ContextFreeGrammar.Derives.refl
        (g := v62TerminalIsolationGrammar g) []
  | cons x xs ih =>
      have htail : ∀ a : T, Symbol.terminal a ∈ xs →
          a ∈ v62GrammarTerminals g := by
        intro a ha
        exact hterm a (List.mem_cons_of_mem x ha)
      have ih' := ih htail
      cases x with
      | nonterminal A =>
          simpa [v62IsolateLongSymbol, v62TerminalLiftSymbol] using
            ih'.append_left [Symbol.nonterminal (Sum.inl A)]
      | terminal a =>
          have ha : a ∈ v62GrammarTerminals g :=
            hterm a (by simp)
          have hhead :=
            (v62_terminal_helper_produces g (a := a) ha).single
          have h1 := hhead.append_right (xs.map v62IsolateLongSymbol)
          have h2 := ih'.append_left [Symbol.terminal a]
          simpa [v62IsolateLongSymbol, v62TerminalLiftSymbol] using
            h1.trans h2

/-- An isolated RHS derives the plainly lifted old RHS. -/
theorem v62_isolated_output_derives_terminal_lift
    {T : Type} (g : ContextFreeGrammar T)
    (r : ContextFreeRule T g.NT) (hr : r ∈ g.rules) :
    (v62TerminalIsolationGrammar g).Derives
      (v62IsolateOutput r.output)
      (r.output.map v62TerminalLiftSymbol) := by
  by_cases hlong : 2 ≤ r.output.length
  · simp only [v62IsolateOutput, hlong, if_true]
    exact v62_isolate_long_derives_terminal_lift g r.output
      (fun a ha => v62_terminal_mem_grammarTerminals_of_rule hr ha)
  · simpa [v62IsolateOutput, hlong] using
      (ContextFreeGrammar.Derives.refl
        (g := v62TerminalIsolationGrammar g)
        (r.output.map v62TerminalLiftSymbol))

/-- One old grammar step is simulated by a derivation after terminal isolation. -/
theorem v62_terminal_isolation_simulates_produces
    {T : Type} {g : ContextFreeGrammar T}
    {u v : List (Symbol T g.NT)}
    (h : g.Produces u v) :
    (v62TerminalIsolationGrammar g).Derives
      (u.map v62TerminalLiftSymbol)
      (v.map v62TerminalLiftSymbol) := by
  classical
  rcases h with ⟨r, hr, hrew⟩
  rcases hrew.exists_parts with ⟨p, s, hu, hv⟩
  have hStep :
      (v62TerminalIsolationGrammar g).Produces
        (u.map v62TerminalLiftSymbol)
        (p.map v62TerminalLiftSymbol ++
          v62IsolateOutput r.output ++
          s.map v62TerminalLiftSymbol) := by
    refine ⟨v62IsolateRule r, ?_, ?_⟩
    · change v62IsolateRule r ∈
        g.rules.image v62IsolateRule ∪
          (v62GrammarTerminals g).image v62TerminalHelperRule
      exact Finset.mem_union_left _
        (Finset.mem_image.mpr ⟨r, hr, rfl⟩)
    · rw [ContextFreeRule.rewrites_iff]
      refine ⟨p.map v62TerminalLiftSymbol,
        s.map v62TerminalLiftSymbol, ?_, ?_⟩
      · rw [hu]
        simp [List.map_append, v62IsolateRule,
          v62TerminalLiftSymbol]
      · rfl
  have hExpand :=
    ((v62_isolated_output_derives_terminal_lift g r hr).append_left
      (p.map v62TerminalLiftSymbol)).append_right
        (s.map v62TerminalLiftSymbol)
  have hAll := hStep.single.trans hExpand
  rw [hv]
  simpa [List.map_append, List.append_assoc] using hAll

/-- Every old derivation is simulated by the terminal-isolated grammar. -/
theorem v62_terminal_isolation_simulates_derives
    {T : Type} {g : ContextFreeGrammar T}
    {u v : List (Symbol T g.NT)}
    (h : g.Derives u v) :
    (v62TerminalIsolationGrammar g).Derives
      (u.map v62TerminalLiftSymbol)
      (v.map v62TerminalLiftSymbol) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ last ih =>
      exact ih.trans (v62_terminal_isolation_simulates_produces last)

/-- Lifting a terminal word changes only the nonterminal type. -/
@[simp] theorem v62_terminal_lift_terminal_word
    {T : Type} {g : ContextFreeGrammar T} (w : List T) :
    (w.map (@Symbol.terminal T g.NT)).map v62TerminalLiftSymbol =
      w.map (@Symbol.terminal T (Sum g.NT T)) := by
  induction w with
  | nil => rfl
  | cons a w ih => simp [v62TerminalLiftSymbol, ih]

/-- Old word derivations survive terminal isolation. -/
theorem v62_terminal_isolation_preserves_old_word_derivation
    {T : Type} {g : ContextFreeGrammar T}
    {A : g.NT} {w : List T}
    (h : V62CFGDerivesWordFrom g A w) :
    V62CFGDerivesWordFrom (v62TerminalIsolationGrammar g) (Sum.inl A) w := by
  unfold V62CFGDerivesWordFrom at h ⊢
  have hSim := v62_terminal_isolation_simulates_derives h
  change (v62TerminalIsolationGrammar g).Derives
    [Symbol.nonterminal (Sum.inl A)]
    (w.map (@Symbol.terminal T (Sum g.NT T)))
  rw [← v62_terminal_lift_terminal_word (g := g) w]
  simpa only [List.map_cons, List.map_nil, v62TerminalLiftSymbol] using hSim

/-- Terminal isolation does not lose any old generated word. -/
theorem v62_language_subset_terminal_isolation
    {T : Type} (g : ContextFreeGrammar T) :
    ∀ w : List T,
      w ∈ g.language → w ∈ (v62TerminalIsolationGrammar g).language := by
  intro w hw
  rw [ContextFreeGrammar.mem_language_iff] at hw ⊢
  have hSim := v62_terminal_isolation_simulates_derives hw
  change (v62TerminalIsolationGrammar g).Derives
    [Symbol.nonterminal (Sum.inl g.initial)]
    (w.map (@Symbol.terminal T (Sum g.NT T)))
  rw [← v62_terminal_lift_terminal_word (g := g) w]
  simpa only [List.map_cons, List.map_nil, v62TerminalLiftSymbol] using hSim

/-- Terminal isolation preserves the generated language exactly. -/
theorem v62_terminal_isolation_language_eq
    {T : Type} (g : ContextFreeGrammar T) :
    (v62TerminalIsolationGrammar g).language = g.language := by
  apply Set.ext
  intro w
  constructor
  · exact v62_terminal_isolation_language_subset g w
  · exact v62_language_subset_terminal_isolation g w

end FixedHCFG
end LeanCfgProject
