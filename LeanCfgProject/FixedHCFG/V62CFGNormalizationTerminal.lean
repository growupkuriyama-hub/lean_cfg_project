import LeanCfgProject.FixedHCFG.V62CFGNormalizationProjection

namespace LeanCfgProject
namespace FixedHCFG

/-!
# Terminal isolation for the v62 CFG normalization

This is the second executable normalization stage used by Proposition
`thick-ssbnf-normal`.  Old nonterminals are embedded in the left summand
`Sum g.NT T`; the right summand supplies one helper nonterminal for every
terminal occurring in the finite rule set.  In RHSs of length at least two,
terminal symbols are replaced by their helper nonterminals.  Singleton
terminal productions are left unchanged.

This file establishes the transformed grammar, its terminal-isolation
invariant, a linear rule-count envelope in terms of the number of terminals
occurring in the old rules, and the reverse simulation showing that no new
terminal word is introduced.  Forward simulation is kept as the next proof
layer because it requires iterating the helper rules through a whole RHS.
-/

/-- Extract the terminal carried by a grammar symbol, if any. -/
def v62TerminalOfSymbol {T N : Type*} : Symbol T N → Option T
  | .terminal a => some a
  | .nonterminal _ => none

/-- Terminals occurring in one rule RHS. -/
noncomputable def v62RuleTerminals {T N : Type*}
    (r : ContextFreeRule T N) : Finset T := by
  classical
  exact (r.output.filterMap v62TerminalOfSymbol).toFinset

/-- The finite set of terminals occurring anywhere in the grammar rules. -/
noncomputable def v62GrammarTerminals {T : Type*}
    (g : ContextFreeGrammar T) : Finset T := by
  classical
  exact g.rules.biUnion v62RuleTerminals

/-- Embed an old symbol without isolating terminals. -/
def v62TerminalLiftSymbol {T N : Type*} :
    Symbol T N → Symbol T (Sum N T)
  | .terminal a => .terminal a
  | .nonterminal A => .nonterminal (Sum.inl A)

/-- Replace every terminal by its dedicated helper nonterminal. -/
def v62IsolateLongSymbol {T N : Type*} :
    Symbol T N → Symbol T (Sum N T)
  | .terminal a => .nonterminal (Sum.inr a)
  | .nonterminal A => .nonterminal (Sum.inl A)

/-- Only mixed/long RHSs need terminal isolation. -/
def v62IsolateOutput {T N : Type*} (u : List (Symbol T N)) :
    List (Symbol T (Sum N T)) :=
  if 2 ≤ u.length then u.map v62IsolateLongSymbol
  else u.map v62TerminalLiftSymbol

/-- Transform one old rule. -/
def v62IsolateRule {T N : Type*}
    (r : ContextFreeRule T N) : ContextFreeRule T (Sum N T) :=
  { input := Sum.inl r.input
    output := v62IsolateOutput r.output }

/-- Helper production `T_a -> a`. -/
def v62TerminalHelperRule {T N : Type*} (a : T) :
    ContextFreeRule T (Sum N T) :=
  { input := Sum.inr a
    output := [Symbol.terminal a] }

/-- The executable terminal-isolation grammar. -/
@[reducible] noncomputable def v62TerminalIsolationGrammar {T : Type*}
    (g : ContextFreeGrammar T) : ContextFreeGrammar T := by
  classical
  exact
    { NT := Sum g.NT T
      initial := Sum.inl g.initial
      rules := g.rules.image v62IsolateRule ∪
        (v62GrammarTerminals g).image v62TerminalHelperRule }

/-- A long isolated RHS contains no terminal symbols. -/
theorem v62_terminal_not_mem_isolate_long
    {T N : Type*} (u : List (Symbol T N)) (a : T) :
    Symbol.terminal a ∉ u.map v62IsolateLongSymbol := by
  induction u with
  | nil => simp
  | cons x xs ih =>
      cases x <;> simp [v62IsolateLongSymbol, ih]

/-- Terminal-isolated means that every RHS of length at least two is all-NT. -/
def V62CFGTerminalsIsolated {T : Type*} (g : ContextFreeGrammar T) : Prop :=
  ∀ r ∈ g.rules, 2 ≤ r.output.length →
    ∀ a : T, Symbol.terminal a ∉ r.output

/-- The executable transformation satisfies the terminal-isolation invariant. -/
theorem v62_terminal_isolation_invariant
    {T : Type*} (g : ContextFreeGrammar T) :
    V62CFGTerminalsIsolated (v62TerminalIsolationGrammar g) := by
  classical
  unfold V62CFGTerminalsIsolated
  intro r hr hlen a
  change r ∈ g.rules.image v62IsolateRule ∪
    (v62GrammarTerminals g).image v62TerminalHelperRule at hr
  rw [Finset.mem_union] at hr
  rcases hr with hOld | hHelper
  · rcases Finset.mem_image.mp hOld with ⟨q, hq, hqr⟩
    subst r
    by_cases hlong : 2 ≤ q.output.length
    · simp only [v62IsolateRule, v62IsolateOutput, hlong, if_true]
      exact v62_terminal_not_mem_isolate_long q.output a
    · simp [v62IsolateRule, v62IsolateOutput, hlong] at hlen
      omega
  · rcases Finset.mem_image.mp hHelper with ⟨b, hb, hbr⟩
    subst r
    simp [v62TerminalHelperRule] at hlen

/-- Terminal isolation adds at most one helper rule per occurring terminal. -/
theorem v62_terminal_isolation_rule_card_le
    {T : Type*} (g : ContextFreeGrammar T) :
    (v62TerminalIsolationGrammar g).rules.card ≤
      g.rules.card + (v62GrammarTerminals g).card := by
  classical
  change (g.rules.image v62IsolateRule ∪
      (v62GrammarTerminals g).image v62TerminalHelperRule).card ≤
    g.rules.card + (v62GrammarTerminals g).card
  exact (Finset.card_union_le _ _).trans
    (Nat.add_le_add Finset.card_image_le Finset.card_image_le)

/-- Project helper nonterminals back to the terminals they stand for. -/
def v62ProjectIsolatedSymbol {T : Type*} (g : ContextFreeGrammar T) :
    Symbol T (Sum g.NT T) → Symbol T g.NT
  | .terminal a => .terminal a
  | .nonterminal (Sum.inl A) => .nonterminal A
  | .nonterminal (Sum.inr a) => .terminal a

@[simp] theorem v62_project_terminal_lift_symbol
    {T : Type*} (g : ContextFreeGrammar T) (x : Symbol T g.NT) :
    v62ProjectIsolatedSymbol g (v62TerminalLiftSymbol x) = x := by
  cases x <;> rfl

@[simp] theorem v62_project_isolate_long_symbol
    {T : Type*} (g : ContextFreeGrammar T) (x : Symbol T g.NT) :
    v62ProjectIsolatedSymbol g (v62IsolateLongSymbol x) = x := by
  cases x <;> rfl

/-- Projection of an isolated RHS is the original RHS in both length cases. -/
@[simp] theorem v62_project_isolated_output
    {T : Type*} (g : ContextFreeGrammar T) (u : List (Symbol T g.NT)) :
    (v62IsolateOutput u).map (v62ProjectIsolatedSymbol g) = u := by
  by_cases hlong : 2 ≤ u.length
  · simp [v62IsolateOutput, hlong, List.map_map, Function.comp_def]
  · simp [v62IsolateOutput, hlong, List.map_map, Function.comp_def]

/--
One terminal-isolation step projects either to an identity helper step or to
one genuine step of the old grammar.
-/
theorem v62_project_terminal_isolation_produces
    {T : Type*} {g : ContextFreeGrammar T}
    {u v : List (Symbol T (Sum g.NT T))}
    (h : (v62TerminalIsolationGrammar g).Produces u v) :
    u.map (v62ProjectIsolatedSymbol g) =
        v.map (v62ProjectIsolatedSymbol g) ∨
      g.Produces
        (u.map (v62ProjectIsolatedSymbol g))
        (v.map (v62ProjectIsolatedSymbol g)) := by
  classical
  rcases h with ⟨r, hr, hrew⟩
  change r ∈ g.rules.image v62IsolateRule ∪
    (v62GrammarTerminals g).image v62TerminalHelperRule at hr
  rw [Finset.mem_union] at hr
  rcases hr with hOld | hHelper
  · rcases Finset.mem_image.mp hOld with ⟨q, hq, hqr⟩
    subst r
    right
    refine ⟨q, hq, ?_⟩
    rcases hrew.exists_parts with ⟨p, s, hu, hv⟩
    rw [ContextFreeRule.rewrites_iff]
    refine ⟨p.map (v62ProjectIsolatedSymbol g),
      s.map (v62ProjectIsolatedSymbol g), ?_, ?_⟩
    · rw [hu]
      simp [List.map_append, v62IsolateRule,
        v62ProjectIsolatedSymbol]
    · rw [hv]
      simp only [List.map_append, v62IsolateRule]
      rw [v62_project_isolated_output g q.output]
  · rcases Finset.mem_image.mp hHelper with ⟨a, ha, har⟩
    subst r
    left
    rcases hrew.exists_parts with ⟨p, s, hu, hv⟩
    rw [hu, hv]
    simp [List.map_append, v62TerminalHelperRule,
      v62ProjectIsolatedSymbol]

/-- Every terminal-isolation derivation projects to an old derivation. -/
theorem v62_project_terminal_isolation_derives
    {T : Type*} {g : ContextFreeGrammar T}
    {u v : List (Symbol T (Sum g.NT T))}
    (h : (v62TerminalIsolationGrammar g).Derives u v) :
    g.Derives
      (u.map (v62ProjectIsolatedSymbol g))
      (v.map (v62ProjectIsolatedSymbol g)) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ last ih =>
      rcases v62_project_terminal_isolation_produces last with heq | hstep
      · simpa [heq] using ih
      · exact ih.trans_produces hstep

/-- Terminal isolation cannot introduce a new generated terminal word. -/
theorem v62_terminal_isolation_language_subset
    {T : Type*} (g : ContextFreeGrammar T) :
    ∀ w : List T,
      w ∈ (v62TerminalIsolationGrammar g).language → w ∈ g.language := by
  intro w hw
  rw [ContextFreeGrammar.mem_language_iff] at hw ⊢
  have hp := v62_project_terminal_isolation_derives hw
  change g.Derives
    [Symbol.nonterminal g.initial]
    ((w.map (@Symbol.terminal T (Sum g.NT T))).map
      (v62ProjectIsolatedSymbol g)) at hp
  have hterm :
      (w.map (@Symbol.terminal T (Sum g.NT T))).map
          (v62ProjectIsolatedSymbol g) =
        w.map (@Symbol.terminal T g.NT) := by
    induction w with
    | nil => rfl
    | cons a w ih => simp [v62ProjectIsolatedSymbol, ih]
  rw [hterm] at hp
  exact hp

end FixedHCFG
end LeanCfgProject
