import LeanCfgProject.FixedHCFG.V62CFGNormalizationStart

namespace LeanCfgProject
namespace FixedHCFG

/-!
# Reverse simulation for the v62 fresh-start normalization

The fresh nonterminal `none` is projected back to the old start nonterminal,
while `some A` is projected to `A`.  Under this projection the added rule
`S0 -> S` becomes an identity step and every lifted old rule becomes the
corresponding old rule.  This gives the reverse language inclusion, exact
language preservation, and preservation of the thickness upper bound.
-/

/-- Project the fresh start nonterminal back to the old start symbol. -/
def v62ProjectFreshNT {T : Type*} (g : ContextFreeGrammar T) :
    Option g.NT → g.NT
  | none => g.initial
  | some A => A

/-- Project symbols of the fresh-start grammar back to old symbols. -/
def v62ProjectFreshSymbol {T : Type*} (g : ContextFreeGrammar T) :
    Symbol T (Option g.NT) → Symbol T g.NT
  | .terminal a => .terminal a
  | .nonterminal A => .nonterminal (v62ProjectFreshNT g A)

@[simp] theorem v62_project_lift_symbol
    {T : Type*} (g : ContextFreeGrammar T) (x : Symbol T g.NT) :
    v62ProjectFreshSymbol g (v62LiftCFGSymbol x) = x := by
  cases x <;> rfl

@[simp] theorem v62_project_lift_word
    {T : Type*} (g : ContextFreeGrammar T) (u : List (Symbol T g.NT)) :
    (u.map v62LiftCFGSymbol).map (v62ProjectFreshSymbol g) = u := by
  induction u with
  | nil => rfl
  | cons x xs ih => simp [ih]

@[simp] theorem v62_project_terminal_word
    {T : Type*} (g : ContextFreeGrammar T) (w : List T) :
    (w.map (@Symbol.terminal T (Option g.NT))).map
        (v62ProjectFreshSymbol g) =
      w.map (@Symbol.terminal T g.NT) := by
  induction w with
  | nil => rfl
  | cons a w ih => simp [v62ProjectFreshSymbol, ih]

/--
A single fresh-start grammar step projects either to an identity or to one old
grammar step.  The identity case is exactly the added rule `S0 -> S`.
-/
theorem v62_project_fresh_produces
    {T : Type*} {g : ContextFreeGrammar T}
    {u v : List (Symbol T (Option g.NT))}
    (h : (v62FreshStartGrammar g).Produces u v) :
    u.map (v62ProjectFreshSymbol g) =
        v.map (v62ProjectFreshSymbol g) ∨
      g.Produces
        (u.map (v62ProjectFreshSymbol g))
        (v.map (v62ProjectFreshSymbol g)) := by
  classical
  rcases h with ⟨r, hr, hrew⟩
  change r ∈ g.rules.image v62LiftCFGRule ∪ {v62FreshStartRule g} at hr
  rw [Finset.mem_union] at hr
  rcases hr with hOld | hFresh
  · rcases Finset.mem_image.mp hOld with ⟨q, hq, hqr⟩
    subst r
    right
    refine ⟨q, hq, ?_⟩
    rcases hrew.exists_parts with ⟨p, s, hu, hv⟩
    rw [ContextFreeRule.rewrites_iff]
    refine ⟨p.map (v62ProjectFreshSymbol g),
      s.map (v62ProjectFreshSymbol g), ?_, ?_⟩
    · rw [hu]
      simp [List.map_append, v62LiftCFGRule,
        v62ProjectFreshSymbol, v62ProjectFreshNT]
    · rw [hv]
      simp only [List.map_append, v62LiftCFGRule]
      rw [v62_project_lift_word g q.output]
  · have hrEq : r = v62FreshStartRule g := by simpa using hFresh
    subst r
    left
    rcases hrew.exists_parts with ⟨p, s, hu, hv⟩
    rw [hu, hv]
    simp [List.map_append, v62FreshStartRule,
      v62ProjectFreshSymbol, v62ProjectFreshNT]

/-- Every derivation of the fresh-start grammar projects to an old derivation. -/
theorem v62_project_fresh_derives
    {T : Type*} {g : ContextFreeGrammar T}
    {u v : List (Symbol T (Option g.NT))}
    (h : (v62FreshStartGrammar g).Derives u v) :
    g.Derives
      (u.map (v62ProjectFreshSymbol g))
      (v.map (v62ProjectFreshSymbol g)) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ last ih =>
      rcases v62_project_fresh_produces last with heq | hstep
      · simpa [heq] using ih
      · exact ih.trans_produces hstep

/-- Productivity in the fresh-start grammar projects to old productivity. -/
theorem v62_fresh_productive_projects
    {T : Type*} {g : ContextFreeGrammar T}
    (A : Option g.NT)
    (h : V62CFGProductive (v62FreshStartGrammar g) A) :
    V62CFGProductive g (v62ProjectFreshNT g A) := by
  rcases h with ⟨w, hw⟩
  refine ⟨w, ?_⟩
  unfold V62CFGDerivesWordFrom at hw ⊢
  have hp := v62_project_fresh_derives hw
  rw [v62_project_terminal_word g w] at hp
  simpa only [List.map_cons, List.map_nil,
    v62ProjectFreshSymbol, v62ProjectFreshNT] using hp

/-- No terminal word is introduced by fresh-start separation. -/
theorem v62_fresh_start_language_subset
    {T : Type*} (g : ContextFreeGrammar T) :
    ∀ w : List T, w ∈ (v62FreshStartGrammar g).language → w ∈ g.language := by
  intro w hw
  rw [ContextFreeGrammar.mem_language_iff] at hw ⊢
  have hp := v62_project_fresh_derives hw
  rw [v62_project_terminal_word g w] at hp
  simpa only [List.map_cons, List.map_nil,
    v62ProjectFreshSymbol, v62ProjectFreshNT] using hp

/-- Fresh-start separation preserves the generated language exactly. -/
theorem v62_fresh_start_language_eq
    {T : Type*} (g : ContextFreeGrammar T) :
    (v62FreshStartGrammar g).language = g.language := by
  apply Set.ext
  intro w
  constructor
  · exact v62_fresh_start_language_subset g w
  · exact v62_language_subset_fresh_start g w

/--
Fresh-start separation does not increase the thickness upper bound: an old
short witness works for `some A`, and for `none` it is preceded only by the new
start rule.
-/
theorem v62_fresh_start_preserves_thickness_bound
    {T : Type*} {g : ContextFreeGrammar T} {tau : Nat}
    (hTau : V62CFGThicknessBound g tau) :
    V62CFGThicknessBound (v62FreshStartGrammar g) tau := by
  intro A hProd
  have hOldProd := v62_fresh_productive_projects (g := g) A hProd
  rcases hTau (v62ProjectFreshNT g A) hOldProd with ⟨w, hw, hlen⟩
  refine ⟨w, ?_, hlen⟩
  cases A with
  | none =>
      have hwStart : V62CFGDerivesWordFrom g g.initial w := by
        simpa [v62ProjectFreshNT] using hw
      have hwSome :
          V62CFGDerivesWordFrom (v62FreshStartGrammar g) (some g.initial) w :=
        v62_fresh_start_preserves_old_word_derivation hwStart
      unfold V62CFGDerivesWordFrom at hwSome ⊢
      exact (v62_fresh_start_produces g).single.trans hwSome
  | some B =>
      have hwB : V62CFGDerivesWordFrom g B w := by
        simpa [v62ProjectFreshNT] using hw
      exact v62_fresh_start_preserves_old_word_derivation hwB

end FixedHCFG
end LeanCfgProject
