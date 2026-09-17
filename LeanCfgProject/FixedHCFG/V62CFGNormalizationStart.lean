import Mathlib.Computability.ContextFreeGrammar
import Mathlib.Tactic

namespace LeanCfgProject
namespace FixedHCFG

/-!
# First executable stage of the v62 CFG-to-SSBNF normalization

The earlier `V62ThicknessNormalization` file formalizes the polynomial
arithmetic used after a normalization has been supplied.  This file starts the
missing grammar transformation itself, using mathlib's concrete
`ContextFreeGrammar` rewrite semantics.

The first manuscript operation is start-symbol separation.  We add a genuinely
fresh start nonterminal, lift every old rule to the old-nonterminal summand,
and add the single rule `S0 -> S`.  The lemmas below verify the forward
simulation of every old derivation, the start-separation invariant, and the
linear rule-count bound.  Reverse simulation and the following terminal
isolation / binarization stages are deliberately left for subsequent files.
-/

/-- A word derivation from an arbitrary nonterminal of a mathlib CFG. -/
def V62CFGDerivesWordFrom {T : Type*} (g : ContextFreeGrammar T)
    (A : g.NT) (w : List T) : Prop :=
  g.Derives [Symbol.nonterminal A] (w.map Symbol.terminal)

/-- A nonterminal is productive when it derives at least one terminal word. -/
def V62CFGProductive {T : Type*} (g : ContextFreeGrammar T) (A : g.NT) : Prop :=
  ∃ w : List T, V62CFGDerivesWordFrom g A w

/--
Upper-bound form of the manuscript thickness parameter: every productive
nonterminal has some terminal yield of length at most `tau`.
-/
def V62CFGThicknessBound {T : Type*} (g : ContextFreeGrammar T)
    (tau : Nat) : Prop :=
  ∀ A : g.NT, V62CFGProductive g A →
    ∃ w : List T, V62CFGDerivesWordFrom g A w ∧ w.length ≤ tau

/-- Lift an old symbol into the `some` part of the fresh-start grammar. -/
def v62LiftCFGSymbol {T N : Type*} : Symbol T N → Symbol T (Option N)
  | .terminal a => .terminal a
  | .nonterminal A => .nonterminal (some A)

/-- Lifting a terminal word changes only the nonterminal type parameter. -/
@[simp] theorem v62_lift_terminal_word
    {T N : Type*} (w : List T) :
    (w.map (@Symbol.terminal T N)).map v62LiftCFGSymbol =
      w.map (@Symbol.terminal T (Option N)) := by
  induction w with
  | nil => rfl
  | cons a w ih =>
      simp only [List.map_cons, v62LiftCFGSymbol]
      rw [ih]

/-- Lift one old CFG rule into the fresh-start grammar. -/
def v62LiftCFGRule {T N : Type*}
    (r : ContextFreeRule T N) : ContextFreeRule T (Option N) :=
  { input := some r.input
    output := r.output.map v62LiftCFGSymbol }

/-- The one new rule `S0 -> S`. -/
def v62FreshStartRule {T : Type*} (g : ContextFreeGrammar T) :
    ContextFreeRule T (Option g.NT) :=
  { input := none
    output := [Symbol.nonterminal (some g.initial)] }

/--
The first normalization stage: all old nonterminals become `some A`, while
`none` is a fresh start symbol occurring only on the left of the added rule.
The definition is reducible so its nonterminal type is definitionally visible
as `Option g.NT` in the simulation lemmas below.
-/
@[reducible] noncomputable def v62FreshStartGrammar {T : Type*}
    (g : ContextFreeGrammar T) : ContextFreeGrammar T := by
  classical
  exact
    { NT := Option g.NT
      initial := none
      rules := g.rules.image v62LiftCFGRule ∪ {v62FreshStartRule g} }

/-- The fresh start symbol never occurs in a lifted sentential form. -/
theorem v62_fresh_symbol_not_mem_lifted
    {T N : Type*} (u : List (Symbol T N)) :
    Symbol.nonterminal (none : Option N) ∉ u.map v62LiftCFGSymbol := by
  induction u with
  | nil => simp
  | cons x xs ih =>
      cases x <;> simp [v62LiftCFGSymbol, ih]

/-- Start-separated means that the initial nonterminal never appears on a RHS. -/
def V62CFGStartSeparated {T : Type*} (g : ContextFreeGrammar T) : Prop :=
  ∀ r ∈ g.rules, Symbol.nonterminal g.initial ∉ r.output

/-- The fresh-start construction is start-separated. -/
theorem v62_fresh_start_separated
    {T : Type*} (g : ContextFreeGrammar T) :
    V62CFGStartSeparated (v62FreshStartGrammar g) := by
  classical
  unfold V62CFGStartSeparated
  change ∀ r : ContextFreeRule T (Option g.NT),
    r ∈ g.rules.image v62LiftCFGRule ∪ {v62FreshStartRule g} →
      Symbol.nonterminal (none : Option g.NT) ∉ r.output
  intro r hr
  rw [Finset.mem_union] at hr
  rcases hr with hOld | hFresh
  · rcases Finset.mem_image.mp hOld with ⟨q, hq, hqr⟩
    subst r
    simpa [v62LiftCFGRule] using
      (v62_fresh_symbol_not_mem_lifted q.output)
  · have hrEq : r = v62FreshStartRule g := by simpa using hFresh
    subst r
    simp [v62FreshStartRule]

/-- Adding the fresh start rule increases the number of rules by at most one. -/
theorem v62_fresh_start_rule_card_le
    {T : Type*} (g : ContextFreeGrammar T) :
    (v62FreshStartGrammar g).rules.card ≤ g.rules.card + 1 := by
  classical
  change (g.rules.image v62LiftCFGRule ∪ {v62FreshStartRule g}).card ≤
    g.rules.card + 1
  exact (Finset.card_union_le _ _).trans
    (Nat.add_le_add Finset.card_image_le (by simp))

/-- One application of an old rule is simulated by its lifted rule. -/
theorem v62_lift_rule_rewrites
    {T N : Type*} {r : ContextFreeRule T N}
    {u v : List (Symbol T N)}
    (h : r.Rewrites u v) :
    (v62LiftCFGRule r).Rewrites
      (u.map v62LiftCFGSymbol) (v.map v62LiftCFGSymbol) := by
  rcases h.exists_parts with ⟨p, q, rfl, rfl⟩
  simpa [v62LiftCFGRule, v62LiftCFGSymbol, List.map_append] using
    (ContextFreeRule.rewrites_of_exists_parts
      (v62LiftCFGRule r)
      (p.map v62LiftCFGSymbol) (q.map v62LiftCFGSymbol))

/-- One old grammar step is simulated by the fresh-start grammar. -/
theorem v62_lift_produces
    {T : Type*} {g : ContextFreeGrammar T}
    {u v : List (Symbol T g.NT)}
    (h : g.Produces u v) :
    (v62FreshStartGrammar g).Produces
      (u.map v62LiftCFGSymbol) (v.map v62LiftCFGSymbol) := by
  classical
  rcases h with ⟨r, hr, hrew⟩
  refine ⟨v62LiftCFGRule r, ?_, v62_lift_rule_rewrites hrew⟩
  change v62LiftCFGRule r ∈
    g.rules.image v62LiftCFGRule ∪ {v62FreshStartRule g}
  exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨r, hr, rfl⟩)

/-- Every old multi-step derivation is simulated after lifting symbols. -/
theorem v62_lift_derives
    {T : Type*} {g : ContextFreeGrammar T}
    {u v : List (Symbol T g.NT)}
    (h : g.Derives u v) :
    (v62FreshStartGrammar g).Derives
      (u.map v62LiftCFGSymbol) (v.map v62LiftCFGSymbol) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ last ih =>
      exact ih.trans_produces (v62_lift_produces last)

/-- The new start symbol performs its intended first step. -/
theorem v62_fresh_start_produces
    {T : Type*} (g : ContextFreeGrammar T) :
    (v62FreshStartGrammar g).Produces
      [Symbol.nonterminal (none : Option g.NT)]
      [Symbol.nonterminal (some g.initial)] := by
  classical
  refine ⟨v62FreshStartRule g, ?_, ?_⟩
  · change v62FreshStartRule g ∈
      g.rules.image v62LiftCFGRule ∪ {v62FreshStartRule g}
    exact Finset.mem_union_right _ (by simp)
  · change (v62FreshStartRule g).Rewrites
      [Symbol.nonterminal (none : Option g.NT)]
      [Symbol.nonterminal (some g.initial)]
    exact ContextFreeRule.Rewrites.input_output

/-- Every terminal word derivable from an old nonterminal remains derivable. -/
theorem v62_fresh_start_preserves_old_word_derivation
    {T : Type*} {g : ContextFreeGrammar T}
    {A : g.NT} {w : List T}
    (h : V62CFGDerivesWordFrom g A w) :
    V62CFGDerivesWordFrom (v62FreshStartGrammar g) (some A) w := by
  unfold V62CFGDerivesWordFrom at h ⊢
  have hLift := v62_lift_derives h
  change (v62FreshStartGrammar g).Derives
    [Symbol.nonterminal (some A)]
    (w.map (@Symbol.terminal T (Option g.NT)))
  rw [← v62_lift_terminal_word (N := g.NT) w]
  simpa only [List.map_cons, List.map_nil, v62LiftCFGSymbol] using hLift

/-- Hence every old language word is generated by the fresh-start grammar. -/
theorem v62_language_subset_fresh_start
    {T : Type*} (g : ContextFreeGrammar T) :
    ∀ w : List T, w ∈ g.language → w ∈ (v62FreshStartGrammar g).language := by
  intro w hw
  rw [ContextFreeGrammar.mem_language_iff] at hw ⊢
  have hLift := v62_lift_derives hw
  have hRest :
      (v62FreshStartGrammar g).Derives
        [Symbol.nonterminal (some g.initial)]
        (w.map (@Symbol.terminal T (Option g.NT))) := by
    rw [← v62_lift_terminal_word (N := g.NT) w]
    simpa only [List.map_cons, List.map_nil, v62LiftCFGSymbol] using hLift
  have hFirst :
      (v62FreshStartGrammar g).Derives
        [Symbol.nonterminal (none : Option g.NT)]
        [Symbol.nonterminal (some g.initial)] :=
    (v62_fresh_start_produces g).single
  have hAll := hFirst.trans hRest
  change (v62FreshStartGrammar g).Derives
    [Symbol.nonterminal (none : Option g.NT)]
    (w.map (@Symbol.terminal T (Option g.NT)))
  exact hAll

end FixedHCFG
end LeanCfgProject
