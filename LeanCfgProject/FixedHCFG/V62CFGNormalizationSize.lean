import LeanCfgProject.FixedHCFG.V62CFGNormalizationUnitReverse

namespace LeanCfgProject
namespace FixedHCFG

/-!
# Concrete finite-size envelope for executable v62 normalization

The manuscript writes `|G|` for a standard finite grammar encoding size.  For
the executable mathlib CFG representation it is convenient to use the
equivalent coarse measure

`1 + sum_{r in P} (|rhs(r)| + 1)`.

It charges one slot for the start symbol, one slot per production, and one slot
per RHS symbol.  The lemmas below connect this concrete measure to the active
nonterminal support, maximum RHS length, and the quadratic unit-closure rule
bound.
-/

/-- A concrete finite encoding-size measure for mathlib CFGs. -/
def V62CFGEncodingSize {T : Type*} (g : ContextFreeGrammar T) : Nat :=
  1 + ∑ r ∈ g.rules, (r.output.length + 1)

/-- The finite nonterminal set extracted from one RHS has at most its length. -/
theorem v62_rhs_nonterminal_card_le_length
    {T N : Type*} [DecidableEq N] (u : List (Symbol T N)) :
    (u.filterMap v62NonterminalOfSymbol).toFinset.card ≤ u.length := by
  classical
  induction u with
  | nil => simp
  | cons x xs ih =>
      cases x with
      | terminal a =>
          simpa [v62NonterminalOfSymbol] using
            ih.trans (Nat.le_succ xs.length)
      | nonterminal A =>
          calc
            ((Symbol.nonterminal A :: xs).filterMap
                v62NonterminalOfSymbol).toFinset.card
                ≤ (xs.filterMap v62NonterminalOfSymbol).toFinset.card + 1 := by
                  simpa [v62NonterminalOfSymbol] using
                    (Finset.card_insert_le A
                      (xs.filterMap v62NonterminalOfSymbol).toFinset)
            _ ≤ xs.length + 1 := Nat.add_le_add_right ih 1
            _ = (Symbol.nonterminal A :: xs).length := by simp [Nat.add_comm]

/-- One production mentions at most one plus its RHS length many nonterminals. -/
theorem v62_rule_nonterminal_card_le
    {T N : Type*} (r : ContextFreeRule T N) :
    (v62RuleNonterminals r).card ≤ r.output.length + 1 := by
  classical
  unfold v62RuleNonterminals
  exact (Finset.card_insert_le r.input
    (r.output.filterMap v62NonterminalOfSymbol).toFinset).trans
      (Nat.add_le_add_right
        (v62_rhs_nonterminal_card_le_length r.output) 1)

/-- The finite active nonterminal support is bounded by the concrete encoding size. -/
theorem v62_grammar_nonterminal_card_le_size
    {T : Type} (g : ContextFreeGrammar T) :
    (v62GrammarNonterminals g).card ≤ V62CFGEncodingSize g := by
  classical
  unfold v62GrammarNonterminals V62CFGEncodingSize
  calc
    (insert g.initial
      (g.rules.biUnion v62RuleNonterminals)).card
        ≤ (g.rules.biUnion v62RuleNonterminals).card + 1 :=
      Finset.card_insert_le _ _
    _ ≤ (∑ r ∈ g.rules, (v62RuleNonterminals r).card) + 1 := by
      exact Nat.add_le_add_right Finset.card_biUnion_le 1
    _ ≤ (∑ r ∈ g.rules, (r.output.length + 1)) + 1 := by
      apply Nat.add_le_add_right
      exact Finset.sum_le_sum fun r hr => v62_rule_nonterminal_card_le r
    _ = 1 + ∑ r ∈ g.rules, (r.output.length + 1) := by omega

/-- The number of productions is bounded by the concrete encoding size. -/
theorem v62_rule_card_le_size
    {T : Type} (g : ContextFreeGrammar T) :
    g.rules.card ≤ V62CFGEncodingSize g := by
  classical
  unfold V62CFGEncodingSize
  calc
    g.rules.card = ∑ _r ∈ g.rules, 1 := by simp
    _ ≤ ∑ r ∈ g.rules, (r.output.length + 1) := by
      apply Finset.sum_le_sum
      intro r hr
      omega
    _ ≤ 1 + ∑ r ∈ g.rules, (r.output.length + 1) := by omega

/-- Every installed RHS length is bounded by the concrete encoding size. -/
theorem v62_rhs_length_le_size
    {T : Type} (g : ContextFreeGrammar T)
    {r : ContextFreeRule T g.NT} (hr : r ∈ g.rules) :
    r.output.length ≤ V62CFGEncodingSize g := by
  classical
  unfold V62CFGEncodingSize
  have hsingle :
      r.output.length + 1 ≤
        ∑ q ∈ g.rules, (q.output.length + 1) :=
    Finset.single_le_sum
      (fun q hq => Nat.zero_le (q.output.length + 1)) hr
  omega

/-- Unit elimination has a quadratic rule-count bound in the concrete input size. -/
theorem v62_unit_elimination_rule_card_le_size_sq
    {T : Type} (g : ContextFreeGrammar T) :
    (v62UnitEliminationGrammar g).rules.card ≤
      V62CFGEncodingSize g * V62CFGEncodingSize g := by
  exact (v62_unit_elimination_rule_card_le g).trans
    (Nat.mul_le_mul
      (v62_grammar_nonterminal_card_le_size g)
      (v62_rule_card_le_size g))

/--
The executable fresh-start / terminal-isolation / binarization thickness bound
can be instantiated directly with the concrete grammar encoding size.
-/
theorem v62_first_three_stages_thickness_by_size
    {T : Type} {g : ContextFreeGrammar T} {tau : Nat}
    (hTau : V62CFGThicknessBound g tau)
    (hAll : V62CFGAllProductive g) :
    V62CFGThicknessBound
      (v62BinarizedGrammar
        (v62TerminalIsolationGrammar (v62FreshStartGrammar g)))
      (V62CFGBinarizationThicknessEnvelope
        (tau + 1) (max (V62CFGEncodingSize g) 1)) := by
  exact v62_first_three_normalization_stages_thickness
    hTau hAll (fun r hr => v62_rhs_length_le_size g hr)

end FixedHCFG
end LeanCfgProject
