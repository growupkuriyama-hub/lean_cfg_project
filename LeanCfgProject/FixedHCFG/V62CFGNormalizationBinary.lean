import LeanCfgProject.FixedHCFG.V62CFGNormalizationTerminalThickness

namespace LeanCfgProject
namespace FixedHCFG

/-!
# Executable long-rule binarization for the v62 normalization

After terminal isolation, the next manuscript transformation replaces every
right-hand side of length greater than two by a chain of binary productions.
This file implements that transformation for mathlib CFGs.

A helper nonterminal is named by the old rule together with a natural-number
position.  Thus helpers belonging to distinct old productions cannot collide.
The first rule consumes the first RHS symbol and enters helper `0`; each helper
then consumes one further symbol until the final helper emits the last two
symbols.  Rules of length at most two are only lifted.

This first layer proves the structural endpoint needed by the later SSBNF
pipeline: every transformed RHS has length at most two.  Semantic simulation,
size accounting, and thickness transfer are layered separately.
-/

/-- Lift an old symbol into the old-nonterminal summand of the binary grammar. -/
def v62BinarizeLiftSymbol {T N : Type*} :
    Symbol T N → Symbol T (Sum N (ContextFreeRule T N × Nat))
  | .terminal a => .terminal a
  | .nonterminal A => .nonterminal (Sum.inl A)

/-- The helper symbol attached to rule `r` at chain position `i`. -/
def v62BinarizeHelperSymbol {T N : Type*}
    (r : ContextFreeRule T N) (i : Nat) :
    Symbol T (Sum N (ContextFreeRule T N × Nat)) :=
  .nonterminal (Sum.inr (r, i))

/--
Binary helper rules for a remaining suffix.  A list of two symbols is emitted
by one final binary rule; a longer list emits its head and passes the rest to
the next helper.
-/
def v62BinarizeTailRules {T N : Type*}
    (r : ContextFreeRule T N) :
    Nat → List (Symbol T N) →
      List (ContextFreeRule T (Sum N (ContextFreeRule T N × Nat)))
  | _, [] => []
  | _, [_] => []
  | i, x :: y :: [] =>
      [{ input := Sum.inr (r, i)
         output := [v62BinarizeLiftSymbol x, v62BinarizeLiftSymbol y] }]
  | i, x :: y :: z :: xs =>
      { input := Sum.inr (r, i)
        output := [v62BinarizeLiftSymbol x,
          v62BinarizeHelperSymbol r (i + 1)] } ::
        v62BinarizeTailRules r (i + 1) (y :: z :: xs)

/-- Rules replacing one old production. -/
def v62BinarizeRulesFor {T N : Type*}
    (r : ContextFreeRule T N) :
    List (ContextFreeRule T (Sum N (ContextFreeRule T N × Nat))) :=
  match r.output with
  | x :: y :: z :: xs =>
      { input := Sum.inl r.input
        output := [v62BinarizeLiftSymbol x,
          v62BinarizeHelperSymbol r 0] } ::
        v62BinarizeTailRules r 0 (y :: z :: xs)
  | _ =>
      [{ input := Sum.inl r.input
         output := r.output.map v62BinarizeLiftSymbol }]

/-- The executable grammar obtained by binarizing every old production. -/
@[reducible] noncomputable def v62BinarizedGrammar {T : Type}
    (g : ContextFreeGrammar T) : ContextFreeGrammar T := by
  classical
  exact
    { NT := Sum g.NT (ContextFreeRule T g.NT × Nat)
      initial := Sum.inl g.initial
      rules := g.rules.biUnion
        (fun r => (v62BinarizeRulesFor r).toFinset) }

/-- Every helper rule produced by the chain construction is binary. -/
theorem v62_binarize_tail_rule_length_eq_two
    {T N : Type*} {r : ContextFreeRule T N} {i : Nat}
    {u : List (Symbol T N)} {q : ContextFreeRule T
      (Sum N (ContextFreeRule T N × Nat))}
    (hq : q ∈ v62BinarizeTailRules r i u) :
    q.output.length = 2 := by
  induction u generalizing i with
  | nil =>
      simp [v62BinarizeTailRules] at hq
  | cons x xs ih =>
      cases xs with
      | nil =>
          simp [v62BinarizeTailRules] at hq
      | cons y ys =>
          cases ys with
          | nil =>
              simp [v62BinarizeTailRules] at hq
              subst q
              rfl
          | cons z zs =>
              simp only [v62BinarizeTailRules, List.mem_cons] at hq
              rcases hq with hq | hq
              · subst q
                rfl
              · exact ih (i := i + 1) hq

/-- Every rule replacing one old production has RHS length at most two. -/
theorem v62_binarize_rule_for_length_le_two
    {T N : Type*} {r : ContextFreeRule T N}
    {q : ContextFreeRule T (Sum N (ContextFreeRule T N × Nat))}
    (hq : q ∈ v62BinarizeRulesFor r) :
    q.output.length ≤ 2 := by
  cases h0 : r.output with
  | nil =>
      simp [v62BinarizeRulesFor, h0] at hq
      subst q
      simp
  | cons x xs =>
      cases xs with
      | nil =>
          simp [v62BinarizeRulesFor, h0] at hq
          subst q
          simp
      | cons y ys =>
          cases ys with
          | nil =>
              simp [v62BinarizeRulesFor, h0] at hq
              subst q
              simp
          | cons z zs =>
              simp only [v62BinarizeRulesFor, h0, List.mem_cons] at hq
              rcases hq with hq | hq
              · subst q
                simp
              · exact Nat.le_of_eq
                  (v62_binarize_tail_rule_length_eq_two hq)

/-- Binary-form invariant: no production has more than two RHS symbols. -/
def V62CFGRHSAtMostTwo {T : Type*} (g : ContextFreeGrammar T) : Prop :=
  ∀ r ∈ g.rules, r.output.length ≤ 2

/-- The executable binarization satisfies the binary-form invariant. -/
theorem v62_binarized_grammar_rhs_at_most_two
    {T : Type} (g : ContextFreeGrammar T) :
    V62CFGRHSAtMostTwo (v62BinarizedGrammar g) := by
  classical
  unfold V62CFGRHSAtMostTwo
  intro q hq
  change q ∈ g.rules.biUnion
    (fun r => (v62BinarizeRulesFor r).toFinset) at hq
  rcases Finset.mem_biUnion.mp hq with ⟨r, hr, hqr⟩
  have hList : q ∈ v62BinarizeRulesFor r := by
    simpa only [List.mem_toFinset] using hqr
  exact v62_binarize_rule_for_length_le_two hList

end FixedHCFG
end LeanCfgProject
