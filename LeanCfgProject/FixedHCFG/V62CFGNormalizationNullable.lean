import LeanCfgProject.FixedHCFG.V62CFGNormalizationReducedness

namespace LeanCfgProject
namespace FixedHCFG

/-!
# Executable non-start lambda elimination for the v62 normalization

This is the next construction in Appendix `app:thick-ssbnf` after terminal
isolation and binarization.  Because the input at this stage is binary, a rule
`A -> B C` produces only the original binary rule and, when appropriate, the
two unit variants `A -> B` and `A -> C`.  Empty old productions are removed;
the sole possible empty production is reintroduced at the start symbol exactly
when the old start is nullable.

This file establishes the executable rule transformation, the absence of
non-start empty productions, and the constant-factor rule-count bound.  The
semantic preservation of nonempty terminal languages is layered separately.
-/

/-- A nonterminal is nullable when it derives the empty terminal word. -/
def V62CFGNullable {T : Type*} (g : ContextFreeGrammar T) (A : g.NT) : Prop :=
  V62CFGDerivesWordFrom g A []

/-- The distinguished start epsilon rule. -/
def v62StartEpsilonRule {T : Type*} (g : ContextFreeGrammar T) :
    ContextFreeRule T g.NT :=
  { input := g.initial, output := [] }

/--
Variants contributed by one old production.  Empty productions are removed.
A binary all-nonterminal production contributes at most the two manuscript
unit variants obtained by deleting one nullable child.
-/
noncomputable def v62NullableVariants {T : Type*}
    (g : ContextFreeGrammar T) (r : ContextFreeRule T g.NT) :
    List (ContextFreeRule T g.NT) := by
  classical
  if h0 : r.output = [] then
    exact []
  else
    match r.output with
    | [Symbol.nonterminal B, Symbol.nonterminal C] =>
        exact [r] ++
          (if V62CFGNullable g B then
            [{ input := r.input, output := [Symbol.nonterminal C] }]
           else []) ++
          (if V62CFGNullable g C then
            [{ input := r.input, output := [Symbol.nonterminal B] }]
           else [])
    | _ => exact [r]

/-- The executable grammar after eliminating all non-start lambda rules. -/
@[reducible] noncomputable def v62NullableEliminationGrammar {T : Type}
    (g : ContextFreeGrammar T) : ContextFreeGrammar T := by
  classical
  exact
    { NT := g.NT
      initial := g.initial
      rules :=
        g.rules.biUnion (fun r => (v62NullableVariants g r).toFinset) ∪
          (if V62CFGNullable g g.initial
            then {v62StartEpsilonRule g}
            else ∅) }

/-- One binary old rule contributes at most three transformed rules. -/
theorem v62_nullable_variants_length_le_three
    {T : Type*} (g : ContextFreeGrammar T)
    (r : ContextFreeRule T g.NT) :
    (v62NullableVariants g r).length ≤ 3 := by
  classical
  unfold v62NullableVariants
  split
  · simp
  · rename_i h0
    cases h : r.output with
    | nil => exact (h0 h).elim
    | cons x xs =>
        cases xs with
        | nil => simp [h]
        | cons y ys =>
            cases ys with
            | nil =>
                cases x with
                | terminal a => simp [h]
                | nonterminal B =>
                    cases y with
                    | terminal a => simp [h]
                    | nonterminal C =>
                        by_cases hB : V62CFGNullable g B <;>
                        by_cases hC : V62CFGNullable g C <;>
                        simp [h, hB, hC]
            | cons z zs => simp [h]

/-- Every per-rule nullable-elimination variant has a nonempty RHS. -/
theorem v62_nullable_variant_output_ne_nil
    {T : Type*} {g : ContextFreeGrammar T}
    {r q : ContextFreeRule T g.NT}
    (hq : q ∈ v62NullableVariants g r) :
    q.output ≠ [] := by
  classical
  unfold v62NullableVariants at hq
  split at hq
  · simp at hq
  · rename_i h0
    cases h : r.output with
    | nil => exact (h0 h).elim
    | cons x xs =>
        cases xs with
        | nil =>
            simp [h] at hq
            subst q
            exact h0
        | cons y ys =>
            cases ys with
            | nil =>
                cases x with
                | terminal a =>
                    simp [h] at hq
                    subst q
                    simp [h]
                | nonterminal B =>
                    cases y with
                    | terminal a =>
                        simp [h] at hq
                        subst q
                        simp [h]
                    | nonterminal C =>
                        by_cases hB : V62CFGNullable g B <;>
                        by_cases hC : V62CFGNullable g C <;>
                        simp [h, hB, hC] at hq
                        all_goals rcases hq with rfl | rfl | rfl <;> simp [h]
            | cons z zs =>
                simp [h] at hq
                subst q
                simp [h]

/-- Normal-form invariant: only the start symbol may own an empty production. -/
def V62CFGNoNonStartEpsilon {T : Type*}
    (g : ContextFreeGrammar T) : Prop :=
  ∀ r ∈ g.rules, r.output = [] → r.input = g.initial

/-- The executable nullable-elimination grammar has no non-start epsilon rule. -/
theorem v62_nullable_elimination_no_nonstart_epsilon
    {T : Type} (g : ContextFreeGrammar T) :
    V62CFGNoNonStartEpsilon (v62NullableEliminationGrammar g) := by
  classical
  intro q hq hout
  change q ∈
      g.rules.biUnion (fun r => (v62NullableVariants g r).toFinset) ∪
        (if V62CFGNullable g g.initial
          then {v62StartEpsilonRule g}
          else ∅) at hq
  rw [Finset.mem_union] at hq
  rcases hq with hOld | hStart
  · rcases Finset.mem_biUnion.mp hOld with ⟨r, hr, hqr⟩
    have hlist : q ∈ v62NullableVariants g r := by
      simpa only [List.mem_toFinset] using hqr
    exact (v62_nullable_variant_output_ne_nil hlist hout).elim
  · by_cases hNull : V62CFGNullable g g.initial
    · simp [hNull, v62StartEpsilonRule] at hStart
      simpa [hStart, v62StartEpsilonRule]
    · simp [hNull] at hStart

/-- Constant-factor finite rule-count bound for binary nullable elimination. -/
theorem v62_nullable_elimination_rule_card_le
    {T : Type} (g : ContextFreeGrammar T) :
    (v62NullableEliminationGrammar g).rules.card ≤
      3 * g.rules.card + 1 := by
  classical
  change
    (g.rules.biUnion (fun r => (v62NullableVariants g r).toFinset) ∪
      (if V62CFGNullable g g.initial
        then {v62StartEpsilonRule g}
        else ∅)).card ≤
      3 * g.rules.card + 1
  calc
    _ ≤
        (g.rules.biUnion
          (fun r => (v62NullableVariants g r).toFinset)).card + 1 := by
      refine (Finset.card_union_le _ _).trans ?_
      apply Nat.add_le_add_left
      by_cases hNull : V62CFGNullable g g.initial <;> simp [hNull]
    _ ≤
        (∑ r ∈ g.rules, (v62NullableVariants g r).toFinset.card) + 1 := by
      apply Nat.add_le_add_right
      exact Finset.card_biUnion_le
    _ ≤ (∑ _r ∈ g.rules, 3) + 1 := by
      apply Nat.add_le_add_right
      exact Finset.sum_le_sum fun r hr =>
        (List.toFinset_card_le _).trans
          (v62_nullable_variants_length_le_three g r)
    _ = 3 * g.rules.card + 1 := by
      simp [Nat.mul_comm]

end FixedHCFG
end LeanCfgProject
