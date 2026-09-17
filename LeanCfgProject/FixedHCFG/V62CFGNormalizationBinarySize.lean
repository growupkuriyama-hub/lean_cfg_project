import LeanCfgProject.FixedHCFG.V62CFGNormalizationBinaryForward

namespace LeanCfgProject
namespace FixedHCFG

/-!
# Rule-count accounting for executable v62 binarization

The appendix only needs a linear-size envelope for the binarization stage.  A
long rule creates one primary binary production and one helper production for
each remaining chain position; short rules create one lifted production.
Accordingly the number of generated productions is bounded by the total old
RHS-symbol count plus one slot per old rule.

The helper *type* used by the executable grammar is intentionally larger than
the finite set of helpers that occur in rules.  This keeps the construction
simple; later trimming removes unused nonterminals.  The bound here is on the
actual finite rule set, which is the quantity used by the normalization-size
argument.
-/

/-- A helper chain creates no more rules than symbols in its represented suffix. -/
theorem v62_binarize_tail_rules_length_le
    {T N : Type*} (r : ContextFreeRule T N) (i : Nat)
    (u : List (Symbol T N)) :
    (v62BinarizeTailRules r i u).length ≤ u.length := by
  induction u generalizing i with
  | nil => simp [v62BinarizeTailRules]
  | cons x xs ih =>
      cases xs with
      | nil => simp [v62BinarizeTailRules]
      | cons y ys =>
          cases ys with
          | nil => simp [v62BinarizeTailRules]
          | cons z zs =>
              have hrec := ih (i := i + 1)
              simp only [v62BinarizeTailRules, List.length_cons]
              omega

/-- One old production creates at most `|RHS|+1` binary-stage productions. -/
theorem v62_binarize_rules_for_length_le
    {T N : Type*} (r : ContextFreeRule T N) :
    (v62BinarizeRulesFor r).length ≤ r.output.length + 1 := by
  cases h0 : r.output with
  | nil => simp [v62BinarizeRulesFor, h0]
  | cons x xs =>
      cases xs with
      | nil => simp [v62BinarizeRulesFor, h0]
      | cons y ys =>
          cases ys with
          | nil => simp [v62BinarizeRulesFor, h0]
          | cons z zs =>
              have htail :=
                v62_binarize_tail_rules_length_le r 0 (y :: z :: zs)
              simp only [v62BinarizeRulesFor, h0, List.length_cons]
              omega

/-- Total old RHS-symbol count plus one rule slot per old production. -/
noncomputable def V62CFGBinarizationRuleEnvelope {T : Type*}
    (g : ContextFreeGrammar T) : Nat :=
  ∑ r ∈ g.rules, (r.output.length + 1)

/-- The actual finite binarized rule set is bounded by the linear envelope. -/
theorem v62_binarized_rule_card_le_envelope
    {T : Type} (g : ContextFreeGrammar T) :
    (v62BinarizedGrammar g).rules.card ≤
      V62CFGBinarizationRuleEnvelope g := by
  classical
  change (g.rules.biUnion
      (fun r => (v62BinarizeRulesFor r).toFinset)).card ≤
    ∑ r ∈ g.rules, (r.output.length + 1)
  calc
    (g.rules.biUnion
        (fun r => (v62BinarizeRulesFor r).toFinset)).card
        ≤ ∑ r ∈ g.rules, (v62BinarizeRulesFor r).toFinset.card :=
      Finset.card_biUnion_le
    _ ≤ ∑ r ∈ g.rules, (v62BinarizeRulesFor r).length := by
      exact Finset.sum_le_sum fun r hr => List.toFinset_card_le _
    _ ≤ ∑ r ∈ g.rules, (r.output.length + 1) := by
      exact Finset.sum_le_sum fun r hr =>
        v62_binarize_rules_for_length_le r

end FixedHCFG
end LeanCfgProject
