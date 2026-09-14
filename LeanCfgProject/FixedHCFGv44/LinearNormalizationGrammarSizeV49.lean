import LeanCfgProject.FixedHCFGv44.LinearNormalizationCoreV49

namespace LeanCfgProject
namespace FixedHCFGv44

universe u v

/-!
Grammar-level size accounting for the Appendix A linear-spine normalization.

This file starts after the standard preprocessing phase described in the
manuscript: start-symbol separation, useless-symbol elimination, non-start
epsilon elimination, and non-start unit elimination.  At that point every
surviving non-start production is either a non-unit linear body `u B v` with
`|u|+|v|>0`, or a nonempty terminal-only body.

`LinearNormalizationCoreV49` proves the exact rule-local factorization and
fresh-chain counts.  Here we package a finite family of such prepared rules
and sum those bounds.  This is the global size-accounting bridge needed for
Proposition `prop:linear-normal`; whole-grammar language equivalence is kept
for the next layer.
-/

/-- One non-start production after epsilon/unit elimination. -/
inductive PreparedLinearRule (N : Type v) (Sigma : Type u) where
  | context
      (lhs : N)
      (body : LinearContextBody N Sigma)
      (nonunit : body.Nonunit)
  | terminal
      (lhs : N)
      (body : NonemptyTerminalBody Sigma)

namespace PreparedLinearRule

/-- Encoded right-hand-side length of a prepared production. -/
def rhsLength {N : Type v} {Sigma : Type u} :
    PreparedLinearRule N Sigma → Nat
  | .context _ body _ => body.left.length + 1 + body.right.length
  | .terminal _ body => body.word.length

/-- Fresh `R/J/Theta` chain symbols introduced for one production. -/
def freshStateCount {N : Type v} {Sigma : Type u} :
    PreparedLinearRule N Sigma → Nat
  | .context _ body _ => body.freshChainCount
  | .terminal _ body => body.freshChainCount

/--
Number of normalized non-wrapper rules contributed by one prepared rule.
Wrapper terminal rules `W_a -> a` are shared globally and counted separately.
-/
def normalizedLocalRuleCount {N : Type v} {Sigma : Type u} :
    PreparedLinearRule N Sigma → Nat
  | .context _ body _ => body.spineOps.length
  | .terminal _ body => body.word.length

/-- Every prepared right-hand side is nonempty. -/
theorem rhsLength_pos
    {N : Type v} {Sigma : Type u}
    (r : PreparedLinearRule N Sigma) :
    0 < r.rhsLength := by
  cases r with
  | context lhs body h =>
      simp [rhsLength]
  | terminal lhs body =>
      simp [rhsLength, NonemptyTerminalBody.word]

/-- Local fresh-state growth is at most the original RHS length. -/
theorem freshStateCount_le_rhsLength
    {N : Type v} {Sigma : Type u}
    (r : PreparedLinearRule N Sigma) :
    r.freshStateCount ≤ r.rhsLength := by
  cases r with
  | context lhs body h =>
      have hLocal := body.freshChainCount_le_spineSteps
      rw [LinearContextBody.spineOps, contextSpineOps_length] at hLocal
      simp [freshStateCount, rhsLength]
      omega
  | terminal lhs body =>
      simp [freshStateCount, rhsLength, NonemptyTerminalBody.freshChainCount,
        NonemptyTerminalBody.word]

/-- Local normalized-rule growth is at most the original RHS length. -/
theorem normalizedLocalRuleCount_le_rhsLength
    {N : Type v} {Sigma : Type u}
    (r : PreparedLinearRule N Sigma) :
    r.normalizedLocalRuleCount ≤ r.rhsLength := by
  cases r with
  | context lhs body h =>
      rw [normalizedLocalRuleCount, LinearContextBody.spineOps,
        contextSpineOps_length]
      simp [rhsLength]
      omega
  | terminal lhs body =>
      simp [normalizedLocalRuleCount, rhsLength]

end PreparedLinearRule

/-- Total RHS length of the prepared non-start grammar. -/
def preparedTotalRhsLength
    {N : Type v} {Sigma : Type u}
    (rules : List (PreparedLinearRule N Sigma)) : Nat :=
  (rules.map PreparedLinearRule.rhsLength).sum

/-- Total number of fresh chain symbols introduced production-by-production. -/
def normalizationFreshStateCount
    {N : Type v} {Sigma : Type u}
    (rules : List (PreparedLinearRule N Sigma)) : Nat :=
  (rules.map PreparedLinearRule.freshStateCount).sum

/-- Total normalized non-wrapper rules contributed by prepared productions. -/
def normalizationLocalRuleCount
    {N : Type v} {Sigma : Type u}
    (rules : List (PreparedLinearRule N Sigma)) : Nat :=
  (rules.map PreparedLinearRule.normalizedLocalRuleCount).sum

/-- Summed fresh-chain growth is linear in total RHS length. -/
theorem normalizationFreshStateCount_le_totalRhsLength
    {N : Type v} {Sigma : Type u}
    (rules : List (PreparedLinearRule N Sigma)) :
    normalizationFreshStateCount rules ≤ preparedTotalRhsLength rules := by
  induction rules with
  | nil => simp [normalizationFreshStateCount, preparedTotalRhsLength]
  | cons r rs ih =>
      simp [normalizationFreshStateCount, preparedTotalRhsLength]
      exact Nat.add_le_add
        (PreparedLinearRule.freshStateCount_le_rhsLength r) ih

/-- Summed normalized-rule growth is linear in total RHS length. -/
theorem normalizationLocalRuleCount_le_totalRhsLength
    {N : Type v} {Sigma : Type u}
    (rules : List (PreparedLinearRule N Sigma)) :
    normalizationLocalRuleCount rules ≤ preparedTotalRhsLength rules := by
  induction rules with
  | nil => simp [normalizationLocalRuleCount, preparedTotalRhsLength]
  | cons r rs ih =>
      simp [normalizationLocalRuleCount, preparedTotalRhsLength]
      exact Nat.add_le_add
        (PreparedLinearRule.normalizedLocalRuleCount_le_rhsLength r) ih

/--
A simple encoded size for the prepared grammar.  `startRuleCount` records the
separated start rules, which are not changed by the wrapper-chain
factorization.
-/
def preparedGrammarSize
    {N : Type v} {Sigma : Type u}
    [Fintype N] [Fintype Sigma]
    (rules : List (PreparedLinearRule N Sigma))
    (startRuleCount : Nat) : Nat :=
  Fintype.card N + Fintype.card Sigma + rules.length +
    preparedTotalRhsLength rules + startRuleCount

/--
Upper bound on normalized non-start symbols: original symbols, at most one
shared wrapper per terminal, and the fresh production-local chain symbols.
-/
def normalizationNonterminalBudget
    {N : Type v} {Sigma : Type u}
    [Fintype N] [Fintype Sigma]
    (rules : List (PreparedLinearRule N Sigma)) : Nat :=
  Fintype.card N + Fintype.card Sigma + normalizationFreshStateCount rules

/--
Upper bound on normalized productions: one wrapper terminal rule per terminal,
all production-local normalized rules, and unchanged separated start rules.
-/
def normalizationProductionBudget
    {N : Type v} {Sigma : Type u}
    [Fintype Sigma]
    (rules : List (PreparedLinearRule N Sigma))
    (startRuleCount : Nat) : Nat :=
  Fintype.card Sigma + normalizationLocalRuleCount rules + startRuleCount

/-- The normalized nonterminal budget is linear in the prepared grammar size. -/
theorem normalizationNonterminalBudget_le_preparedGrammarSize
    {N : Type v} {Sigma : Type u}
    [Fintype N] [Fintype Sigma]
    (rules : List (PreparedLinearRule N Sigma))
    (startRuleCount : Nat) :
    normalizationNonterminalBudget rules ≤
      preparedGrammarSize rules startRuleCount := by
  have h := normalizationFreshStateCount_le_totalRhsLength rules
  simp [normalizationNonterminalBudget, preparedGrammarSize]
  omega

/-- The normalized production budget is linear in the prepared grammar size. -/
theorem normalizationProductionBudget_le_preparedGrammarSize
    {N : Type v} {Sigma : Type u}
    [Fintype N] [Fintype Sigma]
    (rules : List (PreparedLinearRule N Sigma))
    (startRuleCount : Nat) :
    normalizationProductionBudget rules startRuleCount ≤
      preparedGrammarSize rules startRuleCount := by
  have h := normalizationLocalRuleCount_le_totalRhsLength rules
  simp [normalizationProductionBudget, preparedGrammarSize]
  omega

/--
Combined global size contract for the wrapper-chain phase of Appendix A.
Both the number of resulting non-start symbols and the number of productions
are bounded linearly by the prepared input size.
-/
theorem linearNormalization_global_size_core_v49
    {N : Type v} {Sigma : Type u}
    [Fintype N] [Fintype Sigma]
    (rules : List (PreparedLinearRule N Sigma))
    (startRuleCount : Nat) :
    normalizationNonterminalBudget rules ≤
        preparedGrammarSize rules startRuleCount ∧
      normalizationProductionBudget rules startRuleCount ≤
        preparedGrammarSize rules startRuleCount := by
  exact ⟨
    normalizationNonterminalBudget_le_preparedGrammarSize
      rules startRuleCount,
    normalizationProductionBudget_le_preparedGrammarSize
      rules startRuleCount⟩

end FixedHCFGv44
end LeanCfgProject
