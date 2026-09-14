import LeanCfgProject.FixedHCFGv44.LinearPreprocessingPreparedEnumerationV49
import LeanCfgProject.FixedHCFGv44.LinearNormalizationGrammarSizeV49

namespace LeanCfgProject
namespace FixedHCFGv44

universe u v

/-!
Source-size accounting for the Appendix A normalization pipeline.

The prepared-grammar phase is already linear in its prepared input size.
This file bounds the explicit finite prepared enumeration polynomially in a
simple source grammar encoding.  Together these estimates give the remaining
source-size polynomial bridge for Proposition `prop:linear-normal`.
-/

/-- Encoded RHS length of one source linear production. -/
def SourceLinearRule.rhsLength
    {N : Type v} {Sigma : Type u} : SourceLinearRule N Sigma → Nat
  | .context _ u _ v => u.length + 1 + v.length
  | .terminal _ w => w.length

/-- Total encoded RHS length of the finite source grammar. -/
def sourceTotalRhsLength
    {N : Type v} {Sigma : Type u}
    (rules : List (SourceLinearRule N Sigma)) : Nat :=
  (rules.map SourceLinearRule.rhsLength).sum

/-- A simple source grammar size used for the polynomial envelope. -/
def sourceLinearGrammarSize
    {N : Type v} {Sigma : Type u}
    [Fintype N] [Fintype Sigma]
    (rules : List (SourceLinearRule N Sigma)) : Nat :=
  Fintype.card N + Fintype.card Sigma + rules.length +
    sourceTotalRhsLength rules + 1

/-- One source rule contributes at most two prepared productions for a fixed copied LHS. -/
theorem preparedRulesFromSourceAt_length_le_two
    {N : Type v} {Sigma : Type u}
    (allRules : List (SourceLinearRule N Sigma)) (A : N)
    (r : SourceLinearRule N Sigma) :
    (preparedRulesFromSourceAt allRules A r).length ≤ 2 := by
  classical
  cases r with
  | context B u C v =>
      by_cases hreach : LinearUnitReach allRules A B
      · by_cases hnonunit : u ≠ [] ∨ v ≠ []
        · by_cases hnullable : SourceNullable allRules C
          · by_cases hne : u ++ v ≠ []
            · simp [preparedRulesFromSourceAt, hreach, hnonunit, hnullable, hne]
            · simp [preparedRulesFromSourceAt, hreach, hnonunit, hnullable, hne]
          · simp [preparedRulesFromSourceAt, hreach, hnonunit, hnullable]
        · by_cases hnullable : SourceNullable allRules C
          · by_cases hne : u ++ v ≠ []
            · simp [preparedRulesFromSourceAt, hreach, hnonunit, hnullable, hne]
            · simp [preparedRulesFromSourceAt, hreach, hnonunit, hnullable, hne]
          · simp [preparedRulesFromSourceAt, hreach, hnonunit, hnullable]
      · simp [preparedRulesFromSourceAt, hreach]
  | terminal B w =>
      by_cases hreach : LinearUnitReach allRules A B
      · by_cases hne : w ≠ []
        · simp [preparedRulesFromSourceAt, hreach, hne]
        · simp [preparedRulesFromSourceAt, hreach, hne]
      · simp [preparedRulesFromSourceAt, hreach]

/-- One source rule contributes at most twice its encoded RHS length. -/
theorem preparedRulesFromSourceAt_rhs_le_twice
    {N : Type v} {Sigma : Type u}
    (allRules : List (SourceLinearRule N Sigma)) (A : N)
    (r : SourceLinearRule N Sigma) :
    preparedTotalRhsLength (preparedRulesFromSourceAt allRules A r) ≤
      2 * r.rhsLength := by
  classical
  cases r with
  | context B u C v =>
      by_cases hreach : LinearUnitReach allRules A B
      · by_cases hnonunit : u ≠ [] ∨ v ≠ []
        · by_cases hnullable : SourceNullable allRules C
          · by_cases hne : u ++ v ≠ []
            · simp [preparedRulesFromSourceAt, hreach, hnonunit, hnullable, hne,
                preparedTotalRhsLength, PreparedLinearRule.rhsLength,
                SourceLinearRule.rhsLength, nonemptyTerminalBodyOf_word] <;> omega
            · simp [preparedRulesFromSourceAt, hreach, hnonunit, hnullable, hne,
                preparedTotalRhsLength, PreparedLinearRule.rhsLength,
                SourceLinearRule.rhsLength] <;> omega
          · simp [preparedRulesFromSourceAt, hreach, hnonunit, hnullable,
              preparedTotalRhsLength, PreparedLinearRule.rhsLength,
              SourceLinearRule.rhsLength] <;> omega
        · by_cases hnullable : SourceNullable allRules C
          · by_cases hne : u ++ v ≠ []
            · simp [preparedRulesFromSourceAt, hreach, hnonunit, hnullable, hne,
                preparedTotalRhsLength, PreparedLinearRule.rhsLength,
                SourceLinearRule.rhsLength, nonemptyTerminalBodyOf_word] <;> omega
            · simp [preparedRulesFromSourceAt, hreach, hnonunit, hnullable, hne,
                preparedTotalRhsLength, PreparedLinearRule.rhsLength,
                SourceLinearRule.rhsLength] <;> omega
          · simp [preparedRulesFromSourceAt, hreach, hnonunit, hnullable,
              preparedTotalRhsLength, PreparedLinearRule.rhsLength,
              SourceLinearRule.rhsLength] <;> omega
      · simp [preparedRulesFromSourceAt, hreach, preparedTotalRhsLength,
          SourceLinearRule.rhsLength]
  | terminal B w =>
      by_cases hreach : LinearUnitReach allRules A B
      · by_cases hne : w ≠ []
        · simp [preparedRulesFromSourceAt, hreach, hne, preparedTotalRhsLength,
            PreparedLinearRule.rhsLength, SourceLinearRule.rhsLength,
            nonemptyTerminalBodyOf_word] <;> omega
        · simp [preparedRulesFromSourceAt, hreach, hne, preparedTotalRhsLength,
            SourceLinearRule.rhsLength]
      · simp [preparedRulesFromSourceAt, hreach, preparedTotalRhsLength,
          SourceLinearRule.rhsLength]

/-- Prepared RHS length is additive over list append. -/
theorem preparedTotalRhsLength_append
    {N : Type v} {Sigma : Type u}
    (xs ys : List (PreparedLinearRule N Sigma)) :
    preparedTotalRhsLength (xs ++ ys) =
      preparedTotalRhsLength xs + preparedTotalRhsLength ys := by
  simp [preparedTotalRhsLength, List.map_append]

/-- Source RHS length is additive over list append. -/
theorem sourceTotalRhsLength_cons
    {N : Type v} {Sigma : Type u}
    (r : SourceLinearRule N Sigma) (rs : List (SourceLinearRule N Sigma)) :
    sourceTotalRhsLength (r :: rs) =
      r.rhsLength + sourceTotalRhsLength rs := by
  simp [sourceTotalRhsLength]

/-- For one copied LHS, scanning all source rules creates at most two copies per rule. -/
theorem preparedRulesScan_length_le
    {N : Type v} {Sigma : Type u}
    (allRules scan : List (SourceLinearRule N Sigma)) (A : N) :
    (scan.flatMap (preparedRulesFromSourceAt allRules A)).length ≤
      2 * scan.length := by
  induction scan with
  | nil => simp
  | cons r rs ih =>
      change
        (preparedRulesFromSourceAt allRules A r ++
          rs.flatMap (preparedRulesFromSourceAt allRules A)).length ≤
          2 * (r :: rs).length
      simp only [List.length_append, List.length_cons]
      have hlocal := preparedRulesFromSourceAt_length_le_two allRules A r
      omega

/-- For one copied LHS, total prepared RHS length is at most twice the source total. -/
theorem preparedRulesScan_rhs_le
    {N : Type v} {Sigma : Type u}
    (allRules scan : List (SourceLinearRule N Sigma)) (A : N) :
    preparedTotalRhsLength
        (scan.flatMap (preparedRulesFromSourceAt allRules A)) ≤
      2 * sourceTotalRhsLength scan := by
  induction scan with
  | nil => simp [preparedTotalRhsLength, sourceTotalRhsLength]
  | cons r rs ih =>
      change
        preparedTotalRhsLength
          (preparedRulesFromSourceAt allRules A r ++
            rs.flatMap (preparedRulesFromSourceAt allRules A)) ≤
          2 * sourceTotalRhsLength (r :: rs)
      rw [preparedTotalRhsLength_append, sourceTotalRhsLength_cons]
      have hlocal := preparedRulesFromSourceAt_rhs_le_twice allRules A r
      omega

/-- Repeating the scan over a finite list of possible copied LHS symbols. -/
theorem preparedRulesMany_length_le
    {N : Type v} {Sigma : Type u}
    (allRules : List (SourceLinearRule N Sigma)) (As : List N) :
    (As.flatMap fun A =>
      allRules.flatMap (preparedRulesFromSourceAt allRules A)).length ≤
      2 * (As.length * allRules.length) := by
  induction As with
  | nil => simp
  | cons A As ih =>
      change
        (allRules.flatMap (preparedRulesFromSourceAt allRules A) ++
          As.flatMap fun B =>
            allRules.flatMap (preparedRulesFromSourceAt allRules B)).length ≤
          2 * ((A :: As).length * allRules.length)
      simp only [List.length_append, List.length_cons, Nat.add_mul, one_mul]
      have hOne := preparedRulesScan_length_le allRules allRules A
      omega

/-- Repeating the scan over copied LHS symbols preserves a quadratic RHS envelope. -/
theorem preparedRulesMany_rhs_le
    {N : Type v} {Sigma : Type u}
    (allRules : List (SourceLinearRule N Sigma)) (As : List N) :
    preparedTotalRhsLength
        (As.flatMap fun A =>
          allRules.flatMap (preparedRulesFromSourceAt allRules A)) ≤
      2 * (As.length * sourceTotalRhsLength allRules) := by
  induction As with
  | nil => simp [preparedTotalRhsLength]
  | cons A As ih =>
      change
        preparedTotalRhsLength
          (allRules.flatMap (preparedRulesFromSourceAt allRules A) ++
            As.flatMap fun B =>
              allRules.flatMap (preparedRulesFromSourceAt allRules B)) ≤
          2 * ((A :: As).length * sourceTotalRhsLength allRules)
      rw [preparedTotalRhsLength_append]
      simp only [List.length_cons, Nat.add_mul, one_mul]
      have hOne := preparedRulesScan_rhs_le allRules allRules A
      omega

/-- The explicit prepared enumeration has at most `2 |N| |P|` rules. -/
theorem enumeratePreparedLinearRules_length_bound_v49
    {N : Type v} {Sigma : Type u} [Fintype N]
    (sourceRules : List (SourceLinearRule N Sigma)) :
    (enumeratePreparedLinearRules sourceRules).length ≤
      2 * (Fintype.card N * sourceRules.length) := by
  classical
  simpa [enumeratePreparedLinearRules] using
    (preparedRulesMany_length_le sourceRules (Finset.univ.toList : List N))

/-- The explicit prepared enumeration has total RHS length at most `2 |N| R`. -/
theorem enumeratePreparedLinearRules_rhs_bound_v49
    {N : Type v} {Sigma : Type u} [Fintype N]
    (sourceRules : List (SourceLinearRule N Sigma)) :
    preparedTotalRhsLength (enumeratePreparedLinearRules sourceRules) ≤
      2 * (Fintype.card N * sourceTotalRhsLength sourceRules) := by
  classical
  simpa [enumeratePreparedLinearRules] using
    (preparedRulesMany_rhs_le sourceRules (Finset.univ.toList : List N))

/-- Quadratic polynomial used as a source-size envelope for normalization. -/
def sourceLinearNormalizationPolynomial
    {N : Type v} {Sigma : Type u}
    [Fintype N] [Fintype Sigma]
    (sourceRules : List (SourceLinearRule N Sigma)) : Nat :=
  let s := sourceLinearGrammarSize sourceRules
  4 * (s * s) + s

/-- Prepared grammar size is quadratically bounded by the source encoding. -/
theorem enumerated_preparedGrammarSize_le_sourcePolynomial_v49
    {N : Type v} {Sigma : Type u}
    [Fintype N] [Fintype Sigma]
    (sourceRules : List (SourceLinearRule N Sigma)) :
    preparedGrammarSize (enumeratePreparedLinearRules sourceRules) 1 ≤
      sourceLinearNormalizationPolynomial sourceRules := by
  let s := sourceLinearGrammarSize sourceRules
  have hlen := enumeratePreparedLinearRules_length_bound_v49 sourceRules
  have hrhs := enumeratePreparedLinearRules_rhs_bound_v49 sourceRules
  have hN : Fintype.card N ≤ s := by
    dsimp [s, sourceLinearGrammarSize]
    omega
  have hP : sourceRules.length ≤ s := by
    dsimp [s, sourceLinearGrammarSize]
    omega
  have hR : sourceTotalRhsLength sourceRules ≤ s := by
    dsimp [s, sourceLinearGrammarSize]
    omega
  have hNP : Fintype.card N * sourceRules.length ≤ s * s :=
    Nat.mul_le_mul hN hP
  have hNR : Fintype.card N * sourceTotalRhsLength sourceRules ≤ s * s :=
    Nat.mul_le_mul hN hR
  have hBase :
      Fintype.card N + Fintype.card Sigma + 1 ≤ s := by
    dsimp [s, sourceLinearGrammarSize]
    omega
  change
    Fintype.card N + Fintype.card Sigma +
        (enumeratePreparedLinearRules sourceRules).length +
        preparedTotalRhsLength (enumeratePreparedLinearRules sourceRules) + 1 ≤
      4 * (s * s) + s
  omega

/-- Both untrimmed normalized symbol/rule budgets satisfy the same source polynomial. -/
theorem linearNormalization_source_polynomial_size_v49
    {N : Type v} {Sigma : Type u}
    [Fintype N] [Fintype Sigma]
    (sourceRules : List (SourceLinearRule N Sigma)) :
    normalizationNonterminalBudget (enumeratePreparedLinearRules sourceRules) ≤
        sourceLinearNormalizationPolynomial sourceRules ∧
      normalizationProductionBudget
          (enumeratePreparedLinearRules sourceRules) 1 ≤
        sourceLinearNormalizationPolynomial sourceRules := by
  have hPrepared :=
    enumerated_preparedGrammarSize_le_sourcePolynomial_v49 sourceRules
  have hCore :=
    linearNormalization_global_size_core_v49
      (enumeratePreparedLinearRules sourceRules) 1
  exact ⟨le_trans hCore.1 hPrepared, le_trans hCore.2 hPrepared⟩

end FixedHCFGv44
end LeanCfgProject
