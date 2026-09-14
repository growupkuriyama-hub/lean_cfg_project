import LeanCfgProject.FixedHCFGv44.LinearNormalizationEndToEndV49
import LeanCfgProject.FixedHCFGv44.LinearNormalizationSourceSizeV49

namespace LeanCfgProject
namespace FixedHCFGv44

universe u v

/-!
Manuscript-facing synchronization package for TCS v49 Proposition
`prop:linear-normal`.

This file packages the clauses that are currently formalized directly:

* exact language preservation from an arbitrary finite source linear CFG;
* reducedness of every state participating in a retained rule;
* the single-spine binary-rule shape with unique terminal wrappers; and
* an explicit polynomial bound on the normalized nonterminal/production
  budgets in terms of a finite source-grammar encoding.

The proposition's algorithmic phrase "computed in polynomial time" is not
claimed here as a machine-level runtime theorem.  The formal development gives
an explicit finite construction and polynomial output-size accounting; an
executable cost model for nullability, unit closure, enumeration, and trimming
remains a separate complexity layer.
-/

/--
Certificate collecting the non-runtime clauses of the manuscript's
linear-spine SSBNF normalization proposition.
-/
structure LinearNormalizationCertificateV49
    {N : Type v} {Sigma : Type u}
    [Fintype N] [Fintype Sigma]
    (sourceRules : List (SourceLinearRule N Sigma)) (S : N) : Prop where
  languageEq :
    SourceNormalizedLanguageV49 sourceRules S =
      SourceLinearLanguage sourceRules S
  binarySingleSpine :
    ∀ ⦃X Y Z : LinearNormNT N Sigma⦄,
      SourceNormalizedBinaryV49 sourceRules S X Y Z →
        LinearNormSingleSpineRule Y Z
  wrapperTerminalUnique :
    ∀ ⦃a b : Sigma⦄,
      SourceNormalizedTerminalV49 sourceRules S (.wrap a) b → b = a
  binaryStatesReduced :
    ∀ ⦃X Y Z : LinearNormNT N Sigma⦄,
      SourceNormalizedBinaryV49 sourceRules S X Y Z →
        UntypedKept
            (LinearNormTerminal (enumeratePreparedLinearRules sourceRules))
            (LinearNormBinary (enumeratePreparedLinearRules sourceRules))
            (LinearNormStartRules (SourceSeparatedStart S)) X ∧
          UntypedKept
            (LinearNormTerminal (enumeratePreparedLinearRules sourceRules))
            (LinearNormBinary (enumeratePreparedLinearRules sourceRules))
            (LinearNormStartRules (SourceSeparatedStart S)) Y ∧
          UntypedKept
            (LinearNormTerminal (enumeratePreparedLinearRules sourceRules))
            (LinearNormBinary (enumeratePreparedLinearRules sourceRules))
            (LinearNormStartRules (SourceSeparatedStart S)) Z
  terminalLhsReduced :
    ∀ ⦃X : LinearNormNT N Sigma⦄ ⦃a : Sigma⦄,
      SourceNormalizedTerminalV49 sourceRules S X a →
        UntypedKept
          (LinearNormTerminal (enumeratePreparedLinearRules sourceRules))
          (LinearNormBinary (enumeratePreparedLinearRules sourceRules))
          (LinearNormStartRules (SourceSeparatedStart S)) X
  startTargetReduced :
    ∀ ⦃X : LinearNormNT N Sigma⦄,
      SourceNormalizedStartV49 sourceRules S X →
        UntypedKept
          (LinearNormTerminal (enumeratePreparedLinearRules sourceRules))
          (LinearNormBinary (enumeratePreparedLinearRules sourceRules))
          (LinearNormStartRules (SourceSeparatedStart S)) X
  nonterminalBudget :
    normalizationNonterminalBudget (enumeratePreparedLinearRules sourceRules) ≤
      sourceLinearNormalizationPolynomial sourceRules
  productionBudget :
    normalizationProductionBudget
        (enumeratePreparedLinearRules sourceRules) 1 ≤
      sourceLinearNormalizationPolynomial sourceRules

/--
TCS v49 Proposition `prop:linear-normal`, formalized through all semantic,
structural, reducedness, and polynomial-size clauses.  Runtime complexity is
intentionally excluded from this theorem and tracked separately.
-/
theorem proposition_linear_normal_semantic_size_v49
    {N : Type v} {Sigma : Type u}
    [Fintype N] [Fintype Sigma]
    (sourceRules : List (SourceLinearRule N Sigma)) (S : N) :
    LinearNormalizationCertificateV49 sourceRules S := by
  have hSize := linearNormalization_source_polynomial_size_v49 sourceRules
  refine
    { languageEq := linearNormalization_source_language_eq_v49 sourceRules S
      binarySingleSpine := ?_
      wrapperTerminalUnique := ?_
      binaryStatesReduced := ?_
      terminalLhsReduced := ?_
      startTargetReduced := ?_
      nonterminalBudget := hSize.1
      productionBudget := hSize.2 }
  · intro X Y Z h
    exact sourceNormalizedBinary_single_spine_v49 h
  · intro a b h
    exact trimmedLinearNorm_wrapper_terminal_unique h
  · intro X Y Z h
    exact sourceNormalizedBinary_states_reduced_v49 h
  · intro X a h
    exact sourceNormalizedTerminal_lhs_reduced_v49 h
  · intro X h
    exact sourceNormalizedStart_target_reduced_v49 h

end FixedHCFGv44
end LeanCfgProject
