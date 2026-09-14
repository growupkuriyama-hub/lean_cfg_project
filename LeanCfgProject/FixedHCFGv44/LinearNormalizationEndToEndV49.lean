import LeanCfgProject.FixedHCFGv44.LinearPreprocessingPreparedEnumerationV49
import LeanCfgProject.FixedHCFGv44.LinearNormalizationTrimmedV49

namespace LeanCfgProject
namespace FixedHCFGv44

universe u v

/-!
End-to-end semantic and structural form of Appendix A for an arbitrary finite
source linear CFG.

The source grammar is first separated at the start interface, non-start epsilon
and unit behavior is compiled into the explicit finite prepared enumeration,
and that prepared grammar is then reified as a single-spine SSBNF and trimmed.
This file composes the already verified phases; it does not yet attach a source-
size polynomial bound to the preprocessing enumeration.
-/

/-- Final terminal rules obtained from a finite source linear grammar. -/
noncomputable def SourceNormalizedTerminalV49
    {N : Type v} {Sigma : Type u} [Fintype N]
    (sourceRules : List (SourceLinearRule N Sigma)) (S : N) :
    TerminalRules (LinearNormNT N Sigma) Sigma :=
  TrimmedLinearNormTerminal
    (enumeratePreparedLinearRules sourceRules)
    (SourceSeparatedStart S)

/-- Final binary rules obtained from a finite source linear grammar. -/
noncomputable def SourceNormalizedBinaryV49
    {N : Type v} {Sigma : Type u} [Fintype N]
    (sourceRules : List (SourceLinearRule N Sigma)) (S : N) :
    BinaryRules (LinearNormNT N Sigma) :=
  TrimmedLinearNormBinary
    (enumeratePreparedLinearRules sourceRules)
    (SourceSeparatedStart S)

/-- Final separated start rules obtained from a finite source linear grammar. -/
noncomputable def SourceNormalizedStartV49
    {N : Type v} {Sigma : Type u} [Fintype N]
    (sourceRules : List (SourceLinearRule N Sigma)) (S : N) :
    StartRules (LinearNormNT N Sigma) :=
  TrimmedLinearNormStart
    (enumeratePreparedLinearRules sourceRules)
    (SourceSeparatedStart S)

/-- Language of the final reduced single-spine SSBNF produced from the source grammar. -/
noncomputable def SourceNormalizedLanguageV49
    {N : Type v} {Sigma : Type u} [Fintype N]
    (sourceRules : List (SourceLinearRule N Sigma)) (S : N) :
    Language Sigma :=
  ReducedLinearSpineSSBNFLanguage
    (enumeratePreparedLinearRules sourceRules)
    (SourceSeparatedStart S)
    (SourceNullable sourceRules S)

/-- The complete normalization preserves the original source language exactly. -/
theorem linearNormalization_source_language_eq_v49
    {N : Type v} {Sigma : Type u} [Fintype N]
    (sourceRules : List (SourceLinearRule N Sigma)) (S : N) :
    SourceNormalizedLanguageV49 sourceRules S =
      SourceLinearLanguage sourceRules S := by
  calc
    SourceNormalizedLanguageV49 sourceRules S =
        PreparedLinearLanguage
          (enumeratePreparedLinearRules sourceRules)
          (SourceSeparatedStart S)
          (SourceNullable sourceRules S) := by
      simpa [SourceNormalizedLanguageV49] using
        (linearNormalization_trimmed_language_eq_v49
          (enumeratePreparedLinearRules sourceRules)
          (SourceSeparatedStart S)
          (SourceNullable sourceRules S))
    _ = SourceLinearLanguage sourceRules S :=
      enumerated_prepared_language_eq_source_v49 sourceRules S

/-- Every final binary rule has exactly one wrapper child and one spine child. -/
theorem sourceNormalizedBinary_single_spine_v49
    {N : Type v} {Sigma : Type u} [Fintype N]
    {sourceRules : List (SourceLinearRule N Sigma)} {S : N}
    {X Y Z : LinearNormNT N Sigma}
    (h : SourceNormalizedBinaryV49 sourceRules S X Y Z) :
    LinearNormSingleSpineRule Y Z := by
  exact trimmedLinearNormBinary_single_spine_shape h

/-- Every state participating in a final binary rule is productive and reachable. -/
theorem sourceNormalizedBinary_states_reduced_v49
    {N : Type v} {Sigma : Type u} [Fintype N]
    {sourceRules : List (SourceLinearRule N Sigma)} {S : N}
    {X Y Z : LinearNormNT N Sigma}
    (h : SourceNormalizedBinaryV49 sourceRules S X Y Z) :
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
        (LinearNormStartRules (SourceSeparatedStart S)) Z := by
  exact trimmedLinearNorm_binary_states_reduced h

/-- Every final terminal-rule left-hand side is productive and reachable. -/
theorem sourceNormalizedTerminal_lhs_reduced_v49
    {N : Type v} {Sigma : Type u} [Fintype N]
    {sourceRules : List (SourceLinearRule N Sigma)} {S : N}
    {X : LinearNormNT N Sigma} {a : Sigma}
    (h : SourceNormalizedTerminalV49 sourceRules S X a) :
    UntypedKept
      (LinearNormTerminal (enumeratePreparedLinearRules sourceRules))
      (LinearNormBinary (enumeratePreparedLinearRules sourceRules))
      (LinearNormStartRules (SourceSeparatedStart S)) X := by
  exact trimmedLinearNorm_terminal_lhs_reduced h

/-- Every final start target is productive and reachable. -/
theorem sourceNormalizedStart_target_reduced_v49
    {N : Type v} {Sigma : Type u} [Fintype N]
    {sourceRules : List (SourceLinearRule N Sigma)} {S : N}
    {X : LinearNormNT N Sigma}
    (h : SourceNormalizedStartV49 sourceRules S X) :
    UntypedKept
      (LinearNormTerminal (enumeratePreparedLinearRules sourceRules))
      (LinearNormBinary (enumeratePreparedLinearRules sourceRules))
      (LinearNormStartRules (SourceSeparatedStart S)) X := by
  exact trimmedLinearNorm_start_target_reduced h

/--
Manuscript-facing end-to-end normalization package, modulo the remaining
source-size polynomial accounting for the preprocessing enumeration.
-/
theorem linearNormalization_source_end_to_end_v49
    {N : Type v} {Sigma : Type u} [Fintype N]
    (sourceRules : List (SourceLinearRule N Sigma)) (S : N) :
    SourceNormalizedLanguageV49 sourceRules S =
        SourceLinearLanguage sourceRules S ∧
      (∀ ⦃X Y Z : LinearNormNT N Sigma⦄,
        SourceNormalizedBinaryV49 sourceRules S X Y Z →
          LinearNormSingleSpineRule Y Z) ∧
      (∀ ⦃X Y Z : LinearNormNT N Sigma⦄,
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
              (LinearNormStartRules (SourceSeparatedStart S)) Z) := by
  refine ⟨linearNormalization_source_language_eq_v49 sourceRules S, ?_, ?_⟩
  · intro X Y Z h
    exact sourceNormalizedBinary_single_spine_v49 h
  · intro X Y Z h
    exact sourceNormalizedBinary_states_reduced_v49 h

end FixedHCFGv44
end LeanCfgProject
