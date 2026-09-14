import LeanCfgProject.FixedHCFGv44.LinearNormalizationSSBNFShapeV49
import LeanCfgProject.FixedHCFGv44.LinearNormalizationGrammarSizeV49

namespace LeanCfgProject
namespace FixedHCFGv44

universe u v

/-!
Manuscript-facing post-preprocessing form of Appendix A.

The remaining gap to the full Proposition `prop:linear-normal` is now isolated
before this theorem: one must transform an arbitrary finite linear CFG into the
prepared representation by start separation, useless-symbol elimination,
non-start epsilon elimination, and non-start unit elimination, and finally
trim the reified grammar if a reduced output object is required.

Once a prepared grammar is supplied, the results below are unconditional: the
constructed grammar is a genuine terminal/binary SSBNF grammar, it preserves
the start language exactly, every binary production has the single-spine
shape, and the wrapper-chain symbol/rule budgets are linear in the prepared
encoded size.
-/

/-- The two possible orientations of a single-spine binary production. -/
def LinearNormSingleSpineRule
    {N : Type v} {Sigma : Type u}
    (Y Z : LinearNormNT N Sigma) : Prop :=
  (IsLinearNormWrapper Y ∧ IsLinearNormSpine Z) ∨
    (IsLinearNormSpine Y ∧ IsLinearNormWrapper Z)

/--
Complete post-preprocessing normalization package used by Appendix A.
This theorem combines exact language preservation, the structural single-spine
invariant, and global linear size accounting.
-/
theorem linearNormalization_postPreprocessing_v49
    {N : Type v} {Sigma : Type u}
    [Fintype N] [Fintype Sigma]
    (rules : List (PreparedLinearRule N Sigma))
    (start : N → Prop) (epsilonStart : Prop)
    (startRuleCount : Nat) :
    ReifiedLinearSpineSSBNFLanguage rules start epsilonStart =
        PreparedLinearLanguage rules start epsilonStart ∧
      (∀ ⦃X Y Z : LinearNormNT N Sigma⦄,
        LinearNormBinary rules X Y Z → LinearNormSingleSpineRule Y Z) ∧
      normalizationNonterminalBudget rules ≤
        preparedGrammarSize rules startRuleCount ∧
      normalizationProductionBudget rules startRuleCount ≤
        preparedGrammarSize rules startRuleCount := by
  refine ⟨
    linearNormalization_reifiedSSBNF_language_eq_v49
      rules start epsilonStart,
    ?_,
    normalizationNonterminalBudget_le_preparedGrammarSize
      rules startRuleCount,
    normalizationProductionBudget_le_preparedGrammarSize
      rules startRuleCount⟩
  intro X Y Z h
  exact linearNormBinary_single_spine_shape h

/--
A compact structural corollary: every binary rule of the constructed SSBNF
contains exactly one wrapper child, and wrappers themselves are terminal-only.
-/
theorem linearNormalization_postPreprocessing_spine_contract_v49
    {N : Type v} {Sigma : Type u}
    {rules : List (PreparedLinearRule N Sigma)} :
    (∀ ⦃X Y Z : LinearNormNT N Sigma⦄,
        LinearNormBinary rules X Y Z → LinearNormSingleSpineRule Y Z) ∧
      (∀ ⦃a b : Sigma⦄,
        LinearNormTerminal rules (.wrap a) b → b = a) ∧
      (∀ ⦃a : Sigma⦄ ⦃Y Z : LinearNormNT N Sigma⦄,
        ¬ LinearNormBinary rules (.wrap a) Y Z) := by
  refine ⟨?_, ?_, ?_⟩
  · intro X Y Z h
    exact linearNormBinary_single_spine_shape h
  · intro a b h
    exact linearNorm_wrapper_terminal_unique h
  · intro a Y Z
    exact linearNorm_wrapper_never_binary_lhs

end FixedHCFGv44
end LeanCfgProject
