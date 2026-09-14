import LeanCfgProject.FixedHCFGv44.LinearNormalizationEndToEndV49
import LeanCfgProject.FixedHCFGv44.LinearSpineTypedBridge

namespace LeanCfgProject
namespace FixedHCFGv44

universe u v

/-!
Bridge from the explicit Appendix A normalized SSBNF to the
`TypedLinearSpineShape` certificate consumed by the short-witness and linear
learning theorems.

Yield typing does not alter the underlying nonterminal labels of a binary or
start rule.  Consequently the untyped wrapper/spine shape proved for the
normalized grammar lifts directly to every retained yield-typed rule.
-/

/-- Wrapper and spine are complementary predicates on normalized symbols. -/
theorem isLinearNormSpine_iff_not_wrapper
    {N : Type v} {Sigma : Type u} (X : LinearNormNT N Sigma) :
    IsLinearNormSpine X ↔ ¬ IsLinearNormWrapper X := by
  cases X <;> simp [IsLinearNormSpine, IsLinearNormWrapper]

/-- A normalized symbol is a wrapper iff it is literally one of the shared `W_a`. -/
theorem isLinearNormWrapper_iff
    {N : Type v} {Sigma : Type u} (X : LinearNormNT N Sigma) :
    IsLinearNormWrapper X ↔ ∃ a : Sigma, X = .wrap a := by
  cases X <;> simp [IsLinearNormWrapper]

/-- No retained start target of the normalized source grammar is a wrapper. -/
theorem sourceNormalizedStart_not_wrapper_v49
    {N : Type v} {Sigma : Type u} [Fintype N]
    {sourceRules : List (SourceLinearRule N Sigma)} {S : N}
    {X : LinearNormNT N Sigma}
    (h : SourceNormalizedStartV49 sourceRules S X) :
    ¬ IsLinearNormWrapper X := by
  intro hWrap
  rcases (isLinearNormWrapper_iff X).1 hWrap with ⟨a, rfl⟩
  have hBase : LinearNormStartRules (SourceSeparatedStart S)
      (LinearNormNT.wrap a) := h.1
  exact hBase

/-- No retained binary rule of the normalized source grammar has a wrapper parent. -/
theorem sourceNormalizedBinary_parent_not_wrapper_v49
    {N : Type v} {Sigma : Type u} [Fintype N]
    {sourceRules : List (SourceLinearRule N Sigma)} {S : N}
    {X Y Z : LinearNormNT N Sigma}
    (h : SourceNormalizedBinaryV49 sourceRules S X Y Z) :
    ¬ IsLinearNormWrapper X := by
  intro hWrap
  rcases (isLinearNormWrapper_iff X).1 hWrap with ⟨a, rfl⟩
  exact trimmedLinearNorm_wrapper_never_binary_lhs h

/--
The final normalized grammar automatically supplies the typed single-spine
certificate used by Appendix B and `thm:linear-poly`.
-/
def sourceNormalizedTypedLinearSpineShapeV49
    {N : Type v} {Sigma : Type u} [Fintype N]
    (Obs : Observer Sigma)
    (sourceRules : List (SourceLinearRule N Sigma)) (S : N) :
    TypedLinearSpineShape Obs
      (SourceNormalizedTerminalV49 sourceRules S)
      (SourceNormalizedBinaryV49 sourceRules S)
      (SourceNormalizedStartV49 sourceRules S) where
  isWrapper := fun X => IsLinearNormWrapper X.label
  start_not_wrapper := by
    intro X hStart hWrap
    exact sourceNormalizedStart_not_wrapper_v49 hStart hWrap
  binary_shape := by
    intro X Y Z hRule
    have hParent : ¬ IsLinearNormWrapper X.1.label :=
      sourceNormalizedBinary_parent_not_wrapper_v49 hRule.1
    have hChildren : LinearNormSingleSpineRule Y.1.label Z.1.label :=
      sourceNormalizedBinary_single_spine_v49 hRule.1
    refine ⟨hParent, ?_⟩
    rcases hChildren with hLeft | hRight
    · exact Or.inl ⟨hLeft.1,
        (isLinearNormSpine_iff_not_wrapper Z.1.label).1 hLeft.2⟩
    · exact Or.inr ⟨
        (isLinearNormSpine_iff_not_wrapper Y.1.label).1 hRight.1,
        hRight.2⟩

end FixedHCFGv44
end LeanCfgProject
