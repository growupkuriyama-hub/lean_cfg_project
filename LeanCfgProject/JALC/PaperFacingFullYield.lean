import LeanCfgProject.JALC.FullYieldPruningKernel

namespace LeanCfgProject
namespace JALC
namespace PaperFacingFullYield

/-
Paper-facing full-yield checks.
-/

universe u v w

open InverseKernel RoundTripKernel
open ReachableProductiveKernel
open FullRefinementKernel
open FullYieldKernel FullYieldPruningKernel


/-- Paper-facing check: full typed derivations have the annotated yield type. -/
theorem checked_full_derivation_yield_type
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    (tau : Sigma → M)
    (G : UntypedStructure V Sigma)
    {s : TypedState V M} {word : List Sigma}
    (d : DerivationLiftKernel.TypedRuleDeriv (fullTypedStructure tau G) s word) :
    wordType tau word = s.yt :=
  full_derivation_yield_type tau G d


/-- Paper-facing check: full typed derivations reflect to untyped derivations. -/
theorem checked_full_derivation_reflected
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    (tau : Sigma → M)
    (G : UntypedStructure V Sigma)
    {s : TypedState V M} {word : List Sigma}
    (d : DerivationLiftKernel.TypedRuleDeriv (fullTypedStructure tau G) s word) :
    DerivationLiftKernel.UntypedDeriv G s.label word :=
  full_derivation_reflected tau G d


/-- Paper-facing check: productive full copies have correct yield. -/
theorem checked_full_productive_copy_correct_yield
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    (T : StateTyping V M)
    (tau : Sigma → M)
    (G : UntypedStructure V Sigma)
    (sound : UntypedYieldSound tau T G)
    {s : TypedState V M}
    (h : TypedProductive (fullTypedStructure tau G) s) :
    YieldCorrectCopy T s :=
  full_productive_copy_correct_yield T tau G sound h


/-- Paper-facing check: wrong-yield full copies are nonproductive. -/
theorem checked_wrong_yield_copy_not_productive
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    (T : StateTyping V M)
    (tau : Sigma → M)
    (G : UntypedStructure V Sigma)
    (sound : UntypedYieldSound tau T G)
    {s : TypedState V M}
    (hwrong : s.yt ≠ T.yt s.label) :
    ¬ TypedProductive (fullTypedStructure tau G) s :=
  wrong_yield_copy_not_productive T tau G sound hwrong


/-- Paper-facing check: the first pruning step is captured by yield correctness. -/
theorem checked_yieldProductiveKept_iff_productive
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    (T : StateTyping V M)
    (tau : Sigma → M)
    (G : UntypedStructure V Sigma)
    (sound : UntypedYieldSound tau T G)
    (s : TypedState V M) :
    YieldProductiveKept T tau G s ↔
      TypedProductive (fullTypedStructure tau G) s :=
  yieldProductiveKept_iff_productive T tau G sound s

end PaperFacingFullYield
end JALC
end LeanCfgProject
