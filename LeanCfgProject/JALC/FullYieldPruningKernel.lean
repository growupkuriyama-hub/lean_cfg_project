import LeanCfgProject.JALC.FullYieldKernel

namespace LeanCfgProject
namespace JALC
namespace FullYieldPruningKernel

/-
Yield-pruning kernel for the full all-copy typed refinement.

This module packages the first pruning step: productivity in the full
all-copy refinement eliminates all wrong-yield copies, assuming the original
untyped structure is yield-sound.
-/

universe u v w

open InverseKernel RoundTripKernel
open ReachableProductiveKernel
open FullRefinementKernel
open FullYieldKernel


/-- Predicate for copies surviving the yield-correct productivity filter. -/
def YieldProductiveKept
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    (T : StateTyping V M)
    (tau : Sigma → M)
    (G : UntypedStructure V Sigma)
    (s : TypedState V M) : Prop :=
  TypedProductive (fullTypedStructure tau G) s ∧ YieldCorrectCopy T s


/--
Every productive full-refinement copy is in the yield-correct productive
subtype, under untyped yield soundness.
-/
theorem full_productive_implies_yieldProductiveKept
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    (T : StateTyping V M)
    (tau : Sigma → M)
    (G : UntypedStructure V Sigma)
    (sound : UntypedYieldSound tau T G)
    {s : TypedState V M}
    (h : TypedProductive (fullTypedStructure tau G) s) :
    YieldProductiveKept T tau G s := by
  exact ⟨h, full_productive_copy_correct_yield T tau G sound h⟩


/--
The yield-correct productive subtype has the same underlying productive
predicate under untyped yield soundness.
-/
theorem yieldProductiveKept_iff_productive
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    (T : StateTyping V M)
    (tau : Sigma → M)
    (G : UntypedStructure V Sigma)
    (sound : UntypedYieldSound tau T G)
    (s : TypedState V M) :
    YieldProductiveKept T tau G s ↔
      TypedProductive (fullTypedStructure tau G) s := by
  constructor
  · intro h
    exact h.1
  · intro h
    exact full_productive_implies_yieldProductiveKept T tau G sound h


/--
The intended copy of a productive untyped state is productive in the full
all-copy refinement, under rule-typing compatibility.
-/
theorem intendedCopy_full_productive
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    (T : StateTyping V M)
    (tau : Sigma → M)
    (G : UntypedStructure V Sigma)
    (comp : TypingCompatible tau T G)
    {X : V}
    (h : UntypedProductive G X) :
    TypedProductive (fullTypedStructure tau G) (intendedCopy T X) := by
  rcases h with ⟨word, d⟩
  exact ⟨word, FullRefinementLanguageKernel.full_refinement_derivation_preserved
    T tau G comp d⟩


/--
The intended copy of a productive untyped state survives the yield-correct
productivity filter.
-/
theorem intendedCopy_yieldProductiveKept
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    (T : StateTyping V M)
    (tau : Sigma → M)
    (G : UntypedStructure V Sigma)
    (comp : TypingCompatible tau T G)
    {X : V}
    (h : UntypedProductive G X) :
    YieldProductiveKept T tau G (intendedCopy T X) := by
  have hp : TypedProductive (fullTypedStructure tau G) (intendedCopy T X) :=
    intendedCopy_full_productive T tau G comp h
  exact ⟨hp, by simp [YieldCorrectCopy, intendedCopy]⟩

end FullYieldPruningKernel
end JALC
end LeanCfgProject
