import LeanCfgProject.JALC.PaperFacingFullRefinement

namespace LeanCfgProject
namespace JALC
namespace FullYieldKernel

/-
Yield-type kernels for the full all-copy typed refinement.

This module proves that every typed derivation in the full all-copy refinement
has a terminal word whose finite type equals the yield component of the typed
left-hand state. It also reflects such typed derivations back to untyped
derivations.
-/

universe u v w

open InverseKernel RoundTripKernel
open DerivationLiftKernel StartLanguageKernel
open ReachableProductiveKernel
open FullRefinementKernel FullRefinementLanguageKernel


/-- Word type induced by a terminal type map. -/
def wordType {Sigma : Type w} {M : Type v} [Monoid M]
    (tau : Sigma → M) : List Sigma → M
  | [] => 1
  | a :: rest => tau a * wordType tau rest


/-- Multiplicativity of word type over append. -/
theorem wordType_append
    {Sigma : Type w} {M : Type v} [Monoid M]
    (tau : Sigma → M) :
    ∀ u v : List Sigma,
      wordType tau (u ++ v) = wordType tau u * wordType tau v := by
  intro u v
  induction u with
  | nil =>
      simp [wordType]
  | cons a rest ih =>
      simp [wordType, ih, mul_assoc]


/--
Every full-refinement typed derivation has the yield type indicated by its
typed left-hand state.
-/
theorem full_derivation_yield_type
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    (tau : Sigma → M)
    (G : UntypedStructure V Sigma)
    {s : TypedState V M} {word : List Sigma}
    (d : TypedRuleDeriv (fullTypedStructure tau G) s word) :
    wordType tau word = s.yt := by
  induction d with
  | terminal h =>
      rcases h with ⟨r, hr, hlhs, hterm, hy⟩
      simpa [wordType] using hy
  | binary h left right ihLeft ihRight =>
      rcases h with
        ⟨r, hr, hparent, hleft, hright, hyield,
          hll, hlr, hrl, hrr⟩
      simpa [wordType_append, ihLeft, ihRight] using hyield


/--
Every full-refinement typed derivation reflects to an untyped derivation from
the label of its typed left-hand state.
-/
theorem full_derivation_reflected
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    (tau : Sigma → M)
    (G : UntypedStructure V Sigma)
    {s : TypedState V M} {word : List Sigma}
    (d : TypedRuleDeriv (fullTypedStructure tau G) s word) :
    UntypedDeriv G s.label word := by
  induction d with
  | terminal h =>
      rcases h with ⟨r, hr, hlhs, hterm, hy⟩
      simpa [hlhs, hterm] using UntypedDeriv.terminal hr
  | binary h left right ihLeft ihRight =>
      rcases h with
        ⟨r, hr, hparent, hleft, hright, hyield,
          hll, hlr, hrl, hrr⟩
      simpa [hparent, hleft, hright] using
        (UntypedDeriv.binary hr ihLeft ihRight)


/-- Soundness of an untyped structure with respect to the intended yield map. -/
def UntypedYieldSound
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    (tau : Sigma → M)
    (T : StateTyping V M)
    (G : UntypedStructure V Sigma) : Prop :=
  ∀ {X : V} {word : List Sigma},
    UntypedDeriv G X word → wordType tau word = T.yt X


/-- A typed copy has the correct yield component relative to the intended map. -/
def YieldCorrectCopy
    {V : Type u} {M : Type v}
    (T : StateTyping V M)
    (s : TypedState V M) : Prop :=
  s.yt = T.yt s.label


/--
If the untyped structure is yield-sound, then every productive typed state in
the full all-copy refinement has the correct yield component.
-/
theorem full_productive_copy_correct_yield
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    (T : StateTyping V M)
    (tau : Sigma → M)
    (G : UntypedStructure V Sigma)
    (sound : UntypedYieldSound tau T G)
    {s : TypedState V M}
    (h : TypedProductive (fullTypedStructure tau G) s) :
    YieldCorrectCopy T s := by
  rcases h with ⟨word, d⟩
  have htyped : wordType tau word = s.yt :=
    full_derivation_yield_type tau G d
  have huntyped : UntypedDeriv G s.label word :=
    full_derivation_reflected tau G d
  have hsound : wordType tau word = T.yt s.label :=
    sound huntyped
  exact htyped.symm.trans hsound


/--
Wrong-yield copies are nonproductive in the full all-copy refinement, provided
the original structure is yield-sound.
-/
theorem wrong_yield_copy_not_productive
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    (T : StateTyping V M)
    (tau : Sigma → M)
    (G : UntypedStructure V Sigma)
    (sound : UntypedYieldSound tau T G)
    {s : TypedState V M}
    (hwrong : s.yt ≠ T.yt s.label) :
    ¬ TypedProductive (fullTypedStructure tau G) s := by
  intro hprod
  exact hwrong (full_productive_copy_correct_yield T tau G sound hprod)

end FullYieldKernel
end JALC
end LeanCfgProject
