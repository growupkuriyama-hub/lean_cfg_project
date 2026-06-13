import LeanCfgProject.JALC.FullYieldPruningKernel

namespace LeanCfgProject
namespace JALC
namespace FullFrameReachabilityKernel

/-
Frame-reachability kernel for the full all-copy typed refinement.

This module captures reachability inside the productive part of the full
typed refinement.  The key result is that such reachability forces the left and
right frame components of a typed copy to agree with the intended frame of its
underlying label.
-/

universe u v w

open InverseKernel RoundTripKernel
open ReachableProductiveKernel
open FullRefinementKernel FullRefinementLanguageKernel
open FullYieldKernel FullYieldPruningKernel


/-- A typed copy has the correct left and right frame components. -/
def FrameCorrectCopy
    {V : Type u} {M : Type v}
    (T : StateTyping V M)
    (s : TypedState V M) : Prop :=
  s.lt = T.lt s.label ∧ s.rt = T.rt s.label


/--
Reachability in the productive part of the full all-copy typed refinement.

For a binary step to a left child, the right sibling is required to be
productive; for a step to a right child, the left sibling is required to be
productive.  This is the inductive form of reachability after the first
productivity filter has been applied.
-/
inductive ProductiveReachableFull
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    (tau : Sigma → M)
    (G : UntypedStructure V Sigma) :
    TypedState V M → Prop
  | start {r : TypedStartRule V M}
      (h : (fullTypedStructure tau G).start r) :
      ProductiveReachableFull tau G r.state
  | left {r : TypedBinaryRule V M}
      (h : (fullTypedStructure tau G).binary r)
      (parent : ProductiveReachableFull tau G r.parent)
      (right_productive :
        TypedProductive (fullTypedStructure tau G) r.right) :
      ProductiveReachableFull tau G r.left
  | right {r : TypedBinaryRule V M}
      (h : (fullTypedStructure tau G).binary r)
      (parent : ProductiveReachableFull tau G r.parent)
      (left_productive :
        TypedProductive (fullTypedStructure tau G) r.left) :
      ProductiveReachableFull tau G r.right


/--
Reachability in the original structure is preserved as productive-part
reachability of intended copies in the full refinement, provided the original
structure is reduced.
-/
theorem productiveReachableFull_preserved_of_reduced
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    (T : StateTyping V M)
    (tau : Sigma → M)
    (G : UntypedStructure V Sigma)
    (comp : TypingCompatible tau T G)
    (red : UntypedReduced G)
    {X : V}
    (h : UntypedReachable G X) :
    ProductiveReachableFull tau G (intendedCopy T X) := by
  induction h with
  | start hs =>
      exact ProductiveReachableFull.start
        (full_start_contains_intended T tau G comp hs)
  | left hb hp ih =>
      exact ProductiveReachableFull.left
        (full_binary_contains_intended T tau G comp hb)
        ih
        (intendedCopy_full_productive T tau G comp (red.productive _))
  | right hb hp ih =>
      exact ProductiveReachableFull.right
        (full_binary_contains_intended T tau G comp hb)
        ih
        (intendedCopy_full_productive T tau G comp (red.productive _))


/--
In the full refinement, productive-part reachability forces the intended frame.
-/
theorem productiveReachableFull_frame_correct
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    (T : StateTyping V M)
    (tau : Sigma → M)
    (G : UntypedStructure V Sigma)
    (comp : TypingCompatible tau T G)
    (sound : UntypedYieldSound tau T G)
    {s : TypedState V M}
    (h : ProductiveReachableFull tau G s) :
    FrameCorrectCopy T s := by
  induction h with
  | start hs =>
      rcases hs with ⟨r, hr, hstate, hlt, hrt⟩
      rcases comp.start r hr with ⟨hltT, hrtT⟩
      constructor
      · calc
          _ = (1 : M) := hlt
          _ = T.lt r.state := hltT.symm
          _ = T.lt _ := by simpa [hstate]
      · calc
          _ = (1 : M) := hrt
          _ = T.rt r.state := hrtT.symm
          _ = T.rt _ := by simpa [hstate]
  | left hb parent right_productive ih =>
      rcases hb with
        ⟨r, hr, hparent, hleft, hright, hyield,
          hll, hlr, hrl, hrr⟩
      let bc := comp.binary r hr
      have right_yield :
          right_productive.s.yt = T.yt right_productive.s.label := by
        exact full_productive_copy_correct_yield T tau G sound
          right_productive
      have c_lt :
          T.lt right_productive.s.label =
            T.lt right_productive.s.label := rfl
      have parent_lt : parent.s.lt = T.lt parent.s.label := ih.1
      have parent_rt : parent.s.rt = T.rt parent.s.label := ih.2
      have target_lt :
          T.lt parent.s.label = T.lt right_productive.s.label → True := by
        intro _
        trivial
      have compat_left_lt :
          T.lt parent.s.label = T.lt _ := by
        have c := bc.left_left_eq
        simpa [hleft, hparent] using c.symm
      have compat_left_rt :
          T.rt _ = T.yt right_productive.s.label * T.rt parent.s.label := by
        have c := bc.left_right_eq
        simpa [hleft, hright, hparent] using c
      constructor
      · calc
          _ = parent.s.lt := hll
          _ = T.lt parent.s.label := parent_lt
          _ = T.lt _ := compat_left_lt
      · calc
          _ = right_productive.s.yt * parent.s.rt := hlr
          _ = T.yt right_productive.s.label * T.rt parent.s.label := by
              rw [right_yield, parent_rt]
          _ = T.rt _ := compat_left_rt.symm
  | right hb parent left_productive ih =>
      rcases hb with
        ⟨r, hr, hparent, hleft, hright, hyield,
          hll, hlr, hrl, hrr⟩
      let bc := comp.binary r hr
      have left_yield :
          left_productive.s.yt = T.yt left_productive.s.label := by
        exact full_productive_copy_correct_yield T tau G sound
          left_productive
      have parent_lt : parent.s.lt = T.lt parent.s.label := ih.1
      have parent_rt : parent.s.rt = T.rt parent.s.label := ih.2
      have compat_right_lt :
          T.lt _ = T.lt parent.s.label * T.yt left_productive.s.label := by
        have c := bc.right_left_eq
        simpa [hleft, hright, hparent] using c
      have compat_right_rt :
          T.rt parent.s.label = T.rt _ := by
        have c := bc.right_right_eq
        simpa [hright, hparent] using c.symm
      constructor
      · calc
          _ = parent.s.lt * left_productive.s.yt := hrl
          _ = T.lt parent.s.label * T.yt left_productive.s.label := by
              rw [parent_lt, left_yield]
          _ = T.lt _ := compat_right_lt.symm
      · calc
          _ = parent.s.rt := hrr
          _ = T.rt parent.s.label := parent_rt
          _ = T.rt _ := compat_right_rt

end FullFrameReachabilityKernel
end JALC
end LeanCfgProject
