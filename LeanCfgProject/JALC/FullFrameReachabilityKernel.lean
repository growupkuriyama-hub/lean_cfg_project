import LeanCfgProject.JALC.FullYieldPruningKernel

namespace LeanCfgProject
namespace JALC
namespace FullFrameReachabilityKernel

/-
Frame-reachability kernel for the full all-copy typed refinement.

This module captures reachability inside the productive part of the full
typed refinement. The key result is that such reachability forces the left and
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
productive. This is the inductive form of reachability after the first
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


/-- Start-frame correctness for a full-refinement start rule. -/
theorem start_frame_correct
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    (T : StateTyping V M)
    (tau : Sigma → M)
    (G : UntypedStructure V Sigma)
    (comp : TypingCompatible tau T G)
    {sr : TypedStartRule V M}
    (hs : (fullTypedStructure tau G).start sr) :
    FrameCorrectCopy T sr.state := by
  rcases hs with ⟨r, hr, hstate, hlt, hrt⟩
  rcases comp.start r hr with ⟨hltT, hrtT⟩
  constructor
  · calc
      sr.state.lt = (1 : M) := hlt
      _ = T.lt r.state := hltT.symm
      _ = T.lt sr.state.label := by simpa [hstate]
  · calc
      sr.state.rt = (1 : M) := hrt
      _ = T.rt r.state := hrtT.symm
      _ = T.rt sr.state.label := by simpa [hstate]


/-- Left-child frame correctness for a productive binary step. -/
theorem left_frame_correct
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    (T : StateTyping V M)
    (tau : Sigma → M)
    (G : UntypedStructure V Sigma)
    (comp : TypingCompatible tau T G)
    (sound : UntypedYieldSound tau T G)
    {br : TypedBinaryRule V M}
    (hb : (fullTypedStructure tau G).binary br)
    (parent_frame : FrameCorrectCopy T br.parent)
    (right_productive :
      TypedProductive (fullTypedStructure tau G) br.right) :
    FrameCorrectCopy T br.left := by
  rcases hb with
    ⟨r, hr, hparent, hleft, hright, hyield,
      hll, hlr, hrl, hrr⟩
  let bc := comp.binary r hr
  have right_yield :
      br.right.yt = T.yt br.right.label :=
    full_productive_copy_correct_yield T tau G sound right_productive
  have parent_lt : br.parent.lt = T.lt br.parent.label := parent_frame.1
  have parent_rt : br.parent.rt = T.rt br.parent.label := parent_frame.2
  have compat_left_lt :
      T.lt br.parent.label = T.lt br.left.label := by
    have c := bc.left_left_eq.symm
    simpa [hleft, hparent] using c
  have compat_left_rt :
      T.yt br.right.label * T.rt br.parent.label =
        T.rt br.left.label := by
    have c := bc.left_right_eq.symm
    simpa [hleft, hright, hparent] using c
  constructor
  · calc
      br.left.lt = br.parent.lt := hll
      _ = T.lt br.parent.label := parent_lt
      _ = T.lt br.left.label := compat_left_lt
  · calc
      br.left.rt = br.right.yt * br.parent.rt := hlr
      _ = T.yt br.right.label * T.rt br.parent.label := by
          rw [right_yield, parent_rt]
      _ = T.rt br.left.label := compat_left_rt


/-- Right-child frame correctness for a productive binary step. -/
theorem right_frame_correct
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    (T : StateTyping V M)
    (tau : Sigma → M)
    (G : UntypedStructure V Sigma)
    (comp : TypingCompatible tau T G)
    (sound : UntypedYieldSound tau T G)
    {br : TypedBinaryRule V M}
    (hb : (fullTypedStructure tau G).binary br)
    (parent_frame : FrameCorrectCopy T br.parent)
    (left_productive :
      TypedProductive (fullTypedStructure tau G) br.left) :
    FrameCorrectCopy T br.right := by
  rcases hb with
    ⟨r, hr, hparent, hleft, hright, hyield,
      hll, hlr, hrl, hrr⟩
  let bc := comp.binary r hr
  have left_yield :
      br.left.yt = T.yt br.left.label :=
    full_productive_copy_correct_yield T tau G sound left_productive
  have parent_lt : br.parent.lt = T.lt br.parent.label := parent_frame.1
  have parent_rt : br.parent.rt = T.rt br.parent.label := parent_frame.2
  have compat_right_lt :
      T.lt br.parent.label * T.yt br.left.label =
        T.lt br.right.label := by
    have c := bc.right_left_eq.symm
    simpa [hleft, hright, hparent] using c
  have compat_right_rt :
      T.rt br.parent.label = T.rt br.right.label := by
    have c := bc.right_right_eq.symm
    simpa [hright, hparent] using c
  constructor
  · calc
      br.right.lt = br.parent.lt * br.left.yt := hrl
      _ = T.lt br.parent.label * T.yt br.left.label := by
          rw [parent_lt, left_yield]
      _ = T.lt br.right.label := compat_right_lt
  · calc
      br.right.rt = br.parent.rt := hrr
      _ = T.rt br.parent.label := parent_rt
      _ = T.rt br.right.label := compat_right_rt


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
      exact start_frame_correct T tau G comp hs
  | left hb parent right_productive ih =>
      exact left_frame_correct T tau G comp sound hb ih right_productive
  | right hb parent left_productive ih =>
      exact right_frame_correct T tau G comp sound hb ih left_productive

end FullFrameReachabilityKernel
end JALC
end LeanCfgProject
