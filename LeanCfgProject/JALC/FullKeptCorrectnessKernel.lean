import LeanCfgProject.JALC.FullFrameReachabilityKernel

namespace LeanCfgProject
namespace JALC
namespace FullKeptCorrectnessKernel

/-
Full kept-correctness kernel.

This module combines full-refinement productivity with reachability inside the
productive part.  The result is that kept full-refinement copies are intended
copies, under yield soundness and rule-typing compatibility.
-/

universe u v w

open InverseKernel RoundTripKernel
open ReachableProductiveKernel
open FullRefinementKernel
open FullYieldKernel FullYieldPruningKernel
open FullFrameReachabilityKernel


/-- A copy is fully correct when yield and both frame components are correct. -/
def FullCorrectCopy
    {V : Type u} {M : Type v}
    (T : StateTyping V M)
    (s : TypedState V M) : Prop :=
  YieldCorrectCopy T s ∧ FrameCorrectCopy T s


/-- The full kept predicate after productivity and productive-part reachability. -/
def FullKept
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    (tau : Sigma → M)
    (G : UntypedStructure V Sigma)
    (s : TypedState V M) : Prop :=
  TypedProductive (fullTypedStructure tau G) s ∧
    ProductiveReachableFull tau G s


/-- A fully correct typed copy is an intended copy. -/
theorem fullCorrectCopy_isIntended
    {V : Type u} {M : Type v}
    (T : StateTyping V M)
    {s : TypedState V M}
    (h : FullCorrectCopy T s) :
    IsIntended T s := by
  rcases h with ⟨hy, hlt, hrt⟩
  refine ⟨s.label, ?_⟩
  cases s with
  | mk label yt lt rt =>
      simp [YieldCorrectCopy, FrameCorrectCopy, intendedCopy] at hy hlt hrt ⊢
      cases hy
      cases hlt
      cases hrt
      rfl


/-- Every full kept copy is fully correct. -/
theorem fullKept_correctCopy
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    (T : StateTyping V M)
    (tau : Sigma → M)
    (G : UntypedStructure V Sigma)
    (comp : TypingCompatible tau T G)
    (sound : UntypedYieldSound tau T G)
    {s : TypedState V M}
    (h : FullKept tau G s) :
    FullCorrectCopy T s := by
  exact ⟨full_productive_copy_correct_yield T tau G sound h.1,
    productiveReachableFull_frame_correct T tau G comp sound h.2⟩


/-- Every full kept copy is intended. -/
theorem fullKept_isIntended
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    (T : StateTyping V M)
    (tau : Sigma → M)
    (G : UntypedStructure V Sigma)
    (comp : TypingCompatible tau T G)
    (sound : UntypedYieldSound tau T G)
    {s : TypedState V M}
    (h : FullKept tau G s) :
    IsIntended T s :=
  fullCorrectCopy_isIntended T
    (fullKept_correctCopy T tau G comp sound h)


/-- In a reduced structure, every intended copy is full kept. -/
theorem intendedCopy_fullKept_of_reduced
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    (T : StateTyping V M)
    (tau : Sigma → M)
    (G : UntypedStructure V Sigma)
    (comp : TypingCompatible tau T G)
    (red : UntypedReduced G)
    (X : V) :
    FullKept tau G (intendedCopy T X) := by
  exact ⟨intendedCopy_full_productive T tau G comp (red.productive X),
    productiveReachableFull_preserved_of_reduced T tau G comp red
      (red.reachable X)⟩


/--
Full kept-correctness kernel: in the full all-copy refinement, productivity
followed by productive-part reachability leaves exactly intended copies.
-/
theorem fullKept_correctness_kernel
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    (T : StateTyping V M)
    (tau : Sigma → M)
    (G : UntypedStructure V Sigma)
    (comp : TypingCompatible tau T G)
    (sound : UntypedYieldSound tau T G)
    (red : UntypedReduced G) :
    (∀ X : V, FullKept tau G (intendedCopy T X)) ∧
      (∀ s : TypedState V M, FullKept tau G s → IsIntended T s) := by
  constructor
  · intro X
    exact intendedCopy_fullKept_of_reduced T tau G comp red X
  · intro s h
    exact fullKept_isIntended T tau G comp sound h


/--
Representation kernel obtained from the full kept-correctness statement.
-/
theorem representation_from_fullKept_correctness
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    (T : StateTyping V M)
    (tau : Sigma → M)
    (G : UntypedStructure V Sigma)
    (comp : TypingCompatible tau T G)
    (sound : UntypedYieldSound tau T G)
    (red : UntypedReduced G) :
    RepresentationKernel.RepresentationKernel T G (FullKept tau G) := by
  exact
    RepresentationKernel.representationKernel_from_kept_intended
      T G (FullKept tau G)
      (intendedCopy_fullKept_of_reduced T tau G comp red)
      (fun s h => fullKept_isIntended T tau G comp sound h)

end FullKeptCorrectnessKernel
end JALC
end LeanCfgProject
