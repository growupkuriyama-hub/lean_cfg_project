import LeanCfgProject.JALC.FullKeptCorrectnessKernel

namespace LeanCfgProject
namespace JALC
namespace PaperFacingFullKept

/-
Paper-facing full kept-correctness checks.
-/

universe u v w

open InverseKernel RoundTripKernel
open ReachableProductiveKernel
open FullRefinementKernel
open FullYieldKernel
open FullFrameReachabilityKernel FullKeptCorrectnessKernel


/-- Paper-facing check: productive-part reachability forces correct frames. -/
theorem checked_productiveReachableFull_frame_correct
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    (T : StateTyping V M)
    (tau : Sigma → M)
    (G : UntypedStructure V Sigma)
    (comp : TypingCompatible tau T G)
    (sound : UntypedYieldSound tau T G)
    {s : TypedState V M}
    (h : ProductiveReachableFull tau G s) :
    FrameCorrectCopy T s :=
  productiveReachableFull_frame_correct T tau G comp sound h


/-- Paper-facing check: full kept copies are fully correct. -/
theorem checked_fullKept_correctCopy
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    (T : StateTyping V M)
    (tau : Sigma → M)
    (G : UntypedStructure V Sigma)
    (comp : TypingCompatible tau T G)
    (sound : UntypedYieldSound tau T G)
    {s : TypedState V M}
    (h : FullKept tau G s) :
    FullCorrectCopy T s :=
  fullKept_correctCopy T tau G comp sound h


/-- Paper-facing check: full kept copies are intended. -/
theorem checked_fullKept_isIntended
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
  fullKept_isIntended T tau G comp sound h


/--
Paper-facing check: full productivity plus productive-part reachability leaves
exactly intended copies.
-/
theorem checked_fullKept_correctness_kernel
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    (T : StateTyping V M)
    (tau : Sigma → M)
    (G : UntypedStructure V Sigma)
    (comp : TypingCompatible tau T G)
    (sound : UntypedYieldSound tau T G)
    (red : UntypedReduced G) :
    (∀ X : V, FullKept tau G (intendedCopy T X)) ∧
      (∀ s : TypedState V M, FullKept tau G s → IsIntended T s) :=
  fullKept_correctness_kernel T tau G comp sound red


/-- Paper-facing check: representation kernel follows from full kept-correctness. -/
theorem checked_representation_from_fullKept_correctness
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    (T : StateTyping V M)
    (tau : Sigma → M)
    (G : UntypedStructure V Sigma)
    (comp : TypingCompatible tau T G)
    (sound : UntypedYieldSound tau T G)
    (red : UntypedReduced G) :
    RepresentationKernel.RepresentationKernel T G (FullKept tau G) :=
  representation_from_fullKept_correctness T tau G comp sound red

end PaperFacingFullKept
end JALC
end LeanCfgProject
