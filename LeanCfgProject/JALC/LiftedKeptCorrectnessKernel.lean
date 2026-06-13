import LeanCfgProject.JALC.ReachableProductiveKernel

namespace LeanCfgProject
namespace JALC
namespace LiftedKeptCorrectnessKernel

/-
Kept-correctness kernel for the intended-copy lift.

This is a formal intermediate target for the remaining prose-level theorem.
It proves that, for the intended-copy lifted structure, the states that are both
productive and reachable are exactly the intended copies, provided the original
untyped structure is reduced.
-/

universe u v w

open InverseKernel RoundTripKernel
open ReachableProductiveKernel


/-- The kept predicate obtained by productivity and reachability in the lift. -/
def LiftedKept {V : Type u} {M : Type v} {Sigma : Type w}
    (T : StateTyping V M)
    (G : UntypedStructure V Sigma)
    (s : TypedState V M) : Prop :=
  TypedProductive (liftStructure T G) s ∧
    TypedReachable (liftStructure T G) s


/-- In a reduced structure, every intended copy is kept in the lifted structure. -/
theorem intendedCopy_liftedKept_of_reduced
    {V : Type u} {M : Type v} {Sigma : Type w}
    (T : StateTyping V M)
    (G : UntypedStructure V Sigma)
    (red : UntypedReduced G)
    (X : V) :
    LiftedKept T G (intendedCopy T X) := by
  exact ⟨productive_preserved T G (red.productive X),
    reachable_preserved T G (red.reachable X)⟩


/-- Every kept state of the lifted structure is an intended copy. -/
theorem liftedKept_isIntended
    {V : Type u} {M : Type v} {Sigma : Type w}
    (T : StateTyping V M)
    (G : UntypedStructure V Sigma)
    {s : TypedState V M}
    (h : LiftedKept T G s) :
    IsIntended T s := by
  exact typed_reachable_lifted_is_intended T G h.2


/--
The intended-copy lift satisfies the kept-correctness statement under
untyped reducedness.
-/
theorem liftedKept_correctness_kernel
    {V : Type u} {M : Type v} {Sigma : Type w}
    (T : StateTyping V M)
    (G : UntypedStructure V Sigma)
    (red : UntypedReduced G) :
    (∀ X : V, LiftedKept T G (intendedCopy T X)) ∧
      (∀ s : TypedState V M, LiftedKept T G s → IsIntended T s) := by
  constructor
  · intro X
    exact intendedCopy_liftedKept_of_reduced T G red X
  · intro s h
    exact liftedKept_isIntended T G h


/--
Representation kernel obtained from the lifted kept-correctness statement.
-/
theorem representation_from_liftedKept_correctness
    {V : Type u} {M : Type v} {Sigma : Type w}
    (T : StateTyping V M)
    (G : UntypedStructure V Sigma)
    (red : UntypedReduced G) :
    RepresentationKernel.RepresentationKernel T G (LiftedKept T G) := by
  exact
    RepresentationKernel.representationKernel_from_kept_intended
      T G (LiftedKept T G)
      (intendedCopy_liftedKept_of_reduced T G red)
      (fun s h => liftedKept_isIntended T G h)

end LiftedKeptCorrectnessKernel
end JALC
end LeanCfgProject
