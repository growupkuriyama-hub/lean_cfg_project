import LeanCfgProject.JALC.LiftedKeptCorrectnessKernel

namespace LeanCfgProject
namespace JALC
namespace PaperFacingKeptCorrectness

/-
Paper-facing kept-correctness checks for the intended-copy lift.
-/

universe u v w

open InverseKernel RoundTripKernel
open ReachableProductiveKernel LiftedKeptCorrectnessKernel


/-- Paper-facing check: reachable typed states in the lift are intended. -/
theorem checked_lifted_reachable_is_intended
    {V : Type u} {M : Type v} {Sigma : Type w}
    (T : StateTyping V M)
    (G : UntypedStructure V Sigma)
    {s : TypedState V M}
    (h : TypedReachable (liftStructure T G) s) :
    IsIntended T s :=
  typed_reachable_lifted_is_intended T G h


/-- Paper-facing check: productive typed states in the lift are intended. -/
theorem checked_lifted_productive_is_intended
    {V : Type u} {M : Type v} {Sigma : Type w}
    (T : StateTyping V M)
    (G : UntypedStructure V Sigma)
    {s : TypedState V M}
    (h : TypedProductive (liftStructure T G) s) :
    IsIntended T s :=
  typed_productive_lifted_is_intended T G h


/--
Paper-facing check: under reducedness, kept states in the intended-copy lift
are exactly intended copies.
-/
theorem checked_lifted_kept_correctness_kernel
    {V : Type u} {M : Type v} {Sigma : Type w}
    (T : StateTyping V M)
    (G : UntypedStructure V Sigma)
    (red : UntypedReduced G) :
    (∀ X : V, LiftedKept T G (intendedCopy T X)) ∧
      (∀ s : TypedState V M, LiftedKept T G s → IsIntended T s) :=
  liftedKept_correctness_kernel T G red


/--
Paper-facing check: the representation kernel follows for the kept predicate
given by productivity and reachability in the intended-copy lift.
-/
theorem checked_representation_from_lifted_kept_correctness
    {V : Type u} {M : Type v} {Sigma : Type w}
    (T : StateTyping V M)
    (G : UntypedStructure V Sigma)
    (red : UntypedReduced G) :
    RepresentationKernel.RepresentationKernel T G (LiftedKept T G) :=
  representation_from_liftedKept_correctness T G red

end PaperFacingKeptCorrectness
end JALC
end LeanCfgProject
