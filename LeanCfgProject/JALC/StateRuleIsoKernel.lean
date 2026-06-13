import LeanCfgProject.JALC.RuleLiftSummary

namespace LeanCfgProject
namespace JALC
namespace StateRuleIsoKernel

/-
State-and-rule kernel for the intended-copy construction.

This module combines the state-level equivalence with the rule preservation
and reflection summary.
-/

universe u v w

open InverseKernel RoundTripKernel IntendedCopyEquiv RuleLift


/-- Packaged state-and-rule kernel for the intended-copy lift. -/
structure StateRuleKernel {V : Type u} {M : Type v} {Sigma : Type w}
    (T : StateTyping V M) (G : UntypedStructure V Sigma) : Prop where
  state_left :
    ∀ X : V,
      intendedSubtypeLabel T (intendedCopyToSubtype T X) = X
  state_right :
    ∀ s : IntendedSubtype T,
      intendedCopyToSubtype T (intendedSubtypeLabel T s) = s
  rules :
    RuleLiftSummary T G


/-- The intended-copy construction satisfies the packaged state-and-rule kernel. -/
theorem stateRuleKernel_holds {V : Type u} {M : Type v} {Sigma : Type w}
    (T : StateTyping V M) (G : UntypedStructure V Sigma) :
    StateRuleKernel T G := by
  refine ⟨?_, ?_, ?_⟩
  · intro X
    exact intendedCopyToSubtype_left_inverse T X
  · intro s
    exact intendedCopyToSubtype_right_inverse T s
  · exact ruleLiftSummary_holds T G


/--
Paper-facing state-and-rule kernel.

This theorem packages the finite-state equivalence and the preservation and
reflection of terminal, binary, and start rules under the intended-copy lift.
-/
theorem state_rule_kernel_for_intended_lift
    {V : Type u} {M : Type v} {Sigma : Type w}
    (T : StateTyping V M) (G : UntypedStructure V Sigma) :
    StateRuleKernel T G :=
  stateRuleKernel_holds T G

end StateRuleIsoKernel
end JALC
end LeanCfgProject
