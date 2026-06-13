import LeanCfgProject.JALC.IntendedCopyEquiv

namespace LeanCfgProject
namespace JALC
namespace RuleLift

/-
Rule-lift summary for the intended-copy construction.

This module packages the preservation and reflection facts already proved for
terminal rules, binary rules, and start declarations.
-/

universe u v w

open InverseKernel RoundTripKernel


/-- Rule preservation and reflection summary for the lifted structure. -/
structure RuleLiftSummary {V : Type u} {M : Type v} {Sigma : Type w}
    (T : StateTyping V M) (G : UntypedStructure V Sigma) : Prop where
  terminal :
    ∀ r : TerminalRule V Sigma,
      (liftStructure T G).terminal (liftTerminal T r) ↔ G.terminal r
  binary :
    ∀ r : BinaryRule V,
      (liftStructure T G).binary (liftBinary T r) ↔ G.binary r
  start :
    ∀ r : StartRule V,
      (liftStructure T G).start (liftStart T r) ↔ G.start r


/-- The intended-copy lift satisfies the rule summary. -/
theorem ruleLiftSummary_holds {V : Type u} {M : Type v} {Sigma : Type w}
    (T : StateTyping V M) (G : UntypedStructure V Sigma) :
    RuleLiftSummary T G := by
  refine ⟨?_, ?_, ?_⟩
  · intro r
    exact terminal_lift_iff T G r
  · intro r
    exact binary_lift_iff T G r
  · intro r
    exact start_lift_iff T G r


/-- Terminal component of the packaged rule-lift summary. -/
theorem ruleLiftSummary_terminal {V : Type u} {M : Type v} {Sigma : Type w}
    (T : StateTyping V M) (G : UntypedStructure V Sigma)
    (r : TerminalRule V Sigma) :
    (liftStructure T G).terminal (liftTerminal T r) ↔ G.terminal r :=
  (ruleLiftSummary_holds T G).terminal r


/-- Binary component of the packaged rule-lift summary. -/
theorem ruleLiftSummary_binary {V : Type u} {M : Type v} {Sigma : Type w}
    (T : StateTyping V M) (G : UntypedStructure V Sigma)
    (r : BinaryRule V) :
    (liftStructure T G).binary (liftBinary T r) ↔ G.binary r :=
  (ruleLiftSummary_holds T G).binary r


/-- Start component of the packaged rule-lift summary. -/
theorem ruleLiftSummary_start {V : Type u} {M : Type v} {Sigma : Type w}
    (T : StateTyping V M) (G : UntypedStructure V Sigma)
    (r : StartRule V) :
    (liftStructure T G).start (liftStart T r) ↔ G.start r :=
  (ruleLiftSummary_holds T G).start r


/-- Combined rule-lift kernel in packaged form. -/
theorem rule_lift_summary_kernel {V : Type u} {M : Type v} {Sigma : Type w}
    (T : StateTyping V M) (G : UntypedStructure V Sigma) :
    RuleLiftSummary T G :=
  ruleLiftSummary_holds T G

end RuleLift
end JALC
end LeanCfgProject
