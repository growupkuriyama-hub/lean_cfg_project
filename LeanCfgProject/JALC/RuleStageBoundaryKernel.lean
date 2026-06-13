import LeanCfgProject.JALC.StagePayloadBridgeKernel

namespace LeanCfgProject
namespace JALC
namespace RuleStageBoundaryKernel

/-
Rule-stage boundary for a later executable implementation.

This module records a slightly richer payload: a certified extraction together
with decidable terminal, binary, and start predicates for the concrete full rule
data, plus decidability of the two computed stages.  The rule-predicate fields
are not used to derive the stage decisions here; deriving them by finite
iteration is exactly the next implementation phase.
-/

universe u v w

open InverseKernel RoundTripKernel
open FullRefinementKernel
open AlgorithmicExtractionKernel
open FullAlgorithmicAgreementKernel
open StageDecidabilityKernel
open StagePayloadBridgeKernel
open AlgorithmicFiniteMainKernel


/--
A boundary payload containing decidable concrete rule predicates and decidable
computed stages.
-/
structure RuleStageBoundaryData
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    (tau : Sigma → M)
    (G : UntypedStructure V Sigma) : Type (max u v w) where
  extraction :
    CertifiedExtraction (fullExtractionRuleData tau G)
  terminal_decidable :
    DecidablePred (fullExtractionRuleData tau G).terminal
  start_decidable :
    DecidablePred (fullExtractionRuleData tau G).start
  binary_decidable :
    ∀ parent left right : TypedState V M,
      Decidable ((fullExtractionRuleData tau G).binary parent left right)
  productive_decidable :
    DecidablePred (computedProductive extraction)
  reachable_decidable :
    DecidablePred (computedReachable extraction)


/-- Forget the rule-predicate part and keep the stage-decidable certified run. -/
def toStageDecidableCertifiedRun
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    (tau : Sigma → M)
    (G : UntypedStructure V Sigma)
    (B : RuleStageBoundaryData tau G) :
    StageDecidableCertifiedRun tau G :=
  { extraction := B.extraction,
    productive_decidable := B.productive_decidable,
    reachable_decidable := B.reachable_decidable }


/-- A rule-stage boundary payload reaches the algorithmic finite-main boundary. -/
theorem ruleStageBoundary_to_algorithmic_finite_boundary
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    (tau : Sigma → M)
    (G : UntypedStructure V Sigma)
    (B : RuleStageBoundaryData tau G) :
    AlgorithmicFiniteMainBoundary tau G B.extraction :=
  stageDecidableRun_to_algorithmic_finite_boundary tau G
    (toStageDecidableCertifiedRun tau G B)


/-- A rule-stage boundary payload supplies FullKept decidability. -/
theorem ruleStageBoundary_to_fullKept_decidable
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    (tau : Sigma → M)
    (G : UntypedStructure V Sigma)
    (B : RuleStageBoundaryData tau G) :
    Nonempty (DecidablePred (FullKeptCorrectnessKernel.FullKept tau G)) :=
  (ruleStageBoundary_to_algorithmic_finite_boundary tau G B).fullkept_decidable


/--
The rule-predicate decisions are explicitly present in the boundary payload.
This theorem records the terminal/start components as a compact pair.
-/
theorem ruleStageBoundary_rule_decisions
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    (tau : Sigma → M)
    (G : UntypedStructure V Sigma)
    (B : RuleStageBoundaryData tau G) :
    Nonempty (DecidablePred (fullExtractionRuleData tau G).terminal) ∧
      Nonempty (DecidablePred (fullExtractionRuleData tau G).start) :=
  ⟨⟨B.terminal_decidable⟩, ⟨B.start_decidable⟩⟩

end RuleStageBoundaryKernel
end JALC
end LeanCfgProject
