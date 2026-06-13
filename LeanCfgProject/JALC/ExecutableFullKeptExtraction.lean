import LeanCfgProject.JALC.AlgorithmicFiniteMainKernel

namespace LeanCfgProject
namespace JALC
namespace ExecutableFullKeptExtraction

/-
Certificate carrier for an executable extraction phase.

This module does not implement a finite enumerator. Instead, it isolates the
exact certificate payload that an executable phase would need to produce:
a certified Algorithm 1 run over fullExtractionRuleData and decidability of its
computed kept predicate.
-/

universe u v w

open InverseKernel RoundTripKernel
open FullRefinementKernel
open AlgorithmicExtractionKernel
open FullAlgorithmicAgreementKernel
open AlgorithmicFiniteMainKernel


/-- Payload expected from a later executable extraction phase. -/
structure ExecutableFullKeptExtractionData
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    (tau : Sigma → M)
    (G : UntypedStructure V Sigma) : Type (max u v w) where
  extraction :
    CertifiedExtraction (fullExtractionRuleData tau G)
  computed_decidable :
    DecidablePred (computedKept extraction)


/--
A supplied executable-extraction payload gives the algorithmic finite-main
boundary package.
-/
theorem executable_payload_to_algorithmic_finite_boundary
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    (tau : Sigma → M)
    (G : UntypedStructure V Sigma)
    (X : ExecutableFullKeptExtractionData tau G) :
    AlgorithmicFiniteMainBoundary tau G X.extraction :=
  algorithmic_finite_main_boundary tau G X.extraction X.computed_decidable


/-- The current phase has isolated the remaining executable payload. -/
def executable_payload_boundary_recorded : Prop := True

/-- Marker theorem for the executable extraction boundary. -/
theorem checked_executable_payload_boundary :
    executable_payload_boundary_recorded := by
  trivial

end ExecutableFullKeptExtraction
end JALC
end LeanCfgProject
