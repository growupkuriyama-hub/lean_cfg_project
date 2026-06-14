import LeanCfgProject.JALC.ProductiveReachableStepDecidabilityKernel
import LeanCfgProject.JALC.PaperFacingIteratorFromDecidableIterates

namespace LeanCfgProject
namespace JALC
namespace PaperFacingStepDecidability

/-
Paper-facing target for finite-iterate decidability by step recursion.

This target records that if the productive and reachable steps preserve
decidable predicates, then the certified iterates at their closure heights
produce iterator outputs and reach FullKept decidability.
-/

open IterDecidabilityKernel
open ProductiveReachableStepDecidabilityKernel
open FinalArtifactKernel


/-- The previous final artifact target remains available. -/
theorem checked_previous_final_artifact_from_step_decidability :
    FinalArtifactChecked :=
  final_artifact_checked


/-- Paper-facing generic finite-iterate decidability theorem. -/
theorem checked_decidablePred_iter_nonempty
    {α : Type u}
    (F : (α → Prop) → α → Prop)
    (pres : PreservesDecidablePred F)
    (n : Nat) :
    Nonempty (DecidablePred (FiniteClosureKernel.Iter F n)) :=
  decidablePred_iter_nonempty F pres n


/--
Paper-facing version of the step-decidability data to FullKept decidability
transfer.
-/
theorem checked_stepDecidabilityData_to_fullKept_decidable
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    [DecidableEq (InverseKernel.TypedState V M)]
    (tau : Sigma → M)
    (G : RoundTripKernel.UntypedStructure V Sigma)
    (E : AlgorithmicExtractionKernel.CertifiedExtraction
      (FullAlgorithmicAgreementKernel.fullExtractionRuleData tau G))
    (D : ProductiveReachableStepDecidabilityData tau G E) :
    Nonempty (DecidablePred (FullKeptCorrectnessKernel.FullKept tau G)) :=
  stepDecidabilityData_to_fullKept_decidable tau G E D

end PaperFacingStepDecidability
end JALC
end LeanCfgProject
