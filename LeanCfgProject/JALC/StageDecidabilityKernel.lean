import LeanCfgProject.JALC.FullKeptDecidabilityKernel

namespace LeanCfgProject
namespace JALC
namespace StageDecidabilityKernel

/-
Stage-level decidability for certified Algorithm 1.

The previous closure target showed that decidability of computedKept transfers
to FullKept.  This module reduces that input to decidability of the two computed
stages: computedProductive and computedReachable.
-/

universe u v w

open InverseKernel RoundTripKernel
open FullRefinementKernel
open AlgorithmicExtractionKernel
open FullAlgorithmicAgreementKernel
open FullKeptDecidabilityKernel


/-- Decidability of both computed stages gives decidability of computedKept. -/
@[reducible]
def computedKeptDecidable_of_stages
    {V : Type u} {M : Type v}
    {D : ExtractionRuleData (TypedState V M)}
    (E : CertifiedExtraction D)
    (prodDec : DecidablePred (computedProductive E))
    (reachDec : DecidablePred (computedReachable E)) :
    DecidablePred (computedKept E) :=
  fun s =>
    letI : DecidablePred (computedProductive E) := prodDec
    letI : DecidablePred (computedReachable E) := reachDec
    match (inferInstance : Decidable (computedProductive E s)),
          (inferInstance : Decidable (computedReachable E s)) with
    | isTrue hp, isTrue hr =>
        isTrue ⟨hp, hr⟩
    | isFalse hnp, _ =>
        isFalse (fun h => hnp h.1)
    | _, isFalse hnr =>
        isFalse (fun h => hnr h.2)


/--
For the concrete full rule data, stage decidability supplies FullKept
decidability through the checked Algorithm 1 / FullKept agreement theorem.
-/
theorem fullKept_decidable_of_stage_decidability
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    (tau : Sigma → M)
    (G : UntypedStructure V Sigma)
    (E : CertifiedExtraction (fullExtractionRuleData tau G))
    (prodDec : DecidablePred (computedProductive E))
    (reachDec : DecidablePred (computedReachable E)) :
    Nonempty (DecidablePred (FullKeptCorrectnessKernel.FullKept tau G)) :=
  fullKept_decidable_from_certified_run tau G E
    (computedKeptDecidable_of_stages E prodDec reachDec)


/--
Payload for a certified Algorithm 1 run whose two stages are decidable.
This is a smaller boundary than requiring decidability of computedKept directly.
-/
structure StageDecidableCertifiedRun
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    (tau : Sigma → M)
    (G : UntypedStructure V Sigma) : Type (max u v w) where
  extraction :
    CertifiedExtraction (fullExtractionRuleData tau G)
  productive_decidable :
    DecidablePred (computedProductive extraction)
  reachable_decidable :
    DecidablePred (computedReachable extraction)


/-- A stage-decidable certified run supplies FullKept decidability. -/
theorem stageDecidableRun_fullKept_decidable
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    (tau : Sigma → M)
    (G : UntypedStructure V Sigma)
    (R : StageDecidableCertifiedRun tau G) :
    Nonempty (DecidablePred (FullKeptCorrectnessKernel.FullKept tau G)) :=
  fullKept_decidable_of_stage_decidability tau G R.extraction
    R.productive_decidable R.reachable_decidable


/-- The computed kept predicate is decidable for a stage-decidable run. -/
theorem stageDecidableRun_computedKept_decidable
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    (tau : Sigma → M)
    (G : UntypedStructure V Sigma)
    (R : StageDecidableCertifiedRun tau G) :
    Nonempty (DecidablePred (computedKept R.extraction)) :=
  ⟨computedKeptDecidable_of_stages R.extraction
    R.productive_decidable R.reachable_decidable⟩

end StageDecidabilityKernel
end JALC
end LeanCfgProject
