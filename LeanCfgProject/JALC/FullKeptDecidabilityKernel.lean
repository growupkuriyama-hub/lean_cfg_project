import LeanCfgProject.JALC.PaperFacingFullAlgorithmicAgreement

namespace LeanCfgProject
namespace JALC
namespace FullKeptDecidabilityKernel

/-
Decidability transfer for FullKept.

A certified run of Algorithm 1 gives a computed kept predicate.  If that
computed predicate is decidable and agrees with FullKept, then FullKept is
decidable as well.  The concrete full all-copy rule data case uses the checked
agreement theorem from FullAlgorithmicAgreementKernel.
-/

universe u v w

open InverseKernel RoundTripKernel
open FullRefinementKernel
open FullYieldKernel
open FullKeptCorrectnessKernel
open AlgorithmicExtractionKernel
open AlgorithmicFullBridgeKernel
open FullAlgorithmicAgreementKernel


/-- Transfer decidability across an agreement proof. -/
def fullKeptDecidable_of_computed
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    {D : ExtractionRuleData (TypedState V M)}
    (E : CertifiedExtraction D)
    (tau : Sigma → M)
    (G : UntypedStructure V Sigma)
    [DecidablePred (computedKept E)]
    (agree : ComputedAgreesWithFullKept E tau G) :
    DecidablePred (FullKept tau G) :=
  fun s =>
    match (inferInstance : Decidable (computedKept E s)) with
    | isTrue h =>
        isTrue ((agree s).1 h)
    | isFalse hnot =>
        isFalse (fun hfull => hnot ((agree s).2 hfull))


/--
For the concrete full all-copy rule data, decidability of the certified computed
predicate supplies decidability of FullKept.
-/
def fullKeptDecidable_of_fullExtraction
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    (tau : Sigma → M)
    (G : UntypedStructure V Sigma)
    (E : CertifiedExtraction (fullExtractionRuleData tau G))
    [DecidablePred (computedKept E)] :
    DecidablePred (FullKept tau G) :=
  fullKeptDecidable_of_computed E tau G
    (fullAlgorithmicComputedKept_agrees tau G E)


/-- Paper-usable marker: FullKept decidability is supplied by a decidable certified run. -/
theorem fullKept_decidable_from_certified_run
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    (tau : Sigma → M)
    (G : UntypedStructure V Sigma)
    (E : CertifiedExtraction (fullExtractionRuleData tau G))
    [DecidablePred (computedKept E)] :
    Nonempty (DecidablePred (FullKept tau G)) :=
  ⟨fullKeptDecidable_of_fullExtraction tau G E⟩

end FullKeptDecidabilityKernel
end JALC
end LeanCfgProject
