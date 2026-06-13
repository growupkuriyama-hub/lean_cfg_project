import LeanCfgProject.JALC.FullKeptDecidabilityKernel
import LeanCfgProject.JALC.PaperFacingFullFiniteMain

namespace LeanCfgProject
namespace JALC
namespace AlgorithmicFiniteMainKernel

/-
Algorithmic finite-main boundary.

The completed finite-main theorem package still expects decidability of
FullKept.  The CI #304 agreement theorem allows this boundary to be moved to
the computed kept predicate of a certified Algorithm 1 run.

This module intentionally avoids rebuilding FullFiniteMainKernel.  It records
the exact decidability transfer needed to use that package algorithmically.
-/

universe u v w

open InverseKernel RoundTripKernel
open FullRefinementKernel
open FullYieldKernel
open FullKeptCorrectnessKernel
open AlgorithmicExtractionKernel
open AlgorithmicFullBridgeKernel
open FullAlgorithmicAgreementKernel
open FullKeptDecidabilityKernel


/--
Boundary package: a certified Algorithm 1 run over the concrete full rule data
agrees with FullKept and supplies FullKept decidability when its computed kept
predicate is decidable.
-/
structure AlgorithmicFiniteMainBoundary
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    (tau : Sigma → M)
    (G : UntypedStructure V Sigma)
    (E : CertifiedExtraction (fullExtractionRuleData tau G)) : Prop where
  agreement :
    ComputedAgreesWithFullKept E tau G
  fullkept_decidable :
    Nonempty (DecidablePred (FullKept tau G))


/-- Construct the boundary package from a decidable certified run. -/
theorem algorithmic_finite_main_boundary
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    (tau : Sigma → M)
    (G : UntypedStructure V Sigma)
    (E : CertifiedExtraction (fullExtractionRuleData tau G))
    (dec : DecidablePred (computedKept E)) :
    AlgorithmicFiniteMainBoundary tau G E := by
  exact
    { agreement := fullAlgorithmicComputedKept_agrees tau G E,
      fullkept_decidable :=
        fullKept_decidable_from_certified_run tau G E dec }


/-- Extract the decidability component needed by finite-main theorem packages. -/
theorem algorithmic_finite_main_fullkept_decidable
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    (tau : Sigma → M)
    (G : UntypedStructure V Sigma)
    (E : CertifiedExtraction (fullExtractionRuleData tau G))
    (dec : DecidablePred (computedKept E)) :
    Nonempty (DecidablePred (FullKept tau G)) :=
  (algorithmic_finite_main_boundary tau G E dec).fullkept_decidable


/-- Extract the Algorithm 1 / FullKept agreement component. -/
theorem algorithmic_finite_main_agreement
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    (tau : Sigma → M)
    (G : UntypedStructure V Sigma)
    (E : CertifiedExtraction (fullExtractionRuleData tau G))
    (dec : DecidablePred (computedKept E)) :
    ComputedAgreesWithFullKept E tau G :=
  (algorithmic_finite_main_boundary tau G E dec).agreement

end AlgorithmicFiniteMainKernel
end JALC
end LeanCfgProject
