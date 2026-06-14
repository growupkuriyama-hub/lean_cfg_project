import LeanCfgProject.JALC.ConcreteTwoStageSearchConsistencyKernel

namespace LeanCfgProject
namespace JALC
namespace PaperFacingConcreteTwoStageSearchConsistency

/-
Paper-facing target for consistency of the concrete two-stage search and the
successful-run certificate object.
-/

universe u v w

open ConcreteBoundedWitnessBridgeKernel
open ConcreteTwoStageBoundedSearchKernel
open ConcreteTwoStageSearchCertificateKernel
open ConcreteTwoStageSearchConsistencyKernel


/-- Paper-facing stored result equation for a search certificate. -/
theorem checked_searchCertificate_result_eq
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    (tau : Sigma → M)
    (G : RoundTripKernel.UntypedStructure V Sigma)
    (C : ConcreteTwoStageSearchCertificate tau G) :
    findConcreteBoundedWitnessData
      tau G C.input C.productive_fuel C.reachable_fuel = some C.result :=
  searchCertificate_result_eq tau G C


/-- Paper-facing certificate existence from a successful search branch. -/
theorem checked_search_some_to_certificate_exists
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    (tau : Sigma → M)
    (G : RoundTripKernel.UntypedStructure V Sigma)
    (input : ConcreteTwoStageBoundedSearchInput tau G)
    (productive_fuel reachable_fuel : Nat)
    {B : ConcreteBoundedWitnessData tau G}
    (h :
      findConcreteBoundedWitnessData
        tau G input productive_fuel reachable_fuel = some B) :
    ∃ C : ConcreteTwoStageSearchCertificate tau G,
      C.input = input ∧
      C.productive_fuel = productive_fuel ∧
      C.reachable_fuel = reachable_fuel ∧
      C.result = B :=
  search_some_to_certificate_exists
    tau G input productive_fuel reachable_fuel h


/-- Paper-facing direct route from a successful search branch to FullKept decidability. -/
theorem checked_search_some_to_certificate_fullKept_decidable
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    [DecidableEq (InverseKernel.TypedState V M)]
    (tau : Sigma → M)
    (G : RoundTripKernel.UntypedStructure V Sigma)
    (input : ConcreteTwoStageBoundedSearchInput tau G)
    (productive_fuel reachable_fuel : Nat)
    {B : ConcreteBoundedWitnessData tau G}
    (h :
      findConcreteBoundedWitnessData
        tau G input productive_fuel reachable_fuel = some B) :
    Nonempty (DecidablePred (FullKeptCorrectnessKernel.FullKept tau G)) :=
  search_some_to_certificate_fullKept_decidable
    tau G input productive_fuel reachable_fuel h


/-- Paper-facing certified extraction from a successful search branch. -/
def checked_certifiedExtraction_of_search_some
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    (tau : Sigma → M)
    (G : RoundTripKernel.UntypedStructure V Sigma)
    (input : ConcreteTwoStageBoundedSearchInput tau G)
    (productive_fuel reachable_fuel : Nat)
    {B : ConcreteBoundedWitnessData tau G}
    (h :
      findConcreteBoundedWitnessData
        tau G input productive_fuel reachable_fuel = some B) :
    AlgorithmicExtractionKernel.CertifiedExtraction
      (FullAlgorithmicAgreementKernel.fullExtractionRuleData tau G) :=
  certifiedExtraction_of_search_some
    tau G input productive_fuel reachable_fuel h


/-- Paper-facing certified-extraction kernel from a successful search branch. -/
theorem checked_certifiedExtraction_of_search_some_kernel
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    (tau : Sigma → M)
    (G : RoundTripKernel.UntypedStructure V Sigma)
    (input : ConcreteTwoStageBoundedSearchInput tau G)
    (productive_fuel reachable_fuel : Nat)
    {B : ConcreteBoundedWitnessData tau G}
    (h :
      findConcreteBoundedWitnessData
        tau G input productive_fuel reachable_fuel = some B) :
    AlgorithmicExtractionKernel.CertifiedExtractionKernel
      (certifiedExtraction_of_search_some
        tau G input productive_fuel reachable_fuel h) :=
  certifiedExtraction_of_search_some_kernel
    tau G input productive_fuel reachable_fuel h

end PaperFacingConcreteTwoStageSearchConsistency
end JALC
end LeanCfgProject
