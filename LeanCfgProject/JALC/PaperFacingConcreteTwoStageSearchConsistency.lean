import LeanCfgProject.JALC.ConcreteTwoStageSearchConsistencyKernel

namespace LeanCfgProject
namespace JALC
namespace PaperFacingConcreteTwoStageSearchConsistency

/-
Paper-facing target for consistency of the option-valued two-stage search and
its successful-run certificate object.
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


/-- Paper-facing completeness of optional certificate construction on success. -/
theorem checked_certificateOption_exists_of_search_some
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
      certificateOption_of_search
        tau G input productive_fuel reachable_fuel = some C ∧
      C.result = B :=
  certificateOption_exists_of_search_some
    tau G input productive_fuel reachable_fuel h


/-- Paper-facing none branch consistency. -/
theorem checked_certificateOption_none_of_search_none
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    (tau : Sigma → M)
    (G : RoundTripKernel.UntypedStructure V Sigma)
    (input : ConcreteTwoStageBoundedSearchInput tau G)
    (productive_fuel reachable_fuel : Nat)
    (h :
      findConcreteBoundedWitnessData
        tau G input productive_fuel reachable_fuel = none) :
    certificateOption_of_search
      tau G input productive_fuel reachable_fuel = none :=
  certificateOption_none_of_search_none
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

end PaperFacingConcreteTwoStageSearchConsistency
end JALC
end LeanCfgProject
