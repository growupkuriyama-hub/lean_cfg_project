import LeanCfgProject.JALC.ConcreteTwoStageSearchCertificateKernel

namespace LeanCfgProject
namespace JALC
namespace ConcreteTwoStageSearchConsistencyKernel

/-
Consistency layer for the option-valued concrete two-stage search.

The optional certificate constructor in the previous file is implemented by a
dependent match, because the certificate stores the equation witnessing the
successful search result.  To keep this layer robust, the main consistency facts
below avoid rewriting through that dependent match.  Instead, they use the
explicit constructor `certificate_of_search_eq`.
-/

universe u v w

open ConcreteBoundedWitnessBridgeKernel
open ConcreteTwoStageBoundedSearchKernel
open ConcreteTwoStageSearchCertificateKernel


/-- The result equation stored in a successful search certificate. -/
theorem searchCertificate_result_eq
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    (tau : Sigma → M)
    (G : RoundTripKernel.UntypedStructure V Sigma)
    (C : ConcreteTwoStageSearchCertificate tau G) :
    findConcreteBoundedWitnessData
      tau G C.input C.productive_fuel C.reachable_fuel = some C.result :=
  C.result_eq


/--
If the underlying two-stage search returns bounded-witness data, then there is
an explicit successful-run certificate with that result.
-/
theorem search_some_to_certificate_exists
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
  by
    let C :=
      certificate_of_search_eq
        tau G input productive_fuel reachable_fuel h
    exact ⟨C, rfl, rfl, rfl, rfl⟩


/--
The certificate constructed from a successful-search equation stores the same
search equation.
-/
theorem certificate_of_search_eq_result_eq
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
    searchCertificate_result_eq
      tau G
      (certificate_of_search_eq
        tau G input productive_fuel reachable_fuel h) = h :=
  rfl


/--
A successful search branch gives a successful-run certificate, and that
certificate feeds the FullKept-decidability chain.
-/
theorem search_some_to_certificate_fullKept_decidable
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
  by
    let C :=
      certificate_of_search_eq
        tau G input productive_fuel reachable_fuel h
    exact searchCertificate_to_fullKept_decidable tau G C


/--
A successful search branch also gives a certified extraction through the
constructed certificate.
-/
def certifiedExtraction_of_search_some
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
  certifiedExtraction_of_searchCertificate
    tau G
    (certificate_of_search_eq
      tau G input productive_fuel reachable_fuel h)


/--
The certified extraction obtained from a successful search branch satisfies the
certified-extraction kernel.
-/
theorem certifiedExtraction_of_search_some_kernel
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
  searchCertificate_certifiedExtractionKernel
    tau G
    (certificate_of_search_eq
      tau G input productive_fuel reachable_fuel h)

end ConcreteTwoStageSearchConsistencyKernel
end JALC
end LeanCfgProject
