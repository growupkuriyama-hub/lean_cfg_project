import LeanCfgProject.JALC.ConcreteTwoStageSearchCertificateKernel

namespace LeanCfgProject
namespace JALC
namespace ConcreteTwoStageSearchConsistencyKernel

/-
Consistency layer for the option-valued concrete two-stage search.

The certificate layer packages a successful `some` branch as an explicit
certificate.  This file records the small but useful round-trip facts connecting
the optional certificate constructor back to the underlying option-valued search.
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
If the optional certificate constructor returns a certificate, then the
underlying two-stage search returned the bounded-witness data stored in that
certificate.
-/
theorem certificateOption_some_result_eq
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    (tau : Sigma → M)
    (G : RoundTripKernel.UntypedStructure V Sigma)
    (input : ConcreteTwoStageBoundedSearchInput tau G)
    (productive_fuel reachable_fuel : Nat)
    {C : ConcreteTwoStageSearchCertificate tau G}
    (_h :
      certificateOption_of_search
        tau G input productive_fuel reachable_fuel = some C) :
    findConcreteBoundedWitnessData
      tau G C.input C.productive_fuel C.reachable_fuel = some C.result :=
  C.result_eq


/--
If the underlying search returns bounded-witness data, then the optional
certificate constructor returns some successful-run certificate.
-/
theorem certificateOption_exists_of_search_some
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
  by
    unfold certificateOption_of_search
    rw [h]
    simp


/--
If the underlying search returns no data, then the optional certificate
constructor returns none.
-/
theorem certificateOption_none_of_search_none
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
  by
    unfold certificateOption_of_search
    rw [h]
    rfl


/--
The optional certificate constructor is complete for successful search branches:
a successful search gives a certificate that routes to FullKept decidability.
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
    rcases
      certificateOption_exists_of_search_some
        tau G input productive_fuel reachable_fuel h with
    | ⟨C, _hC, _hres⟩ =>
        exact searchCertificate_to_fullKept_decidable tau G C

end ConcreteTwoStageSearchConsistencyKernel
end JALC
end LeanCfgProject
