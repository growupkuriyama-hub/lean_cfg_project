import LeanCfgProject.JALC.ConcreteTwoStageBoundedSearchKernel

namespace LeanCfgProject
namespace JALC
namespace ConcreteTwoStageSearchCertificateKernel

/-
Successful-run certificate layer for the concrete two-stage bounded search.

The previous target defines an option-valued two-stage search.  This file turns
a successful `some` result into an explicit certificate object and routes that
certificate through the already checked concrete bounded-witness bridge.
-/

universe u v w

open InverseKernel RoundTripKernel
open ConcreteBoundedWitnessBridgeKernel
open ConcreteTwoStageBoundedSearchKernel
open FullAlgorithmicAgreementKernel


/--
A successful run of the concrete two-stage bounded search.

This object records the input, the two fuel bounds, the returned bounded-witness
data, and the equation saying that the option-valued search returned exactly
that data.
-/
structure ConcreteTwoStageSearchCertificate
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    (tau : Sigma → M)
    (G : UntypedStructure V Sigma) :
    Type (max (u + 1) (max (v + 1) (w + 1))) where
  input :
    ConcreteTwoStageBoundedSearchInput tau G
  productive_fuel :
    Nat
  reachable_fuel :
    Nat
  result :
    ConcreteBoundedWitnessData tau G
  result_eq :
    findConcreteBoundedWitnessData
      tau G input productive_fuel reachable_fuel = some result


/-- Build a successful-run certificate from an explicit successful-search equation. -/
def certificate_of_search_eq
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    (tau : Sigma → M)
    (G : UntypedStructure V Sigma)
    (input : ConcreteTwoStageBoundedSearchInput tau G)
    (productive_fuel reachable_fuel : Nat)
    {result : ConcreteBoundedWitnessData tau G}
    (h :
      findConcreteBoundedWitnessData
        tau G input productive_fuel reachable_fuel = some result) :
    ConcreteTwoStageSearchCertificate tau G :=
  { input := input,
    productive_fuel := productive_fuel,
    reachable_fuel := reachable_fuel,
    result := result,
    result_eq := h }


/--
Turn the option-valued search result into an optional successful-run
certificate.
-/
def certificateOption_of_search
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    (tau : Sigma → M)
    (G : UntypedStructure V Sigma)
    (input : ConcreteTwoStageBoundedSearchInput tau G)
    (productive_fuel reachable_fuel : Nat) :
    Option (ConcreteTwoStageSearchCertificate tau G) :=
  match h :
    findConcreteBoundedWitnessData
      tau G input productive_fuel reachable_fuel with
  | none =>
      none
  | some result =>
      some
        { input := input,
          productive_fuel := productive_fuel,
          reachable_fuel := reachable_fuel,
          result := result,
          result_eq := h }


/-- Extract the concrete bounded-witness data from a successful-run certificate. -/
def boundedWitnessData_of_searchCertificate
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    (tau : Sigma → M)
    (G : UntypedStructure V Sigma)
    (C : ConcreteTwoStageSearchCertificate tau G) :
    ConcreteBoundedWitnessData tau G :=
  C.result


/-- A successful-run certificate gives a certified extraction. -/
def certifiedExtraction_of_searchCertificate
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    (tau : Sigma → M)
    (G : UntypedStructure V Sigma)
    (C : ConcreteTwoStageSearchCertificate tau G) :
    AlgorithmicExtractionKernel.CertifiedExtraction
      (fullExtractionRuleData tau G) :=
  certifiedExtraction_of_boundedWitnessData tau G C.result


/-- The certified extraction obtained from a successful run satisfies the kernel. -/
theorem searchCertificate_certifiedExtractionKernel
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    (tau : Sigma → M)
    (G : UntypedStructure V Sigma)
    (C : ConcreteTwoStageSearchCertificate tau G) :
    AlgorithmicExtractionKernel.CertifiedExtractionKernel
      (certifiedExtraction_of_searchCertificate tau G C) :=
  boundedWitnessData_certifiedExtractionKernel tau G C.result


/-- A successful-run certificate supplies FullKept decidability. -/
theorem searchCertificate_to_fullKept_decidable
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    [DecidableEq (InverseKernel.TypedState V M)]
    (tau : Sigma → M)
    (G : UntypedStructure V Sigma)
    (C : ConcreteTwoStageSearchCertificate tau G) :
    Nonempty (DecidablePred (FullKeptCorrectnessKernel.FullKept tau G)) :=
  boundedWitnessData_to_fullKept_decidable tau G C.result


/--
If the optional certificate constructor returns a certificate, that certificate
feeds the FullKept-decidability chain.
-/
theorem certificateOption_some_to_fullKept_decidable
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    [DecidableEq (InverseKernel.TypedState V M)]
    (tau : Sigma → M)
    (G : UntypedStructure V Sigma)
    (input : ConcreteTwoStageBoundedSearchInput tau G)
    (productive_fuel reachable_fuel : Nat)
    {C : ConcreteTwoStageSearchCertificate tau G}
    (_h :
      certificateOption_of_search
        tau G input productive_fuel reachable_fuel = some C) :
    Nonempty (DecidablePred (FullKeptCorrectnessKernel.FullKept tau G)) :=
  searchCertificate_to_fullKept_decidable tau G C

end ConcreteTwoStageSearchCertificateKernel
end JALC
end LeanCfgProject
