import LeanCfgProject.JALC.ConcreteTwoStageSearchCertificateKernel

namespace LeanCfgProject
namespace JALC
namespace PaperFacingConcreteTwoStageSearchCertificate

/-
Paper-facing target for successful concrete two-stage search certificates.
-/

universe u v w

open ConcreteTwoStageBoundedSearchKernel
open ConcreteTwoStageSearchCertificateKernel


/-- Paper-facing successful-run certificate type. -/
abbrev CheckedConcreteTwoStageSearchCertificate
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    (tau : Sigma → M)
    (G : RoundTripKernel.UntypedStructure V Sigma) :=
  ConcreteTwoStageSearchCertificate tau G


/-- Paper-facing optional certificate constructor from the two-stage search. -/
def checked_certificateOption_of_search
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    (tau : Sigma → M)
    (G : RoundTripKernel.UntypedStructure V Sigma)
    (input : ConcreteTwoStageBoundedSearchInput tau G)
    (productive_fuel reachable_fuel : Nat) :
    Option (ConcreteTwoStageSearchCertificate tau G) :=
  certificateOption_of_search
    tau G input productive_fuel reachable_fuel


/-- Paper-facing certified extraction from a successful-run certificate. -/
def checked_certifiedExtraction_of_searchCertificate
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    (tau : Sigma → M)
    (G : RoundTripKernel.UntypedStructure V Sigma)
    (C : ConcreteTwoStageSearchCertificate tau G) :
    AlgorithmicExtractionKernel.CertifiedExtraction
      (FullAlgorithmicAgreementKernel.fullExtractionRuleData tau G) :=
  certifiedExtraction_of_searchCertificate tau G C


/-- Paper-facing certified-extraction kernel from a successful-run certificate. -/
theorem checked_searchCertificate_certifiedExtractionKernel
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    (tau : Sigma → M)
    (G : RoundTripKernel.UntypedStructure V Sigma)
    (C : ConcreteTwoStageSearchCertificate tau G) :
    AlgorithmicExtractionKernel.CertifiedExtractionKernel
      (certifiedExtraction_of_searchCertificate tau G C) :=
  searchCertificate_certifiedExtractionKernel tau G C


/-- Paper-facing FullKept decidability from a successful-run certificate. -/
theorem checked_searchCertificate_to_fullKept_decidable
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    [DecidableEq (InverseKernel.TypedState V M)]
    (tau : Sigma → M)
    (G : RoundTripKernel.UntypedStructure V Sigma)
    (C : ConcreteTwoStageSearchCertificate tau G) :
    Nonempty (DecidablePred (FullKeptCorrectnessKernel.FullKept tau G)) :=
  searchCertificate_to_fullKept_decidable tau G C


/-- Paper-facing successful optional-certificate branch. -/
theorem checked_certificateOption_some_to_fullKept_decidable
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    [DecidableEq (InverseKernel.TypedState V M)]
    (tau : Sigma → M)
    (G : RoundTripKernel.UntypedStructure V Sigma)
    (input : ConcreteTwoStageBoundedSearchInput tau G)
    (productive_fuel reachable_fuel : Nat)
    {C : ConcreteTwoStageSearchCertificate tau G}
    (_h :
      certificateOption_of_search
        tau G input productive_fuel reachable_fuel = some C) :
    Nonempty (DecidablePred (FullKeptCorrectnessKernel.FullKept tau G)) :=
  certificateOption_some_to_fullKept_decidable
    tau G input productive_fuel reachable_fuel _h

end PaperFacingConcreteTwoStageSearchCertificate
end JALC
end LeanCfgProject
