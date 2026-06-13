import LeanCfgProject.JALC.ListCertificateKernel

namespace LeanCfgProject
namespace JALC
namespace ClosureTraceListKernel

/-
Closure trace list certificates.

This module is a small step from list-certified predicates toward a real
fixed-point iterator.  A CertifiedExtraction already contains finite closure
heights.  If a future iterator returns finite lists representing the iterates at
those heights, then this module turns those iterate-list certificates into the
stage-list boundary used by the previous experiment.
-/

universe u v w

open InverseKernel RoundTripKernel
open FiniteClosureKernel
open ProductiveReachableClosureKernel
open AlgorithmicExtractionKernel
open FullAlgorithmicAgreementKernel
open StageDecidabilityKernel
open ListCertificateKernel


/--
List certificate for the productive iterate at the certified productivity
height of a certified extraction.
-/
abbrev ProductiveTraceListCertificate
    {α : Type u}
    {D : ExtractionRuleData α}
    (E : CertifiedExtraction D) :=
  ListPredicateCertificate
    (Iter (ProductiveStep D.terminal D.binary)
      E.productiveCert.height)


/--
List certificate for the reachable iterate at the certified reachability height
of a certified extraction.
-/
abbrev ReachableTraceListCertificate
    {α : Type u}
    {D : ExtractionRuleData α}
    (E : CertifiedExtraction D) :=
  ListPredicateCertificate
    (Iter (ReachableStep D.start D.binary (computedProductive E))
      E.reachableCert.height)


/--
A productive iterate certificate at the certified height is the same predicate
as computedProductive.
-/
def productiveListCertificate_of_trace
    {α : Type u}
    {D : ExtractionRuleData α}
    (E : CertifiedExtraction D)
    (C : ProductiveTraceListCertificate E) :
    ListPredicateCertificate (computedProductive E) :=
  C


/--
A reachable iterate certificate at the certified height is the same predicate
as computedReachable.
-/
def reachableListCertificate_of_trace
    {α : Type u}
    {D : ExtractionRuleData α}
    (E : CertifiedExtraction D)
    (C : ReachableTraceListCertificate E) :
    ListPredicateCertificate (computedReachable E) :=
  C


/--
Trace-list data for the two certified fixed-point stages of Algorithm 1.
-/
structure StageTraceListBoundaryData
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    (tau : Sigma → M)
    (G : UntypedStructure V Sigma) : Type (max u v w) where
  extraction :
    CertifiedExtraction (fullExtractionRuleData tau G)
  productive_trace :
    ProductiveTraceListCertificate extraction
  reachable_trace :
    ReachableTraceListCertificate extraction


/-- Convert trace-list data to the previous stage-list boundary. -/
def stageListBoundary_of_traceListBoundary
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    (tau : Sigma → M)
    (G : UntypedStructure V Sigma)
    (T : StageTraceListBoundaryData tau G) :
    StageListBoundaryData tau G :=
  { extraction := T.extraction,
    productive_list :=
      productiveListCertificate_of_trace T.extraction T.productive_trace,
    reachable_list :=
      reachableListCertificate_of_trace T.extraction T.reachable_trace }


/--
A trace-list boundary supplies FullKept decidability, assuming decidable equality
on typed states.
-/
theorem traceListBoundary_to_fullKept_decidable
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    [DecidableEq (TypedState V M)]
    (tau : Sigma → M)
    (G : UntypedStructure V Sigma)
    (T : StageTraceListBoundaryData tau G) :
    Nonempty (DecidablePred (FullKeptCorrectnessKernel.FullKept tau G)) :=
  stageListBoundary_to_fullKept_decidable tau G
    (stageListBoundary_of_traceListBoundary tau G T)


/--
The productive trace list certificate exposes decidability of computedProductive.
-/
theorem traceListBoundary_productive_decidable
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    [DecidableEq (TypedState V M)]
    (tau : Sigma → M)
    (G : UntypedStructure V Sigma)
    (T : StageTraceListBoundaryData tau G) :
    Nonempty (DecidablePred (computedProductive T.extraction)) :=
  ⟨decidablePred_of_listCertificate
    (productiveListCertificate_of_trace T.extraction T.productive_trace)⟩


/--
The reachable trace list certificate exposes decidability of computedReachable.
-/
theorem traceListBoundary_reachable_decidable
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    [DecidableEq (TypedState V M)]
    (tau : Sigma → M)
    (G : UntypedStructure V Sigma)
    (T : StageTraceListBoundaryData tau G) :
    Nonempty (DecidablePred (computedReachable T.extraction)) :=
  ⟨decidablePred_of_listCertificate
    (reachableListCertificate_of_trace T.extraction T.reachable_trace)⟩

end ClosureTraceListKernel
end JALC
end LeanCfgProject
