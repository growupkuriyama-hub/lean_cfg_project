import LeanCfgProject.JALC.IteratorTraceBoundaryKernel

namespace LeanCfgProject
namespace JALC
namespace ListIterateCertificateKernel

/-
List certificates for closure iterates.

This module fixes the finite-list interface for the iterates used by a later
iterator.  It does not implement iteration yet; it records how an iterate list
certificate is passed into the existing trace-list boundary.
-/

universe u v w

open InverseKernel RoundTripKernel
open FiniteClosureKernel
open ProductiveReachableClosureKernel
open AlgorithmicExtractionKernel
open FullAlgorithmicAgreementKernel
open ListCertificateKernel
open ClosureTraceListKernel
open IteratorTraceBoundaryKernel


/-- A finite list certificate for the nth iterate of a monotone-style step. -/
abbrev ListIterateCertificate
    {α : Type u}
    (F : (α → Prop) → α → Prop)
    (n : Nat) :=
  ListPredicateCertificate (Iter F n)


/-- Productive iterate list certificate for a certified extraction. -/
abbrev ProductiveIterateCertificate
    {α : Type u}
    {D : ExtractionRuleData α}
    (E : CertifiedExtraction D) :=
  ListIterateCertificate
    (ProductiveStep D.terminal D.binary)
    E.productiveCert.height


/-- Reachable iterate list certificate for a certified extraction. -/
abbrev ReachableIterateCertificate
    {α : Type u}
    {D : ExtractionRuleData α}
    (E : CertifiedExtraction D) :=
  ListIterateCertificate
    (ReachableStep D.start D.binary (computedProductive E))
    E.reachableCert.height


/-- Productive iterate certificates coincide with the previous trace-list certificates. -/
def productiveTrace_of_iterateCertificate
    {α : Type u}
    {D : ExtractionRuleData α}
    (E : CertifiedExtraction D)
    (C : ProductiveIterateCertificate E) :
    ProductiveTraceListCertificate E :=
  C


/-- Reachable iterate certificates coincide with the previous trace-list certificates. -/
def reachableTrace_of_iterateCertificate
    {α : Type u}
    {D : ExtractionRuleData α}
    (E : CertifiedExtraction D)
    (C : ReachableIterateCertificate E) :
    ReachableTraceListCertificate E :=
  C


/--
Finite iterate-list data for the two closure heights of a certified Algorithm 1
run.
-/
structure StageIterateListBoundaryData
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    (tau : Sigma → M)
    (G : UntypedStructure V Sigma) : Type (max u v w) where
  extraction :
    CertifiedExtraction (fullExtractionRuleData tau G)
  productive_iterate :
    ProductiveIterateCertificate extraction
  reachable_iterate :
    ReachableIterateCertificate extraction


/-- Convert iterate-list data to the previous trace-list boundary. -/
def toStageTraceListBoundaryData
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    (tau : Sigma → M)
    (G : UntypedStructure V Sigma)
    (B : StageIterateListBoundaryData tau G) :
    StageTraceListBoundaryData tau G :=
  { extraction := B.extraction,
    productive_trace :=
      productiveTrace_of_iterateCertificate B.extraction B.productive_iterate,
    reachable_trace :=
      reachableTrace_of_iterateCertificate B.extraction B.reachable_iterate }


/-- Iterate-list data supplies FullKept decidability through trace-list data. -/
theorem stageIterateListBoundary_to_fullKept_decidable
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    [DecidableEq (TypedState V M)]
    (tau : Sigma → M)
    (G : UntypedStructure V Sigma)
    (B : StageIterateListBoundaryData tau G) :
    Nonempty (DecidablePred (FullKeptCorrectnessKernel.FullKept tau G)) :=
  traceListBoundary_to_fullKept_decidable tau G
    (toStageTraceListBoundaryData tau G B)


/-- Iterate-list data exposes a productive-stage list certificate. -/
theorem stageIterateListBoundary_productive_list
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    (tau : Sigma → M)
    (G : UntypedStructure V Sigma)
    (B : StageIterateListBoundaryData tau G) :
    Nonempty (ListPredicateCertificate (computedProductive B.extraction)) :=
  ⟨productiveListCertificate_of_trace B.extraction
    (productiveTrace_of_iterateCertificate B.extraction B.productive_iterate)⟩

end ListIterateCertificateKernel
end JALC
end LeanCfgProject
