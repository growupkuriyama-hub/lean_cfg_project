import LeanCfgProject.JALC.ListIterateCertificateKernel

namespace LeanCfgProject
namespace JALC
namespace MonotoneListIteratorKernel

/-
Monotone list-iterator boundary.

This module records the output interface for a later monotone list iterator:
for a step F and height n, the iterator should return a ListIterateCertificate
for Iter F n.
-/

universe u v w

open InverseKernel RoundTripKernel
open FiniteClosureKernel
open ProductiveReachableClosureKernel
open AlgorithmicExtractionKernel
open FullAlgorithmicAgreementKernel
open ListCertificateKernel
open ListIterateCertificateKernel


/-- Output expected from a list iterator for one step and one height. -/
structure ListIteratorOutput
    {α : Type u}
    (F : (α → Prop) → α → Prop)
    (n : Nat) : Type u where
  certificate :
    ListIterateCertificate F n


/-- Extract the certificate from a one-stage iterator output. -/
def listIterateCertificate_of_output
    {α : Type u}
    {F : (α → Prop) → α → Prop}
    {n : Nat}
    (O : ListIteratorOutput F n) :
    ListIterateCertificate F n :=
  O.certificate


/-- Iterator output for the productive closure height of a certified extraction. -/
abbrev ProductiveIteratorOutput
    {α : Type u}
    {D : ExtractionRuleData α}
    (E : CertifiedExtraction D) :=
  ListIteratorOutput
    (ProductiveStep D.terminal D.binary)
    E.productiveCert.height


/-- Iterator output for the reachable closure height of a certified extraction. -/
abbrev ReachableIteratorOutput
    {α : Type u}
    {D : ExtractionRuleData α}
    (E : CertifiedExtraction D) :=
  ListIteratorOutput
    (ReachableStep D.start D.binary (computedProductive E))
    E.reachableCert.height


/--
Two iterator outputs for the certified productive and reachable heights.
-/
structure StageIteratorBoundaryData
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    (tau : Sigma → M)
    (G : UntypedStructure V Sigma) : Type (max u v w) where
  extraction :
    CertifiedExtraction (fullExtractionRuleData tau G)
  productive_output :
    ProductiveIteratorOutput extraction
  reachable_output :
    ReachableIteratorOutput extraction


/-- Convert iterator outputs to iterate-list boundary data. -/
def toStageIterateListBoundaryData
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    (tau : Sigma → M)
    (G : UntypedStructure V Sigma)
    (B : StageIteratorBoundaryData tau G) :
    StageIterateListBoundaryData tau G :=
  { extraction := B.extraction,
    productive_iterate :=
      listIterateCertificate_of_output B.productive_output,
    reachable_iterate :=
      listIterateCertificate_of_output B.reachable_output }


/-- Stage iterator outputs supply FullKept decidability. -/
theorem stageIteratorBoundary_to_fullKept_decidable
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    [DecidableEq (TypedState V M)]
    (tau : Sigma → M)
    (G : UntypedStructure V Sigma)
    (B : StageIteratorBoundaryData tau G) :
    Nonempty (DecidablePred (FullKeptCorrectnessKernel.FullKept tau G)) :=
  stageIterateListBoundary_to_fullKept_decidable tau G
    (toStageIterateListBoundaryData tau G B)


/--
A one-stage iterator output exposes decidability of its represented iterate
predicate.
-/
theorem listIteratorOutput_decidable
    {α : Type u}
    [DecidableEq α]
    {F : (α → Prop) → α → Prop}
    {n : Nat}
    (O : ListIteratorOutput F n) :
    Nonempty (DecidablePred (Iter F n)) :=
  ⟨decidablePred_of_listCertificate O.certificate⟩

end MonotoneListIteratorKernel
end JALC
end LeanCfgProject
