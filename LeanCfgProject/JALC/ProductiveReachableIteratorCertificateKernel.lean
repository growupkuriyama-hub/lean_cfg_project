import LeanCfgProject.JALC.RulePredicateListCertificateKernel

namespace LeanCfgProject
namespace JALC
namespace ProductiveReachableIteratorCertificateKernel

/-
Productive/reachable iterator certificate boundary.

This module combines rule-list certificates and iterator outputs into the
IteratorTraceBoundaryData payload used by the preceding experiment.
-/

universe u v w

open InverseKernel RoundTripKernel
open AlgorithmicExtractionKernel
open FullAlgorithmicAgreementKernel
open ListCertificateKernel
open ListIterateCertificateKernel
open MonotoneListIteratorKernel
open IteratorTraceBoundaryKernel
open RulePredicateListCertificateKernel


/--
Final pre-implementation payload: rule-list certificates plus iterator outputs
for the productive and reachable closure heights.
-/
structure ProductiveReachableIteratorCertificateData
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    (tau : Sigma → M)
    (G : UntypedStructure V Sigma) : Type (max u v w) where
  extraction :
    CertifiedExtraction (fullExtractionRuleData tau G)
  rule_lists :
    FullRuleListCertificates tau G
  productive_output :
    ProductiveIteratorOutput extraction
  reachable_output :
    ReachableIteratorOutput extraction


/-- Convert the final pre-implementation payload to IteratorTraceBoundaryData. -/
def toIteratorTraceBoundaryData
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    (tau : Sigma → M)
    (G : UntypedStructure V Sigma)
    (B : ProductiveReachableIteratorCertificateData tau G) :
    IteratorTraceBoundaryData tau G :=
  { extraction := B.extraction,
    terminal_list := B.rule_lists.terminal_list,
    start_list := B.rule_lists.start_list,
    binary_list := B.rule_lists.binary_list,
    productive_trace :=
      productiveTrace_of_iterateCertificate B.extraction
        (listIterateCertificate_of_output B.productive_output),
    reachable_trace :=
      reachableTrace_of_iterateCertificate B.extraction
        (listIterateCertificate_of_output B.reachable_output) }


/-- The final pre-implementation payload supplies FullKept decidability. -/
theorem productiveReachableIteratorCertificate_to_fullKept_decidable
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    [DecidableEq (TypedState V M)]
    (tau : Sigma → M)
    (G : UntypedStructure V Sigma)
    (B : ProductiveReachableIteratorCertificateData tau G) :
    Nonempty (DecidablePred (FullKeptCorrectnessKernel.FullKept tau G)) :=
  iteratorTraceBoundary_to_fullKept_decidable_via_trace tau G
    (toIteratorTraceBoundaryData tau G B)


/-- The same payload also reaches FullKept decidability through the rule-list path. -/
theorem productiveReachableIteratorCertificate_to_fullKept_decidable_via_rules
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    [DecidableEq (TypedState V M)]
    (tau : Sigma → M)
    (G : UntypedStructure V Sigma)
    (B : ProductiveReachableIteratorCertificateData tau G) :
    Nonempty (DecidablePred (FullKeptCorrectnessKernel.FullKept tau G)) :=
  iteratorTraceBoundary_to_fullKept_decidable_via_rule_list tau G
    (toIteratorTraceBoundaryData tau G B)


/-- The payload exposes both iterator outputs as iterate-list certificates. -/
theorem productiveReachableIteratorCertificate_stage_lists
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    (tau : Sigma → M)
    (G : UntypedStructure V Sigma)
    (B : ProductiveReachableIteratorCertificateData tau G) :
    Nonempty (ListPredicateCertificate (computedProductive B.extraction)) ∧
      Nonempty (ListPredicateCertificate (computedReachable B.extraction)) :=
  iteratorTraceBoundary_stage_lists tau G
    (toIteratorTraceBoundaryData tau G B)

end ProductiveReachableIteratorCertificateKernel
end JALC
end LeanCfgProject
