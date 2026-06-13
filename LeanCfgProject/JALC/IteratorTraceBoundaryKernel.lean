import LeanCfgProject.JALC.ClosureTraceListKernel

namespace LeanCfgProject
namespace JALC
namespace IteratorTraceBoundaryKernel

/-
Iterator trace boundary.

This module bundles the finite data that a later iterator should return:
finite list certificates for the concrete rule predicates, plus finite list
certificates for the two certified closure iterates.
-/

universe u v w

open InverseKernel RoundTripKernel
open AlgorithmicExtractionKernel
open FullAlgorithmicAgreementKernel
open ListCertificateKernel
open ClosureTraceListKernel


/--
Combined finite-data payload for the concrete full all-copy extraction.
The rule lists describe the finite rule predicates; the trace lists describe
the two closure iterates used by the certified extraction.
-/
structure IteratorTraceBoundaryData
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    (tau : Sigma → M)
    (G : UntypedStructure V Sigma) : Type (max u v w) where
  extraction :
    CertifiedExtraction (fullExtractionRuleData tau G)
  terminal_list :
    ListPredicateCertificate (fullExtractionRuleData tau G).terminal
  start_list :
    ListPredicateCertificate (fullExtractionRuleData tau G).start
  binary_list :
    ListPredicateCertificate (binaryTriplePred (fullExtractionRuleData tau G))
  productive_trace :
    ProductiveTraceListCertificate extraction
  reachable_trace :
    ReachableTraceListCertificate extraction


/-- Forget the rule lists and keep the two closure trace lists. -/
def toStageTraceListBoundaryData
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    (tau : Sigma → M)
    (G : UntypedStructure V Sigma)
    (B : IteratorTraceBoundaryData tau G) :
    StageTraceListBoundaryData tau G :=
  { extraction := B.extraction,
    productive_trace := B.productive_trace,
    reachable_trace := B.reachable_trace }


/-- Convert iterator trace data to the previous rule-list boundary. -/
def toRuleListBoundaryData
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    (tau : Sigma → M)
    (G : UntypedStructure V Sigma)
    (B : IteratorTraceBoundaryData tau G) :
    RuleListBoundaryData tau G :=
  { extraction := B.extraction,
    terminal_list := B.terminal_list,
    start_list := B.start_list,
    binary_list := B.binary_list,
    productive_list :=
      productiveListCertificate_of_trace B.extraction B.productive_trace,
    reachable_list :=
      reachableListCertificate_of_trace B.extraction B.reachable_trace }


/--
Iterator trace data supplies FullKept decidability via the closure trace-list
path.
-/
theorem iteratorTraceBoundary_to_fullKept_decidable_via_trace
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    [DecidableEq (TypedState V M)]
    (tau : Sigma → M)
    (G : UntypedStructure V Sigma)
    (B : IteratorTraceBoundaryData tau G) :
    Nonempty (DecidablePred (FullKeptCorrectnessKernel.FullKept tau G)) :=
  traceListBoundary_to_fullKept_decidable tau G
    (toStageTraceListBoundaryData tau G B)


/--
Iterator trace data also supplies FullKept decidability via the rule-list
boundary path.
-/
theorem iteratorTraceBoundary_to_fullKept_decidable_via_rule_list
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    [DecidableEq (TypedState V M)]
    (tau : Sigma → M)
    (G : UntypedStructure V Sigma)
    (B : IteratorTraceBoundaryData tau G) :
    Nonempty (DecidablePred (FullKeptCorrectnessKernel.FullKept tau G)) :=
  ruleListBoundary_to_fullKept_decidable tau G
    (toRuleListBoundaryData tau G B)


/--
The two paths give the same kind of output: a decidability package for
FullKept.
-/
theorem iteratorTraceBoundary_two_paths
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    [DecidableEq (TypedState V M)]
    (tau : Sigma → M)
    (G : UntypedStructure V Sigma)
    (B : IteratorTraceBoundaryData tau G) :
    Nonempty (DecidablePred (FullKeptCorrectnessKernel.FullKept tau G)) ∧
      Nonempty (DecidablePred (FullKeptCorrectnessKernel.FullKept tau G)) :=
  ⟨iteratorTraceBoundary_to_fullKept_decidable_via_trace tau G B,
    iteratorTraceBoundary_to_fullKept_decidable_via_rule_list tau G B⟩


/--
Iterator trace data exposes list certificates for both computed stages.
-/
theorem iteratorTraceBoundary_stage_lists
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    (tau : Sigma → M)
    (G : UntypedStructure V Sigma)
    (B : IteratorTraceBoundaryData tau G) :
    Nonempty (ListPredicateCertificate (computedProductive B.extraction)) ∧
      Nonempty (ListPredicateCertificate (computedReachable B.extraction)) :=
  ⟨⟨productiveListCertificate_of_trace B.extraction B.productive_trace⟩,
    ⟨reachableListCertificate_of_trace B.extraction B.reachable_trace⟩⟩

end IteratorTraceBoundaryKernel
end JALC
end LeanCfgProject
