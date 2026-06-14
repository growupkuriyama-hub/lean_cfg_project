import LeanCfgProject.JALC.ProductiveReachableIteratorCertificateKernel

namespace LeanCfgProject
namespace JALC
namespace IteratorFromDecidableIteratesKernel

/-
Iterator outputs from decidable iterates over a finite universe list.

The previous boundary expected iterator outputs.  This module shows how to
obtain such outputs by filtering a complete finite universe list, once the
target iterate predicates are decidable.  This is a direct step toward an
actual executable iterator.
-/

universe u v w

open InverseKernel RoundTripKernel
open FiniteClosureKernel
open ProductiveReachableClosureKernel
open AlgorithmicExtractionKernel
open FullAlgorithmicAgreementKernel
open ListCertificateKernel
open FiniteUniverseListEnumerationKernel
open MonotoneListIteratorKernel
open RulePredicateListCertificateKernel
open ProductiveReachableIteratorCertificateKernel


/--
From a complete finite universe list and decidability of the nth iterate, build
the list-iterator output for that iterate.
-/
def listIteratorOutput_of_decidableIterate
    {α : Type u}
    (U : UniverseList α)
    (F : (α → Prop) → α → Prop)
    (n : Nat)
    (dec : DecidablePred (Iter F n)) :
    ListIteratorOutput F n :=
  { certificate := filteredListCertificate U (Iter F n) dec }


/--
Finite decision data for the two certified iterates of Algorithm 1.
The rule lists are already supplied; the new data are the finite state universe
and decisions for the productive and reachable iterates at the certified
heights.
-/
structure ProductiveReachableIterateDecisionData
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    (tau : Sigma → M)
    (G : UntypedStructure V Sigma) : Type (max u v w) where
  extraction :
    CertifiedExtraction (fullExtractionRuleData tau G)
  state_universe :
    TypedStateUniverseList V M
  rule_lists :
    FullRuleListCertificates tau G
  productive_iterate_decidable :
    DecidablePred
      (Iter
        (ProductiveStep
          (fullExtractionRuleData tau G).terminal
          (fullExtractionRuleData tau G).binary)
        extraction.productiveCert.height)
  reachable_iterate_decidable :
    DecidablePred
      (Iter
        (ReachableStep
          (fullExtractionRuleData tau G).start
          (fullExtractionRuleData tau G).binary
          (computedProductive extraction))
        extraction.reachableCert.height)


/-- Build the productive iterator output by filtering the finite state universe. -/
def productiveIteratorOutput_of_iterateDecisionData
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    (tau : Sigma → M)
    (G : UntypedStructure V Sigma)
    (D : ProductiveReachableIterateDecisionData tau G) :
    ProductiveIteratorOutput D.extraction :=
  listIteratorOutput_of_decidableIterate D.state_universe
    (ProductiveStep
      (fullExtractionRuleData tau G).terminal
      (fullExtractionRuleData tau G).binary)
    D.extraction.productiveCert.height
    D.productive_iterate_decidable


/-- Build the reachable iterator output by filtering the finite state universe. -/
def reachableIteratorOutput_of_iterateDecisionData
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    (tau : Sigma → M)
    (G : UntypedStructure V Sigma)
    (D : ProductiveReachableIterateDecisionData tau G) :
    ReachableIteratorOutput D.extraction :=
  listIteratorOutput_of_decidableIterate D.state_universe
    (ReachableStep
      (fullExtractionRuleData tau G).start
      (fullExtractionRuleData tau G).binary
      (computedProductive D.extraction))
    D.extraction.reachableCert.height
    D.reachable_iterate_decidable


/--
Convert iterate-decision data into the previous productive/reachable iterator
certificate payload.
-/
def productiveReachableIteratorCertificate_of_iterateDecisionData
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    (tau : Sigma → M)
    (G : UntypedStructure V Sigma)
    (D : ProductiveReachableIterateDecisionData tau G) :
    ProductiveReachableIteratorCertificateData tau G :=
  { extraction := D.extraction,
    rule_lists := D.rule_lists,
    productive_output :=
      productiveIteratorOutput_of_iterateDecisionData tau G D,
    reachable_output :=
      reachableIteratorOutput_of_iterateDecisionData tau G D }


/--
Iterate-decision data supplies FullKept decidability through the existing
productive/reachable iterator certificate boundary.
-/
theorem iterateDecisionData_to_fullKept_decidable
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    [DecidableEq (TypedState V M)]
    (tau : Sigma → M)
    (G : UntypedStructure V Sigma)
    (D : ProductiveReachableIterateDecisionData tau G) :
    Nonempty (DecidablePred (FullKeptCorrectnessKernel.FullKept tau G)) :=
  productiveReachableIteratorCertificate_to_fullKept_decidable tau G
    (productiveReachableIteratorCertificate_of_iterateDecisionData tau G D)


/--
The same data expose both iterator outputs, which are the expected finite outputs
of a later implementation.
-/
theorem iterateDecisionData_outputs_available
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    (tau : Sigma → M)
    (G : UntypedStructure V Sigma)
    (D : ProductiveReachableIterateDecisionData tau G) :
    Nonempty (ProductiveIteratorOutput D.extraction) ∧
      Nonempty (ReachableIteratorOutput D.extraction) :=
  ⟨⟨productiveIteratorOutput_of_iterateDecisionData tau G D⟩,
    ⟨reachableIteratorOutput_of_iterateDecisionData tau G D⟩⟩

end IteratorFromDecidableIteratesKernel
end JALC
end LeanCfgProject
