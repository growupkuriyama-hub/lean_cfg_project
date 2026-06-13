import LeanCfgProject.JALC.FiniteUniverseListEnumerationKernel

namespace LeanCfgProject
namespace JALC
namespace RulePredicateListCertificateKernel

/-
Rule-predicate list certificates.

Given finite universe lists and decidability of the concrete rule predicates,
this module constructs list certificates for the terminal, start, and binary
predicates of fullExtractionRuleData.
-/

universe u v w

open InverseKernel RoundTripKernel
open AlgorithmicExtractionKernel
open FullAlgorithmicAgreementKernel
open ListCertificateKernel
open FiniteUniverseListEnumerationKernel
open IteratorTraceBoundaryKernel


/-- Decidability payload for the concrete full rule predicates. -/
structure FullRulePredicateDecisions
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    (tau : Sigma → M)
    (G : UntypedStructure V Sigma) : Type (max u v w) where
  terminal_decidable :
    DecidablePred (fullExtractionRuleData tau G).terminal
  start_decidable :
    DecidablePred (fullExtractionRuleData tau G).start
  binary_decidable :
    DecidablePred (binaryTriplePred (fullExtractionRuleData tau G))


/-- Build a terminal-rule list certificate from a complete typed-state list. -/
def terminalListCertificate_of_universe
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    (tau : Sigma → M)
    (G : UntypedStructure V Sigma)
    (U : TypedStateUniverseList V M)
    (D : FullRulePredicateDecisions tau G) :
    ListPredicateCertificate (fullExtractionRuleData tau G).terminal :=
  filteredListCertificate U
    (fullExtractionRuleData tau G).terminal
    D.terminal_decidable


/-- Build a start-rule list certificate from a complete typed-state list. -/
def startListCertificate_of_universe
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    (tau : Sigma → M)
    (G : UntypedStructure V Sigma)
    (U : TypedStateUniverseList V M)
    (D : FullRulePredicateDecisions tau G) :
    ListPredicateCertificate (fullExtractionRuleData tau G).start :=
  filteredListCertificate U
    (fullExtractionRuleData tau G).start
    D.start_decidable


/-- Build a binary-rule list certificate from a complete binary-triple list. -/
def binaryListCertificate_of_universe
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    (tau : Sigma → M)
    (G : UntypedStructure V Sigma)
    (U : BinaryTripleUniverseList V M)
    (D : FullRulePredicateDecisions tau G) :
    ListPredicateCertificate (binaryTriplePred (fullExtractionRuleData tau G)) :=
  filteredListCertificate U
    (binaryTriplePred (fullExtractionRuleData tau G))
    D.binary_decidable


/--
Rule-list certificates obtained by filtering complete finite universe lists.
-/
structure FullRuleListCertificates
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    (tau : Sigma → M)
    (G : UntypedStructure V Sigma) : Type (max u v w) where
  terminal_list :
    ListPredicateCertificate (fullExtractionRuleData tau G).terminal
  start_list :
    ListPredicateCertificate (fullExtractionRuleData tau G).start
  binary_list :
    ListPredicateCertificate (binaryTriplePred (fullExtractionRuleData tau G))


/-- Construct all rule-list certificates from universe lists and decisions. -/
def fullRuleListCertificates_of_universes
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    (tau : Sigma → M)
    (G : UntypedStructure V Sigma)
    (U : FullRuleUniverseLists V M)
    (D : FullRulePredicateDecisions tau G) :
    FullRuleListCertificates tau G :=
  { terminal_list :=
      terminalListCertificate_of_universe tau G U.states D,
    start_list :=
      startListCertificate_of_universe tau G U.states D,
    binary_list :=
      binaryListCertificate_of_universe tau G U.triples D }


/-- Rule-list certificates expose terminal and start decidability. -/
theorem fullRuleListCertificates_terminal_start_decidable
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    [DecidableEq (TypedState V M)]
    (tau : Sigma → M)
    (G : UntypedStructure V Sigma)
    (C : FullRuleListCertificates tau G) :
    Nonempty (DecidablePred (fullExtractionRuleData tau G).terminal) ∧
      Nonempty (DecidablePred (fullExtractionRuleData tau G).start) :=
  ⟨⟨decidablePred_of_listCertificate C.terminal_list⟩,
    ⟨decidablePred_of_listCertificate C.start_list⟩⟩

end RulePredicateListCertificateKernel
end JALC
end LeanCfgProject
