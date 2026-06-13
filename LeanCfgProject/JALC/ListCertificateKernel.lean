import LeanCfgProject.JALC.RuleStageBoundaryKernel

namespace LeanCfgProject
namespace JALC
namespace ListCertificateKernel

/-
Finite list certificates for predicate decidability.

This is a small step toward an executable fixed-point implementation.  A later
iterator can output a finite list of states together with soundness and
completeness proofs.  Such a list certificate immediately supplies a decidable
predicate.
-/

universe u v w

open InverseKernel RoundTripKernel
open FullRefinementKernel
open AlgorithmicExtractionKernel
open FullAlgorithmicAgreementKernel
open StageDecidabilityKernel
open StagePayloadBridgeKernel
open RuleStageBoundaryKernel


/-- A finite list exactly representing a predicate. -/
structure ListPredicateCertificate {α : Type u} (P : α → Prop) : Type u where
  support : List α
  sound : ∀ {x : α}, x ∈ support → P x
  complete : ∀ {x : α}, P x → x ∈ support


/-- A list certificate gives a decidable predicate, assuming decidable equality. -/
@[reducible]
def decidablePred_of_listCertificate
    {α : Type u} [DecidableEq α] {P : α → Prop}
    (C : ListPredicateCertificate P) :
    DecidablePred P :=
  fun x =>
    if hm : x ∈ C.support then
      isTrue (C.sound hm)
    else
      isFalse (fun hp => hm (C.complete hp))


/-- Triple type for binary rule predicates. -/
abbrev BinaryTriple (V : Type u) (M : Type v) :=
  TypedState V M × TypedState V M × TypedState V M


/-- Turn the curried binary predicate of extraction data into a predicate on triples. -/
def binaryTriplePred
    {V : Type u} {M : Type v}
    (D : ExtractionRuleData (TypedState V M)) :
    BinaryTriple V M → Prop :=
  fun t => D.binary t.1 t.2.1 t.2.2


/-- A list certificate for binary triples gives decidability of the curried binary predicate. -/
def binaryDecidable_of_listCertificate
    {V : Type u} {M : Type v}
    [DecidableEq (TypedState V M)]
    (D : ExtractionRuleData (TypedState V M))
    (C : ListPredicateCertificate (binaryTriplePred D)) :
    ∀ parent left right : TypedState V M,
      Decidable (D.binary parent left right) :=
  fun parent left right =>
    let decTriple :
        DecidablePred (binaryTriplePred D) :=
      decidablePred_of_listCertificate C
    decTriple (parent, left, right)


/--
List-level stage data for a certified run.  The two computed stages are given
by finite list certificates.
-/
structure StageListBoundaryData
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    (tau : Sigma → M)
    (G : UntypedStructure V Sigma) : Type (max u v w) where
  extraction :
    CertifiedExtraction (fullExtractionRuleData tau G)
  productive_list :
    ListPredicateCertificate (computedProductive extraction)
  reachable_list :
    ListPredicateCertificate (computedReachable extraction)


/-- A list-level stage payload gives a stage-decidable certified run. -/
def stageDecidableRun_of_stageListBoundary
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    [DecidableEq (TypedState V M)]
    (tau : Sigma → M)
    (G : UntypedStructure V Sigma)
    (B : StageListBoundaryData tau G) :
    StageDecidableCertifiedRun tau G :=
  { extraction := B.extraction,
    productive_decidable :=
      decidablePred_of_listCertificate B.productive_list,
    reachable_decidable :=
      decidablePred_of_listCertificate B.reachable_list }


/-- A list-level stage payload supplies FullKept decidability. -/
theorem stageListBoundary_to_fullKept_decidable
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    [DecidableEq (TypedState V M)]
    (tau : Sigma → M)
    (G : UntypedStructure V Sigma)
    (B : StageListBoundaryData tau G) :
    Nonempty (DecidablePred (FullKeptCorrectnessKernel.FullKept tau G)) :=
  stageDecidableRun_to_fullKept_decidable tau G
    (stageDecidableRun_of_stageListBoundary tau G B)


/--
List-level rule and stage data.  This is the finite-data interface expected from
a later rule-universe enumerator and fixed-point iterator.
-/
structure RuleListBoundaryData
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
  productive_list :
    ListPredicateCertificate (computedProductive extraction)
  reachable_list :
    ListPredicateCertificate (computedReachable extraction)


/-- Forget rule lists and keep the stage list payload. -/
def toStageListBoundaryData
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    (tau : Sigma → M)
    (G : UntypedStructure V Sigma)
    (B : RuleListBoundaryData tau G) :
    StageListBoundaryData tau G :=
  { extraction := B.extraction,
    productive_list := B.productive_list,
    reachable_list := B.reachable_list }


/-- A rule-list payload gives the previous rule-stage boundary payload. -/
def ruleStageBoundary_of_ruleListBoundary
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    [DecidableEq (TypedState V M)]
    (tau : Sigma → M)
    (G : UntypedStructure V Sigma)
    (B : RuleListBoundaryData tau G) :
    RuleStageBoundaryData tau G :=
  { extraction := B.extraction,
    terminal_decidable :=
      decidablePred_of_listCertificate B.terminal_list,
    start_decidable :=
      decidablePred_of_listCertificate B.start_list,
    binary_decidable :=
      binaryDecidable_of_listCertificate
        (fullExtractionRuleData tau G) B.binary_list,
    productive_decidable :=
      decidablePred_of_listCertificate B.productive_list,
    reachable_decidable :=
      decidablePred_of_listCertificate B.reachable_list }


/-- A rule-list payload supplies FullKept decidability. -/
theorem ruleListBoundary_to_fullKept_decidable
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    [DecidableEq (TypedState V M)]
    (tau : Sigma → M)
    (G : UntypedStructure V Sigma)
    (B : RuleListBoundaryData tau G) :
    Nonempty (DecidablePred (FullKeptCorrectnessKernel.FullKept tau G)) :=
  ruleStageBoundary_to_fullKept_decidable tau G
    (ruleStageBoundary_of_ruleListBoundary tau G B)


/-- The rule-list payload exposes the terminal rule decision through its list certificate. -/
theorem ruleListBoundary_terminal_decidable
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    [DecidableEq (TypedState V M)]
    (tau : Sigma → M)
    (G : UntypedStructure V Sigma)
    (B : RuleListBoundaryData tau G) :
    Nonempty (DecidablePred (fullExtractionRuleData tau G).terminal) :=
  ⟨decidablePred_of_listCertificate B.terminal_list⟩

end ListCertificateKernel
end JALC
end LeanCfgProject
