import LeanCfgProject.JALC.PaperFacingListStabilityDecision

namespace LeanCfgProject
namespace JALC
namespace BoundedListStabilitySearchKernel

/-
Bounded search for finite list-stability witnesses.
-/

universe u v w

open FiniteClosureKernel
open ProductiveReachableClosureKernel
open AlgorithmicExtractionKernel
open FiniteUniverseListEnumerationKernel
open ListStabilityKernel
open ListStabilityDecisionKernel
open ConcreteListStabilityKernel
open FullAlgorithmicAgreementKernel
open InverseKernel RoundTripKernel


/-- A witness that `F` has stabilized at height `n` on a finite universe list. -/
abbrev ListStabilityWitness
    {α : Type u}
    (U : UniverseList α)
    (F : (α → Prop) → α → Prop) : Type u :=
  Σ n : Nat,
    AgreeOnList U.support
      (F (Iter F n))
      (Iter F n)


/-- Convert a finite list-stability witness into a closure certificate. -/
def closureCertificate_of_listStabilityWitness
    {α : Type u}
    {U : UniverseList α}
    {F : (α → Prop) → α → Prop}
    (W : ListStabilityWitness U F) :
    ClosureCertificate F :=
  closureCertificate_of_listStability U F W.1 W.2


/--
Search for a list-stability witness up to a given fuel.  This is a bounded
search; it does not assert that a witness must be found.
-/
def findListStabilityWitness
    {α : Type u}
    (U : UniverseList α)
    (F : (α → Prop) → α → Prop)
    (dec :
      ∀ n : Nat,
        Decidable
          (AgreeOnList U.support
            (F (Iter F n))
            (Iter F n))) :
    Nat → Option (ListStabilityWitness U F)
  | 0 =>
      match dec 0 with
      | isTrue h =>
          some ⟨0, h⟩
      | isFalse _ =>
          none
  | Nat.succ fuel =>
      match findListStabilityWitness U F dec fuel with
      | some W =>
          some W
      | none =>
          match dec (Nat.succ fuel) with
          | isTrue h =>
              some ⟨Nat.succ fuel, h⟩
          | isFalse _ =>
              none


/-- Concrete finite data used for bounded stability search. -/
structure ConcreteBoundedSearchData
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    (tau : Sigma → M)
    (G : UntypedStructure V Sigma) :
    Type (max u v w) where
  rule_universes :
    FullRuleUniverseLists V M
  rule_decisions :
    FullRulePredicateDecisions tau G


/-- The full productive step for the concrete full rule data. -/
abbrev ProductiveFullStep
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    (tau : Sigma → M)
    (G : UntypedStructure V Sigma) :
    (InverseKernel.TypedState V M → Prop) →
      InverseKernel.TypedState V M → Prop :=
  ProductiveStep
    (fullExtractionRuleData tau G).terminal
    (fullExtractionRuleData tau G).binary


/-- The full reachable step after fixing the productive height. -/
abbrev ReachableFullStepAt
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    (tau : Sigma → M)
    (G : UntypedStructure V Sigma)
    (productive_height : Nat) :
    (InverseKernel.TypedState V M → Prop) →
      InverseKernel.TypedState V M → Prop :=
  ReachableStep
    (fullExtractionRuleData tau G).start
    (fullExtractionRuleData tau G).binary
    (Iter (ProductiveFullStep tau G) productive_height)


/-- Turn bounded-search data into fixed-height decision data. -/
def decisionDataAt
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    (tau : Sigma → M)
    (G : UntypedStructure V Sigma)
    (B : ConcreteBoundedSearchData tau G)
    (productive_height reachable_height : Nat) :
    ConcreteListStabilityDecisionData tau G :=
  { rule_universes := B.rule_universes,
    rule_decisions := B.rule_decisions,
    productive_height := productive_height,
    reachable_height := reachable_height }


/-- Decider for productive list-stability at a chosen height. -/
def productiveStabilityDecidableAt
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    (tau : Sigma → M)
    (G : UntypedStructure V Sigma)
    (B : ConcreteBoundedSearchData tau G)
    (productive_height : Nat) :
    Decidable
      (AgreeOnList B.rule_universes.states.support
        (ProductiveFullStep tau G
          (Iter (ProductiveFullStep tau G) productive_height))
        (Iter (ProductiveFullStep tau G) productive_height)) :=
  productiveListStabilityDecidable tau G
    (decisionDataAt tau G B productive_height 0)


/-- Bounded search for a productive stability witness. -/
def findProductiveStabilityWitness
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    (tau : Sigma → M)
    (G : UntypedStructure V Sigma)
    (B : ConcreteBoundedSearchData tau G)
    (fuel : Nat) :
    Option
      (ListStabilityWitness
        B.rule_universes.states
        (ProductiveFullStep tau G)) :=
  findListStabilityWitness
    B.rule_universes.states
    (ProductiveFullStep tau G)
    (fun n => productiveStabilityDecidableAt tau G B n)
    fuel


/-- Decider for reachable list-stability at chosen productive/reachable heights. -/
def reachableStabilityDecidableAt
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    (tau : Sigma → M)
    (G : UntypedStructure V Sigma)
    (B : ConcreteBoundedSearchData tau G)
    (productive_height reachable_height : Nat) :
    Decidable
      (AgreeOnList B.rule_universes.states.support
        (ReachableFullStepAt tau G productive_height
          (Iter (ReachableFullStepAt tau G productive_height) reachable_height))
        (Iter (ReachableFullStepAt tau G productive_height) reachable_height)) :=
  reachableListStabilityDecidable tau G
    (decisionDataAt tau G B productive_height reachable_height)


/-- Bounded search for a reachable stability witness after fixing productivity. -/
def findReachableStabilityWitness
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    (tau : Sigma → M)
    (G : UntypedStructure V Sigma)
    (B : ConcreteBoundedSearchData tau G)
    (productive_height fuel : Nat) :
    Option
      (ListStabilityWitness
        B.rule_universes.states
        (ReachableFullStepAt tau G productive_height)) :=
  findListStabilityWitness
    B.rule_universes.states
    (ReachableFullStepAt tau G productive_height)
    (fun n => reachableStabilityDecidableAt tau G B productive_height n)
    fuel


/-- A successful two-stage bounded search. -/
structure ConcreteBoundedSearchSuccess
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    (tau : Sigma → M)
    (G : UntypedStructure V Sigma) :
    Type (max u v w) where
  data :
    ConcreteBoundedSearchData tau G
  productive_witness :
    ListStabilityWitness
      data.rule_universes.states
      (ProductiveFullStep tau G)
  reachable_witness :
    ListStabilityWitness
      data.rule_universes.states
      (ReachableFullStepAt tau G productive_witness.1)


/-- Convert a successful bounded search into concrete list-stability data. -/
def concreteListStabilityData_of_boundedSearchSuccess
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    (tau : Sigma → M)
    (G : UntypedStructure V Sigma)
    (S : ConcreteBoundedSearchSuccess tau G) :
    ConcreteListStabilityData tau G :=
  { rule_universes := S.data.rule_universes,
    rule_decisions := S.data.rule_decisions,
    productive_height := S.productive_witness.1,
    productive_stable_on_list := S.productive_witness.2,
    reachable_height := S.reachable_witness.1,
    reachable_stable_on_list := S.reachable_witness.2 }


/-- A successful bounded search supplies FullKept decidability. -/
theorem boundedSearchSuccess_to_fullKept_decidable
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    [DecidableEq (InverseKernel.TypedState V M)]
    (tau : Sigma → M)
    (G : UntypedStructure V Sigma)
    (S : ConcreteBoundedSearchSuccess tau G) :
    Nonempty (DecidablePred (FullKeptCorrectnessKernel.FullKept tau G)) :=
  concreteListStability_to_fullKept_decidable
    tau G
    (concreteListStabilityData_of_boundedSearchSuccess tau G S)

end BoundedListStabilitySearchKernel
end JALC
end LeanCfgProject
