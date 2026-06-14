import LeanCfgProject.JALC.ConcreteListStabilityKernel

namespace LeanCfgProject
namespace JALC
namespace BoundedListStabilitySearchKernel

/-
Self-contained bounded search for finite list-stability witnesses.

This version deliberately does not import ListStabilityDecisionKernel.  The
finite decision procedures needed for bounded search are included here, avoiding
an extra file dependency.
-/

universe u v w

open FiniteClosureKernel
open ProductiveReachableClosureKernel
open AlgorithmicExtractionKernel
open FiniteUniverseListEnumerationKernel
open ListStabilityKernel
open ConcreteListStabilityKernel
open ConcreteStepPreservationKernel
open FullAlgorithmicAgreementKernel
open InverseKernel RoundTripKernel


/-- Finite list agreement is decidable when both predicates are decidable. -/
def decidableAgreeOnListForSearch
    {α : Type u}
    (xs : List α)
    (P Q : α → Prop)
    (Pdec : DecidablePred P)
    (Qdec : DecidablePred Q) :
    Decidable (AgreeOnList xs P Q) :=
  match xs with
  | [] =>
      isTrue (by
        intro x hx
        cases hx)
  | a :: rest =>
      letI : Decidable (P a) := Pdec a
      letI : Decidable (Q a) := Qdec a
      match inferInstanceAs (Decidable (P a ↔ Q a)) with
      | isFalse hneq =>
          isFalse (by
            intro h
            exact hneq (h a (List.mem_cons.mpr (Or.inl rfl))))
      | isTrue ha =>
          match decidableAgreeOnListForSearch rest P Q Pdec Qdec with
          | isTrue hrest =>
              isTrue (by
                intro x hx
                have hx' : x = a ∨ x ∈ rest := List.mem_cons.mp hx
                cases hx' with
                | inl heq =>
                    subst x
                    exact ha
                | inr hmem =>
                    exact hrest x hmem)
          | isFalse hbad =>
              isFalse (by
                intro h
                exact hbad (by
                  intro x hx
                  exact h x (List.mem_cons.mpr (Or.inr hx))))


/-- List-stability at a fixed height is decidable from predicate deciders. -/
def decidableListStabilityAtForSearch
    {α : Type u}
    (U : UniverseList α)
    (F : (α → Prop) → α → Prop)
    (n : Nat)
    (nextDec : DecidablePred (F (Iter F n)))
    (iterDec : DecidablePred (Iter F n)) :
    Decidable
      (AgreeOnList U.support
        (F (Iter F n))
        (Iter F n)) :=
  decidableAgreeOnListForSearch U.support
    (F (Iter F n))
    (Iter F n)
    nextDec
    iterDec


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
Search for a list-stability witness up to a given fuel.
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


/-- Productive-step preservation induced by bounded-search data. -/
@[reducible]
def productivePreserves_of_boundedData
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    (tau : Sigma → M)
    (G : UntypedStructure V Sigma)
    (B : ConcreteBoundedSearchData tau G) :
    PreservesDecidablePred (ProductiveFullStep tau G) :=
  productiveStep_preserves_decidable_of_universe
    B.rule_universes.states
    (fullExtractionRuleData tau G).terminal
    (fullExtractionRuleData tau G).binary
    B.rule_decisions.terminal_decidable
    (curriedBinaryDecidable_of_triple
      (fullExtractionRuleData tau G)
      B.rule_decisions.binary_decidable)


/-- Decider for the productive iterate at a chosen height. -/
@[reducible]
def productiveIterDecidableAt
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    (tau : Sigma → M)
    (G : UntypedStructure V Sigma)
    (B : ConcreteBoundedSearchData tau G)
    (productive_height : Nat) :
    DecidablePred
      (Iter (ProductiveFullStep tau G) productive_height) :=
  decidablePred_iter
    (ProductiveFullStep tau G)
    (productivePreserves_of_boundedData tau G B)
    productive_height


/-- Decider for the next productive-stage predicate. -/
@[reducible]
def productiveNextDecidableAt
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    (tau : Sigma → M)
    (G : UntypedStructure V Sigma)
    (B : ConcreteBoundedSearchData tau G)
    (productive_height : Nat) :
    DecidablePred
      (ProductiveFullStep tau G
        (Iter (ProductiveFullStep tau G) productive_height)) :=
  (productivePreserves_of_boundedData tau G B)
    (Iter (ProductiveFullStep tau G) productive_height)
    (productiveIterDecidableAt tau G B productive_height)


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
  decidableListStabilityAtForSearch
    B.rule_universes.states
    (ProductiveFullStep tau G)
    productive_height
    (productiveNextDecidableAt tau G B productive_height)
    (productiveIterDecidableAt tau G B productive_height)


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


/-- Reachable-step preservation induced by bounded-search data. -/
@[reducible]
def reachablePreserves_of_boundedData
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    (tau : Sigma → M)
    (G : UntypedStructure V Sigma)
    (B : ConcreteBoundedSearchData tau G)
    (productive_height : Nat) :
    PreservesDecidablePred
      (ReachableFullStepAt tau G productive_height) :=
  reachableStep_preserves_decidable_of_universe
    B.rule_universes.states
    (fullExtractionRuleData tau G).start
    (fullExtractionRuleData tau G).binary
    (Iter (ProductiveFullStep tau G) productive_height)
    B.rule_decisions.start_decidable
    (curriedBinaryDecidable_of_triple
      (fullExtractionRuleData tau G)
      B.rule_decisions.binary_decidable)
    (productiveIterDecidableAt tau G B productive_height)


/-- Decider for the reachable iterate at a chosen height. -/
@[reducible]
def reachableIterDecidableAt
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    (tau : Sigma → M)
    (G : UntypedStructure V Sigma)
    (B : ConcreteBoundedSearchData tau G)
    (productive_height reachable_height : Nat) :
    DecidablePred
      (Iter (ReachableFullStepAt tau G productive_height) reachable_height) :=
  decidablePred_iter
    (ReachableFullStepAt tau G productive_height)
    (reachablePreserves_of_boundedData tau G B productive_height)
    reachable_height


/-- Decider for the next reachable-stage predicate. -/
@[reducible]
def reachableNextDecidableAt
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    (tau : Sigma → M)
    (G : UntypedStructure V Sigma)
    (B : ConcreteBoundedSearchData tau G)
    (productive_height reachable_height : Nat) :
    DecidablePred
      (ReachableFullStepAt tau G productive_height
        (Iter (ReachableFullStepAt tau G productive_height) reachable_height)) :=
  (reachablePreserves_of_boundedData tau G B productive_height)
    (Iter (ReachableFullStepAt tau G productive_height) reachable_height)
    (reachableIterDecidableAt tau G B productive_height reachable_height)


/-- Decider for reachable list-stability at chosen heights. -/
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
  decidableListStabilityAtForSearch
    B.rule_universes.states
    (ReachableFullStepAt tau G productive_height)
    reachable_height
    (reachableNextDecidableAt tau G B productive_height reachable_height)
    (reachableIterDecidableAt tau G B productive_height reachable_height)


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
