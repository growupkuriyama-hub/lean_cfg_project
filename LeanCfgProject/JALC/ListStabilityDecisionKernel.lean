import LeanCfgProject.JALC.PaperFacingListStabilityExtraction

namespace LeanCfgProject
namespace JALC
namespace ListStabilityDecisionKernel

/-
Decision procedures for finite list-stability checks.

The previous target showed that list-stability over a complete finite universe
yields a certified extraction.  This module proves that the list-stability
condition itself is decidable once the two predicates are decidable.
-/

universe u v w

open FiniteClosureKernel
open ProductiveReachableClosureKernel
open AlgorithmicExtractionKernel
open FiniteUniverseListEnumerationKernel
open IterDecidabilityKernel
open StepPreservationKernel
open ConcreteStepPreservationKernel
open ListStabilityKernel
open ConcreteListStabilityKernel
open FullAlgorithmicAgreementKernel
open InverseKernel RoundTripKernel


/-- Finite list agreement is decidable when the two predicates are decidable. -/
def decidableAgreeOnList
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
          match decidableAgreeOnList rest P Q Pdec Qdec with
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


/-- List-stability at a fixed height is decidable from the two predicate deciders. -/
def decidableListStabilityAt
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
  decidableAgreeOnList U.support
    (F (Iter F n))
    (Iter F n)
    nextDec
    iterDec


/--
Finite data needed to decide the productive and reachable list-stability checks
at chosen heights.
-/
structure ConcreteListStabilityDecisionData
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    (tau : Sigma → M)
    (G : UntypedStructure V Sigma) :
    Type (max u v w) where
  rule_universes :
    FullRuleUniverseLists V M
  rule_decisions :
    FullRulePredicateDecisions tau G
  productive_height :
    Nat
  reachable_height :
    Nat


/-- Productive-step preservation induced by concrete decision data. -/
@[reducible]
def productivePreserves_of_decisionData
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    (tau : Sigma → M)
    (G : UntypedStructure V Sigma)
    (D : ConcreteListStabilityDecisionData tau G) :
    PreservesDecidablePred
      (ProductiveStep
        (fullExtractionRuleData tau G).terminal
        (fullExtractionRuleData tau G).binary) :=
  productiveStep_preserves_decidable_of_universe
    D.rule_universes.states
    (fullExtractionRuleData tau G).terminal
    (fullExtractionRuleData tau G).binary
    D.rule_decisions.terminal_decidable
    (curriedBinaryDecidable_of_triple
      (fullExtractionRuleData tau G)
      D.rule_decisions.binary_decidable)


/-- Decider for the productive iterate at the chosen height. -/
@[reducible]
def productiveIterDecidable_of_decisionData
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    (tau : Sigma → M)
    (G : UntypedStructure V Sigma)
    (D : ConcreteListStabilityDecisionData tau G) :
    DecidablePred
      (Iter
        (ProductiveStep
          (fullExtractionRuleData tau G).terminal
          (fullExtractionRuleData tau G).binary)
        D.productive_height) :=
  decidablePred_iter
    (ProductiveStep
      (fullExtractionRuleData tau G).terminal
      (fullExtractionRuleData tau G).binary)
    (productivePreserves_of_decisionData tau G D)
    D.productive_height


/-- Decider for the next productive-stage predicate at the chosen height. -/
@[reducible]
def productiveNextDecidable_of_decisionData
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    (tau : Sigma → M)
    (G : UntypedStructure V Sigma)
    (D : ConcreteListStabilityDecisionData tau G) :
    DecidablePred
      (ProductiveStep
        (fullExtractionRuleData tau G).terminal
        (fullExtractionRuleData tau G).binary
        (Iter
          (ProductiveStep
            (fullExtractionRuleData tau G).terminal
            (fullExtractionRuleData tau G).binary)
          D.productive_height)) :=
  (productivePreserves_of_decisionData tau G D)
    (Iter
      (ProductiveStep
        (fullExtractionRuleData tau G).terminal
        (fullExtractionRuleData tau G).binary)
      D.productive_height)
    (productiveIterDecidable_of_decisionData tau G D)


/-- The productive list-stability check is decidable. -/
def productiveListStabilityDecidable
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    (tau : Sigma → M)
    (G : UntypedStructure V Sigma)
    (D : ConcreteListStabilityDecisionData tau G) :
    Decidable
      (AgreeOnList D.rule_universes.states.support
        (ProductiveStep
          (fullExtractionRuleData tau G).terminal
          (fullExtractionRuleData tau G).binary
          (Iter
            (ProductiveStep
              (fullExtractionRuleData tau G).terminal
              (fullExtractionRuleData tau G).binary)
            D.productive_height))
        (Iter
          (ProductiveStep
            (fullExtractionRuleData tau G).terminal
            (fullExtractionRuleData tau G).binary)
          D.productive_height)) :=
  decidableListStabilityAt
    D.rule_universes.states
    (ProductiveStep
      (fullExtractionRuleData tau G).terminal
      (fullExtractionRuleData tau G).binary)
    D.productive_height
    (productiveNextDecidable_of_decisionData tau G D)
    (productiveIterDecidable_of_decisionData tau G D)


/-- Reachable-step preservation induced by concrete decision data. -/
@[reducible]
def reachablePreserves_of_decisionData
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    (tau : Sigma → M)
    (G : UntypedStructure V Sigma)
    (D : ConcreteListStabilityDecisionData tau G) :
    PreservesDecidablePred
      (ReachableStep
        (fullExtractionRuleData tau G).start
        (fullExtractionRuleData tau G).binary
        (Iter
          (ProductiveStep
            (fullExtractionRuleData tau G).terminal
            (fullExtractionRuleData tau G).binary)
          D.productive_height)) :=
  reachableStep_preserves_decidable_of_universe
    D.rule_universes.states
    (fullExtractionRuleData tau G).start
    (fullExtractionRuleData tau G).binary
    (Iter
      (ProductiveStep
        (fullExtractionRuleData tau G).terminal
        (fullExtractionRuleData tau G).binary)
      D.productive_height)
    D.rule_decisions.start_decidable
    (curriedBinaryDecidable_of_triple
      (fullExtractionRuleData tau G)
      D.rule_decisions.binary_decidable)
    (productiveIterDecidable_of_decisionData tau G D)


/-- Decider for the reachable iterate at the chosen height. -/
@[reducible]
def reachableIterDecidable_of_decisionData
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    (tau : Sigma → M)
    (G : UntypedStructure V Sigma)
    (D : ConcreteListStabilityDecisionData tau G) :
    DecidablePred
      (Iter
        (ReachableStep
          (fullExtractionRuleData tau G).start
          (fullExtractionRuleData tau G).binary
          (Iter
            (ProductiveStep
              (fullExtractionRuleData tau G).terminal
              (fullExtractionRuleData tau G).binary)
            D.productive_height))
        D.reachable_height) :=
  decidablePred_iter
    (ReachableStep
      (fullExtractionRuleData tau G).start
      (fullExtractionRuleData tau G).binary
      (Iter
        (ProductiveStep
          (fullExtractionRuleData tau G).terminal
          (fullExtractionRuleData tau G).binary)
        D.productive_height))
    (reachablePreserves_of_decisionData tau G D)
    D.reachable_height


/-- Decider for the next reachable-stage predicate at the chosen height. -/
@[reducible]
def reachableNextDecidable_of_decisionData
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    (tau : Sigma → M)
    (G : UntypedStructure V Sigma)
    (D : ConcreteListStabilityDecisionData tau G) :
    DecidablePred
      (ReachableStep
        (fullExtractionRuleData tau G).start
        (fullExtractionRuleData tau G).binary
        (Iter
          (ProductiveStep
            (fullExtractionRuleData tau G).terminal
            (fullExtractionRuleData tau G).binary)
          D.productive_height)
        (Iter
          (ReachableStep
            (fullExtractionRuleData tau G).start
            (fullExtractionRuleData tau G).binary
            (Iter
              (ProductiveStep
                (fullExtractionRuleData tau G).terminal
                (fullExtractionRuleData tau G).binary)
              D.productive_height))
          D.reachable_height)) :=
  (reachablePreserves_of_decisionData tau G D)
    (Iter
      (ReachableStep
        (fullExtractionRuleData tau G).start
        (fullExtractionRuleData tau G).binary
        (Iter
          (ProductiveStep
            (fullExtractionRuleData tau G).terminal
            (fullExtractionRuleData tau G).binary)
          D.productive_height))
      D.reachable_height)
    (reachableIterDecidable_of_decisionData tau G D)


/-- The reachable list-stability check is decidable. -/
def reachableListStabilityDecidable
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    (tau : Sigma → M)
    (G : UntypedStructure V Sigma)
    (D : ConcreteListStabilityDecisionData tau G) :
    Decidable
      (AgreeOnList D.rule_universes.states.support
        (ReachableStep
          (fullExtractionRuleData tau G).start
          (fullExtractionRuleData tau G).binary
          (Iter
            (ProductiveStep
              (fullExtractionRuleData tau G).terminal
              (fullExtractionRuleData tau G).binary)
            D.productive_height)
          (Iter
            (ReachableStep
              (fullExtractionRuleData tau G).start
              (fullExtractionRuleData tau G).binary
              (Iter
                (ProductiveStep
                  (fullExtractionRuleData tau G).terminal
                  (fullExtractionRuleData tau G).binary)
                D.productive_height))
            D.reachable_height))
        (Iter
          (ReachableStep
            (fullExtractionRuleData tau G).start
            (fullExtractionRuleData tau G).binary
            (Iter
              (ProductiveStep
                (fullExtractionRuleData tau G).terminal
                (fullExtractionRuleData tau G).binary)
              D.productive_height))
          D.reachable_height)) :=
  decidableListStabilityAt
    D.rule_universes.states
    (ReachableStep
      (fullExtractionRuleData tau G).start
      (fullExtractionRuleData tau G).binary
      (Iter
        (ProductiveStep
          (fullExtractionRuleData tau G).terminal
          (fullExtractionRuleData tau G).binary)
        D.productive_height))
    D.reachable_height
    (reachableNextDecidable_of_decisionData tau G D)
    (reachableIterDecidable_of_decisionData tau G D)


/--
A chosen pair of successful stability checks can be converted to the previous
concrete list-stability package.
-/
structure ConcreteListStabilityCheckedData
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    (tau : Sigma → M)
    (G : UntypedStructure V Sigma) :
    Type (max u v w) where
  decision_data :
    ConcreteListStabilityDecisionData tau G
  productive_stable :
    AgreeOnList decision_data.rule_universes.states.support
      (ProductiveStep
        (fullExtractionRuleData tau G).terminal
        (fullExtractionRuleData tau G).binary
        (Iter
          (ProductiveStep
            (fullExtractionRuleData tau G).terminal
            (fullExtractionRuleData tau G).binary)
          decision_data.productive_height))
      (Iter
        (ProductiveStep
          (fullExtractionRuleData tau G).terminal
          (fullExtractionRuleData tau G).binary)
        decision_data.productive_height)
  reachable_stable :
    AgreeOnList decision_data.rule_universes.states.support
      (ReachableStep
        (fullExtractionRuleData tau G).start
        (fullExtractionRuleData tau G).binary
        (Iter
          (ProductiveStep
            (fullExtractionRuleData tau G).terminal
            (fullExtractionRuleData tau G).binary)
          decision_data.productive_height)
        (Iter
          (ReachableStep
            (fullExtractionRuleData tau G).start
            (fullExtractionRuleData tau G).binary
            (Iter
              (ProductiveStep
                (fullExtractionRuleData tau G).terminal
                (fullExtractionRuleData tau G).binary)
              decision_data.productive_height))
          decision_data.reachable_height))
      (Iter
        (ReachableStep
          (fullExtractionRuleData tau G).start
          (fullExtractionRuleData tau G).binary
          (Iter
            (ProductiveStep
              (fullExtractionRuleData tau G).terminal
              (fullExtractionRuleData tau G).binary)
            decision_data.productive_height))
        decision_data.reachable_height)


/-- Convert checked decision data into concrete list-stability data. -/
def concreteListStabilityData_of_checked
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    (tau : Sigma → M)
    (G : UntypedStructure V Sigma)
    (C : ConcreteListStabilityCheckedData tau G) :
    ConcreteListStabilityData tau G :=
  { rule_universes := C.decision_data.rule_universes,
    rule_decisions := C.decision_data.rule_decisions,
    productive_height := C.decision_data.productive_height,
    productive_stable_on_list := C.productive_stable,
    reachable_height := C.decision_data.reachable_height,
    reachable_stable_on_list := C.reachable_stable }


/-- Checked stability data supplies FullKept decidability. -/
theorem checkedListStability_to_fullKept_decidable
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    [DecidableEq (InverseKernel.TypedState V M)]
    (tau : Sigma → M)
    (G : UntypedStructure V Sigma)
    (C : ConcreteListStabilityCheckedData tau G) :
    Nonempty (DecidablePred (FullKeptCorrectnessKernel.FullKept tau G)) :=
  concreteListStability_to_fullKept_decidable
    tau G (concreteListStabilityData_of_checked tau G C)

end ListStabilityDecisionKernel
end JALC
end LeanCfgProject
