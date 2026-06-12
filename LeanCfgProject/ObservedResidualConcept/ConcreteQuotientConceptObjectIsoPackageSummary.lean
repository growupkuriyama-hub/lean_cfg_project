import LeanCfgProject.ObservedResidualConcept.ConcreteQuotientConceptObjectIsoPackage
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace LeanCfgProject

universe u

/-
ConcreteQuotientConceptObjectIsoPackageSummary.lean

Top-level target for the bundled concrete observed quotient concept-object
order / closure / product isomorphism package.
-/

variable {Q : Type u} [Monoid Q]

/--
Paper-facing summary: the concrete observed syntactic quotient induces a
bundled order/closure/product isomorphism core for concept objects.
-/
theorem concreteObservedSyntacticQuotient_bundledIso_available
    (S : Set Q) :
    ∃ P : ConcreteQuotientConceptObjectIsoPackage (Q := Q) S,
      P.toSet = concreteQuotientConceptTo (Q := Q) S
        ∧
      P.fromSet = concreteQuotientConceptFrom (Q := Q) S
        ∧
      (∀ U : Set Q,
        IsConceptExtent S U →
        P.fromSet (P.toSet U) = U)
        ∧
      (∀ Ubar : Set (ObservedSyntacticQuotient (Q := Q) S),
        IsConceptExtent (concreteObservedQuotientObservedSet (Q := Q) S) Ubar →
        P.toSet (P.fromSet Ubar) = Ubar)
        ∧
      (∀ A B : Set Q,
        P.toSet (ConceptProduct S A B)
          =
        ConceptProduct
          (concreteObservedQuotientObservedSet (Q := Q) S)
          (P.toSet A)
          (P.toSet B)) := by
  refine ⟨concreteObservedSyntacticQuotient_conceptObjectIsoPackage (Q := Q) S, ?_⟩
  constructor
  · rfl
  constructor
  · rfl
  constructor
  · intro U hU
    exact
      (concreteObservedSyntacticQuotient_conceptObjectIsoPackage
        (Q := Q) S).from_to_closed U hU
  constructor
  · intro Ubar hUbar
    exact
      (concreteObservedSyntacticQuotient_conceptObjectIsoPackage
        (Q := Q) S).to_from_closed Ubar hUbar
  · intro A B
    exact
      (concreteObservedSyntacticQuotient_conceptObjectIsoPackage
        (Q := Q) S).product_preserved A B

/--
Order-equivalence summary extracted from the bundle.
-/
theorem concreteObservedSyntacticQuotient_bundledOrder_available
    (S : Set Q) :
    (∀ U V : Set Q,
      IsConceptExtent S U →
      IsConceptExtent S V →
      (concreteQuotientConceptTo (Q := Q) S U
        ⊆
       concreteQuotientConceptTo (Q := Q) S V
        ↔
       U ⊆ V))
      ∧
    (∀ Ubar Vbar : Set (ObservedSyntacticQuotient (Q := Q) S),
      IsConceptExtent (concreteObservedQuotientObservedSet (Q := Q) S) Ubar →
      IsConceptExtent (concreteObservedQuotientObservedSet (Q := Q) S) Vbar →
      (concreteQuotientConceptFrom (Q := Q) S Ubar
        ⊆
       concreteQuotientConceptFrom (Q := Q) S Vbar
        ↔
       Ubar ⊆ Vbar)) := by
  constructor
  · intro U V hU hV
    exact concreteQuotientConceptTo_subset_iff_closed
      (Q := Q) S hU hV
  · intro Ubar Vbar hUbar hVbar
    exact concreteQuotientConceptFrom_subset_iff_closed
      (Q := Q) S hUbar hVbar

end LeanCfgProject
