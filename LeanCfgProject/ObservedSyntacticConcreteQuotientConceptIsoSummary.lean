import LeanCfgProject.ObservedSyntacticConcreteQuotientConceptIso

set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace LeanCfgProject

universe u

/-
ObservedSyntacticConcreteQuotientConceptIsoSummary.lean

Theorem-body summary target for the concrete quotient concept-object
round-trip layer.
-/

variable {Q : Type u} [Monoid Q]

/--
Set-level concept-object round-trip package for the concrete observed syntactic
quotient.

This is the checked core needed to upgrade the paper's future target
"Concrete quotient concept-object isomorphism": closed original extents and
closed quotient extents round-trip through image and preimage along the concrete
observed syntactic quotient projection.
-/
theorem concreteObservedSyntacticQuotient_conceptObject_roundtrip_package
    (S : Set Q) :
    (∀ U : Set Q,
      { x : Q |
          observedSyntacticQuotientMap (Q := Q) S x
            ∈
          Set.image (observedSyntacticQuotientMap (Q := Q) S)
            (ConceptClosure S U) }
        =
      ConceptClosure S U)
      ∧
    (∀ U : Set Q,
      IsConceptExtent S U →
      { x : Q |
          observedSyntacticQuotientMap (Q := Q) S x
            ∈
          Set.image (observedSyntacticQuotientMap (Q := Q) S) U }
        =
      U)
      ∧
    (∀ Ubar : Set (ObservedSyntacticQuotient (Q := Q) S),
      Set.image (observedSyntacticQuotientMap (Q := Q) S)
        { x : Q |
            observedSyntacticQuotientMap (Q := Q) S x ∈ Ubar }
        =
      Ubar)
      ∧
    (∀ U : Set Q,
      IsConceptExtent S U →
      IsConceptExtent
        (Set.image (observedSyntacticQuotientMap (Q := Q) S) S)
        (Set.image (observedSyntacticQuotientMap (Q := Q) S) U))
      ∧
    (∀ Ubar : Set (ObservedSyntacticQuotient (Q := Q) S),
      IsConceptExtent
        (Set.image (observedSyntacticQuotientMap (Q := Q) S) S)
        Ubar →
      IsConceptExtent S
        { x : Q |
            observedSyntacticQuotientMap (Q := Q) S x ∈ Ubar }) := by
  constructor
  · intro U
    exact concreteObservedSyntacticQuotient_preimage_image_conceptClosure_eq
      (Q := Q) S U
  constructor
  · intro U hU
    exact concreteObservedSyntacticQuotient_preimage_image_closedExtent_eq
      (Q := Q) S U hU
  constructor
  · intro Ubar
    exact concreteObservedSyntacticQuotient_image_preimage_eq
      (Q := Q) S Ubar
  constructor
  · intro U hU
    exact concreteObservedSyntacticQuotient_image_closedExtent
      (Q := Q) S U hU
  · intro Ubar hUbar
    exact concreteObservedSyntacticQuotient_pullback_closedExtent
      (Q := Q) S Ubar hUbar

/--
Closure-form quotient-side round-trip package.
-/
theorem concreteObservedSyntacticQuotient_closure_roundtrip_package
    (S : Set Q) :
    ∀ Ubar : Set (ObservedSyntacticQuotient (Q := Q) S),
      Set.image (observedSyntacticQuotientMap (Q := Q) S)
        (ConceptClosure S
          { x : Q | observedSyntacticQuotientMap (Q := Q) S x ∈ Ubar })
        =
      ConceptClosure
        (Set.image (observedSyntacticQuotientMap (Q := Q) S) S)
        Ubar := by
  intro Ubar
  exact concreteObservedSyntacticQuotient_image_conceptClosure_preimage_eq
    (Q := Q) S Ubar

end LeanCfgProject
