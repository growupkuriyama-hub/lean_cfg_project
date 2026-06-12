import LeanCfgProject.ObservedResidualConcept.ObservedSyntacticConcreteQuotientConsequences
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace LeanCfgProject

universe u w

/-
ObservedSyntacticConcreteQuotientPaperSummary.lean

Theorem-body summary target.

This packages the concrete quotient type by SameObservedSyntactic S, its
quotient multiplication, exact kernel, residual/concept/product preservation,
and universal property.
-/

variable {Q : Type u} [Monoid Q]

/-- Concrete quotient-map package for the observed syntactic quotient. -/
theorem observedSyntacticConcreteQuotient_map_package
    (S : Set Q) :
    (∀ x y : Q,
      observedSyntacticQuotientMap (Q := Q) S (x * y)
        =
      observedSyntacticQuotientMap (Q := Q) S x
        *
      observedSyntacticQuotientMap (Q := Q) S y)
      ∧
    (observedSyntacticQuotientMap (Q := Q) S 1
      =
      (1 : ObservedSyntacticQuotient (Q := Q) S))
      ∧
    (∀ y : ObservedSyntacticQuotient (Q := Q) S,
      ∃ x : Q, observedSyntacticQuotientMap (Q := Q) S x = y)
      ∧
    (∀ x y : Q,
      observedSyntacticQuotientMap (Q := Q) S x
        =
      observedSyntacticQuotientMap (Q := Q) S y
        ↔
      SameObservedSyntactic S x y) := by
  exact observedSyntacticQuotientMap_exact_package (Q := Q) S

/--
Concrete quotient preservation package for residuals, closures, point concepts,
and concept products.
-/
theorem observedSyntacticConcreteQuotient_preservation_package
    (S : Set Q) :
    (∀ x : Q,
      observedSyntacticQuotientMap (Q := Q) S x
        ∈
      Set.image (observedSyntacticQuotientMap (Q := Q) S) S
        ↔
      x ∈ S)
      ∧
    (∀ a b : Q,
      Set.image (observedSyntacticQuotientMap (Q := Q) S)
        (TwoSidedResidual S a b)
        =
      TwoSidedResidual
        (Set.image (observedSyntacticQuotientMap (Q := Q) S) S)
        (observedSyntacticQuotientMap (Q := Q) S a)
        (observedSyntacticQuotientMap (Q := Q) S b))
      ∧
    (∀ W : Set Q,
      Set.image (observedSyntacticQuotientMap (Q := Q) S)
        (ConceptClosure S W)
        =
      ConceptClosure
        (Set.image (observedSyntacticQuotientMap (Q := Q) S) S)
        (Set.image (observedSyntacticQuotientMap (Q := Q) S) W))
      ∧
    (∀ gamma : Q,
      Set.image (observedSyntacticQuotientMap (Q := Q) S)
        (ConceptClosure S ({gamma} : Set Q))
        =
      ConceptClosure
        (Set.image (observedSyntacticQuotientMap (Q := Q) S) S)
        ({observedSyntacticQuotientMap (Q := Q) S gamma} :
          Set (ObservedSyntacticQuotient (Q := Q) S)))
      ∧
    (∀ A B : Set Q,
      Set.image (observedSyntacticQuotientMap (Q := Q) S)
        (ConceptProduct S A B)
        =
      ConceptProduct
        (Set.image (observedSyntacticQuotientMap (Q := Q) S) S)
        (Set.image (observedSyntacticQuotientMap (Q := Q) S) A)
        (Set.image (observedSyntacticQuotientMap (Q := Q) S) B)) := by
  constructor
  · exact concreteObservedSyntacticQuotient_pullback_eq (Q := Q) S
  constructor
  · intro a b
    exact concreteObservedSyntacticQuotient_residual_image_eq (Q := Q) S a b
  constructor
  · intro W
    exact concreteObservedSyntacticQuotient_conceptClosure_image_eq (Q := Q) S W
  constructor
  · intro gamma
    exact concreteObservedSyntacticQuotient_pointConcept_image_eq (Q := Q) S gamma
  · intro A B
    exact concreteObservedSyntacticQuotient_conceptProduct_image_eq (Q := Q) S A B

/-- Concrete quotient universal-property package. -/
theorem observedSyntacticConcreteQuotient_universal_package
    {R : Type w}
    (S : Set Q)
    (φ : Q → R)
    (hφ : RespectsSameObservedSyntactic S φ) :
    ∃ ψ : ObservedSyntacticQuotient (Q := Q) S → R,
      (∀ x : Q, ψ (observedSyntacticQuotientMap (Q := Q) S x) = φ x)
        ∧
      (∀ ψ' : ObservedSyntacticQuotient (Q := Q) S → R,
        (∀ x : Q, ψ' (observedSyntacticQuotientMap (Q := Q) S x) = φ x)
          → ψ' = ψ) := by
  exact concreteObservedSyntacticQuotient_universal_property
    (Q := Q) S φ hφ

/-- Concrete quotient multiplicative universal-property package. -/
theorem observedSyntacticConcreteQuotient_multiplicative_universal_package
    {R : Type w} [Semigroup R]
    (S : Set Q)
    (φ : Q → R)
    (hφ : RespectsSameObservedSyntactic S φ)
    (hφ_mul : ∀ x y : Q, φ (x * y) = φ x * φ y) :
    (∀ x : Q,
      exactObservedQuotientLift
        (observedSyntacticQuotientMap (Q := Q) S)
        (observedSyntacticQuotientMap_surjective (Q := Q) S)
        φ
        (observedSyntacticQuotientMap (Q := Q) S x)
        =
      φ x)
      ∧
    (∀ x y : ObservedSyntacticQuotient (Q := Q) S,
      exactObservedQuotientLift
        (observedSyntacticQuotientMap (Q := Q) S)
        (observedSyntacticQuotientMap_surjective (Q := Q) S)
        φ
        (x * y)
        =
      exactObservedQuotientLift
        (observedSyntacticQuotientMap (Q := Q) S)
        (observedSyntacticQuotientMap_surjective (Q := Q) S)
        φ x
        *
      exactObservedQuotientLift
        (observedSyntacticQuotientMap (Q := Q) S)
        (observedSyntacticQuotientMap_surjective (Q := Q) S)
        φ y) := by
  exact concreteObservedSyntacticQuotient_multiplicative_universal_property
    (Q := Q) S φ hφ hφ_mul

end LeanCfgProject
