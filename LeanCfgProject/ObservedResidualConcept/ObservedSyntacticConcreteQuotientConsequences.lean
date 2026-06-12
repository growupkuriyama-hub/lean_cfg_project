import LeanCfgProject.ObservedResidualConcept.ObservedSyntacticConcreteQuotient
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace LeanCfgProject

universe u w

/-
ObservedSyntacticConcreteQuotientConsequences.lean

Theorem-body experiment.

Purpose:
  instantiate the exact observed quotient-map theorems with the concrete
  quotient by SameObservedSyntactic S.
-/

variable {Q : Type u} [Monoid Q]

/-- Exact observed pullback for the concrete observed syntactic quotient. -/
theorem concreteObservedSyntacticQuotient_pullback_eq
    (S : Set Q) :
    ∀ x : Q,
      observedSyntacticQuotientMap (Q := Q) S x
        ∈
      Set.image (observedSyntacticQuotientMap (Q := Q) S) S
        ↔
      x ∈ S := by
  exact exactObservedQuotient_pullback_eq
    (observedSyntacticQuotientMap (Q := Q) S)
    S
    (observedSyntacticQuotientMap_kernel (Q := Q) S)

/-- Residual preimage equality for the concrete observed syntactic quotient. -/
theorem concreteObservedSyntacticQuotient_residual_preimage_eq
    (S : Set Q) (a b : Q) :
    { gamma : Q |
        observedSyntacticQuotientMap (Q := Q) S gamma
          ∈
        TwoSidedResidual
          (Set.image (observedSyntacticQuotientMap (Q := Q) S) S)
          (observedSyntacticQuotientMap (Q := Q) S a)
          (observedSyntacticQuotientMap (Q := Q) S b) }
      =
    TwoSidedResidual S a b := by
  exact exactObservedQuotient_residual_preimage_eq
    (observedSyntacticQuotientMap (Q := Q) S)
    (by
      intro x y
      exact observedSyntacticQuotientMap_mul (Q := Q) S x y)
    S
    (observedSyntacticQuotientMap_kernel (Q := Q) S)
    a b

/-- Residual image equality for the concrete observed syntactic quotient. -/
theorem concreteObservedSyntacticQuotient_residual_image_eq
    (S : Set Q) (a b : Q) :
    Set.image (observedSyntacticQuotientMap (Q := Q) S)
      (TwoSidedResidual S a b)
      =
    TwoSidedResidual
      (Set.image (observedSyntacticQuotientMap (Q := Q) S) S)
      (observedSyntacticQuotientMap (Q := Q) S a)
      (observedSyntacticQuotientMap (Q := Q) S b) := by
  exact exactObservedQuotient_residual_image_eq
    (observedSyntacticQuotientMap (Q := Q) S)
    (by
      intro x y
      exact observedSyntacticQuotientMap_mul (Q := Q) S x y)
    (observedSyntacticQuotientMap_surjective (Q := Q) S)
    S
    (observedSyntacticQuotientMap_kernel (Q := Q) S)
    a b

/-- Common-context preimage equality for the concrete quotient. -/
theorem concreteObservedSyntacticQuotient_commonContexts_preimage_eq
    (S : Set Q)
    (Ubar : Set (ObservedSyntacticQuotient (Q := Q) S)) :
    CommonContexts S
      { gamma : Q |
          observedSyntacticQuotientMap (Q := Q) S gamma ∈ Ubar }
      =
    { ab : Q × Q |
        (observedSyntacticQuotientMap (Q := Q) S ab.1,
          observedSyntacticQuotientMap (Q := Q) S ab.2)
          ∈
        CommonContexts
          (Set.image (observedSyntacticQuotientMap (Q := Q) S) S)
          Ubar } := by
  exact exactObservedQuotient_commonContexts_preimage_eq
    (observedSyntacticQuotientMap (Q := Q) S)
    (by
      intro x y
      exact observedSyntacticQuotientMap_mul (Q := Q) S x y)
    (observedSyntacticQuotientMap_surjective (Q := Q) S)
    S
    (observedSyntacticQuotientMap_kernel (Q := Q) S)
    Ubar

/-- Concept-closure preimage equality for the concrete quotient. -/
theorem concreteObservedSyntacticQuotient_conceptClosure_preimage_eq
    (S : Set Q)
    (Ubar : Set (ObservedSyntacticQuotient (Q := Q) S)) :
    ConceptClosure S
      { gamma : Q |
          observedSyntacticQuotientMap (Q := Q) S gamma ∈ Ubar }
      =
    { gamma : Q |
        observedSyntacticQuotientMap (Q := Q) S gamma
          ∈
        ConceptClosure
          (Set.image (observedSyntacticQuotientMap (Q := Q) S) S)
          Ubar } := by
  exact exactObservedQuotient_conceptClosure_preimage_eq
    (observedSyntacticQuotientMap (Q := Q) S)
    (by
      intro x y
      exact observedSyntacticQuotientMap_mul (Q := Q) S x y)
    (observedSyntacticQuotientMap_surjective (Q := Q) S)
    S
    (observedSyntacticQuotientMap_kernel (Q := Q) S)
    Ubar

/-- Concept-closure image equality for the concrete quotient. -/
theorem concreteObservedSyntacticQuotient_conceptClosure_image_eq
    (S : Set Q) (W : Set Q) :
    Set.image (observedSyntacticQuotientMap (Q := Q) S)
      (ConceptClosure S W)
      =
    ConceptClosure
      (Set.image (observedSyntacticQuotientMap (Q := Q) S) S)
      (Set.image (observedSyntacticQuotientMap (Q := Q) S) W) := by
  exact exactObservedQuotient_conceptClosure_image_eq
    (observedSyntacticQuotientMap (Q := Q) S)
    (by
      intro x y
      exact observedSyntacticQuotientMap_mul (Q := Q) S x y)
    (observedSyntacticQuotientMap_surjective (Q := Q) S)
    S
    (observedSyntacticQuotientMap_kernel (Q := Q) S)
    W

/-- Point-concept image equality for the concrete quotient. -/
theorem concreteObservedSyntacticQuotient_pointConcept_image_eq
    (S : Set Q) (gamma : Q) :
    Set.image (observedSyntacticQuotientMap (Q := Q) S)
      (ConceptClosure S ({gamma} : Set Q))
      =
    ConceptClosure
      (Set.image (observedSyntacticQuotientMap (Q := Q) S) S)
      ({observedSyntacticQuotientMap (Q := Q) S gamma} :
        Set (ObservedSyntacticQuotient (Q := Q) S)) := by
  exact exactObservedQuotient_pointConcept_image_eq
    (observedSyntacticQuotientMap (Q := Q) S)
    (by
      intro x y
      exact observedSyntacticQuotientMap_mul (Q := Q) S x y)
    (observedSyntacticQuotientMap_surjective (Q := Q) S)
    S
    (observedSyntacticQuotientMap_kernel (Q := Q) S)
    gamma

/-- ConceptProduct image equality for the concrete quotient. -/
theorem concreteObservedSyntacticQuotient_conceptProduct_image_eq
    (S : Set Q) (A B : Set Q) :
    Set.image (observedSyntacticQuotientMap (Q := Q) S)
      (ConceptProduct S A B)
      =
    ConceptProduct
      (Set.image (observedSyntacticQuotientMap (Q := Q) S) S)
      (Set.image (observedSyntacticQuotientMap (Q := Q) S) A)
      (Set.image (observedSyntacticQuotientMap (Q := Q) S) B) := by
  exact exactObservedQuotient_conceptProduct_image_eq
    (observedSyntacticQuotientMap (Q := Q) S)
    (by
      intro x y
      exact observedSyntacticQuotientMap_mul (Q := Q) S x y)
    (observedSyntacticQuotientMap_surjective (Q := Q) S)
    S
    (observedSyntacticQuotientMap_kernel (Q := Q) S)
    A B

/-- Closed extents pull back to closed extents along the concrete quotient. -/
theorem concreteObservedSyntacticQuotient_preimage_isConceptExtent
    (S : Set Q)
    (Ubar : Set (ObservedSyntacticQuotient (Q := Q) S))
    (hUbar :
      IsConceptExtent
        (Set.image (observedSyntacticQuotientMap (Q := Q) S) S)
        Ubar) :
    IsConceptExtent S
      { gamma : Q |
          observedSyntacticQuotientMap (Q := Q) S gamma ∈ Ubar } := by
  exact exactObservedQuotient_preimage_isConceptExtent
    (observedSyntacticQuotientMap (Q := Q) S)
    (by
      intro x y
      exact observedSyntacticQuotientMap_mul (Q := Q) S x y)
    (observedSyntacticQuotientMap_surjective (Q := Q) S)
    S
    (observedSyntacticQuotientMap_kernel (Q := Q) S)
    Ubar hUbar

/-- Universal property of the concrete observed syntactic quotient. -/
theorem concreteObservedSyntacticQuotient_universal_property
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
  exact exactObservedQuotient_universal_property
    (observedSyntacticQuotientMap (Q := Q) S)
    (observedSyntacticQuotientMap_surjective (Q := Q) S)
    S
    (observedSyntacticQuotientMap_kernel (Q := Q) S)
    φ hφ

/-- Multiplicative universal property of the concrete observed syntactic quotient. -/
theorem concreteObservedSyntacticQuotient_multiplicative_universal_property
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
  exact exactObservedQuotient_multiplicative_universal_property
    (observedSyntacticQuotientMap (Q := Q) S)
    (by
      intro x y
      exact observedSyntacticQuotientMap_mul (Q := Q) S x y)
    (observedSyntacticQuotientMap_surjective (Q := Q) S)
    S
    (observedSyntacticQuotientMap_kernel (Q := Q) S)
    φ hφ hφ_mul

end LeanCfgProject
