import LeanCfgProject.ObservedResidualConcept.ObservedSyntacticExactQuotientUniversal
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace LeanCfgProject

universe u v w

/-
ObservedSyntacticQuotientPaperSummary.lean

Current experiment summary target.

This is a theorem-body summary for the new exact observed quotient layer.  It is
not a release certificate or audit wrapper: its theorem statement records the
mathematical payload needed by the paper.

The layer says:

1. an exact observed quotient map has exact observed pullback;
2. residuals, concept closures, point concepts, and ConceptProduct are preserved
   by the quotient map;
3. every map constant on observed-syntactic blocks descends uniquely through the
   quotient map;
4. multiplicative maps descend multiplicatively.
-/

variable {Q : Type u} [Monoid Q]
variable {Qbar : Type v} [Semigroup Qbar]

/--
Paper-facing quotient-invariance package for exact observed quotient maps.
-/
theorem observedSyntacticExactQuotient_paper_package
    (π : Q → Qbar)
    (hπ_mul : ∀ x y : Q, π (x * y) = π x * π y)
    (hπ_surj : ∀ y : Qbar, ∃ x : Q, π x = y)
    (S : Set Q)
    (hkernel :
      ∀ x y : Q, π x = π y ↔ SameObservedSyntactic S x y) :
    (∀ x : Q, π x ∈ Set.image π S ↔ x ∈ S)
      ∧
    (∀ a b : Q,
      { gamma : Q |
          π gamma ∈
            TwoSidedResidual (Set.image π S) (π a) (π b) }
        =
      TwoSidedResidual S a b)
      ∧
    (∀ a b : Q,
      Set.image π (TwoSidedResidual S a b)
        =
      TwoSidedResidual (Set.image π S) (π a) (π b))
      ∧
    (∀ W : Set Q,
      Set.image π (ConceptClosure S W)
        =
      ConceptClosure (Set.image π S) (Set.image π W))
      ∧
    (∀ gamma : Q,
      Set.image π (ConceptClosure S ({gamma} : Set Q))
        =
      ConceptClosure (Set.image π S) ({π gamma} : Set Qbar))
      ∧
    (∀ A B : Set Q,
      Set.image π (ConceptProduct S A B)
        =
      ConceptProduct (Set.image π S)
        (Set.image π A) (Set.image π B)) := by
  constructor
  · exact exactObservedQuotient_pullback_eq π S hkernel
  constructor
  · intro a b
    exact exactObservedQuotient_residual_preimage_eq
      π hπ_mul S hkernel a b
  constructor
  · intro a b
    exact exactObservedQuotient_residual_image_eq
      π hπ_mul hπ_surj S hkernel a b
  constructor
  · intro W
    exact exactObservedQuotient_conceptClosure_image_eq
      π hπ_mul hπ_surj S hkernel W
  constructor
  · intro gamma
    exact exactObservedQuotient_pointConcept_image_eq
      π hπ_mul hπ_surj S hkernel gamma
  · intro A B
    exact exactObservedQuotient_conceptProduct_image_eq
      π hπ_mul hπ_surj S hkernel A B

/--
Paper-facing universal-property package for exact observed quotient maps.

This keeps the universal property separate from the residual/concept invariance
package because the target type `R` need not be a monoid unless one also wants
multiplicativity of the descended map.
-/
theorem observedSyntacticExactQuotient_universal_paper_package
    {R : Type w}
    (π : Q → Qbar)
    (hπ_surj : ∀ y : Qbar, ∃ x : Q, π x = y)
    (S : Set Q)
    (hkernel :
      ∀ x y : Q, π x = π y ↔ SameObservedSyntactic S x y)
    (φ : Q → R)
    (hφ : RespectsSameObservedSyntactic S φ) :
    ∃ ψ : Qbar → R,
      (∀ x : Q, ψ (π x) = φ x)
        ∧
      (∀ ψ' : Qbar → R,
        (∀ x : Q, ψ' (π x) = φ x) → ψ' = ψ) := by
  exact exactObservedQuotient_universal_property
    π hπ_surj S hkernel φ hφ

/--
Paper-facing multiplicative universal-property package.
-/
theorem observedSyntacticExactQuotient_multiplicative_paper_package
    {R : Type w} [Semigroup R]
    (π : Q → Qbar)
    (hπ_mul : ∀ x y : Q, π (x * y) = π x * π y)
    (hπ_surj : ∀ y : Qbar, ∃ x : Q, π x = y)
    (S : Set Q)
    (hkernel :
      ∀ x y : Q, π x = π y ↔ SameObservedSyntactic S x y)
    (φ : Q → R)
    (hφ : RespectsSameObservedSyntactic S φ)
    (hφ_mul : ∀ x y : Q, φ (x * y) = φ x * φ y) :
    (∀ x : Q,
      exactObservedQuotientLift π hπ_surj φ (π x) = φ x)
      ∧
    (∀ x y : Qbar,
      exactObservedQuotientLift π hπ_surj φ (x * y)
        =
      exactObservedQuotientLift π hπ_surj φ x
        *
      exactObservedQuotientLift π hπ_surj φ y) := by
  exact exactObservedQuotient_multiplicative_universal_property
    π hπ_mul hπ_surj S hkernel φ hφ hφ_mul

end LeanCfgProject
