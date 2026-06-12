import LeanCfgProject.ObservedResidualConcept.ObservedQuotientClosureImage
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace LeanCfgProject

universe u v

/-
ObservedSyntacticSaturation.lean

Planned theorem item 4, theorem-body experiment.

Goal:
  connect the abstract quotient/factor-map theorems to the actual observed
  syntactic relation.

This file proves that if a factor map π has fibers contained in
SameObservedSyntactic S, then S is exactly the pullback of its image along π.
This supplies the `hS_pullback` hypothesis used in the previous quotient
residual/closure theorems.

This is not a release/summary/package/certificate/audit/metadata/manifest/
dependency-certificate/smoke-test module.
-/

variable {Q : Type u} {Qbar : Type v}

/--
Observed syntactic equivalence preserves raw membership in S.

This is obtained by testing the two-sided context `(1,1)`.
-/
theorem sameObservedSyntactic_mem_iff
    {Q : Type u} [Monoid Q]
    (S : Set Q) {x y : Q}
    (hxy : SameObservedSyntactic S x y) :
    x ∈ S ↔ y ∈ S := by
  have h := hxy 1 1
  simpa using h

/--
If every fiber of π is contained in SameObservedSyntactic S, then S is
saturated with respect to π-fibers.
-/
theorem mem_iff_of_factor_fibers_sameObservedSyntactic
    {Q : Type u} [Monoid Q]
    {Qbar : Type v}
    (π : Q → Qbar)
    (S : Set Q)
    (hfiber : ∀ x y : Q, π x = π y → SameObservedSyntactic S x y)
    {x y : Q}
    (hxy : π x = π y) :
    x ∈ S ↔ y ∈ S := by
  exact sameObservedSyntactic_mem_iff S (hfiber x y hxy)

/--
If π-fibers are observed-syntactic, then S is exactly the pullback of its
image along π.

This is the concrete source of the `hS_pullback` hypothesis used in
`quotient_residual_preimage_eq`, `quotient_conceptClosure_preimage_eq`,
and `quotient_conceptClosure_image_eq`.
-/
theorem image_pullback_eq_of_fibers_sameObservedSyntactic
    {Q : Type u} [Monoid Q]
    {Qbar : Type v}
    (π : Q → Qbar)
    (S : Set Q)
    (hfiber : ∀ x y : Q, π x = π y → SameObservedSyntactic S x y)
    (x : Q) :
    π x ∈ Set.image π S ↔ x ∈ S := by
  constructor
  · intro hx
    rcases hx with ⟨s, hsS, hs_eq⟩
    have hsx : s ∈ S ↔ x ∈ S :=
      mem_iff_of_factor_fibers_sameObservedSyntactic
        π S hfiber hs_eq
    exact hsx.mp hsS
  · intro hxS
    exact ⟨x, hxS, rfl⟩

/--
Residual pullback specialized to an observed-syntactic factor map.
-/
theorem observedSyntacticFactor_residual_preimage_eq
    {Q : Type u} [Monoid Q]
    {Qbar : Type v} [Semigroup Qbar]
    (π : Q → Qbar)
    (hπ_mul : ∀ x y : Q, π (x * y) = π x * π y)
    (S : Set Q)
    (hfiber : ∀ x y : Q, π x = π y → SameObservedSyntactic S x y)
    (a b : Q) :
    { gamma : Q |
        π gamma ∈ TwoSidedResidual (Set.image π S) (π a) (π b) }
      =
    TwoSidedResidual S a b := by
  exact quotient_residual_preimage_eq
    π hπ_mul S (Set.image π S)
    (image_pullback_eq_of_fibers_sameObservedSyntactic π S hfiber)
    a b

/--
Residual image equality specialized to an observed-syntactic surjective factor
map.
-/
theorem observedSyntacticFactor_residual_image_eq
    {Q : Type u} [Monoid Q]
    {Qbar : Type v} [Semigroup Qbar]
    (π : Q → Qbar)
    (hπ_mul : ∀ x y : Q, π (x * y) = π x * π y)
    (hπ_surj : ∀ y : Qbar, ∃ x : Q, π x = y)
    (S : Set Q)
    (hfiber : ∀ x y : Q, π x = π y → SameObservedSyntactic S x y)
    (a b : Q) :
    Set.image π (TwoSidedResidual S a b)
      =
    TwoSidedResidual (Set.image π S) (π a) (π b) := by
  exact quotient_residual_image_eq
    π hπ_mul hπ_surj S (Set.image π S)
    (image_pullback_eq_of_fibers_sameObservedSyntactic π S hfiber)
    a b

/--
Concept-closure preimage equality specialized to an observed-syntactic
surjective factor map.
-/
theorem observedSyntacticFactor_conceptClosure_preimage_eq
    {Q : Type u} [Monoid Q]
    {Qbar : Type v} [Semigroup Qbar]
    (π : Q → Qbar)
    (hπ_mul : ∀ x y : Q, π (x * y) = π x * π y)
    (hπ_surj : ∀ y : Qbar, ∃ x : Q, π x = y)
    (S : Set Q)
    (hfiber : ∀ x y : Q, π x = π y → SameObservedSyntactic S x y)
    (Ubar : Set Qbar) :
    ConceptClosure S { gamma : Q | π gamma ∈ Ubar }
      =
    { gamma : Q | π gamma ∈ ConceptClosure (Set.image π S) Ubar } := by
  exact quotient_conceptClosure_preimage_eq
    π hπ_mul hπ_surj S (Set.image π S)
    (image_pullback_eq_of_fibers_sameObservedSyntactic π S hfiber)
    Ubar

/--
Concept-closure image equality specialized to an observed-syntactic surjective
factor map.

This is the item 4(c) image theorem with `Sbar = π(S)` and with the pullback
condition supplied by observed-syntactic saturation.
-/
theorem observedSyntacticFactor_conceptClosure_image_eq
    {Q : Type u} [Monoid Q]
    {Qbar : Type v} [Semigroup Qbar]
    (π : Q → Qbar)
    (hπ_mul : ∀ x y : Q, π (x * y) = π x * π y)
    (hπ_surj : ∀ y : Qbar, ∃ x : Q, π x = y)
    (S : Set Q)
    (hfiber : ∀ x y : Q, π x = π y → SameObservedSyntactic S x y)
    (W : Set Q) :
    Set.image π (ConceptClosure S W)
      =
    ConceptClosure (Set.image π S) (Set.image π W) := by
  exact quotient_conceptClosure_image_eq
    π hπ_mul hπ_surj S (Set.image π S)
    (image_pullback_eq_of_fibers_sameObservedSyntactic π S hfiber)
    W

/--
ConceptProduct image equality specialized to an observed-syntactic surjective
factor map.
-/
theorem observedSyntacticFactor_conceptProduct_image_eq
    {Q : Type u} [Monoid Q]
    {Qbar : Type v} [Semigroup Qbar]
    (π : Q → Qbar)
    (hπ_mul : ∀ x y : Q, π (x * y) = π x * π y)
    (hπ_surj : ∀ y : Qbar, ∃ x : Q, π x = y)
    (S : Set Q)
    (hfiber : ∀ x y : Q, π x = π y → SameObservedSyntactic S x y)
    (A B : Set Q) :
    Set.image π (ConceptProduct S A B)
      =
    ConceptProduct (Set.image π S) (Set.image π A) (Set.image π B) := by
  exact quotient_conceptProduct_image_eq
    π hπ_mul hπ_surj S (Set.image π S)
    (image_pullback_eq_of_fibers_sameObservedSyntactic π S hfiber)
    A B

end LeanCfgProject
