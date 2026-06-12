import LeanCfgProject.ObservedResidualConcept.ObservedFactorMinimality
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace LeanCfgProject

universe u v

/-
ObservedSyntacticExactQuotient.lean

Next theorem-body experiment after the CI #216/#217 normal-coset layer.

Goal:
  close the remaining paper-facing gap between the abstract factor-map
  invariance theorems and the intended observed syntactic quotient.

Instead of constructing the quotient type inside this file, we prove the exact
instantiation theorem for any multiplicative surjective factor map π whose
kernel is exactly SameObservedSyntactic S:

    π x = π y  ↔  x ≈_S y.

This is the robust theorem-body layer immediately below the actual quotient
construction Q/≈_S.  Once an actual quotient monoid is installed, its projection
can be plugged into these theorems directly.

This file is not a release wrapper, certificate, manifest, smoke test, or
summary-only module.
-/

variable {Q : Type u} [Monoid Q]
variable {Qbar : Type v} [Semigroup Qbar]

/--
Exact observed quotient maps have exact observed pullback.

If the kernel of `π` is precisely `SameObservedSyntactic S`, then the observed
subset `S` is exactly the pullback of its image along `π`.
-/
theorem exactObservedQuotient_pullback_eq
    (π : Q → Qbar)
    (S : Set Q)
    (hkernel :
      ∀ x y : Q, π x = π y ↔ SameObservedSyntactic S x y) :
    ∀ x : Q, π x ∈ Set.image π S ↔ x ∈ S := by
  intro x
  exact image_pullback_eq_of_fibers_sameObservedSyntactic
    π S
    (fun x y hxy => (hkernel x y).mp hxy)
    x

/--
Residual pullback for an exact observed quotient map.

This specializes the abstract residual theorem to maps whose fibers are exactly
the observed syntactic congruence.
-/
theorem exactObservedQuotient_residual_preimage_eq
    (π : Q → Qbar)
    (hπ_mul : ∀ x y : Q, π (x * y) = π x * π y)
    (S : Set Q)
    (hkernel :
      ∀ x y : Q, π x = π y ↔ SameObservedSyntactic S x y)
    (a b : Q) :
    { gamma : Q |
        π gamma ∈ TwoSidedResidual (Set.image π S) (π a) (π b) }
      =
    TwoSidedResidual S a b := by
  exact observedSyntacticFactor_residual_preimage_eq
    π hπ_mul S
    (fun x y hxy => (hkernel x y).mp hxy)
    a b

/--
Residual image equality for an exact observed quotient map.
-/
theorem exactObservedQuotient_residual_image_eq
    (π : Q → Qbar)
    (hπ_mul : ∀ x y : Q, π (x * y) = π x * π y)
    (hπ_surj : ∀ y : Qbar, ∃ x : Q, π x = y)
    (S : Set Q)
    (hkernel :
      ∀ x y : Q, π x = π y ↔ SameObservedSyntactic S x y)
    (a b : Q) :
    Set.image π (TwoSidedResidual S a b)
      =
    TwoSidedResidual (Set.image π S) (π a) (π b) := by
  exact imagePullbackFactor_residual_image_eq
    π hπ_mul hπ_surj S
    (exactObservedQuotient_pullback_eq π S hkernel)
    a b

/--
Common-context pullback equality for an exact observed quotient map.
-/
theorem exactObservedQuotient_commonContexts_preimage_eq
    (π : Q → Qbar)
    (hπ_mul : ∀ x y : Q, π (x * y) = π x * π y)
    (hπ_surj : ∀ y : Qbar, ∃ x : Q, π x = y)
    (S : Set Q)
    (hkernel :
      ∀ x y : Q, π x = π y ↔ SameObservedSyntactic S x y)
    (Ubar : Set Qbar) :
    CommonContexts S { gamma : Q | π gamma ∈ Ubar }
      =
    { ab : Q × Q |
        (π ab.1, π ab.2) ∈
          CommonContexts (Set.image π S) Ubar } := by
  exact quotient_commonContexts_preimage_eq
    π hπ_mul hπ_surj
    S (Set.image π S)
    (exactObservedQuotient_pullback_eq π S hkernel)
    Ubar

/--
Concept-closure pullback equality for an exact observed quotient map.
-/
theorem exactObservedQuotient_conceptClosure_preimage_eq
    (π : Q → Qbar)
    (hπ_mul : ∀ x y : Q, π (x * y) = π x * π y)
    (hπ_surj : ∀ y : Qbar, ∃ x : Q, π x = y)
    (S : Set Q)
    (hkernel :
      ∀ x y : Q, π x = π y ↔ SameObservedSyntactic S x y)
    (Ubar : Set Qbar) :
    ConceptClosure S { gamma : Q | π gamma ∈ Ubar }
      =
    { gamma : Q |
        π gamma ∈ ConceptClosure (Set.image π S) Ubar } := by
  exact observedSyntacticFactor_conceptClosure_preimage_eq
    π hπ_mul hπ_surj S
    (fun x y hxy => (hkernel x y).mp hxy)
    Ubar

/--
Concept-closure image equality for an exact observed quotient map.
-/
theorem exactObservedQuotient_conceptClosure_image_eq
    (π : Q → Qbar)
    (hπ_mul : ∀ x y : Q, π (x * y) = π x * π y)
    (hπ_surj : ∀ y : Qbar, ∃ x : Q, π x = y)
    (S : Set Q)
    (hkernel :
      ∀ x y : Q, π x = π y ↔ SameObservedSyntactic S x y)
    (W : Set Q) :
    Set.image π (ConceptClosure S W)
      =
    ConceptClosure (Set.image π S) (Set.image π W) := by
  exact imagePullbackFactor_conceptClosure_image_eq
    π hπ_mul hπ_surj S
    (exactObservedQuotient_pullback_eq π S hkernel)
    W

/--
Point-concept image equality for an exact observed quotient map.
-/
theorem exactObservedQuotient_pointConcept_image_eq
    (π : Q → Qbar)
    (hπ_mul : ∀ x y : Q, π (x * y) = π x * π y)
    (hπ_surj : ∀ y : Qbar, ∃ x : Q, π x = y)
    (S : Set Q)
    (hkernel :
      ∀ x y : Q, π x = π y ↔ SameObservedSyntactic S x y)
    (gamma : Q) :
    Set.image π (ConceptClosure S ({gamma} : Set Q))
      =
    ConceptClosure (Set.image π S) ({π gamma} : Set Qbar) := by
  exact quotient_pointConcept_image_eq
    π hπ_mul hπ_surj
    S (Set.image π S)
    (exactObservedQuotient_pullback_eq π S hkernel)
    gamma

/--
ConceptProduct image equality for an exact observed quotient map.
-/
theorem exactObservedQuotient_conceptProduct_image_eq
    (π : Q → Qbar)
    (hπ_mul : ∀ x y : Q, π (x * y) = π x * π y)
    (hπ_surj : ∀ y : Qbar, ∃ x : Q, π x = y)
    (S : Set Q)
    (hkernel :
      ∀ x y : Q, π x = π y ↔ SameObservedSyntactic S x y)
    (A B : Set Q) :
    Set.image π (ConceptProduct S A B)
      =
    ConceptProduct (Set.image π S)
      (Set.image π A) (Set.image π B) := by
  exact imagePullbackFactor_conceptProduct_image_eq
    π hπ_mul hπ_surj S
    (exactObservedQuotient_pullback_eq π S hkernel)
    A B

/--
Closed extents pull back to closed extents for exact observed quotient maps.
-/
theorem exactObservedQuotient_preimage_isConceptExtent
    (π : Q → Qbar)
    (hπ_mul : ∀ x y : Q, π (x * y) = π x * π y)
    (hπ_surj : ∀ y : Qbar, ∃ x : Q, π x = y)
    (S : Set Q)
    (hkernel :
      ∀ x y : Q, π x = π y ↔ SameObservedSyntactic S x y)
    (Ubar : Set Qbar)
    (hUbar : IsConceptExtent (Set.image π S) Ubar) :
    IsConceptExtent S { gamma : Q | π gamma ∈ Ubar } := by
  exact quotient_preimage_isConceptExtent
    π hπ_mul hπ_surj
    S (Set.image π S)
    (exactObservedQuotient_pullback_eq π S hkernel)
    Ubar hUbar

/--
Compact theorem-body package for exact observed quotient invariance.
-/
theorem exactObservedQuotient_invariance_package
    (π : Q → Qbar)
    (hπ_mul : ∀ x y : Q, π (x * y) = π x * π y)
    (hπ_surj : ∀ y : Qbar, ∃ x : Q, π x = y)
    (S : Set Q)
    (hkernel :
      ∀ x y : Q, π x = π y ↔ SameObservedSyntactic S x y) :
    (∀ x : Q, π x ∈ Set.image π S ↔ x ∈ S)
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
    (∀ A B : Set Q,
      Set.image π (ConceptProduct S A B)
        =
      ConceptProduct (Set.image π S)
        (Set.image π A) (Set.image π B)) := by
  constructor
  · exact exactObservedQuotient_pullback_eq π S hkernel
  constructor
  · intro a b
    exact exactObservedQuotient_residual_image_eq
      π hπ_mul hπ_surj S hkernel a b
  constructor
  · intro W
    exact exactObservedQuotient_conceptClosure_image_eq
      π hπ_mul hπ_surj S hkernel W
  · intro A B
    exact exactObservedQuotient_conceptProduct_image_eq
      π hπ_mul hπ_surj S hkernel A B

end LeanCfgProject
