import LeanCfgProject.ObservedSyntacticExactQuotient

set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace LeanCfgProject

universe u v w

/-
ObservedSyntacticExactQuotientUniversal.lean

Next theorem-body experiment.

Goal:
  prove the universal-property side of the exact observed quotient layer.

Given a surjective multiplicative map π whose kernel is exactly
SameObservedSyntactic S, any map φ that is constant on SameObservedSyntactic
classes descends uniquely through π.  If φ is multiplicative, the descended map
is multiplicative.

This is the paper-facing universal property expected of the observed syntactic
quotient, but stated for an exact quotient map π rather than for a particular
Quotient construction.
-/

variable {Q : Type u} [Monoid Q]
variable {Qbar : Type v} [Semigroup Qbar]
variable {R : Type w}

/--
A map is constant on observed-syntactic blocks.
-/
def RespectsSameObservedSyntactic
    (S : Set Q) (φ : Q → R) : Prop :=
  ∀ x y : Q, SameObservedSyntactic S x y → φ x = φ y

/--
Noncomputable lift of a map through a surjective exact observed quotient map.

The representative is chosen using surjectivity of `π`.
-/
noncomputable def exactObservedQuotientLift
    (π : Q → Qbar)
    (hπ_surj : ∀ y : Qbar, ∃ x : Q, π x = y)
    (φ : Q → R) :
    Qbar → R :=
  fun y => φ (Classical.choose (hπ_surj y))

/--
The lifted map commutes with the quotient projection.
-/
theorem exactObservedQuotientLift_commutes
    (π : Q → Qbar)
    (hπ_surj : ∀ y : Qbar, ∃ x : Q, π x = y)
    (S : Set Q)
    (hkernel :
      ∀ x y : Q, π x = π y ↔ SameObservedSyntactic S x y)
    (φ : Q → R)
    (hφ : RespectsSameObservedSyntactic S φ)
    (x : Q) :
    exactObservedQuotientLift π hπ_surj φ (π x) = φ x := by
  unfold exactObservedQuotientLift
  have hrep :
      π (Classical.choose (hπ_surj (π x))) = π x :=
    Classical.choose_spec (hπ_surj (π x))
  have hsame :
      SameObservedSyntactic S
        (Classical.choose (hπ_surj (π x))) x :=
    (hkernel (Classical.choose (hπ_surj (π x))) x).mp hrep
  exact hφ (Classical.choose (hπ_surj (π x))) x hsame

/--
Uniqueness of the descended map.
-/
theorem exactObservedQuotientLift_unique
    (π : Q → Qbar)
    (hπ_surj : ∀ y : Qbar, ∃ x : Q, π x = y)
    (S : Set Q)
    (hkernel :
      ∀ x y : Q, π x = π y ↔ SameObservedSyntactic S x y)
    (φ : Q → R)
    (hφ : RespectsSameObservedSyntactic S φ)
    (ψ : Qbar → R)
    (hψ : ∀ x : Q, ψ (π x) = φ x) :
    ψ = exactObservedQuotientLift π hπ_surj φ := by
  funext y
  rcases hπ_surj y with ⟨x, hx⟩
  rw [← hx, hψ x]
  symm
  exact exactObservedQuotientLift_commutes
    π hπ_surj S hkernel φ hφ x

/--
Existence-and-uniqueness form of the universal property.
-/
theorem exactObservedQuotient_universal_property
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
  refine ⟨exactObservedQuotientLift π hπ_surj φ, ?_, ?_⟩
  · intro x
    exact exactObservedQuotientLift_commutes
      π hπ_surj S hkernel φ hφ x
  · intro ψ' hψ'
    exact exactObservedQuotientLift_unique
      π hπ_surj S hkernel φ hφ ψ' hψ'

section MultiplicativeLift

variable {R : Type w} [Semigroup R]

/--
If the original map is multiplicative, then its exact quotient lift is
multiplicative.
-/
theorem exactObservedQuotientLift_mul
    (π : Q → Qbar)
    (hπ_mul : ∀ x y : Q, π (x * y) = π x * π y)
    (hπ_surj : ∀ y : Qbar, ∃ x : Q, π x = y)
    (S : Set Q)
    (hkernel :
      ∀ x y : Q, π x = π y ↔ SameObservedSyntactic S x y)
    (φ : Q → R)
    (hφ : RespectsSameObservedSyntactic S φ)
    (hφ_mul : ∀ x y : Q, φ (x * y) = φ x * φ y)
    (x y : Qbar) :
    exactObservedQuotientLift π hπ_surj φ (x * y)
      =
    exactObservedQuotientLift π hπ_surj φ x
      *
    exactObservedQuotientLift π hπ_surj φ y := by
  rcases hπ_surj x with ⟨a, ha⟩
  rcases hπ_surj y with ⟨b, hb⟩
  have hxy : x * y = π (a * b) := by
    rw [← ha, ← hb, hπ_mul a b]
  have hx :
      exactObservedQuotientLift π hπ_surj φ x = φ a := by
    rw [← ha]
    exact exactObservedQuotientLift_commutes
      π hπ_surj S hkernel φ hφ a
  have hy :
      exactObservedQuotientLift π hπ_surj φ y = φ b := by
    rw [← hb]
    exact exactObservedQuotientLift_commutes
      π hπ_surj S hkernel φ hφ b
  have hxy_lift :
      exactObservedQuotientLift π hπ_surj φ (x * y) = φ (a * b) := by
    rw [hxy]
    exact exactObservedQuotientLift_commutes
      π hπ_surj S hkernel φ hφ (a * b)
  rw [hxy_lift, hx, hy, hφ_mul a b]

/--
Multiplicative universal property package.
-/
theorem exactObservedQuotient_multiplicative_universal_property
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
  constructor
  · intro x
    exact exactObservedQuotientLift_commutes
      π hπ_surj S hkernel φ hφ x
  · intro x y
    exact exactObservedQuotientLift_mul
      π hπ_mul hπ_surj S hkernel φ hφ hφ_mul x y

end MultiplicativeLift

end LeanCfgProject
