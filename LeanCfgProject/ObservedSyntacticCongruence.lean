import LeanCfgProject.ObservedSyntacticConcept

set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.overlappingInstances false

namespace LeanCfgProject

universe u

/-
ObservedSyntacticCongruence.lean

This file continues the v25.1 canonical-object layer.

`ObservedSyntacticConcept.lean` introduced the relation

  SameObservedSyntactic S x y

meaning that all two-sided `S`-membership tests agree on `x` and `y`.

Here we prove the congruence/maximality layer:

* the relation is stable under left and right multiplication in a semigroup;
* hence it is compatible with binary multiplication;
* any relation that is stable under left/right multiplication and preserves
  membership in `S` is contained in `SameObservedSyntactic S`.

This v4 avoids the `[Semigroup Q]` / `[Monoid Q]` instance diamond by
separating the semigroup compatibility section from the monoid preservation
and maximality section.
-/

section BasicMaximality

variable {Q : Type u} [Mul Q]
variable {S : Set Q}

/--
A relation is two-sided stable if it is closed under multiplying the same
element on the left and on the right.
-/
def TwoSidedStableRel (R : Q → Q → Prop) : Prop :=
  (∀ a x y : Q, R x y → R (a * x) (a * y))
  ∧
  (∀ b x y : Q, R x y → R (x * b) (y * b))

/--
A relation preserves the observed subset `S` if related elements have the same
membership in `S`.
-/
def PreservesSubset (S : Set Q) (R : Q → Q → Prop) : Prop :=
  ∀ x y : Q, R x y → (x ∈ S ↔ y ∈ S)

/--
If a relation is two-sided stable and preserves `S`, then every related pair
has the same observed syntactic tests.

This core maximality statement only needs `Mul Q`, because the two-sided tests
are written as left-associated products `(a * x) * b`.
-/
theorem rel_subset_sameObservedSyntactic_of_stable_preserves
    {R : Q → Q → Prop}
    (hstable : TwoSidedStableRel R)
    (hpres : PreservesSubset S R)
    {x y : Q}
    (hxy : R x y) :
    SameObservedSyntactic S x y := by
  intro a b
  have hleft : R (a * x) (a * y) := hstable.1 a x y hxy
  have hboth : R ((a * x) * b) ((a * y) * b) :=
    hstable.2 b (a * x) (a * y) hleft
  exact hpres ((a * x) * b) ((a * y) * b) hboth

/--
Set-theoretic version: any two-sided stable, `S`-preserving relation is
contained in the observed syntactic relation.
-/
theorem relation_le_sameObservedSyntactic
    {R : Q → Q → Prop}
    (hstable : TwoSidedStableRel R)
    (hpres : PreservesSubset S R) :
    ∀ x y : Q, R x y → SameObservedSyntactic S x y := by
  intro x y hxy
  exact rel_subset_sameObservedSyntactic_of_stable_preserves
    hstable hpres hxy

end BasicMaximality

section SemigroupCompatibility

variable {Q : Type u} [Semigroup Q]
variable {S : Set Q}

/--
Observed syntactic equivalence is stable under multiplying the same element on
the left.
-/
theorem sameObservedSyntactic_mul_left
    (a : Q) {x y : Q}
    (hxy : SameObservedSyntactic S x y) :
    SameObservedSyntactic S (a * x) (a * y) := by
  intro l r
  calc
    l * (a * x) * r ∈ S
        ↔ (l * a) * x * r ∈ S := by
          rw [mul_assoc l a x]
    _   ↔ (l * a) * y * r ∈ S :=
          hxy (l * a) r
    _   ↔ l * (a * y) * r ∈ S := by
          rw [mul_assoc l a y]

/--
Observed syntactic equivalence is stable under multiplying the same element on
the right.
-/
theorem sameObservedSyntactic_mul_right
    (b : Q) {x y : Q}
    (hxy : SameObservedSyntactic S x y) :
    SameObservedSyntactic S (x * b) (y * b) := by
  intro l r
  simpa [mul_assoc] using hxy l (b * r)

/--
Observed syntactic equivalence is compatible with multiplication.
-/
theorem sameObservedSyntactic_mul
    {x₁ y₁ x₂ y₂ : Q}
    (h₁ : SameObservedSyntactic S x₁ y₁)
    (h₂ : SameObservedSyntactic S x₂ y₂) :
    SameObservedSyntactic S (x₁ * x₂) (y₁ * y₂) := by
  exact sameObservedSyntactic_trans
    (sameObservedSyntactic_mul_right (S := S) x₂ h₁)
    (sameObservedSyntactic_mul_left (S := S) y₁ h₂)

/--
The observed syntactic relation itself is two-sided stable.
-/
theorem sameObservedSyntactic_twoSidedStable :
    TwoSidedStableRel (SameObservedSyntactic S) := by
  constructor
  · intro a x y hxy
    exact sameObservedSyntactic_mul_left (S := S) a hxy
  · intro b x y hxy
    exact sameObservedSyntactic_mul_right (S := S) b hxy

end SemigroupCompatibility

section MonoidPreservationAndMaximality

variable {Q : Type u} [Monoid Q]
variable {S : Set Q}

/--
The observed syntactic relation preserves membership in `S`.

Use the empty context supplied by the unit.
-/
theorem sameObservedSyntactic_preserves_subset :
    PreservesSubset S (SameObservedSyntactic S) := by
  intro x y hxy
  have h := hxy 1 1
  simpa using h

/--
For a monoid, the observed syntactic relation is itself two-sided stable and
preserves the observed subset.
-/
theorem sameObservedSyntactic_is_stable_and_preserving :
    TwoSidedStableRel (SameObservedSyntactic S)
      ∧ PreservesSubset S (SameObservedSyntactic S) := by
  exact ⟨sameObservedSyntactic_twoSidedStable (S := S),
         sameObservedSyntactic_preserves_subset (S := S)⟩

/--
Maximality in monoid form.

If `R` is a two-sided stable relation preserving `S`, then `R` is contained in
the observed syntactic relation.  Since `SameObservedSyntactic S` is itself
two-sided stable and preserves `S`, it is the largest such relation.
-/
theorem sameObservedSyntactic_maximal
    {R : Q → Q → Prop}
    (hstable : TwoSidedStableRel R)
    (hpres : PreservesSubset S R) :
    ∀ x y : Q, R x y → SameObservedSyntactic S x y := by
  exact relation_le_sameObservedSyntactic hstable hpres

/--
A compact summary of the maximality package.
-/
theorem observedSyntacticCongruence_summary :
    TwoSidedStableRel (SameObservedSyntactic S)
      ∧ PreservesSubset S (SameObservedSyntactic S)
      ∧
      (∀ R : Q → Q → Prop,
        TwoSidedStableRel R →
        PreservesSubset S R →
        ∀ x y : Q, R x y → SameObservedSyntactic S x y) := by
  constructor
  · exact sameObservedSyntactic_twoSidedStable (S := S)
  constructor
  · exact sameObservedSyntactic_preserves_subset (S := S)
  · intro R hstable hpres x y hxy
    exact (sameObservedSyntactic_maximal
      (S := S) (R := R) hstable hpres) x y hxy

end MonoidPreservationAndMaximality

end LeanCfgProject
