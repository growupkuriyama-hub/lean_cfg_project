import LeanCfgProject.ObservedSyntacticSaturation

set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace LeanCfgProject

universe u v

/-
ObservedFactorMinimality.lean

Planned theorem item 4, next theorem-body experiment.

Goal:
  prove the minimality/maximality half of observed syntactic quotient
  invariance.

Main mathematical statement:
  If π : Q → Qbar is multiplicative and S is the exact pullback of Sbar
  along π, then every fiber of π is contained in SameObservedSyntactic S.

    π x = π y  ==>  x ≈_S y.

Together with ObservedSyntacticSaturation.lean, this gives the clean
equivalence:

    π⁻¹(π(S)) = S  <->  every π-fiber is contained in ≈_S,

for multiplicative π.
-/

variable {Q : Type u} {Qbar : Type v}
variable [Semigroup Q] [Semigroup Qbar]

/--
Exact observed pullback forces fibers to be observed-syntactic.

This is the key "minimality" direction:
any factor map that preserves the observed accepting set cannot identify
two elements unless they are already equivalent for all two-sided contexts.
-/
theorem sameObservedSyntactic_of_factor_eq_of_pullback
    (π : Q → Qbar)
    (hπ_mul : ∀ x y : Q, π (x * y) = π x * π y)
    (S : Set Q) (Sbar : Set Qbar)
    (hS_pullback : ∀ x : Q, π x ∈ Sbar ↔ x ∈ S)
    {x y : Q}
    (hxy : π x = π y) :
    SameObservedSyntactic S x y := by
  intro a b
  constructor
  · intro hxS
    have hxbar_pre : π (a * x * b) ∈ Sbar :=
      (hS_pullback (a * x * b)).mpr hxS
    have hmapx :
        π (a * x * b) = π a * π x * π b :=
      map_three_mul π hπ_mul a x b
    have hbarx : π a * π x * π b ∈ Sbar := by
      rw [← hmapx]
      exact hxbar_pre
    have hbary : π a * π y * π b ∈ Sbar := by
      simpa [hxy] using hbarx
    have hmapy :
        π (a * y * b) = π a * π y * π b :=
      map_three_mul π hπ_mul a y b
    have hybar_pre : π (a * y * b) ∈ Sbar := by
      rw [hmapy]
      exact hbary
    exact (hS_pullback (a * y * b)).mp hybar_pre
  · intro hyS
    have hybar_pre : π (a * y * b) ∈ Sbar :=
      (hS_pullback (a * y * b)).mpr hyS
    have hmapy :
        π (a * y * b) = π a * π y * π b :=
      map_three_mul π hπ_mul a y b
    have hbary : π a * π y * π b ∈ Sbar := by
      rw [← hmapy]
      exact hybar_pre
    have hbarx : π a * π x * π b ∈ Sbar := by
      simpa [hxy] using hbary
    have hmapx :
        π (a * x * b) = π a * π x * π b :=
      map_three_mul π hπ_mul a x b
    have hxbar_pre : π (a * x * b) ∈ Sbar := by
      rw [hmapx]
      exact hbarx
    exact (hS_pullback (a * x * b)).mp hxbar_pre

/--
Kernel/fiber containment form of the preceding theorem.
-/
theorem factor_kernel_subset_sameObservedSyntactic
    (π : Q → Qbar)
    (hπ_mul : ∀ x y : Q, π (x * y) = π x * π y)
    (S : Set Q) (Sbar : Set Qbar)
    (hS_pullback : ∀ x : Q, π x ∈ Sbar ↔ x ∈ S) :
    ∀ x y : Q, π x = π y → SameObservedSyntactic S x y := by
  intro x y hxy
  exact sameObservedSyntactic_of_factor_eq_of_pullback
    π hπ_mul S Sbar hS_pullback hxy

/--
For the image observed set `π(S)`, exact pullback is equivalent to every fiber
being contained in SameObservedSyntactic S.

The reverse direction uses the saturation theorem from
ObservedSyntacticSaturation.lean; the forward direction is the new minimality
calculation in this file.
-/
theorem image_pullback_iff_fibers_sameObservedSyntactic
    {Q : Type u} [Monoid Q]
    {Qbar : Type v} [Semigroup Qbar]
    (π : Q → Qbar)
    (hπ_mul : ∀ x y : Q, π (x * y) = π x * π y)
    (S : Set Q) :
    (∀ x : Q, π x ∈ Set.image π S ↔ x ∈ S)
      ↔
    (∀ x y : Q, π x = π y → SameObservedSyntactic S x y) := by
  constructor
  · intro hpullback x y hxy
    exact sameObservedSyntactic_of_factor_eq_of_pullback
      π hπ_mul S (Set.image π S) hpullback hxy
  · intro hfiber x
    exact image_pullback_eq_of_fibers_sameObservedSyntactic
      π S hfiber x

/--
If the image-pullback condition holds, then the abstract residual theorem can
be specialized with `Sbar = π(S)` without separately assuming fiber saturation.
-/
theorem imagePullbackFactor_residual_image_eq
    {Q : Type u} [Monoid Q]
    {Qbar : Type v} [Semigroup Qbar]
    (π : Q → Qbar)
    (hπ_mul : ∀ x y : Q, π (x * y) = π x * π y)
    (hπ_surj : ∀ y : Qbar, ∃ x : Q, π x = y)
    (S : Set Q)
    (hpullback : ∀ x : Q, π x ∈ Set.image π S ↔ x ∈ S)
    (a b : Q) :
    Set.image π (TwoSidedResidual S a b)
      =
    TwoSidedResidual (Set.image π S) (π a) (π b) := by
  exact quotient_residual_image_eq
    π hπ_mul hπ_surj S (Set.image π S) hpullback a b

/--
If the image-pullback condition holds, then closure image preservation holds
with `Sbar = π(S)`.
-/
theorem imagePullbackFactor_conceptClosure_image_eq
    {Q : Type u} [Monoid Q]
    {Qbar : Type v} [Semigroup Qbar]
    (π : Q → Qbar)
    (hπ_mul : ∀ x y : Q, π (x * y) = π x * π y)
    (hπ_surj : ∀ y : Qbar, ∃ x : Q, π x = y)
    (S : Set Q)
    (hpullback : ∀ x : Q, π x ∈ Set.image π S ↔ x ∈ S)
    (W : Set Q) :
    Set.image π (ConceptClosure S W)
      =
    ConceptClosure (Set.image π S) (Set.image π W) := by
  exact quotient_conceptClosure_image_eq
    π hπ_mul hπ_surj S (Set.image π S) hpullback W

/--
If the image-pullback condition holds, then ConceptProduct image preservation
holds with `Sbar = π(S)`.
-/
theorem imagePullbackFactor_conceptProduct_image_eq
    {Q : Type u} [Monoid Q]
    {Qbar : Type v} [Semigroup Qbar]
    (π : Q → Qbar)
    (hπ_mul : ∀ x y : Q, π (x * y) = π x * π y)
    (hπ_surj : ∀ y : Qbar, ∃ x : Q, π x = y)
    (S : Set Q)
    (hpullback : ∀ x : Q, π x ∈ Set.image π S ↔ x ∈ S)
    (A B : Set Q) :
    Set.image π (ConceptProduct S A B)
      =
    ConceptProduct (Set.image π S) (Set.image π A) (Set.image π B) := by
  exact quotient_conceptProduct_image_eq
    π hπ_mul hπ_surj S (Set.image π S) hpullback A B

end LeanCfgProject
