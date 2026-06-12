import LeanCfgProject.ObservedResidualConcept.ObservedResidualConceptCore

/-!
# Approx quotient core

This file formalizes the quotient carrier `Q / Approx_S`.

Earlier ORC files deliberately avoided quotient-type bundling and worked on the
unquotiented carrier `Q`.  This file adds the smallest meaningful quotient layer:

* `Approx S` is packaged as a `Setoid`;
* the quotient `ApproxQuotient S` carries a monoid structure;
* the canonical map `Q →* ApproxQuotient S` has kernel exactly `Approx S`;
* the observed membership object descends to the quotient;
* every compatible monoid morphism factors uniquely through the quotient.

This is a theorem-body core for the paper's reduced observed monoid and
canonical reduced object discussion.  It does not attempt to bundle the full
concept quantale isomorphism; it proves the algebraic quotient layer underneath.
-/

open Set

universe u v

namespace ObservedResidualConcept

variable {Q : Type u} [Monoid Q]

/-- The observed syntactic congruence as a Lean setoid. -/
def ApproxSetoid (S : Set Q) : Setoid Q where
  r := Approx S
  iseqv := by
    refine ⟨?_, ?_, ?_⟩
    · intro x
      exact Approx_refl S x
    · intro x y hxy
      exact Approx_symm hxy
    · intro x y z hxy hyz
      exact Approx_trans hxy hyz

/-- Quotient of the observed carrier by the observed syntactic congruence. -/
abbrev ApproxQuotient (S : Set Q) : Type u :=
  Quotient (ApproxSetoid S)

/-- The quotient class of an observed element. -/
def approxClass (S : Set Q) (x : Q) : ApproxQuotient S :=
  Quotient.mk (ApproxSetoid S) x

/-- Equality of quotient classes is exactly `Approx S`. -/
theorem approxClass_eq_iff_Approx (S : Set Q) (x y : Q) :
    approxClass S x = approxClass S y ↔ Approx S x y := by
  constructor
  · intro h
    exact Quotient.exact h
  · intro h
    exact Quotient.sound h

/-- Equality of quotient classes is equivalently equality of point concepts. -/
theorem approxClass_eq_iff_point_eq (S : Set Q) (x y : Q) :
    approxClass S x = approxClass S y ↔ point S x = point S y := by
  exact Iff.trans (approxClass_eq_iff_Approx S x y)
    (point_eq_iff_Approx S x y).symm

/-- Multiplication on the quotient, induced by multiplication on `Q`. -/
def approxMul (S : Set Q) :
    ApproxQuotient S → ApproxQuotient S → ApproxQuotient S :=
  fun X Y =>
    Quotient.liftOn₂ X Y
      (fun x y => approxClass S (x * y))
      (by
        intro x x' y y' hxx' hyy'
        exact Quotient.sound (Approx_mul hxx' hyy'))

/-- The unit on the quotient. -/
def approxOne (S : Set Q) : ApproxQuotient S :=
  approxClass S 1

@[simp] theorem approxMul_class_class (S : Set Q) (x y : Q) :
    approxMul S (approxClass S x) (approxClass S y) = approxClass S (x * y) := by
  rfl

@[simp] theorem approxOne_eq_class_one (S : Set Q) :
    approxOne S = approxClass S 1 := rfl

/-- The quotient by `Approx S` is a monoid. -/
instance instApproxQuotientMonoid (S : Set Q) : Monoid (ApproxQuotient S) where
  one := approxOne S
  mul := approxMul S
  one_mul := by
    intro X
    refine Quotient.inductionOn X ?_
    intro x
    change approxClass S (1 * x) = approxClass S x
    simp
  mul_one := by
    intro X
    refine Quotient.inductionOn X ?_
    intro x
    change approxClass S (x * 1) = approxClass S x
    simp
  mul_assoc := by
    intro X Y Z
    refine Quotient.inductionOn X ?_
    intro x
    refine Quotient.inductionOn Y ?_
    intro y
    refine Quotient.inductionOn Z ?_
    intro z
    change approxClass S ((x * y) * z) = approxClass S (x * (y * z))
    simp [mul_assoc]

/-- The canonical quotient map. -/
def approxQuotientMap (S : Set Q) : Q →* ApproxQuotient S where
  toFun := approxClass S
  map_one' := rfl
  map_mul' := by
    intro x y
    rfl

/-- Kernel of the canonical quotient map is exactly `Approx S`. -/
theorem approxQuotientMap_eq_iff_Approx (S : Set Q) (x y : Q) :
    approxQuotientMap S x = approxQuotientMap S y ↔ Approx S x y := by
  exact approxClass_eq_iff_Approx S x y

/-- Kernel of the canonical quotient map is equivalently equality of point
concepts. -/
theorem approxQuotientMap_eq_iff_point_eq (S : Set Q) (x y : Q) :
    approxQuotientMap S x = approxQuotientMap S y ↔ point S x = point S y := by
  exact approxClass_eq_iff_point_eq S x y

/-- The observed membership object descended to the quotient. -/
def approxObservedSet (S : Set Q) : Set (ApproxQuotient S) :=
  {X | ∃ x : Q, x ∈ S ∧ approxClass S x = X}

/-- Membership in the descended observed set is well-defined on representatives. -/
theorem approxObservedSet_class_iff (S : Set Q) (x : Q) :
    approxClass S x ∈ approxObservedSet S ↔ x ∈ S := by
  constructor
  · intro hx
    rcases hx with ⟨y, hyS, hyx⟩
    have hyxApprox : Approx S y x :=
      (approxClass_eq_iff_Approx S y x).mp hyx
    have hyFrame : 1 * y * 1 ∈ S := by
      simpa using hyS
    have hxFrame : 1 * x * 1 ∈ S :=
      (hyxApprox 1 1).mp hyFrame
    simpa using hxFrame
  · intro hx
    exact ⟨x, hx, rfl⟩

/-- Same statement for the canonical quotient map. -/
theorem approxObservedSet_map_iff (S : Set Q) (x : Q) :
    approxQuotientMap S x ∈ approxObservedSet S ↔ x ∈ S := by
  exact approxObservedSet_class_iff S x

section Universal

variable {R : Type v} [Monoid R]

/-- A monoid morphism compatible with `Approx S` factors through the quotient. -/
def approxQuotientLift (S : Set Q) (f : Q →* R)
    (hcompat : ∀ x y : Q, Approx S x y → f x = f y) :
    ApproxQuotient S →* R where
  toFun := Quotient.lift (fun x : Q => f x)
    (by
      intro x y hxy
      exact hcompat x y hxy)
  map_one' := by
    change f 1 = 1
    exact f.map_one
  map_mul' := by
    intro X Y
    refine Quotient.inductionOn₂ X Y ?_
    intro x y
    change f (x * y) = f x * f y
    exact f.map_mul x y

@[simp] theorem approxQuotientLift_class (S : Set Q) (f : Q →* R)
    (hcompat : ∀ x y : Q, Approx S x y → f x = f y) (x : Q) :
    approxQuotientLift S f hcompat (approxClass S x) = f x := by
  rfl

/-- The lifted morphism composes with the quotient map to the original morphism. -/
theorem approxQuotientLift_comp_map (S : Set Q) (f : Q →* R)
    (hcompat : ∀ x y : Q, Approx S x y → f x = f y) :
    (approxQuotientLift S f hcompat).comp (approxQuotientMap S) = f := by
  ext x
  rfl

/-- Uniqueness of the quotient factorization. -/
theorem approxQuotientLift_unique (S : Set Q) (f : Q →* R)
    (hcompat : ∀ x y : Q, Approx S x y → f x = f y)
    (g : ApproxQuotient S →* R)
    (hg : ∀ x : Q, g (approxClass S x) = f x) :
    g = approxQuotientLift S f hcompat := by
  ext X
  refine Quotient.inductionOn X ?_
  intro x
  change g (approxClass S x) = approxQuotientLift S f hcompat (approxClass S x)
  simpa [approxQuotientLift] using hg x

/-- Universal property of the quotient map. -/
theorem approxQuotient_universal
    (S : Set Q) (f : Q →* R)
    (hcompat : ∀ x y : Q, Approx S x y → f x = f y) :
    ∃! g : ApproxQuotient S →* R,
      g.comp (approxQuotientMap S) = f := by
  refine ⟨approxQuotientLift S f hcompat, ?_, ?_⟩
  · exact approxQuotientLift_comp_map S f hcompat
  · intro g hg
    apply approxQuotientLift_unique S f hcompat
    intro x
    have hx := congrArg (fun h : Q →* R => h x) hg
    simpa [approxQuotientMap] using hx

/-- Paper-facing quotient core package. -/
theorem approx_quotient_core_package
    (S : Set Q) (f : Q →* R)
    (hcompat : ∀ x y : Q, Approx S x y → f x = f y)
    (x y : Q) :
    (approxQuotientMap S x = approxQuotientMap S y ↔ Approx S x y)
      ∧ (approxQuotientMap S x = approxQuotientMap S y ↔ point S x = point S y)
      ∧ (approxQuotientMap S x ∈ approxObservedSet S ↔ x ∈ S)
      ∧ ((approxQuotientLift S f hcompat).comp (approxQuotientMap S) = f) := by
  exact ⟨approxQuotientMap_eq_iff_Approx S x y,
    approxQuotientMap_eq_iff_point_eq S x y,
    approxObservedSet_map_iff S x,
    approxQuotientLift_comp_map S f hcompat⟩

end Universal

end ObservedResidualConcept
