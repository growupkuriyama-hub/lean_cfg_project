import LeanCfgProject.ObservedResidualConcept.ObservedResidualConceptClassificationCore
import LeanCfgProject.ObservedResidualConcept.ObservedResidualConceptReduced

/-!
# Reduced classification from point/product/membership data

This file proves a reduced reverse-classification core.

In the reduced situation (`Approx S` is equality), a bijection of underlying
sets that preserves:

* point-level unit;
* point-level multiplication;
* point-containment in the marked membership object `S`;

is forced to be an isomorphism of observed monoid pairs.

This is the key theorem-body layer for the reverse direction of the paper's
observed Myhill--Nerode classification, avoiding quotient construction and
bundled quantale isomorphisms.
-/

open Set

universe u v

namespace ObservedResidualConcept

variable {Q₁ : Type u} {Q₂ : Type v} [Monoid Q₁] [Monoid Q₂]

/--
A point-object equivalence between two observed pairs.

The structure deliberately states preservation at the concept-object level:
unit and multiplication are preserved after applying `point`, and membership is
preserved as containment in the marked membership object `S`.

For reduced pairs, these point-level statements force the ordinary monoid-pair
isomorphism laws.
-/
structure ReducedPointObjectEquiv (S₁ : Set Q₁) (S₂ : Set Q₂) where
  toFun : Q₁ → Q₂
  invFun : Q₂ → Q₁
  left_inv : ∀ x : Q₁, invFun (toFun x) = x
  right_inv : ∀ y : Q₂, toFun (invFun y) = y
  map_point_one :
    point S₂ (toFun 1) = point S₂ 1
  map_point_mul :
    ∀ x y : Q₁,
      point S₂ (toFun (x * y))
        =
      odot S₂ (point S₂ (toFun x)) (point S₂ (toFun y))
  inv_point_one :
    point S₁ (invFun 1) = point S₁ 1
  inv_point_mul :
    ∀ x y : Q₂,
      point S₁ (invFun (x * y))
        =
      odot S₁ (point S₁ (invFun x)) (point S₁ (invFun y))
  mem_point_iff :
    ∀ x : Q₁, point S₂ (toFun x) ⊆ S₂ ↔ point S₁ x ⊆ S₁

namespace ReducedPointObjectEquiv

variable {S₁ : Set Q₁} {S₂ : Set Q₂}
variable (e : ReducedPointObjectEquiv S₁ S₂)

@[simp] theorem left_inv_apply (x : Q₁) : e.invFun (e.toFun x) = x :=
  e.left_inv x

@[simp] theorem right_inv_apply (y : Q₂) : e.toFun (e.invFun y) = y :=
  e.right_inv y

/-- Point-level unit preservation forces ordinary unit preservation in a
reduced target. -/
theorem map_one_of_reduced (hred₂ : Reduced S₂) :
    e.toFun 1 = 1 := by
  exact (point_eq_iff_eq_of_reduced (S := S₂) hred₂ (e.toFun 1) 1).mp
    e.map_point_one

/-- Point-level multiplication preservation forces ordinary multiplication
preservation in a reduced target. -/
theorem map_mul_of_reduced (hred₂ : Reduced S₂) (x y : Q₁) :
    e.toFun (x * y) = e.toFun x * e.toFun y := by
  have hpoint :
      point S₂ (e.toFun (x * y))
        =
      point S₂ (e.toFun x * e.toFun y) := by
    calc
      point S₂ (e.toFun (x * y))
          =
        odot S₂ (point S₂ (e.toFun x)) (point S₂ (e.toFun y)) :=
          e.map_point_mul x y
      _ = point S₂ (e.toFun x * e.toFun y) :=
          point_mul S₂ (e.toFun x) (e.toFun y)
  exact (point_eq_iff_eq_of_reduced (S := S₂) hred₂
    (e.toFun (x * y)) (e.toFun x * e.toFun y)).mp hpoint

/-- Point-level unit preservation for the inverse forces inverse unit
preservation in a reduced source. -/
theorem inv_map_one_of_reduced (hred₁ : Reduced S₁) :
    e.invFun 1 = 1 := by
  exact (point_eq_iff_eq_of_reduced (S := S₁) hred₁ (e.invFun 1) 1).mp
    e.inv_point_one

/-- Point-level multiplication preservation for the inverse forces ordinary
multiplication preservation in a reduced source. -/
theorem inv_map_mul_of_reduced (hred₁ : Reduced S₁) (x y : Q₂) :
    e.invFun (x * y) = e.invFun x * e.invFun y := by
  have hpoint :
      point S₁ (e.invFun (x * y))
        =
      point S₁ (e.invFun x * e.invFun y) := by
    calc
      point S₁ (e.invFun (x * y))
          =
        odot S₁ (point S₁ (e.invFun x)) (point S₁ (e.invFun y)) :=
          e.inv_point_mul x y
      _ = point S₁ (e.invFun x * e.invFun y) :=
          point_mul S₁ (e.invFun x) (e.invFun y)
  exact (point_eq_iff_eq_of_reduced (S := S₁) hred₁
    (e.invFun (x * y)) (e.invFun x * e.invFun y)).mp hpoint

/-- Membership preservation in the marked object `S` follows from point
containment preservation. -/
theorem mem_iff_of_point_mem (x : Q₁) :
    e.toFun x ∈ S₂ ↔ x ∈ S₁ := by
  exact Iff.trans (mem_iff_point_subset_S (S := S₂) (e.toFun x))
    (Iff.trans (e.mem_point_iff x) (point_subset_S_iff_mem (S := S₁) x))

/--
Reduced reverse classification core.

A point-object equivalence between reduced observed pairs induces an
`ObservedPairIso`, i.e. an isomorphism of the underlying observed monoid pairs.
-/
def toObservedPairIso (hred₁ : Reduced S₁) (hred₂ : Reduced S₂) :
    ObservedPairIso S₁ S₂ where
  toFun := e.toFun
  invFun := e.invFun
  left_inv := e.left_inv
  right_inv := e.right_inv
  map_one := e.map_one_of_reduced hred₂
  map_mul := e.map_mul_of_reduced hred₂
  inv_map_one := e.inv_map_one_of_reduced hred₁
  inv_map_mul := e.inv_map_mul_of_reduced hred₁
  mem_iff := e.mem_iff_of_point_mem

/-- Re-export: the induced observed pair isomorphism transports residuals. -/
theorem induced_image_Res (hred₁ : Reduced S₁) (hred₂ : Reduced S₂)
    (a b : Q₁) :
    e.toFun '' Res S₁ a b = Res S₂ (e.toFun a) (e.toFun b) := by
  exact (e.toObservedPairIso hred₁ hred₂).image_Res a b

/-- Re-export: the induced observed pair isomorphism transports closures. -/
theorem induced_image_cl (hred₁ : Reduced S₁) (hred₂ : Reduced S₂)
    (U : Set Q₁) :
    e.toFun '' cl S₁ U = cl S₂ (e.toFun '' U) := by
  exact (e.toObservedPairIso hred₁ hred₂).image_cl U

/-- Re-export: the induced observed pair isomorphism transports point concepts. -/
theorem induced_image_point (hred₁ : Reduced S₁) (hred₂ : Reduced S₂)
    (x : Q₁) :
    e.toFun '' point S₁ x = point S₂ (e.toFun x) := by
  exact (e.toObservedPairIso hred₁ hred₂).image_point x

/-- Re-export: the induced observed pair isomorphism transports concept
products. -/
theorem induced_image_odot (hred₁ : Reduced S₁) (hred₂ : Reduced S₂)
    (A B : Set Q₁) :
    e.toFun '' odot S₁ A B =
      odot S₂ (e.toFun '' A) (e.toFun '' B) := by
  exact (e.toObservedPairIso hred₁ hred₂).image_odot A B

/-- Re-export: the induced observed pair isomorphism transports the observed
syntactic congruence. -/
theorem induced_approx_iff (hred₁ : Reduced S₁) (hred₂ : Reduced S₂)
    (x y : Q₁) :
    Approx S₁ x y ↔ Approx S₂ (e.toFun x) (e.toFun y) := by
  exact (e.toObservedPairIso hred₁ hred₂).approx_iff x y

/-- Paper-facing reduced classification package. -/
theorem reduced_classification_package
    (hred₁ : Reduced S₁) (hred₂ : Reduced S₂)
    (x y : Q₁) (A B U : Set Q₁) :
    e.toFun (x * y) = e.toFun x * e.toFun y
      ∧ (e.toFun x ∈ S₂ ↔ x ∈ S₁)
      ∧ e.toFun '' point S₁ x = point S₂ (e.toFun x)
      ∧ e.toFun '' cl S₁ U = cl S₂ (e.toFun '' U)
      ∧ e.toFun '' odot S₁ A B =
          odot S₂ (e.toFun '' A) (e.toFun '' B) := by
  exact ⟨e.map_mul_of_reduced hred₂ x y,
    e.mem_iff_of_point_mem x,
    e.induced_image_point hred₁ hred₂ x,
    e.induced_image_cl hred₁ hred₂ U,
    e.induced_image_odot hred₁ hred₂ A B⟩

end ReducedPointObjectEquiv

end ObservedResidualConcept
