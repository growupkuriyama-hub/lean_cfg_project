import LeanCfgProject.ObservedResidualConcept.ObservedResidualConceptCore

/-!
# Reduced observed pairs and reconstruction from point concepts

This file is a small but important layer below the full observed
Myhill--Nerode classification theorem.

The quotient pair `Q / Approx S` is reduced: distinct elements are separated by
two-sided `S`-contexts.  In such a reduced observed pair, the point concept map

  `x ↦ point S x`

is faithful.  Moreover, membership in any closed extent is recoverable from
point containment:

  `point S x ⊆ W ↔ x ∈ W`.

These facts are precisely the ingredients used in the reverse direction of the
paper's classification theorem: once the object is reduced and the point
concepts plus membership object are marked, the underlying observed pair can be
recovered from them.
-/

open Set

universe u

namespace ObservedResidualConcept

variable {Q : Type u} [Monoid Q]

/-- A reduced observed pair is one in which the observed syntactic congruence is
equality.  This is the abstract version of passing to `Q / Approx S`. -/
def Reduced (S : Set Q) : Prop :=
  ∀ x y : Q, Approx S x y → x = y

/-- In a reduced observed pair, equality of point concepts is equality of
points. -/
theorem point_eq_iff_eq_of_reduced {S : Set Q} (hred : Reduced S) (x y : Q) :
    point S x = point S y ↔ x = y := by
  constructor
  · intro h
    exact hred x y ((point_eq_iff_Approx S x y).mp h)
  · intro h
    subst h
    rfl

/-- The point map is injective on reduced observed pairs. -/
theorem point_injective_of_reduced {S : Set Q} (hred : Reduced S) :
    Function.Injective (point S) := by
  intro x y hxy
  exact (point_eq_iff_eq_of_reduced (S := S) hred x y).mp hxy

/-- Membership in a closed extent is equivalent to containment of the point
concept in that extent. -/
theorem point_subset_closed_iff_mem {S W : Set Q} (hW : Closed S W) (x : Q) :
    point S x ⊆ W ↔ x ∈ W := by
  constructor
  · intro hsub
    exact hsub (subset_cl S ({x} : Set Q) (by simp))
  · intro hx
    intro z hz
    have hsingle : ({x} : Set Q) ⊆ W := by
      intro y hy
      simp at hy
      subst hy
      exact hx
    have hcl : point S x ⊆ cl S W := by
      exact cl_mono (S := S) hsingle
    rw [hW] at hcl
    exact hcl hz

/-- In particular, membership in the observed set `S` is recoverable from the
marked membership object and point containment. -/
theorem point_subset_S_iff_mem {S : Set Q} (x : Q) :
    point S x ⊆ S ↔ x ∈ S := by
  exact point_subset_closed_iff_mem (S := S) (W := S) (S_closed S) x

/-- The membership predicate of `S` is determined by point concepts. -/
theorem mem_iff_point_subset_S {S : Set Q} (x : Q) :
    x ∈ S ↔ point S x ⊆ S := by
  exact (point_subset_S_iff_mem (S := S) x).symm

/-- If a point concept is contained in a residual, then the corresponding
middle element is accepted by that frame. -/
theorem point_subset_Res_iff_mem {S : Set Q} (a b x : Q) :
    point S x ⊆ Res S a b ↔ a * x * b ∈ S := by
  constructor
  · intro hsub
    exact hsub (subset_cl S ({x} : Set Q) (by simp))
  · intro hx
    have hclosed : Closed S (Res S a b) := Res_closed S a b
    exact (point_subset_closed_iff_mem (S := S) (W := Res S a b) hclosed x).mpr hx

/-- The product of point concepts determines the product element in reduced
observed pairs. -/
theorem eq_mul_of_point_eq_odot {S : Set Q} (hred : Reduced S)
    {x y z : Q}
    (h : point S z = odot S (point S x) (point S y)) :
    z = x * y := by
  have h' : point S z = point S (x * y) := by
    simpa [point_mul] using h
  exact (point_eq_iff_eq_of_reduced (S := S) hred z (x * y)).mp h'

/-- Equivalent orientation of `eq_mul_of_point_eq_odot`. -/
theorem eq_mul_of_odot_eq_point {S : Set Q} (hred : Reduced S)
    {x y z : Q}
    (h : odot S (point S x) (point S y) = point S z) :
    z = x * y := by
  exact eq_mul_of_point_eq_odot (S := S) hred h.symm

/-- In reduced observed pairs, a point concept is the product of two point
concepts iff the underlying point is the product. -/
theorem point_eq_odot_iff_eq_mul_of_reduced {S : Set Q} (hred : Reduced S)
    (x y z : Q) :
    point S z = odot S (point S x) (point S y) ↔ z = x * y := by
  constructor
  · intro h
    exact eq_mul_of_point_eq_odot (S := S) hred h
  · intro h
    subst h
    exact (point_mul S x y).symm

/-- Reduced observed pairs separate any two distinct elements by a two-sided
membership context. -/
theorem exists_context_separates_of_ne_of_reduced {S : Set Q}
    (hred : Reduced S) {x y : Q} (hxy : x ≠ y) :
    ∃ a b : Q, ¬ (a * x * b ∈ S ↔ a * y * b ∈ S) := by
  by_contra hnone
  have happ : Approx S x y := by
    intro a b
    by_contra hiff
    exact hnone ⟨a, b, hiff⟩
  exact hxy (hred x y happ)

/-- Point concepts separate distinct elements in a reduced observed pair. -/
theorem point_ne_of_ne_of_reduced {S : Set Q}
    (hred : Reduced S) {x y : Q} (hxy : x ≠ y) :
    point S x ≠ point S y := by
  intro h
  exact hxy ((point_eq_iff_eq_of_reduced (S := S) hred x y).mp h)

/-- If two reduced observed pairs have a point-preserving map represented at the
level of underlying elements, point equality on images is equivalent to equality
of image elements.  This is a convenience lemma for later classification files.
-/
theorem image_point_eq_iff_eq_of_reduced
    {Q₂ : Type u} [Monoid Q₂] {S₂ : Set Q₂}
    (hred₂ : Reduced S₂) (f : Q → Q₂) (x y : Q) :
    point S₂ (f x) = point S₂ (f y) ↔ f x = f y := by
  exact point_eq_iff_eq_of_reduced (S := S₂) hred₂ (f x) (f y)

/-- Paper-facing reduced package. -/
theorem reduced_reconstruction_package {S : Set Q} (hred : Reduced S)
    (x y z : Q) :
    (point S x = point S y ↔ x = y)
      ∧ (point S x ⊆ S ↔ x ∈ S)
      ∧ (point S z = odot S (point S x) (point S y) ↔ z = x * y) := by
  exact ⟨point_eq_iff_eq_of_reduced (S := S) hred x y,
    point_subset_S_iff_mem (S := S) x,
    point_eq_odot_iff_eq_mul_of_reduced (S := S) hred x y z⟩

end ObservedResidualConcept
