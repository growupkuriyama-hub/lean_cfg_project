import LeanCfgProject.ObservedResidualConcept.ObservedResidualConceptCyclic
import LeanCfgProject.ObservedResidualConcept.ObservedResidualConceptReducedClassification

/-!
# Main checked theorem packages for observed residual concepts

This file is the paper-facing capstone for the ORC Lean experiments.

It does not introduce a new technical layer.  Instead, it bundles the checked
results from the preceding files into named theorem packages that can be cited
directly from the paper / formalization report.

Covered packages:

* point multiplication and kernel of the point map;
* residual adjunctions and closed-form residual descriptions;
* cyclic phase / Girard-style collapse;
* forward transport under observed pair isomorphism;
* reduced reverse classification from point/product/membership data.

This is intended as the final small file of the current ORC experiment batch.
-/

open Set

universe u v

namespace ObservedResidualConcept

variable {Q : Type u} [Monoid Q]

/-- Main algebraic core: point multiplication and kernel of the point map. -/
theorem main_point_kernel_package (S : Set Q) (x y : Q) :
    odot S (point S x) (point S y) = point S (x * y)
      ∧ (point S x = point S y ↔ Approx S x y) := by
  exact point_homomorphism_kernel S x y

/-- Main residual core: residuation for the concept product against a closed
right-hand side. -/
theorem main_residuation_package {S X V W : Set Q} (hW : Closed S W) :
    (odot S X V ⊆ W ↔ X ⊆ rdiv W V)
      ∧ (odot S V X ⊆ W ↔ X ⊆ ldiv V W) := by
  exact ⟨odot_subset_iff_rdiv (S := S) (X := X) (V := V) (W := W) hW,
    odot_subset_iff_ldiv (S := S) (V := V) (X := X) (W := W) hW⟩

/-- Main closed-form residual package. -/
theorem main_residual_closed_form_package (S : Set Q) (a b : Q) :
    Res S a b = ldiv ({a} : Set Q) (rdiv S ({b} : Set Q))
      ∧ Res S a b = ldiv (point S a) (rdiv S (point S b)) := by
  exact ⟨Res_eq_singleton_division S a b,
    Res_eq_point_division S a b⟩

/-- Main membership object package. -/
theorem main_membership_object_package (S : Set Q) :
    Res S 1 1 = S ∧ Closed S S := by
  exact ⟨Res_one_one_eq S, S_closed S⟩

/-- Main cyclic/Girard-style phase package. -/
theorem main_cyclic_phase_package {S U : Set Q}
    (hS : CyclicSet S) (hU : Closed S U) :
    cl S U = Perp S (Perp S U)
      ∧ rdiv S (ldiv U S) = U
      ∧ ldiv (rdiv S U) S = U := by
  exact cyclic_phase_collapse_package (S := S) (U := U) hS hU

variable {Q₁ : Type u} {Q₂ : Type v} [Monoid Q₁] [Monoid Q₂]

/-- Main forward classification package: observed-pair isomorphisms transport
the concept structure. -/
theorem main_forward_classification_package
    {S₁ : Set Q₁} {S₂ : Set Q₂}
    (e : ObservedPairIso S₁ S₂)
    (x y : Q₁) (A B U : Set Q₁) :
    e.toFun '' point S₁ x = point S₂ (e.toFun x)
      ∧ e.toFun '' cl S₁ U = cl S₂ (e.toFun '' U)
      ∧ e.toFun '' odot S₁ A B =
          odot S₂ (e.toFun '' A) (e.toFun '' B)
      ∧ (Approx S₁ x y ↔ Approx S₂ (e.toFun x) (e.toFun y)) := by
  exact e.transport_package x y A B U

/-- Main reduced reconstruction package: in a reduced pair, points recover
equality, membership, and multiplication. -/
theorem main_reduced_reconstruction_package
    {S : Set Q} (hred : Reduced S) (x y z : Q) :
    (point S x = point S y ↔ x = y)
      ∧ (point S x ⊆ S ↔ x ∈ S)
      ∧ (point S z = odot S (point S x) (point S y) ↔ z = x * y) := by
  exact reduced_reconstruction_package (S := S) hred x y z

/-- Main reduced reverse classification package. -/
theorem main_reduced_reverse_classification_package
    {S₁ : Set Q₁} {S₂ : Set Q₂}
    (e : ReducedPointObjectEquiv S₁ S₂)
    (hred₁ : Reduced S₁) (hred₂ : Reduced S₂)
    (x y : Q₁) (A B U : Set Q₁) :
    e.toFun (x * y) = e.toFun x * e.toFun y
      ∧ (e.toFun x ∈ S₂ ↔ x ∈ S₁)
      ∧ e.toFun '' point S₁ x = point S₂ (e.toFun x)
      ∧ e.toFun '' cl S₁ U = cl S₂ (e.toFun '' U)
      ∧ e.toFun '' odot S₁ A B =
          odot S₂ (e.toFun '' A) (e.toFun '' B) := by
  exact e.reduced_classification_package hred₁ hred₂ x y A B U

/--
Final checked ORC batch package.

This theorem intentionally bundles the single-pair algebraic pieces that are
stable enough to cite as the completed checked core of the present experiment
batch.
-/
theorem main_single_pair_batch_package
    {S U X V W : Set Q} (hW : Closed S W)
    (hcyc : CyclicSet S) (hU : Closed S U)
    (x y a b : Q) :
    (odot S (point S x) (point S y) = point S (x * y)
      ∧ (point S x = point S y ↔ Approx S x y))
      ∧ ((odot S X V ⊆ W ↔ X ⊆ rdiv W V)
          ∧ (odot S V X ⊆ W ↔ X ⊆ ldiv V W))
      ∧ (Res S a b = ldiv ({a} : Set Q) (rdiv S ({b} : Set Q))
          ∧ Res S a b = ldiv (point S a) (rdiv S (point S b)))
      ∧ (cl S U = Perp S (Perp S U)
          ∧ rdiv S (ldiv U S) = U
          ∧ ldiv (rdiv S U) S = U) := by
  exact ⟨main_point_kernel_package S x y,
    main_residuation_package (S := S) (X := X) (V := V) (W := W) hW,
    main_residual_closed_form_package S a b,
    main_cyclic_phase_package (S := S) (U := U) hcyc hU⟩

end ObservedResidualConcept
