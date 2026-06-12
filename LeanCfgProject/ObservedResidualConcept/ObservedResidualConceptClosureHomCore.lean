import LeanCfgProject.ObservedResidualConcept.ObservedResidualConceptCore

/-!
# Closure-homomorphism core

This file checks a compact but useful algebraic core for the paper.

The paper's optional "initial concept semantics" discussion rests on two simple
homomorphism facts:

* a multiplicative word observation sends language concatenation to explicit
  set multiplication;
* the residual closure `cl_S` sends powerset multiplication to the closed
  concept product `odot`.

This file does **not** formalize the full Ginsburg--Rice / Mezei--Wright least
fixed-point theorem.  It checks the algebraic bridge needed below that level:
the composite `cl_S ∘ q[·]` respects binary products, and `cl_S` respects
arbitrary joins after closure.

This is a meaningful theorem-body layer for the v2 paper, while avoiding a
large formalization of CFG polynomial systems.
-/

open Set

universe u v w

namespace ObservedResidualConcept

variable {W : Type u} {Q : Type v}

/-- Image of a set under an observation map. -/
def ObsImage (q : W → Q) (A : Set W) : Set Q :=
  q '' A

section ClosureHom

variable [Monoid Q]

/-- The closure of a union of already-closed pieces is the closure of the
original union.  This is the join part of the closure quotient. -/
theorem cl_iUnion_cl_eq {ι : Sort w} (S : Set Q) (A : ι → Set Q) :
    cl S (⋃ i, cl S (A i)) = cl S (⋃ i, A i) := by
  apply Set.Subset.antisymm
  · have hsub : (⋃ i, cl S (A i)) ⊆ cl S (⋃ i, A i) := by
      intro x hx
      rcases Set.mem_iUnion.mp hx with ⟨i, hxi⟩
      have hi : A i ⊆ (⋃ i, A i) := by
        intro y hy
        exact Set.mem_iUnion.mpr ⟨i, hy⟩
      exact cl_mono (S := S) hi hxi
    have hcl : cl S (⋃ i, cl S (A i)) ⊆ cl S (cl S (⋃ i, A i)) :=
      cl_mono (S := S) hsub
    simpa [cl_idem] using hcl
  · have hsub : (⋃ i, A i) ⊆ (⋃ i, cl S (A i)) := by
      intro x hx
      rcases Set.mem_iUnion.mp hx with ⟨i, hxi⟩
      exact Set.mem_iUnion.mpr ⟨i, subset_cl S (A i) hxi⟩
    exact cl_mono (S := S) hsub

/-- Binary union version of `cl_iUnion_cl_eq`. -/
theorem cl_union_cl_eq (S A B : Set Q) :
    cl S (cl S A ∪ cl S B) = cl S (A ∪ B) := by
  simpa [Set.iUnion_bool_eq, Bool.forall_bool, Bool.false_eq_true]
    using (cl_iUnion_cl_eq (S := S) (A := fun b : Bool => cond b B A))

/-- Multiplicative part of the closure quotient:
closing the raw product is the same as multiplying the closed images by `odot`.

This is the precise theorem-body version of the statement that `cl_S` is the
quotient map from the powerset quantale to the residual concept quantale. -/
theorem cl_mulSet_eq_odot_cl_cl (S A B : Set Q) :
    cl S (mulSet A B) = odot S (cl S A) (cl S B) := by
  unfold odot
  apply Set.Subset.antisymm
  · have hsub : mulSet A B ⊆ mulSet (cl S A) (cl S B) :=
      mulSet_mono (subset_cl S A) (subset_cl S B)
    exact cl_mono (S := S) hsub
  · have hN : mulSet (cl S A) (cl S B) ⊆ cl S (mulSet A B) :=
      mul_cl_subset_cl_mul S A B
    have hcl :
        cl S (mulSet (cl S A) (cl S B)) ⊆ cl S (cl S (mulSet A B)) :=
      cl_mono (S := S) hN
    simpa [cl_idem] using hcl

/-- Closing the product is insensitive to closing the left factor first. -/
theorem cl_mulSet_cl_left_eq (S A B : Set Q) :
    cl S (mulSet (cl S A) B) = cl S (mulSet A B) := by
  apply Set.Subset.antisymm
  · have hsub : mulSet (cl S A) B ⊆ mulSet (cl S A) (cl S B) :=
      mulSet_mono (by intro x hx; exact hx) (subset_cl S B)
    have h1 : cl S (mulSet (cl S A) B) ⊆
        cl S (mulSet (cl S A) (cl S B)) :=
      cl_mono (S := S) hsub
    have h2 : cl S (mulSet (cl S A) (cl S B)) =
        cl S (mulSet A B) := by
      rw [← cl_mulSet_eq_odot_cl_cl (S := S) (A := A) (B := B)]
    simpa [h2] using h1
  · have hsub : mulSet A B ⊆ mulSet (cl S A) B :=
      mulSet_mono (subset_cl S A) (by intro x hx; exact hx)
    exact cl_mono (S := S) hsub

/-- Closing the product is insensitive to closing the right factor first. -/
theorem cl_mulSet_cl_right_eq (S A B : Set Q) :
    cl S (mulSet A (cl S B)) = cl S (mulSet A B) := by
  apply Set.Subset.antisymm
  · have hsub : mulSet A (cl S B) ⊆ mulSet (cl S A) (cl S B) :=
      mulSet_mono (subset_cl S A) (by intro x hx; exact hx)
    have h1 : cl S (mulSet A (cl S B)) ⊆
        cl S (mulSet (cl S A) (cl S B)) :=
      cl_mono (S := S) hsub
    have h2 : cl S (mulSet (cl S A) (cl S B)) =
        cl S (mulSet A B) := by
      rw [← cl_mulSet_eq_odot_cl_cl (S := S) (A := A) (B := B)]
    simpa [h2] using h1
  · have hsub : mulSet A B ⊆ mulSet A (cl S B) :=
      mulSet_mono (by intro x hx; exact hx) (subset_cl S B)
    exact cl_mono (S := S) hsub

/-- Closing both factors before raw multiplication does not change the final
closed product. -/
theorem cl_mulSet_cl_cl_eq (S A B : Set Q) :
    cl S (mulSet (cl S A) (cl S B)) = cl S (mulSet A B) := by
  rw [← cl_mulSet_eq_odot_cl_cl (S := S) (A := A) (B := B)]

/-- Paper-facing closure-homomorphism package. -/
theorem closure_hom_core_package (S A B : Set Q) :
    cl S (mulSet A B) = odot S (cl S A) (cl S B)
      ∧ cl S (mulSet (cl S A) B) = cl S (mulSet A B)
      ∧ cl S (mulSet A (cl S B)) = cl S (mulSet A B)
      ∧ cl S (mulSet (cl S A) (cl S B)) = cl S (mulSet A B) := by
  exact ⟨cl_mulSet_eq_odot_cl_cl S A B,
    cl_mulSet_cl_left_eq S A B,
    cl_mulSet_cl_right_eq S A B,
    cl_mulSet_cl_cl_eq S A B⟩

end ClosureHom

section ObservationImage

variable [Monoid W] [Monoid Q]

/-- A multiplicative observation map.  We keep this as a lightweight structure
rather than importing a bundled monoid hom, to match the paper notation. -/
structure MultiplicativeObservation (W : Type u) (Q : Type v)
    [Monoid W] [Monoid Q] where
  toFun : W → Q
  map_one : toFun 1 = 1
  map_mul : ∀ x y : W, toFun (x * y) = toFun x * toFun y

instance : CoeFun (MultiplicativeObservation W Q) (fun _ => W → Q) where
  coe q := q.toFun

/-- A multiplicative observation sends set products to set products. -/
theorem obsImage_mulSet_eq_mulSet_obsImage
    (q : MultiplicativeObservation W Q) (A B : Set W) :
    q '' mulSet A B = mulSet (q '' A) (q '' B) := by
  ext z
  constructor
  · intro hz
    rcases hz with ⟨w, hw, rfl⟩
    rcases hw with ⟨a, ha, b, hb, hmul⟩
    subst w
    exact ⟨q a, ⟨a, ha, rfl⟩, q b, ⟨b, hb, rfl⟩, by
      simpa using (q.map_mul a b).symm⟩
  · intro hz
    rcases hz with ⟨qa, hqa, qb, hqb, hmul⟩
    rcases hqa with ⟨a, ha, rfl⟩
    rcases hqb with ⟨b, hb, rfl⟩
    refine ⟨a * b, ?_, ?_⟩
    · exact ⟨a, ha, b, hb, rfl⟩
    · calc
        q (a * b) = q a * q b := q.map_mul a b
        _ = z := hmul

/-- The composite `cl_S ∘ q[·]` sends language/set product to concept product. -/
theorem cl_obsImage_mulSet_eq_odot_cl_obsImage
    (S : Set Q) (q : MultiplicativeObservation W Q) (A B : Set W) :
    cl S (q '' mulSet A B)
      = odot S (cl S (q '' A)) (cl S (q '' B)) := by
  calc
    cl S (q '' mulSet A B)
        = cl S (mulSet (q '' A) (q '' B)) := by
          rw [obsImage_mulSet_eq_mulSet_obsImage q A B]
    _ = odot S (cl S (q '' A)) (cl S (q '' B)) :=
          cl_mulSet_eq_odot_cl_cl S (q '' A) (q '' B)

/-- Paper-facing composite homomorphism package. -/
theorem composite_cl_observation_hom_package
    (S : Set Q) (q : MultiplicativeObservation W Q) (A B : Set W) :
    q '' mulSet A B = mulSet (q '' A) (q '' B)
      ∧ cl S (q '' mulSet A B)
          = odot S (cl S (q '' A)) (cl S (q '' B)) := by
  exact ⟨obsImage_mulSet_eq_mulSet_obsImage q A B,
    cl_obsImage_mulSet_eq_odot_cl_obsImage S q A B⟩

end ObservationImage

end ObservedResidualConcept
