import LeanCfgProject.UniversalFrameModelCore

set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false

namespace LeanCfgProject

universe u

/-
PointFrameCorollaries.lean

Additional corollaries from the canonical point-frame incidence core.
These are paper-facing consequences of the v27.1 canonical representation
discussion.
-/

variable {Q : Type u} [Mul Q]

theorem canonicalPoint_subset_frame_of_incidence
    (S : Set Q) {gamma a b : Q}
    (h : a * gamma * b ∈ S) :
    CanonicalPoint S gamma ⊆ CanonicalFrame S a b := by
  exact (canonicalPoint_subset_frame_iff S gamma a b).2 h

theorem incidence_of_canonicalPoint_subset_frame
    (S : Set Q) {gamma a b : Q}
    (h : CanonicalPoint S gamma ⊆ CanonicalFrame S a b) :
    a * gamma * b ∈ S := by
  exact (canonicalPoint_subset_frame_iff S gamma a b).1 h

theorem canonicalPoint_eq_of_sameObservedSyntactic
    (S : Set Q) {x y : Q}
    (hxy : SameObservedSyntactic S x y) :
    CanonicalPoint S x = CanonicalPoint S y := by
  exact (sameObservedSyntactic_iff_canonicalPoint_eq S x y).1 hxy

theorem sameObservedSyntactic_of_canonicalPoint_eq
    (S : Set Q) {x y : Q}
    (hxy : CanonicalPoint S x = CanonicalPoint S y) :
    SameObservedSyntactic S x y := by
  exact (sameObservedSyntactic_iff_canonicalPoint_eq S x y).2 hxy

theorem canonicalPoint_ne_of_not_sameObservedSyntactic
    (S : Set Q) {x y : Q}
    (hxy : ¬ SameObservedSyntactic S x y) :
    CanonicalPoint S x ≠ CanonicalPoint S y := by
  intro hEq
  exact hxy (sameObservedSyntactic_of_canonicalPoint_eq S hEq)

theorem frame_incidence_respects_point_collapse
    (S : Set Q) {x y a b : Q}
    (hxy : CanonicalPoint S x = CanonicalPoint S y) :
    a * x * b ∈ S ↔ a * y * b ∈ S := by
  have hSyn : SameObservedSyntactic S x y :=
    sameObservedSyntactic_of_canonicalPoint_eq S hxy
  exact hSyn a b

theorem point_collapse_respects_all_frames
    (S : Set Q) {x y : Q}
    (hxy : CanonicalPoint S x = CanonicalPoint S y) :
    ∀ a b : Q,
      (CanonicalPoint S x ⊆ CanonicalFrame S a b)
        ↔
      (CanonicalPoint S y ⊆ CanonicalFrame S a b) := by
  intro a b
  constructor
  · intro hx
    rw [hxy] at hx
    exact hx
  · intro hy
    rw [← hxy] at hy
    exact hy

end LeanCfgProject
