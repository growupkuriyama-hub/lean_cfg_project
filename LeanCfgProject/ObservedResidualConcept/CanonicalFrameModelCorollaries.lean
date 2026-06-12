import LeanCfgProject.ObservedResidualConcept.FrameModelCoreBasic
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false

namespace LeanCfgProject

universe u

/-
CanonicalFrameModelCorollaries.lean

Corollaries for the canonical FrameModelCore object.
-/

variable (Q : Type u) [Mul Q] (S : Set Q)

theorem canonicalFrameModelCore_incidence_iff
    (gamma a b : Q) :
    (canonicalFrameModelCore Q S).le
      ((canonicalFrameModelCore Q S).pt gamma)
      ((canonicalFrameModelCore Q S).fr a b)
      ↔ a * gamma * b ∈ S := by
  exact (canonicalFrameModelCore Q S).incidence gamma a b

theorem canonicalFrameModelCore_extent_frame_eq_canonicalFrame
    (a b : Q) :
    (canonicalFrameModelCore Q S).extent
      ((canonicalFrameModelCore Q S).fr a b)
      =
    CanonicalFrame S a b := by
  simpa [CanonicalFrame] using
    canonicalFrameModelCore_extent_frame Q S a b

theorem canonicalFrameModelCore_extent_frame_eq_frameResidual
    (a b : Q) :
    (canonicalFrameModelCore Q S).extent
      ((canonicalFrameModelCore Q S).fr a b)
      =
    FrameResidual S a b := by
  simpa [FrameResidual] using
    canonicalFrameModelCore_extent_frame Q S a b

theorem canonicalFrameModelCore_point_eq_iff
    (x y : Q) :
    (canonicalFrameModelCore Q S).pt x =
      (canonicalFrameModelCore Q S).pt y
    ↔ SameObservedSyntactic S x y := by
  exact canonicalFrameModelCore_point_collapse Q S x y

theorem canonicalFrameModelCore_point_ne_of_not_same
    {x y : Q}
    (hxy : ¬ SameObservedSyntactic S x y) :
    (canonicalFrameModelCore Q S).pt x ≠
      (canonicalFrameModelCore Q S).pt y := by
  intro hEq
  exact hxy ((canonicalFrameModelCore_point_eq_iff Q S x y).1 hEq)

theorem canonicalFrameModelCore_same_of_point_eq
    {x y : Q}
    (hxy :
      (canonicalFrameModelCore Q S).pt x =
        (canonicalFrameModelCore Q S).pt y) :
    SameObservedSyntactic S x y := by
  exact (canonicalFrameModelCore_point_eq_iff Q S x y).1 hxy

theorem canonicalFrameModelCore_point_eq_of_same
    {x y : Q}
    (hxy : SameObservedSyntactic S x y) :
    (canonicalFrameModelCore Q S).pt x =
      (canonicalFrameModelCore Q S).pt y := by
  exact (canonicalFrameModelCore_point_eq_iff Q S x y).2 hxy

end LeanCfgProject
