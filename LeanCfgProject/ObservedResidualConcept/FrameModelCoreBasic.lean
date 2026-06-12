import LeanCfgProject.ObservedResidualConcept.ReducedFrameModelCoreDefs
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false

namespace LeanCfgProject

universe u v

/-
FrameModelCoreBasic.lean

Basic algebra of the lightweight FrameModelCore interface.
This prepares the reduced-frame representation layer without claiming the
full abstract representation theorem.
-/

variable {Q : Type u} [Mul Q] {S : Set Q}

namespace FrameModelCore

/-- The identity homomorphism of a frame model. -/
def id (M : FrameModelCore Q S) : Hom M M where
  map := fun c => c
  preserves_points := by
    intro gamma
    rfl
  preserves_frames := by
    intro a b
    rfl

/-- Composition of frame-model homomorphisms. -/
def comp {M N P : FrameModelCore Q S}
    (g : Hom N P) (f : Hom M N) : Hom M P where
  map := fun c => g.map (f.map c)
  preserves_points := by
    intro gamma
    rw [f.preserves_points gamma, g.preserves_points gamma]
  preserves_frames := by
    intro a b
    rw [f.preserves_frames a b, g.preserves_frames a b]

theorem id_apply (M : FrameModelCore Q S) (c : M.Carrier) :
    (id M).map c = c := by
  rfl

theorem comp_apply {M N P : FrameModelCore Q S}
    (g : Hom N P) (f : Hom M N) (c : M.Carrier) :
    (comp g f).map c = g.map (f.map c) := by
  rfl

theorem id_preserves_points
    (M : FrameModelCore Q S) (gamma : Q) :
    (id M).map (M.pt gamma) = M.pt gamma := by
  rfl

theorem id_preserves_frames
    (M : FrameModelCore Q S) (a b : Q) :
    (id M).map (M.fr a b) = M.fr a b := by
  rfl

theorem comp_preserves_points {M N P : FrameModelCore Q S}
    (g : Hom N P) (f : Hom M N) (gamma : Q) :
    (comp g f).map (M.pt gamma) = P.pt gamma := by
  exact (comp g f).preserves_points gamma

theorem comp_preserves_frames {M N P : FrameModelCore Q S}
    (g : Hom N P) (f : Hom M N) (a b : Q) :
    (comp g f).map (M.fr a b) = P.fr a b := by
  exact (comp g f).preserves_frames a b

/--
Frame extents of corresponding frames are forced by the common incidence,
independently of the model.
-/
theorem extent_frame_eq_extent_frame
    (M N : FrameModelCore Q S) (a b : Q) :
    M.extent (M.fr a b) = N.extent (N.fr a b) := by
  rw [extent_frame_eq_residual M a b, extent_frame_eq_residual N a b]

end FrameModelCore

end LeanCfgProject
