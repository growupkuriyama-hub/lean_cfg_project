import LeanCfgProject.ObservedSyntacticPaperCorollaries

set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false

namespace LeanCfgProject

universe u

/-
ObservedFrameStructure.lean

Basic finite-observed learning layer for the v26.4 paper draft.

The learning target is not the language itself. It is the frame-selected
observed concept data determined by a fixed observed pair (Q,S).
-/

variable {Q : Type u} [Mul Q]

/-- The residual selected by a two-sided observed frame. -/
def FrameResidual (S : Set Q) (a b : Q) : Set Q :=
  TwoSidedResidual S a b

/--
A frame is a single observed block when all elements of its residual are
indistinguishable by the observed syntactic relation.
-/
def SingleObservedBlock (S : Set Q) (a b : Q) : Prop :=
  ∀ x y : Q,
    x ∈ FrameResidual S a b →
    y ∈ FrameResidual S a b →
      SameObservedSyntactic S x y

/--
The frame-concept structure used as the finite observed learning target.
It records the observed syntactic relation, the frame residual map, and the
single-block predicate.
-/
structure ObservedFrameStructure (Q : Type u) where
  rel : Q → Q → Prop
  residual : Q → Q → Set Q
  singleBlock : Q → Q → Prop

/-- The canonical frame-concept structure determined by `(Q,S)`. -/
def canonicalObservedFrameStructure (S : Set Q) :
    ObservedFrameStructure Q where
  rel := SameObservedSyntactic S
  residual := FrameResidual S
  singleBlock := SingleObservedBlock S

theorem canonicalObservedFrameStructure_rel
    (S : Set Q) :
    (canonicalObservedFrameStructure (Q := Q) S).rel =
      SameObservedSyntactic S := by
  rfl

theorem canonicalObservedFrameStructure_residual
    (S : Set Q) :
    (canonicalObservedFrameStructure (Q := Q) S).residual =
      FrameResidual S := by
  rfl

theorem canonicalObservedFrameStructure_singleBlock
    (S : Set Q) :
    (canonicalObservedFrameStructure (Q := Q) S).singleBlock =
      SingleObservedBlock S := by
  rfl

/-- Every frame residual in the canonical structure is a closed concept extent. -/
theorem canonical_frameResidual_closed
    (S : Set Q) (a b : Q) :
    ConceptClosure S (FrameResidual S a b) =
      FrameResidual S a b := by
  exact frame_residual_is_closed_concept S a b

/--
The syntactic-block adequacy package, stated using `FrameResidual` and
`SingleObservedBlock`.
-/
theorem frameResidual_singleBlock_generates_residual
    (S U : Set Q) (a b : Q)
    (hU : U ⊆ FrameResidual S a b)
    (hne : ∃ u0 : Q, u0 ∈ U)
    (hblock : SingleObservedBlock S a b) :
    ConceptClosure S U = FrameResidual S a b := by
  exact syntacticBlockAdequacy S U a b hU hne hblock

end LeanCfgProject
