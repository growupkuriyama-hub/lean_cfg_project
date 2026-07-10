/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG.CharacteristicSampleNamedContextSplicingConstruction

/-!
# CharacteristicSampleNamedContextSplicingPieces.lean

One-hundred-twenty-fourth clean Lean experiment for the fixed-observation MCFG
project.

`CharacteristicSampleNamedContextSplicingConstruction.lean` isolated the
ingredient

```lean
NamedContextSplicingConstructor α.
```

This file opens that ingredient by splitting one binary named-context splicing
object into its left and right construction pieces.

For a parent named context `E` and a binary template `ρ`, the concrete target is:

```lean
BinaryNamedContextSplicing E ρ
```

This file factors it as:

```text
left child-context construction
+
right child-context construction.
```

The new universal record

```lean
NamedContextSplicingPiecewiseConstructor
```

then reassembles those local left/right pieces into the old
`NamedContextSplicingConstructor`.

No new mathematical principle is introduced here; this is a finer interface for
the next actual construction step.

No theorem here uses `sorry`.
-/

namespace MCFG

universe u

section LocalNamedContextSplicingPieces

variable {α : Type u}

/-- The left-child half of concrete named-context splicing.

For each fixed right tuple `y`, it constructs a left child context in which
filling with `x` agrees with filling the parent context by the template
evaluation `body x y`. -/
structure LeftNamedContextSplicingPiece
    {e dB dC : Nat}
    (parent : NamedSentenceContext α e)
    (body : TemplateTuple α e dB dC) where
  leftContext : Tuple α dC → NamedSentenceContext α dB
  left_fill_eq :
    ∀ (y : Tuple α dC) (x : Tuple α dB),
      namedFill dB (leftContext y) x =
        namedFill e parent (evalTemplateTuple body x y)

/-- The right-child half of concrete named-context splicing.

For each fixed left tuple `u`, it constructs a right child context in which
filling with `v` agrees with filling the parent context by the template
evaluation `body u v`. -/
structure RightNamedContextSplicingPiece
    {e dB dC : Nat}
    (parent : NamedSentenceContext α e)
    (body : TemplateTuple α e dB dC) where
  rightContext : Tuple α dB → NamedSentenceContext α dC
  right_fill_eq :
    ∀ (u : Tuple α dB) (v : Tuple α dC),
      namedFill dC (rightContext u) v =
        namedFill e parent (evalTemplateTuple body u v)

namespace LeftNamedContextSplicingPiece

variable {e dB dC : Nat}
variable {parent : NamedSentenceContext α e}
variable {body : TemplateTuple α e dB dC}

/-- A left splicing piece gives the left filling identity for any fixed right
tuple. -/
def toLeftFillingIdentity
    (L : LeftNamedContextSplicingPiece parent body)
    (y : Tuple α dC) :
    LeftFillingIdentity namedFill parent body y where
  ctx := L.leftContext y
  fill_eq := by
    intro x
    exact L.left_fill_eq y x

@[simp] theorem toLeftFillingIdentity_ctx
    (L : LeftNamedContextSplicingPiece parent body)
    (y : Tuple α dC) :
    (L.toLeftFillingIdentity y).ctx = L.leftContext y :=
  rfl

end LeftNamedContextSplicingPiece


namespace RightNamedContextSplicingPiece

variable {e dB dC : Nat}
variable {parent : NamedSentenceContext α e}
variable {body : TemplateTuple α e dB dC}

/-- A right splicing piece gives the right filling identity for any fixed left
tuple. -/
def toRightFillingIdentity
    (R : RightNamedContextSplicingPiece parent body)
    (u : Tuple α dB) :
    RightFillingIdentity namedFill parent body u where
  ctx := R.rightContext u
  fill_eq := by
    intro v
    exact R.right_fill_eq u v

@[simp] theorem toRightFillingIdentity_ctx
    (R : RightNamedContextSplicingPiece parent body)
    (u : Tuple α dB) :
    (R.toRightFillingIdentity u).ctx = R.rightContext u :=
  rfl

end RightNamedContextSplicingPiece


namespace BinaryNamedContextSplicing

variable {e dB dC : Nat}
variable {parent : NamedSentenceContext α e}
variable {body : TemplateTuple α e dB dC}

/-- Reassemble left and right named-context splicing pieces into the previous
binary named-context splicing record. -/
def ofLeftRightPieces
    (L : LeftNamedContextSplicingPiece parent body)
    (R : RightNamedContextSplicingPiece parent body) :
    BinaryNamedContextSplicing parent body where
  leftContext := L.leftContext
  left_fill_eq := L.left_fill_eq
  rightContext := R.rightContext
  right_fill_eq := R.right_fill_eq

/-- Extract the left splicing piece from a binary named-context splicing object. -/
def toLeftPiece
    (S : BinaryNamedContextSplicing parent body) :
    LeftNamedContextSplicingPiece parent body where
  leftContext := S.leftContext
  left_fill_eq := S.left_fill_eq

/-- Extract the right splicing piece from a binary named-context splicing object. -/
def toRightPiece
    (S : BinaryNamedContextSplicing parent body) :
    RightNamedContextSplicingPiece parent body where
  rightContext := S.rightContext
  right_fill_eq := S.right_fill_eq

@[simp] theorem ofLeftRightPieces_leftContext
    (L : LeftNamedContextSplicingPiece parent body)
    (R : RightNamedContextSplicingPiece parent body) :
    (ofLeftRightPieces L R).leftContext = L.leftContext :=
  rfl

@[simp] theorem ofLeftRightPieces_rightContext
    (L : LeftNamedContextSplicingPiece parent body)
    (R : RightNamedContextSplicingPiece parent body) :
    (ofLeftRightPieces L R).rightContext = R.rightContext :=
  rfl

end BinaryNamedContextSplicing

end LocalNamedContextSplicingPieces


section UniversalPiecewiseConstructor

variable {α : Type u}

/-- A universal named-context splicing constructor, split into left and right
local pieces.

This is the next finer-grained target: construct the left child context and
right child context separately for every parent context and binary template. -/
structure NamedContextSplicingPiecewiseConstructor (α : Type u) where
  leftPiece :
    {e dB dC : Nat} →
      (parent : NamedSentenceContext α e) →
      (body : TemplateTuple α e dB dC) →
        LeftNamedContextSplicingPiece parent body
  rightPiece :
    {e dB dC : Nat} →
      (parent : NamedSentenceContext α e) →
      (body : TemplateTuple α e dB dC) →
        RightNamedContextSplicingPiece parent body

namespace NamedContextSplicingPiecewiseConstructor

/-- Reassemble the piecewise constructor into the previous universal
`NamedContextSplicingConstructor`. -/
def toNamedContextSplicingConstructor
    (C : NamedContextSplicingPiecewiseConstructor α) :
    NamedContextSplicingConstructor α where
  splice := by
    intro e dB dC parent body
    exact BinaryNamedContextSplicing.ofLeftRightPieces
      (C.leftPiece parent body)
      (C.rightPiece parent body)

/-- View a piecewise constructor as the paper-facing splicing construction
data. -/
def toNamedContextSplicingConstructionData
    (C : NamedContextSplicingPiecewiseConstructor α) :
    NamedContextSplicingConstructionData (α := α) where
  splicingConstructor := C.toNamedContextSplicingConstructor

/-- View a piecewise constructor as the preferred splicing-constructor target. -/
def toPreferredSplicingConstructorTarget
    (C : NamedContextSplicingPiecewiseConstructor α) :
    PaperPreferredSplicingConstructorTarget (α := α) :=
  C.toNamedContextSplicingConstructionData
    .toPreferredSplicingConstructorTarget

end NamedContextSplicingPiecewiseConstructor

/-- Existence of the piecewise named-context splicing constructor. -/
def ExistsNamedContextSplicingPiecewiseConstructor (α : Type u) : Prop :=
  Nonempty (NamedContextSplicingPiecewiseConstructor α)

/-- A piecewise constructor gives the previous named-context splicing
construction. -/
theorem existsNamedContextSplicingConstruction_of_piecewise
    (h : ExistsNamedContextSplicingPiecewiseConstructor α) :
    ExistsNamedContextSplicingConstruction α :=
  match h with
  | ⟨C⟩ => ⟨C.toNamedContextSplicingConstructionData⟩

/-- A piecewise constructor gives the preferred splicing target. -/
theorem existsPreferredSplicingConstructorTarget_of_piecewise
    (h : ExistsNamedContextSplicingPiecewiseConstructor α) :
    Nonempty (PaperPreferredSplicingConstructorTarget (α := α)) :=
  existsPreferredSplicingConstructorTarget_of_namedContextSplicing
    (existsNamedContextSplicingConstruction_of_piecewise h)

end UniversalPiecewiseConstructor


section PiecewiseConstructorTopLevel

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}

/-- Preferred anchor-common theorem with the splicing constructor supplied in
piecewise left/right form. -/
theorem trimmed_paper_preferred_anchor_common_without_splicing_main_theorem_of_piecewise
    (hC : ExistsPaperPreferredAnchorCommonAllPiecesWithoutSplicing G obs)
    (hS : ExistsNamedContextSplicingPiecewiseConstructor α) :
    PaperConstructiveIdentificationConclusion G obs :=
  trimmed_paper_preferred_anchor_common_without_splicing_main_theorem
    hC
    (existsNamedContextSplicingConstruction_of_piecewise hS)

/-- Preferred anchor-common conclusion package with the splicing constructor
supplied in piecewise left/right form. -/
theorem trimmed_paper_preferred_anchor_common_without_splicing_conclusion_package_of_piecewise
    (hC : ExistsPaperPreferredAnchorCommonAllPiecesWithoutSplicing G obs)
    (hS : ExistsNamedContextSplicingPiecewiseConstructor α) :
    PaperConstructiveLearningConclusionPackage G obs :=
  trimmed_paper_preferred_anchor_common_without_splicing_conclusion_package
    hC
    (existsNamedContextSplicingConstruction_of_piecewise hS)

/-- Bridge from all preferred pieces except splicing plus a piecewise splicing
constructor to the complete all-pieces checklist. -/
theorem trimmed_paper_preferred_anchor_common_all_pieces_of_without_splicing_piecewise
    (hC : ExistsPaperPreferredAnchorCommonAllPiecesWithoutSplicing G obs)
    (hS : ExistsNamedContextSplicingPiecewiseConstructor α) :
    ExistsPaperPreferredAnchorCommonAllPieces G obs :=
  trimmed_paper_preferred_anchor_common_all_pieces_of_without_splicing
    hC
    (existsNamedContextSplicingConstruction_of_piecewise hS)

end PiecewiseConstructorTopLevel

end MCFG
