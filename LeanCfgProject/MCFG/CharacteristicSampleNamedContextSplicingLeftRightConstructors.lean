/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG.CharacteristicSampleNamedContextSplicingPieces

/-!
# CharacteristicSampleNamedContextSplicingLeftRightConstructors.lean

One-hundred-twenty-fifth clean Lean experiment for the fixed-observation MCFG
project.

`CharacteristicSampleNamedContextSplicingPieces.lean` split a binary named
context splicing object into left and right pieces, and introduced

```lean
NamedContextSplicingPiecewiseConstructor
```

with two fields:

```lean
leftPiece
rightPiece.
```

This file splits those two fields into independent universal construction
targets:

```lean
NamedContextLeftSplicingConstructor
NamedContextRightSplicingConstructor
```

A left constructor and a right constructor reassemble into the piecewise
constructor, and hence into the old `NamedContextSplicingConstructor`.

No new mathematical principle is introduced here; this file only gives the next
local construction targets stable names.

No theorem here uses `sorry`.
-/

namespace MCFG

universe u v w

section LeftRightSplicingConstructors

variable {α : Type u}

/-- Universal constructor for the left child context in named-context splicing. -/
structure NamedContextLeftSplicingConstructor (α : Type u) where
  leftPiece :
    {e dB dC : Nat} →
      (parent : NamedSentenceContext α e) →
      (body : TemplateTuple α e dB dC) →
        LeftNamedContextSplicingPiece parent body

/-- Universal constructor for the right child context in named-context splicing. -/
structure NamedContextRightSplicingConstructor (α : Type u) where
  rightPiece :
    {e dB dC : Nat} →
      (parent : NamedSentenceContext α e) →
      (body : TemplateTuple α e dB dC) →
        RightNamedContextSplicingPiece parent body

namespace NamedContextLeftSplicingConstructor

/-- Apply a left splicing constructor to a parent context and binary template. -/
def apply
    (L : NamedContextLeftSplicingConstructor α)
    {e dB dC : Nat}
    (parent : NamedSentenceContext α e)
    (body : TemplateTuple α e dB dC) :
    LeftNamedContextSplicingPiece parent body :=
  L.leftPiece parent body

end NamedContextLeftSplicingConstructor


namespace NamedContextRightSplicingConstructor

/-- Apply a right splicing constructor to a parent context and binary template. -/
def apply
    (R : NamedContextRightSplicingConstructor α)
    {e dB dC : Nat}
    (parent : NamedSentenceContext α e)
    (body : TemplateTuple α e dB dC) :
    RightNamedContextSplicingPiece parent body :=
  R.rightPiece parent body

end NamedContextRightSplicingConstructor


/-- Left and right universal constructors, paired as one target. -/
structure NamedContextLeftRightSplicingConstructors (α : Type u) where
  leftConstructor : NamedContextLeftSplicingConstructor α
  rightConstructor : NamedContextRightSplicingConstructor α

namespace NamedContextLeftRightSplicingConstructors

/-- Reassemble left and right universal constructors into the previous
piecewise constructor. -/
def toPiecewiseConstructor
    (C : NamedContextLeftRightSplicingConstructors α) :
    NamedContextSplicingPiecewiseConstructor α where
  leftPiece := by
    intro e dB dC parent body
    exact C.leftConstructor.apply parent body
  rightPiece := by
    intro e dB dC parent body
    exact C.rightConstructor.apply parent body

/-- Reassemble left and right universal constructors into the old
named-context splicing constructor. -/
def toNamedContextSplicingConstructor
    (C : NamedContextLeftRightSplicingConstructors α) :
    NamedContextSplicingConstructor α :=
  C.toPiecewiseConstructor.toNamedContextSplicingConstructor

/-- Reassemble left and right universal constructors into paper-facing
splicing construction data. -/
def toNamedContextSplicingConstructionData
    (C : NamedContextLeftRightSplicingConstructors α) :
    NamedContextSplicingConstructionData (α := α) where
  splicingConstructor := C.toNamedContextSplicingConstructor

/-- Reassemble left and right universal constructors into the preferred
splicing-constructor target. -/
def toPreferredSplicingConstructorTarget
    (C : NamedContextLeftRightSplicingConstructors α) :
    PaperPreferredSplicingConstructorTarget (α := α) :=
  C.toNamedContextSplicingConstructionData
    .toPreferredSplicingConstructorTarget

end NamedContextLeftRightSplicingConstructors

/-- Existence of left and right universal splicing constructors. -/
def ExistsNamedContextLeftRightSplicingConstructors
    (α : Type u) : Prop :=
  Nonempty (NamedContextLeftRightSplicingConstructors α)

/-- Existence of left and right universal constructors gives a piecewise
splicing constructor. -/
theorem existsNamedContextSplicingPiecewiseConstructor_of_leftRight
    (h : ExistsNamedContextLeftRightSplicingConstructors α) :
    ExistsNamedContextSplicingPiecewiseConstructor α :=
  match h with
  | ⟨C⟩ => ⟨C.toPiecewiseConstructor⟩

/-- Existence of left and right universal constructors gives the previous
named-context splicing construction. -/
theorem existsNamedContextSplicingConstruction_of_leftRight
    (h : ExistsNamedContextLeftRightSplicingConstructors α) :
    ExistsNamedContextSplicingConstruction α :=
  existsNamedContextSplicingConstruction_of_piecewise
    (existsNamedContextSplicingPiecewiseConstructor_of_leftRight h)

/-- Existence of left and right universal constructors gives the preferred
splicing-constructor target. -/
theorem existsPreferredSplicingConstructorTarget_of_leftRight
    (h : ExistsNamedContextLeftRightSplicingConstructors α) :
    Nonempty (PaperPreferredSplicingConstructorTarget (α := α)) :=
  existsPreferredSplicingConstructorTarget_of_piecewise
    (existsNamedContextSplicingPiecewiseConstructor_of_leftRight h)

end LeftRightSplicingConstructors


section LeftRightSplicingConstructorExistentials

variable {α : Type u}

/-- Existence of only the left universal splicing constructor. -/
def ExistsNamedContextLeftSplicingConstructor
    (α : Type u) : Prop :=
  Nonempty (NamedContextLeftSplicingConstructor α)

/-- Existence of only the right universal splicing constructor. -/
def ExistsNamedContextRightSplicingConstructor
    (α : Type u) : Prop :=
  Nonempty (NamedContextRightSplicingConstructor α)

/-- A left constructor and a right constructor give the paired left/right
constructor target. -/
theorem existsNamedContextLeftRightSplicingConstructors_of_left_right
    (hL : ExistsNamedContextLeftSplicingConstructor α)
    (hR : ExistsNamedContextRightSplicingConstructor α) :
    ExistsNamedContextLeftRightSplicingConstructors α :=
  match hL with
  | ⟨L⟩ =>
      match hR with
      | ⟨R⟩ =>
          ⟨{ leftConstructor := L
             rightConstructor := R }⟩

/-- A left constructor and a right constructor give the piecewise splicing
constructor. -/
theorem existsNamedContextSplicingPiecewiseConstructor_of_left_right
    (hL : ExistsNamedContextLeftSplicingConstructor α)
    (hR : ExistsNamedContextRightSplicingConstructor α) :
    ExistsNamedContextSplicingPiecewiseConstructor α :=
  existsNamedContextSplicingPiecewiseConstructor_of_leftRight
    (existsNamedContextLeftRightSplicingConstructors_of_left_right hL hR)

/-- A left constructor and a right constructor give the previous named-context
splicing construction. -/
theorem existsNamedContextSplicingConstruction_of_left_right
    (hL : ExistsNamedContextLeftSplicingConstructor α)
    (hR : ExistsNamedContextRightSplicingConstructor α) :
    ExistsNamedContextSplicingConstruction α :=
  existsNamedContextSplicingConstruction_of_leftRight
    (existsNamedContextLeftRightSplicingConstructors_of_left_right hL hR)

end LeftRightSplicingConstructorExistentials


section LeftRightSplicingTopLevel

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}

/-- Preferred anchor-common theorem with the splicing constructor supplied by
separate left and right universal constructors. -/
theorem trimmed_paper_preferred_anchor_common_without_splicing_main_theorem_of_left_right
    (hC : ExistsPaperPreferredAnchorCommonAllPiecesWithoutSplicing G obs)
    (hL : ExistsNamedContextLeftSplicingConstructor α)
    (hR : ExistsNamedContextRightSplicingConstructor α) :
    PaperConstructiveIdentificationConclusion G obs :=
  trimmed_paper_preferred_anchor_common_without_splicing_main_theorem
    hC
    (existsNamedContextSplicingConstruction_of_left_right hL hR)

/-- Preferred anchor-common conclusion package with the splicing constructor
supplied by separate left and right universal constructors. -/
theorem trimmed_paper_preferred_anchor_common_without_splicing_conclusion_package_of_left_right
    (hC : ExistsPaperPreferredAnchorCommonAllPiecesWithoutSplicing G obs)
    (hL : ExistsNamedContextLeftSplicingConstructor α)
    (hR : ExistsNamedContextRightSplicingConstructor α) :
    PaperConstructiveLearningConclusionPackage G obs :=
  trimmed_paper_preferred_anchor_common_without_splicing_conclusion_package
    hC
    (existsNamedContextSplicingConstruction_of_left_right hL hR)

/-- Bridge from without-splicing preferred pieces plus separate left/right
constructors to the complete all-pieces checklist. -/
theorem trimmed_paper_preferred_anchor_common_all_pieces_of_without_splicing_left_right
    (hC : ExistsPaperPreferredAnchorCommonAllPiecesWithoutSplicing G obs)
    (hL : ExistsNamedContextLeftSplicingConstructor α)
    (hR : ExistsNamedContextRightSplicingConstructor α) :
    ExistsPaperPreferredAnchorCommonAllPieces G obs :=
  trimmed_paper_preferred_anchor_common_all_pieces_of_without_splicing
    hC
    (existsNamedContextSplicingConstruction_of_left_right hL hR)

end LeftRightSplicingTopLevel

end MCFG
