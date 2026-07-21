/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG.CharacteristicSampleNamedContextSplicingLeftRightConstructors

/-!
# CharacteristicSampleNamedContextSplicingLocalTargets.lean

One-hundred-twenty-sixth clean Lean experiment for the fixed-observation MCFG
project.

`CharacteristicSampleNamedContextSplicingLeftRightConstructors.lean` split the
universal splicing constructor into independent left and right constructors:

```lean
NamedContextLeftSplicingConstructor
NamedContextRightSplicingConstructor
```

This file moves one step further inward.  For a fixed parent named context and
a fixed binary template, it names the local targets:

```lean
LeftNamedContextSplicingLocalTarget
RightNamedContextSplicingLocalTarget
```

A universal choice of those local targets reassembles into the left/right
constructors from the previous file.

No new mathematical principle is introduced here; this file just gives stable
names to the local construction targets that the next files should actually
build.

No theorem here uses `sorry`.
-/

namespace MCFG

universe u v w

section LocalSplicingTargets

variable {α : Type u}

/-- Local target for the left child-context construction at one fixed parent
context and one fixed binary template. -/
structure LeftNamedContextSplicingLocalTarget
    {e dB dC : Nat}
    (parent : NamedSentenceContext α e)
    (body : TemplateTuple α e dB dC) where
  piece : LeftNamedContextSplicingPiece parent body

/-- Local target for the right child-context construction at one fixed parent
context and one fixed binary template. -/
structure RightNamedContextSplicingLocalTarget
    {e dB dC : Nat}
    (parent : NamedSentenceContext α e)
    (body : TemplateTuple α e dB dC) where
  piece : RightNamedContextSplicingPiece parent body

namespace LeftNamedContextSplicingLocalTarget

variable {e dB dC : Nat}
variable {parent : NamedSentenceContext α e}
variable {body : TemplateTuple α e dB dC}

/-- Extract the left splicing piece from a local target. -/
def toPiece
    (T : LeftNamedContextSplicingLocalTarget parent body) :
    LeftNamedContextSplicingPiece parent body :=
  T.piece

/-- A local left target gives the corresponding left filling identity for each
fixed right tuple. -/
def toLeftFillingIdentity
    (T : LeftNamedContextSplicingLocalTarget parent body)
    (y : Tuple α dC) :
    LeftFillingIdentity namedFill parent body y :=
  T.piece.toLeftFillingIdentity y

end LeftNamedContextSplicingLocalTarget


namespace RightNamedContextSplicingLocalTarget

variable {e dB dC : Nat}
variable {parent : NamedSentenceContext α e}
variable {body : TemplateTuple α e dB dC}

/-- Extract the right splicing piece from a local target. -/
def toPiece
    (T : RightNamedContextSplicingLocalTarget parent body) :
    RightNamedContextSplicingPiece parent body :=
  T.piece

/-- A local right target gives the corresponding right filling identity for each
fixed left tuple. -/
def toRightFillingIdentity
    (T : RightNamedContextSplicingLocalTarget parent body)
    (u : Tuple α dB) :
    RightFillingIdentity namedFill parent body u :=
  T.piece.toRightFillingIdentity u

end RightNamedContextSplicingLocalTarget


/-- A local binary target consists of both the left and the right local targets
for one parent context and one binary template. -/
structure BinaryNamedContextSplicingLocalTarget
    {e dB dC : Nat}
    (parent : NamedSentenceContext α e)
    (body : TemplateTuple α e dB dC) where
  leftTarget : LeftNamedContextSplicingLocalTarget parent body
  rightTarget : RightNamedContextSplicingLocalTarget parent body

namespace BinaryNamedContextSplicingLocalTarget

variable {e dB dC : Nat}
variable {parent : NamedSentenceContext α e}
variable {body : TemplateTuple α e dB dC}

/-- Reassemble a local binary target into the previous binary splicing record. -/
def toBinaryNamedContextSplicing
    (T : BinaryNamedContextSplicingLocalTarget parent body) :
    BinaryNamedContextSplicing parent body :=
  BinaryNamedContextSplicing.ofLeftRightPieces
    T.leftTarget.piece
    T.rightTarget.piece

/-- Build a local binary target from left and right local targets. -/
def ofLeftRightTargets
    (L : LeftNamedContextSplicingLocalTarget parent body)
    (R : RightNamedContextSplicingLocalTarget parent body) :
    BinaryNamedContextSplicingLocalTarget parent body where
  leftTarget := L
  rightTarget := R

end BinaryNamedContextSplicingLocalTarget

end LocalSplicingTargets


section UniversalLocalTargetConstructors

variable {α : Type u}

/-- Universal constructor for all local left splicing targets. -/
structure NamedContextLeftSplicingLocalConstructor (α : Type u) where
  leftTarget :
    {e dB dC : Nat} →
      (parent : NamedSentenceContext α e) →
      (body : TemplateTuple α e dB dC) →
        LeftNamedContextSplicingLocalTarget parent body

/-- Universal constructor for all local right splicing targets. -/
structure NamedContextRightSplicingLocalConstructor (α : Type u) where
  rightTarget :
    {e dB dC : Nat} →
      (parent : NamedSentenceContext α e) →
      (body : TemplateTuple α e dB dC) →
        RightNamedContextSplicingLocalTarget parent body

namespace NamedContextLeftSplicingLocalConstructor

/-- Convert a universal local-left target constructor to the previous universal
left splicing constructor. -/
def toLeftSplicingConstructor
    (L : NamedContextLeftSplicingLocalConstructor α) :
    NamedContextLeftSplicingConstructor α where
  leftPiece := by
    intro e dB dC parent body
    exact (L.leftTarget parent body).piece

end NamedContextLeftSplicingLocalConstructor


namespace NamedContextRightSplicingLocalConstructor

/-- Convert a universal local-right target constructor to the previous universal
right splicing constructor. -/
def toRightSplicingConstructor
    (R : NamedContextRightSplicingLocalConstructor α) :
    NamedContextRightSplicingConstructor α where
  rightPiece := by
    intro e dB dC parent body
    exact (R.rightTarget parent body).piece

end NamedContextRightSplicingLocalConstructor


/-- Universal constructor for all local binary splicing targets. -/
structure NamedContextBinarySplicingLocalConstructor (α : Type u) where
  binaryTarget :
    {e dB dC : Nat} →
      (parent : NamedSentenceContext α e) →
      (body : TemplateTuple α e dB dC) →
        BinaryNamedContextSplicingLocalTarget parent body

namespace NamedContextBinarySplicingLocalConstructor

/-- Extract the universal local-left constructor from a universal local-binary
constructor. -/
def toLeftLocalConstructor
    (B : NamedContextBinarySplicingLocalConstructor α) :
    NamedContextLeftSplicingLocalConstructor α where
  leftTarget := by
    intro e dB dC parent body
    exact (B.binaryTarget parent body).leftTarget

/-- Extract the universal local-right constructor from a universal local-binary
constructor. -/
def toRightLocalConstructor
    (B : NamedContextBinarySplicingLocalConstructor α) :
    NamedContextRightSplicingLocalConstructor α where
  rightTarget := by
    intro e dB dC parent body
    exact (B.binaryTarget parent body).rightTarget

/-- Convert a universal local-binary constructor to the old universal
named-context splicing constructor. -/
def toNamedContextSplicingConstructor
    (B : NamedContextBinarySplicingLocalConstructor α) :
    NamedContextSplicingConstructor α where
  splice := by
    intro e dB dC parent body
    exact (B.binaryTarget parent body).toBinaryNamedContextSplicing

end NamedContextBinarySplicingLocalConstructor


/-- Existence of a universal local-left target constructor. -/
def ExistsNamedContextLeftSplicingLocalConstructor
    (α : Type u) : Prop :=
  Nonempty (NamedContextLeftSplicingLocalConstructor α)

/-- Existence of a universal local-right target constructor. -/
def ExistsNamedContextRightSplicingLocalConstructor
    (α : Type u) : Prop :=
  Nonempty (NamedContextRightSplicingLocalConstructor α)

/-- Existence of a universal local-binary target constructor. -/
def ExistsNamedContextBinarySplicingLocalConstructor
    (α : Type u) : Prop :=
  Nonempty (NamedContextBinarySplicingLocalConstructor α)

/-- A universal local-left target constructor gives the previous left splicing
constructor. -/
theorem existsNamedContextLeftSplicingConstructor_of_local
    (h : ExistsNamedContextLeftSplicingLocalConstructor α) :
    ExistsNamedContextLeftSplicingConstructor α :=
  match h with
  | ⟨L⟩ => ⟨L.toLeftSplicingConstructor⟩

/-- A universal local-right target constructor gives the previous right splicing
constructor. -/
theorem existsNamedContextRightSplicingConstructor_of_local
    (h : ExistsNamedContextRightSplicingLocalConstructor α) :
    ExistsNamedContextRightSplicingConstructor α :=
  match h with
  | ⟨R⟩ => ⟨R.toRightSplicingConstructor⟩

/-- A universal local-binary target constructor gives a universal local-left
target constructor. -/
theorem existsNamedContextLeftSplicingLocalConstructor_of_binary
    (h : ExistsNamedContextBinarySplicingLocalConstructor α) :
    ExistsNamedContextLeftSplicingLocalConstructor α :=
  match h with
  | ⟨B⟩ => ⟨B.toLeftLocalConstructor⟩

/-- A universal local-binary target constructor gives a universal local-right
target constructor. -/
theorem existsNamedContextRightSplicingLocalConstructor_of_binary
    (h : ExistsNamedContextBinarySplicingLocalConstructor α) :
    ExistsNamedContextRightSplicingLocalConstructor α :=
  match h with
  | ⟨B⟩ => ⟨B.toRightLocalConstructor⟩

/-- A universal local-binary target constructor gives the old named-context
splicing construction. -/
theorem existsNamedContextSplicingConstruction_of_local_binary
    (h : ExistsNamedContextBinarySplicingLocalConstructor α) :
    ExistsNamedContextSplicingConstruction α :=
  match h with
  | ⟨B⟩ =>
      ⟨{ splicingConstructor := B.toNamedContextSplicingConstructor }⟩

/-- Universal local-left and local-right constructors give the previous
named-context splicing construction. -/
theorem existsNamedContextSplicingConstruction_of_local_left_right
    (hL : ExistsNamedContextLeftSplicingLocalConstructor α)
    (hR : ExistsNamedContextRightSplicingLocalConstructor α) :
    ExistsNamedContextSplicingConstruction α :=
  existsNamedContextSplicingConstruction_of_left_right
    (existsNamedContextLeftSplicingConstructor_of_local hL)
    (existsNamedContextRightSplicingConstructor_of_local hR)

end UniversalLocalTargetConstructors


section LocalTargetTopLevel

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}

/-- Preferred anchor-common theorem with splicing supplied by local left and
local right target constructors. -/
theorem trimmed_paper_preferred_anchor_common_without_splicing_main_theorem_of_local_left_right
    (hC : ExistsPaperPreferredAnchorCommonAllPiecesWithoutSplicing G obs)
    (hL : ExistsNamedContextLeftSplicingLocalConstructor α)
    (hR : ExistsNamedContextRightSplicingLocalConstructor α) :
    PaperConstructiveIdentificationConclusion G obs :=
  trimmed_paper_preferred_anchor_common_without_splicing_main_theorem
    hC
    (existsNamedContextSplicingConstruction_of_local_left_right hL hR)

/-- Preferred anchor-common theorem with splicing supplied by a local binary
target constructor. -/
theorem trimmed_paper_preferred_anchor_common_without_splicing_main_theorem_of_local_binary
    (hC : ExistsPaperPreferredAnchorCommonAllPiecesWithoutSplicing G obs)
    (hB : ExistsNamedContextBinarySplicingLocalConstructor α) :
    PaperConstructiveIdentificationConclusion G obs :=
  trimmed_paper_preferred_anchor_common_without_splicing_main_theorem
    hC
    (existsNamedContextSplicingConstruction_of_local_binary hB)

/-- Bridge from without-splicing preferred pieces plus local binary splicing
constructor to the complete all-pieces checklist. -/
theorem trimmed_paper_preferred_anchor_common_all_pieces_of_without_splicing_local_binary
    (hC : ExistsPaperPreferredAnchorCommonAllPiecesWithoutSplicing G obs)
    (hB : ExistsNamedContextBinarySplicingLocalConstructor α) :
    ExistsPaperPreferredAnchorCommonAllPieces G obs :=
  trimmed_paper_preferred_anchor_common_all_pieces_of_without_splicing
    hC
    (existsNamedContextSplicingConstruction_of_local_binary hB)

end LocalTargetTopLevel

end MCFG
