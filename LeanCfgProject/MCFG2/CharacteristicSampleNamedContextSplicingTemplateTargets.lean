/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG2.CharacteristicSampleNamedContextSplicingLocalTargets

/-!
# CharacteristicSampleNamedContextSplicingTemplateTargets.lean

One-hundred-twenty-seventh clean Lean experiment for the fixed-observation MCFG
project.

This file moves the local splicing target one level outward: it fixes the binary
template `body`, while the parent named context varies.

No new mathematical principle is introduced here.

No theorem here uses `sorry`.
-/

namespace MCFG

universe u v w

section TemplateLevelSplicingTargets

variable {α : Type u}

/-- For a fixed binary template, construct all left local splicing targets as
the parent named context varies. -/
structure TemplateLeftNamedContextSplicingConstructor
    {e dB dC : Nat}
    (body : TemplateTuple α e dB dC) where
  leftTarget :
    (parent : NamedSentenceContext α e) →
      LeftNamedContextSplicingLocalTarget parent body

/-- For a fixed binary template, construct all right local splicing targets as
the parent named context varies. -/
structure TemplateRightNamedContextSplicingConstructor
    {e dB dC : Nat}
    (body : TemplateTuple α e dB dC) where
  rightTarget :
    (parent : NamedSentenceContext α e) →
      RightNamedContextSplicingLocalTarget parent body

/-- For a fixed binary template, construct all binary local splicing targets as
the parent named context varies. -/
structure TemplateBinaryNamedContextSplicingConstructor
    {e dB dC : Nat}
    (body : TemplateTuple α e dB dC) where
  binaryTarget :
    (parent : NamedSentenceContext α e) →
      BinaryNamedContextSplicingLocalTarget parent body

namespace TemplateLeftNamedContextSplicingConstructor

variable {e dB dC : Nat}
variable {body : TemplateTuple α e dB dC}

/-- Apply a template-level left constructor to a parent context. -/
def apply
    (L : TemplateLeftNamedContextSplicingConstructor body)
    (parent : NamedSentenceContext α e) :
    LeftNamedContextSplicingLocalTarget parent body :=
  L.leftTarget parent

/-- Convert a template-level left constructor to a local left piece. -/
def toLocalPiece
    (L : TemplateLeftNamedContextSplicingConstructor body)
    (parent : NamedSentenceContext α e) :
    LeftNamedContextSplicingPiece parent body :=
  (L.apply parent).piece

end TemplateLeftNamedContextSplicingConstructor


namespace TemplateRightNamedContextSplicingConstructor

variable {e dB dC : Nat}
variable {body : TemplateTuple α e dB dC}

/-- Apply a template-level right constructor to a parent context. -/
def apply
    (R : TemplateRightNamedContextSplicingConstructor body)
    (parent : NamedSentenceContext α e) :
    RightNamedContextSplicingLocalTarget parent body :=
  R.rightTarget parent

/-- Convert a template-level right constructor to a local right piece. -/
def toLocalPiece
    (R : TemplateRightNamedContextSplicingConstructor body)
    (parent : NamedSentenceContext α e) :
    RightNamedContextSplicingPiece parent body :=
  (R.apply parent).piece

end TemplateRightNamedContextSplicingConstructor


namespace TemplateBinaryNamedContextSplicingConstructor

variable {e dB dC : Nat}
variable {body : TemplateTuple α e dB dC}

/-- Apply a template-level binary constructor to a parent context. -/
def apply
    (B : TemplateBinaryNamedContextSplicingConstructor body)
    (parent : NamedSentenceContext α e) :
    BinaryNamedContextSplicingLocalTarget parent body :=
  B.binaryTarget parent

/-- Extract the template-level left constructor from a template-level binary
constructor. -/
def toLeftConstructor
    (B : TemplateBinaryNamedContextSplicingConstructor body) :
    TemplateLeftNamedContextSplicingConstructor body where
  leftTarget := by
    intro parent
    exact (B.apply parent).leftTarget

/-- Extract the template-level right constructor from a template-level binary
constructor. -/
def toRightConstructor
    (B : TemplateBinaryNamedContextSplicingConstructor body) :
    TemplateRightNamedContextSplicingConstructor body where
  rightTarget := by
    intro parent
    exact (B.apply parent).rightTarget

/-- Convert a template-level binary constructor to a binary splicing record for
each parent context. -/
def toBinaryNamedContextSplicing
    (B : TemplateBinaryNamedContextSplicingConstructor body)
    (parent : NamedSentenceContext α e) :
    BinaryNamedContextSplicing parent body :=
  (B.apply parent).toBinaryNamedContextSplicing

end TemplateBinaryNamedContextSplicingConstructor

end TemplateLevelSplicingTargets


section UniversalTemplateLevelConstructors

variable {α : Type u}

/-- Universal constructor assigning a template-level left constructor to every
binary template. -/
structure NamedContextTemplateLeftSplicingConstructor (α : Type u) where
  templateLeft :
    {e dB dC : Nat} →
      (body : TemplateTuple α e dB dC) →
        TemplateLeftNamedContextSplicingConstructor body

/-- Universal constructor assigning a template-level right constructor to every
binary template. -/
structure NamedContextTemplateRightSplicingConstructor (α : Type u) where
  templateRight :
    {e dB dC : Nat} →
      (body : TemplateTuple α e dB dC) →
        TemplateRightNamedContextSplicingConstructor body

/-- Universal constructor assigning a template-level binary constructor to every
binary template. -/
structure NamedContextTemplateBinarySplicingConstructor (α : Type u) where
  templateBinary :
    {e dB dC : Nat} →
      (body : TemplateTuple α e dB dC) →
        TemplateBinaryNamedContextSplicingConstructor body

namespace NamedContextTemplateLeftSplicingConstructor

/-- Convert template-level left constructors to the previous local-left target
constructor. -/
def toLeftLocalConstructor
    (L : NamedContextTemplateLeftSplicingConstructor α) :
    NamedContextLeftSplicingLocalConstructor α where
  leftTarget := by
    intro e dB dC parent body
    exact (L.templateLeft body).apply parent

/-- Convert template-level left constructors to the previous left splicing
constructor. -/
def toLeftSplicingConstructor
    (L : NamedContextTemplateLeftSplicingConstructor α) :
    NamedContextLeftSplicingConstructor α :=
  L.toLeftLocalConstructor.toLeftSplicingConstructor

end NamedContextTemplateLeftSplicingConstructor


namespace NamedContextTemplateRightSplicingConstructor

/-- Convert template-level right constructors to the previous local-right target
constructor. -/
def toRightLocalConstructor
    (R : NamedContextTemplateRightSplicingConstructor α) :
    NamedContextRightSplicingLocalConstructor α where
  rightTarget := by
    intro e dB dC parent body
    exact (R.templateRight body).apply parent

/-- Convert template-level right constructors to the previous right splicing
constructor. -/
def toRightSplicingConstructor
    (R : NamedContextTemplateRightSplicingConstructor α) :
    NamedContextRightSplicingConstructor α :=
  R.toRightLocalConstructor.toRightSplicingConstructor

end NamedContextTemplateRightSplicingConstructor


namespace NamedContextTemplateBinarySplicingConstructor

/-- Convert template-level binary constructors to the previous local-binary
target constructor. -/
def toBinaryLocalConstructor
    (B : NamedContextTemplateBinarySplicingConstructor α) :
    NamedContextBinarySplicingLocalConstructor α where
  binaryTarget := by
    intro e dB dC parent body
    exact (B.templateBinary body).apply parent

/-- Extract template-level left constructors from template-level binary
constructors. -/
def toTemplateLeftConstructor
    (B : NamedContextTemplateBinarySplicingConstructor α) :
    NamedContextTemplateLeftSplicingConstructor α where
  templateLeft := by
    intro e dB dC body
    exact (B.templateBinary body).toLeftConstructor

/-- Extract template-level right constructors from template-level binary
constructors. -/
def toTemplateRightConstructor
    (B : NamedContextTemplateBinarySplicingConstructor α) :
    NamedContextTemplateRightSplicingConstructor α where
  templateRight := by
    intro e dB dC body
    exact (B.templateBinary body).toRightConstructor

/-- Convert template-level binary constructors to the old universal
named-context splicing constructor. -/
def toNamedContextSplicingConstructor
    (B : NamedContextTemplateBinarySplicingConstructor α) :
    NamedContextSplicingConstructor α :=
  B.toBinaryLocalConstructor.toNamedContextSplicingConstructor

end NamedContextTemplateBinarySplicingConstructor


/-- Existence of universal template-level left constructors. -/
def ExistsNamedContextTemplateLeftSplicingConstructor
    (α : Type u) : Prop :=
  Nonempty (NamedContextTemplateLeftSplicingConstructor α)

/-- Existence of universal template-level right constructors. -/
def ExistsNamedContextTemplateRightSplicingConstructor
    (α : Type u) : Prop :=
  Nonempty (NamedContextTemplateRightSplicingConstructor α)

/-- Existence of universal template-level binary constructors. -/
def ExistsNamedContextTemplateBinarySplicingConstructor
    (α : Type u) : Prop :=
  Nonempty (NamedContextTemplateBinarySplicingConstructor α)

/-- Template-level left constructors give local-left constructors. -/
theorem existsNamedContextLeftSplicingLocalConstructor_of_template
    (h : ExistsNamedContextTemplateLeftSplicingConstructor α) :
    ExistsNamedContextLeftSplicingLocalConstructor α :=
  match h with
  | ⟨L⟩ => ⟨L.toLeftLocalConstructor⟩

/-- Template-level right constructors give local-right constructors. -/
theorem existsNamedContextRightSplicingLocalConstructor_of_template
    (h : ExistsNamedContextTemplateRightSplicingConstructor α) :
    ExistsNamedContextRightSplicingLocalConstructor α :=
  match h with
  | ⟨R⟩ => ⟨R.toRightLocalConstructor⟩

/-- Template-level binary constructors give local-binary constructors. -/
theorem existsNamedContextBinarySplicingLocalConstructor_of_template
    (h : ExistsNamedContextTemplateBinarySplicingConstructor α) :
    ExistsNamedContextBinarySplicingLocalConstructor α :=
  match h with
  | ⟨B⟩ => ⟨B.toBinaryLocalConstructor⟩

/-- Template-level binary constructors give named-context splicing construction. -/
theorem existsNamedContextSplicingConstruction_of_template_binary
    (h : ExistsNamedContextTemplateBinarySplicingConstructor α) :
    ExistsNamedContextSplicingConstruction α :=
  existsNamedContextSplicingConstruction_of_local_binary
    (existsNamedContextBinarySplicingLocalConstructor_of_template h)

/-- Template-level left and right constructors give named-context splicing
construction. -/
theorem existsNamedContextSplicingConstruction_of_template_left_right
    (hL : ExistsNamedContextTemplateLeftSplicingConstructor α)
    (hR : ExistsNamedContextTemplateRightSplicingConstructor α) :
    ExistsNamedContextSplicingConstruction α :=
  existsNamedContextSplicingConstruction_of_local_left_right
    (existsNamedContextLeftSplicingLocalConstructor_of_template hL)
    (existsNamedContextRightSplicingLocalConstructor_of_template hR)

end UniversalTemplateLevelConstructors


section TemplateTargetTopLevel

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}

/-- Preferred anchor-common theorem with splicing supplied by template-level left
and right constructors. -/
theorem trimmed_paper_preferred_anchor_common_without_splicing_main_theorem_of_template_left_right
    (hC : ExistsPaperPreferredAnchorCommonAllPiecesWithoutSplicing G obs)
    (hL : ExistsNamedContextTemplateLeftSplicingConstructor α)
    (hR : ExistsNamedContextTemplateRightSplicingConstructor α) :
    PaperConstructiveIdentificationConclusion G obs :=
  trimmed_paper_preferred_anchor_common_without_splicing_main_theorem
    hC
    (existsNamedContextSplicingConstruction_of_template_left_right hL hR)

/-- Preferred anchor-common theorem with splicing supplied by a template-level
binary constructor. -/
theorem trimmed_paper_preferred_anchor_common_without_splicing_main_theorem_of_template_binary
    (hC : ExistsPaperPreferredAnchorCommonAllPiecesWithoutSplicing G obs)
    (hB : ExistsNamedContextTemplateBinarySplicingConstructor α) :
    PaperConstructiveIdentificationConclusion G obs :=
  trimmed_paper_preferred_anchor_common_without_splicing_main_theorem
    hC
    (existsNamedContextSplicingConstruction_of_template_binary hB)

/-- Bridge from without-splicing preferred pieces plus a template-level binary
constructor to the complete all-pieces checklist. -/
theorem trimmed_paper_preferred_anchor_common_all_pieces_of_without_splicing_template_binary
    (hC : ExistsPaperPreferredAnchorCommonAllPiecesWithoutSplicing G obs)
    (hB : ExistsNamedContextTemplateBinarySplicingConstructor α) :
    ExistsPaperPreferredAnchorCommonAllPieces G obs :=
  trimmed_paper_preferred_anchor_common_all_pieces_of_without_splicing
    hC
    (existsNamedContextSplicingConstruction_of_template_binary hB)

end TemplateTargetTopLevel

end MCFG
