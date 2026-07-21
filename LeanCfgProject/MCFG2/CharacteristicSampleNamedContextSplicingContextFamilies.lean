/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG2.CharacteristicSampleNamedContextSplicingParentChoices

/-!
# CharacteristicSampleNamedContextSplicingContextFamilies.lean

One-hundred-thirtieth clean Lean experiment for the fixed-observation MCFG
project.

`CharacteristicSampleNamedContextSplicingParentChoices.lean` reduced the
splicing-constructor task to the existence of local targets for every binary
template and every parent named context.

This file opens those local targets into the actual data that must eventually
be constructed:

```text
left child context functions
right child context functions
namedFill equations.
```

For a fixed binary template `body`, the new records

```lean
ParentwiseLeftSplicingContextFamily
ParentwiseRightSplicingContextFamily
ParentwiseBinarySplicingContextFamily
```

give explicit parent-indexed context families.  They reassemble into the
parentwise local target interfaces from the previous file.

No new mathematical principle is introduced here; this is a finer construction
interface for the next actual splicing proof.

No theorem here uses `sorry`.
-/

namespace MCFG

universe u v w

section ParentwiseContextFamilies

variable {α : Type u}

/-- For one fixed binary template, a parent-indexed family of left child contexts
together with the left namedFill equation. -/
structure ParentwiseLeftSplicingContextFamily
    {e dB dC : Nat}
    (body : TemplateTuple α e dB dC) where
  leftContext :
    (parent : NamedSentenceContext α e) →
      Tuple α dC → NamedSentenceContext α dB
  left_fill_eq :
    ∀ (parent : NamedSentenceContext α e)
      (y : Tuple α dC) (x : Tuple α dB),
      namedFill dB (leftContext parent y) x =
        namedFill e parent (evalTemplateTuple body x y)

/-- For one fixed binary template, a parent-indexed family of right child
contexts together with the right namedFill equation. -/
structure ParentwiseRightSplicingContextFamily
    {e dB dC : Nat}
    (body : TemplateTuple α e dB dC) where
  rightContext :
    (parent : NamedSentenceContext α e) →
      Tuple α dB → NamedSentenceContext α dC
  right_fill_eq :
    ∀ (parent : NamedSentenceContext α e)
      (u : Tuple α dB) (v : Tuple α dC),
      namedFill dC (rightContext parent u) v =
        namedFill e parent (evalTemplateTuple body u v)

/-- For one fixed binary template, both parent-indexed left and right child
context families. -/
structure ParentwiseBinarySplicingContextFamily
    {e dB dC : Nat}
    (body : TemplateTuple α e dB dC) where
  leftFamily : ParentwiseLeftSplicingContextFamily body
  rightFamily : ParentwiseRightSplicingContextFamily body

namespace ParentwiseLeftSplicingContextFamily

variable {e dB dC : Nat}
variable {body : TemplateTuple α e dB dC}

/-- A parentwise left context family gives a local left splicing piece at each
parent context. -/
def toLeftPiece
    (L : ParentwiseLeftSplicingContextFamily body)
    (parent : NamedSentenceContext α e) :
    LeftNamedContextSplicingPiece parent body where
  leftContext := L.leftContext parent
  left_fill_eq := by
    intro y x
    exact L.left_fill_eq parent y x

/-- A parentwise left context family gives a local left target at each parent
context. -/
def toLeftLocalTarget
    (L : ParentwiseLeftSplicingContextFamily body)
    (parent : NamedSentenceContext α e) :
    LeftNamedContextSplicingLocalTarget parent body where
  piece := L.toLeftPiece parent

/-- A parentwise left context family gives the parentwise local-left target
interface. -/
theorem forallParentLeftLocalTarget
    (L : ParentwiseLeftSplicingContextFamily body) :
    ForallParentLeftNamedContextSplicingLocalTarget body := by
  intro parent
  exact ⟨L.toLeftLocalTarget parent⟩

/-- A parentwise left context family gives a template-level left constructor. -/
def toTemplateLeftConstructor
    (L : ParentwiseLeftSplicingContextFamily body) :
    TemplateLeftNamedContextSplicingConstructor body where
  leftTarget := L.toLeftLocalTarget

end ParentwiseLeftSplicingContextFamily


namespace ParentwiseRightSplicingContextFamily

variable {e dB dC : Nat}
variable {body : TemplateTuple α e dB dC}

/-- A parentwise right context family gives a local right splicing piece at each
parent context. -/
def toRightPiece
    (R : ParentwiseRightSplicingContextFamily body)
    (parent : NamedSentenceContext α e) :
    RightNamedContextSplicingPiece parent body where
  rightContext := R.rightContext parent
  right_fill_eq := by
    intro u v
    exact R.right_fill_eq parent u v

/-- A parentwise right context family gives a local right target at each parent
context. -/
def toRightLocalTarget
    (R : ParentwiseRightSplicingContextFamily body)
    (parent : NamedSentenceContext α e) :
    RightNamedContextSplicingLocalTarget parent body where
  piece := R.toRightPiece parent

/-- A parentwise right context family gives the parentwise local-right target
interface. -/
theorem forallParentRightLocalTarget
    (R : ParentwiseRightSplicingContextFamily body) :
    ForallParentRightNamedContextSplicingLocalTarget body := by
  intro parent
  exact ⟨R.toRightLocalTarget parent⟩

/-- A parentwise right context family gives a template-level right constructor. -/
def toTemplateRightConstructor
    (R : ParentwiseRightSplicingContextFamily body) :
    TemplateRightNamedContextSplicingConstructor body where
  rightTarget := R.toRightLocalTarget

end ParentwiseRightSplicingContextFamily


namespace ParentwiseBinarySplicingContextFamily

variable {e dB dC : Nat}
variable {body : TemplateTuple α e dB dC}

/-- A parentwise binary context family gives a local binary target at each
parent context. -/
def toBinaryLocalTarget
    (B : ParentwiseBinarySplicingContextFamily body)
    (parent : NamedSentenceContext α e) :
    BinaryNamedContextSplicingLocalTarget parent body where
  leftTarget := B.leftFamily.toLeftLocalTarget parent
  rightTarget := B.rightFamily.toRightLocalTarget parent

/-- A parentwise binary context family gives the parentwise local-binary target
interface. -/
theorem forallParentBinaryLocalTarget
    (B : ParentwiseBinarySplicingContextFamily body) :
    ForallParentBinaryNamedContextSplicingLocalTarget body := by
  intro parent
  exact ⟨B.toBinaryLocalTarget parent⟩

/-- A parentwise binary context family gives a template-level binary
constructor. -/
def toTemplateBinaryConstructor
    (B : ParentwiseBinarySplicingContextFamily body) :
    TemplateBinaryNamedContextSplicingConstructor body where
  binaryTarget := B.toBinaryLocalTarget

/-- A parentwise binary context family gives existence of a template-level binary
constructor. -/
theorem existsTemplateBinaryConstructor
    (B : ParentwiseBinarySplicingContextFamily body) :
    ExistsTemplateBinaryNamedContextSplicingConstructor body :=
  ⟨B.toTemplateBinaryConstructor⟩

end ParentwiseBinarySplicingContextFamily

end ParentwiseContextFamilies


section UniversalContextFamilyConstructors

variable {α : Type u}

/-- For every binary template, there is a parent-indexed left context family. -/
def ForallTemplateParentwiseLeftSplicingContextFamily
    (α : Type u) : Prop :=
  ∀ {e dB dC : Nat}
    (body : TemplateTuple α e dB dC),
      Nonempty (ParentwiseLeftSplicingContextFamily body)

/-- For every binary template, there is a parent-indexed right context family. -/
def ForallTemplateParentwiseRightSplicingContextFamily
    (α : Type u) : Prop :=
  ∀ {e dB dC : Nat}
    (body : TemplateTuple α e dB dC),
      Nonempty (ParentwiseRightSplicingContextFamily body)

/-- For every binary template, there is a parent-indexed binary context family. -/
def ForallTemplateParentwiseBinarySplicingContextFamily
    (α : Type u) : Prop :=
  ∀ {e dB dC : Nat}
    (body : TemplateTuple α e dB dC),
      Nonempty (ParentwiseBinarySplicingContextFamily body)

/-- Binary context families give left context families. -/
theorem forallTemplateParentwiseLeftSplicingContextFamily_of_binary
    (h : ForallTemplateParentwiseBinarySplicingContextFamily α) :
    ForallTemplateParentwiseLeftSplicingContextFamily α := by
  intro e dB dC body
  rcases h body with ⟨B⟩
  exact ⟨B.leftFamily⟩

/-- Binary context families give right context families. -/
theorem forallTemplateParentwiseRightSplicingContextFamily_of_binary
    (h : ForallTemplateParentwiseBinarySplicingContextFamily α) :
    ForallTemplateParentwiseRightSplicingContextFamily α := by
  intro e dB dC body
  rcases h body with ⟨B⟩
  exact ⟨B.rightFamily⟩

/-- Parentwise left context families for every template give the previous
parentwise local-left target interface. -/
theorem forallTemplateParentLeftLocalTarget_of_contextFamilies
    (h : ForallTemplateParentwiseLeftSplicingContextFamily α) :
    ForallTemplateParentLeftNamedContextSplicingLocalTarget α := by
  intro e dB dC body
  rcases h body with ⟨L⟩
  exact L.forallParentLeftLocalTarget

/-- Parentwise right context families for every template give the previous
parentwise local-right target interface. -/
theorem forallTemplateParentRightLocalTarget_of_contextFamilies
    (h : ForallTemplateParentwiseRightSplicingContextFamily α) :
    ForallTemplateParentRightNamedContextSplicingLocalTarget α := by
  intro e dB dC body
  rcases h body with ⟨R⟩
  exact R.forallParentRightLocalTarget

/-- Parentwise binary context families for every template give the previous
parentwise local-binary target interface. -/
theorem forallTemplateParentBinaryLocalTarget_of_contextFamilies
    (h : ForallTemplateParentwiseBinarySplicingContextFamily α) :
    ForallTemplateParentBinaryNamedContextSplicingLocalTarget α := by
  intro e dB dC body
  rcases h body with ⟨B⟩
  exact B.forallParentBinaryLocalTarget

/-- Parentwise binary context families for every template give named-context
splicing construction. -/
theorem existsNamedContextSplicingConstruction_of_contextFamilies
    (h : ForallTemplateParentwiseBinarySplicingContextFamily α) :
    ExistsNamedContextSplicingConstruction α :=
  existsNamedContextSplicingConstruction_of_forall_template_parent_binary
    (forallTemplateParentBinaryLocalTarget_of_contextFamilies h)

/-- Parentwise left and right context families for every template give
named-context splicing construction. -/
theorem existsNamedContextSplicingConstruction_of_left_right_contextFamilies
    (hL : ForallTemplateParentwiseLeftSplicingContextFamily α)
    (hR : ForallTemplateParentwiseRightSplicingContextFamily α) :
    ExistsNamedContextSplicingConstruction α :=
  existsNamedContextSplicingConstruction_of_forall_template_parent_left_right
    (forallTemplateParentLeftLocalTarget_of_contextFamilies hL)
    (forallTemplateParentRightLocalTarget_of_contextFamilies hR)

end UniversalContextFamilyConstructors


section ContextFamilyTopLevel

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}

/-- Preferred anchor-common theorem with splicing supplied by parentwise binary
context families for every template. -/
theorem trimmed_paper_preferred_anchor_common_without_splicing_main_theorem_of_context_families
    (hC : ExistsPaperPreferredAnchorCommonAllPiecesWithoutSplicing G obs)
    (hB : ForallTemplateParentwiseBinarySplicingContextFamily α) :
    PaperConstructiveIdentificationConclusion G obs :=
  trimmed_paper_preferred_anchor_common_without_splicing_main_theorem
    hC
    (existsNamedContextSplicingConstruction_of_contextFamilies hB)

/-- Preferred anchor-common conclusion package with splicing supplied by
parentwise binary context families for every template. -/
theorem trimmed_paper_preferred_anchor_common_without_splicing_conclusion_package_of_context_families
    (hC : ExistsPaperPreferredAnchorCommonAllPiecesWithoutSplicing G obs)
    (hB : ForallTemplateParentwiseBinarySplicingContextFamily α) :
    PaperConstructiveLearningConclusionPackage G obs :=
  trimmed_paper_preferred_anchor_common_without_splicing_conclusion_package
    hC
    (existsNamedContextSplicingConstruction_of_contextFamilies hB)

/-- Preferred anchor-common theorem with splicing supplied by separate left and
right parentwise context families for every template. -/
theorem trimmed_paper_preferred_anchor_common_without_splicing_main_theorem_of_left_right_context_families
    (hC : ExistsPaperPreferredAnchorCommonAllPiecesWithoutSplicing G obs)
    (hL : ForallTemplateParentwiseLeftSplicingContextFamily α)
    (hR : ForallTemplateParentwiseRightSplicingContextFamily α) :
    PaperConstructiveIdentificationConclusion G obs :=
  trimmed_paper_preferred_anchor_common_without_splicing_main_theorem
    hC
    (existsNamedContextSplicingConstruction_of_left_right_contextFamilies
      hL hR)

end ContextFamilyTopLevel

end MCFG
