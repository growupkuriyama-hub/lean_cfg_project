/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG2.CharacteristicSampleNamedContextSplicingTemplateChoices

/-!
# CharacteristicSampleNamedContextSplicingParentChoices.lean

One-hundred-twenty-ninth clean Lean experiment for the fixed-observation MCFG
project.

`CharacteristicSampleNamedContextSplicingTemplateChoices.lean` separated
template-level splicing into pointwise existence for each binary template.

This file moves one level further inward.  For one fixed binary template `body`,
it says that a template-level constructor can be assembled from pointwise
`Nonempty` local targets for every parent named context.

In short:

```text
∀ parent, local target for parent/body
⇒ template-level target for body.
```

The file uses `Classical.choice` only as a packaging device for turning
pointwise `Nonempty` data into a function of the parent context.

No new mathematical principle is introduced here.

No theorem here uses `sorry`.
-/

namespace MCFG

universe u v w

section ParentLevelChoices

variable {α : Type u}

/-- For one fixed binary template, every parent context has a local left
splicing target. -/
def ForallParentLeftNamedContextSplicingLocalTarget
    {e dB dC : Nat}
    (body : TemplateTuple α e dB dC) : Prop :=
  ∀ parent : NamedSentenceContext α e,
    Nonempty (LeftNamedContextSplicingLocalTarget parent body)

/-- For one fixed binary template, every parent context has a local right
splicing target. -/
def ForallParentRightNamedContextSplicingLocalTarget
    {e dB dC : Nat}
    (body : TemplateTuple α e dB dC) : Prop :=
  ∀ parent : NamedSentenceContext α e,
    Nonempty (RightNamedContextSplicingLocalTarget parent body)

/-- For one fixed binary template, every parent context has a local binary
splicing target. -/
def ForallParentBinaryNamedContextSplicingLocalTarget
    {e dB dC : Nat}
    (body : TemplateTuple α e dB dC) : Prop :=
  ∀ parent : NamedSentenceContext α e,
    Nonempty (BinaryNamedContextSplicingLocalTarget parent body)

/-- Parentwise binary local targets imply parentwise left local targets. -/
theorem forallParentLeftNamedContextSplicingLocalTarget_of_binary
    {e dB dC : Nat}
    {body : TemplateTuple α e dB dC}
    (h : ForallParentBinaryNamedContextSplicingLocalTarget body) :
    ForallParentLeftNamedContextSplicingLocalTarget body := by
  intro parent
  rcases h parent with ⟨B⟩
  exact ⟨B.leftTarget⟩

/-- Parentwise binary local targets imply parentwise right local targets. -/
theorem forallParentRightNamedContextSplicingLocalTarget_of_binary
    {e dB dC : Nat}
    {body : TemplateTuple α e dB dC}
    (h : ForallParentBinaryNamedContextSplicingLocalTarget body) :
    ForallParentRightNamedContextSplicingLocalTarget body := by
  intro parent
  rcases h parent with ⟨B⟩
  exact ⟨B.rightTarget⟩

noncomputable section

/-- Choose a template-level left constructor from parentwise nonempty local-left
targets. -/
def templateLeftNamedContextSplicingConstructor_of_forall_parent
    {e dB dC : Nat}
    {body : TemplateTuple α e dB dC}
    (h : ForallParentLeftNamedContextSplicingLocalTarget body) :
    TemplateLeftNamedContextSplicingConstructor body where
  leftTarget := by
    intro parent
    exact Classical.choice (h parent)

/-- Choose a template-level right constructor from parentwise nonempty
local-right targets. -/
def templateRightNamedContextSplicingConstructor_of_forall_parent
    {e dB dC : Nat}
    {body : TemplateTuple α e dB dC}
    (h : ForallParentRightNamedContextSplicingLocalTarget body) :
    TemplateRightNamedContextSplicingConstructor body where
  rightTarget := by
    intro parent
    exact Classical.choice (h parent)

/-- Choose a template-level binary constructor from parentwise nonempty
local-binary targets. -/
def templateBinaryNamedContextSplicingConstructor_of_forall_parent
    {e dB dC : Nat}
    {body : TemplateTuple α e dB dC}
    (h : ForallParentBinaryNamedContextSplicingLocalTarget body) :
    TemplateBinaryNamedContextSplicingConstructor body where
  binaryTarget := by
    intro parent
    exact Classical.choice (h parent)

/-- Parentwise local-left targets give a template-level left target. -/
theorem existsTemplateLeftNamedContextSplicingConstructor_of_forall_parent
    {e dB dC : Nat}
    {body : TemplateTuple α e dB dC}
    (h : ForallParentLeftNamedContextSplicingLocalTarget body) :
    ExistsTemplateLeftNamedContextSplicingConstructor body :=
  ⟨templateLeftNamedContextSplicingConstructor_of_forall_parent h⟩

/-- Parentwise local-right targets give a template-level right target. -/
theorem existsTemplateRightNamedContextSplicingConstructor_of_forall_parent
    {e dB dC : Nat}
    {body : TemplateTuple α e dB dC}
    (h : ForallParentRightNamedContextSplicingLocalTarget body) :
    ExistsTemplateRightNamedContextSplicingConstructor body :=
  ⟨templateRightNamedContextSplicingConstructor_of_forall_parent h⟩

/-- Parentwise local-binary targets give a template-level binary target. -/
theorem existsTemplateBinaryNamedContextSplicingConstructor_of_forall_parent
    {e dB dC : Nat}
    {body : TemplateTuple α e dB dC}
    (h : ForallParentBinaryNamedContextSplicingLocalTarget body) :
    ExistsTemplateBinaryNamedContextSplicingConstructor body :=
  ⟨templateBinaryNamedContextSplicingConstructor_of_forall_parent h⟩

end

end ParentLevelChoices


section UniversalParentLevelChoices

variable {α : Type u}

/-- For every binary template and every parent context, there is a local left
splicing target. -/
def ForallTemplateParentLeftNamedContextSplicingLocalTarget
    (α : Type u) : Prop :=
  ∀ {e dB dC : Nat}
    (body : TemplateTuple α e dB dC),
      ForallParentLeftNamedContextSplicingLocalTarget body

/-- For every binary template and every parent context, there is a local right
splicing target. -/
def ForallTemplateParentRightNamedContextSplicingLocalTarget
    (α : Type u) : Prop :=
  ∀ {e dB dC : Nat}
    (body : TemplateTuple α e dB dC),
      ForallParentRightNamedContextSplicingLocalTarget body

/-- For every binary template and every parent context, there is a local binary
splicing target. -/
def ForallTemplateParentBinaryNamedContextSplicingLocalTarget
    (α : Type u) : Prop :=
  ∀ {e dB dC : Nat}
    (body : TemplateTuple α e dB dC),
      ForallParentBinaryNamedContextSplicingLocalTarget body

/-- Universal binary parentwise local targets imply universal left parentwise
local targets. -/
theorem forallTemplateParentLeftNamedContextSplicingLocalTarget_of_binary
    (h : ForallTemplateParentBinaryNamedContextSplicingLocalTarget α) :
    ForallTemplateParentLeftNamedContextSplicingLocalTarget α := by
  intro e dB dC body
  exact forallParentLeftNamedContextSplicingLocalTarget_of_binary
    (h body)

/-- Universal binary parentwise local targets imply universal right parentwise
local targets. -/
theorem forallTemplateParentRightNamedContextSplicingLocalTarget_of_binary
    (h : ForallTemplateParentBinaryNamedContextSplicingLocalTarget α) :
    ForallTemplateParentRightNamedContextSplicingLocalTarget α := by
  intro e dB dC body
  exact forallParentRightNamedContextSplicingLocalTarget_of_binary
    (h body)

noncomputable section

/-- Parentwise local-left construction for every template gives pointwise
template-level left construction. -/
theorem forallTemplateLeftNamedContextSplicingConstructor_of_forall_parent
    (h : ForallTemplateParentLeftNamedContextSplicingLocalTarget α) :
    ForallTemplateLeftNamedContextSplicingConstructor α := by
  intro e dB dC body
  exact existsTemplateLeftNamedContextSplicingConstructor_of_forall_parent
    (h body)

/-- Parentwise local-right construction for every template gives pointwise
template-level right construction. -/
theorem forallTemplateRightNamedContextSplicingConstructor_of_forall_parent
    (h : ForallTemplateParentRightNamedContextSplicingLocalTarget α) :
    ForallTemplateRightNamedContextSplicingConstructor α := by
  intro e dB dC body
  exact existsTemplateRightNamedContextSplicingConstructor_of_forall_parent
    (h body)

/-- Parentwise local-binary construction for every template gives pointwise
template-level binary construction. -/
theorem forallTemplateBinaryNamedContextSplicingConstructor_of_forall_parent
    (h : ForallTemplateParentBinaryNamedContextSplicingLocalTarget α) :
    ForallTemplateBinaryNamedContextSplicingConstructor α := by
  intro e dB dC body
  exact existsTemplateBinaryNamedContextSplicingConstructor_of_forall_parent
    (h body)

/-- Universal parentwise binary local construction gives the old named-context
splicing construction. -/
theorem existsNamedContextSplicingConstruction_of_forall_template_parent_binary
    (h : ForallTemplateParentBinaryNamedContextSplicingLocalTarget α) :
    ExistsNamedContextSplicingConstruction α :=
  existsNamedContextSplicingConstruction_of_forall_template_binary
    (forallTemplateBinaryNamedContextSplicingConstructor_of_forall_parent h)

/-- Universal parentwise left and right local construction gives the old
named-context splicing construction. -/
theorem existsNamedContextSplicingConstruction_of_forall_template_parent_left_right
    (hL : ForallTemplateParentLeftNamedContextSplicingLocalTarget α)
    (hR : ForallTemplateParentRightNamedContextSplicingLocalTarget α) :
    ExistsNamedContextSplicingConstruction α :=
  existsNamedContextSplicingConstruction_of_forall_template_left_right
    (forallTemplateLeftNamedContextSplicingConstructor_of_forall_parent hL)
    (forallTemplateRightNamedContextSplicingConstructor_of_forall_parent hR)

end

end UniversalParentLevelChoices


section ParentChoiceTopLevel

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}

noncomputable section

/-- Preferred anchor-common theorem with splicing supplied by parentwise local
binary targets for every template. -/
theorem trimmed_paper_preferred_anchor_common_without_splicing_main_theorem_of_forall_template_parent_binary
    (hC : ExistsPaperPreferredAnchorCommonAllPiecesWithoutSplicing G obs)
    (hB : ForallTemplateParentBinaryNamedContextSplicingLocalTarget α) :
    PaperConstructiveIdentificationConclusion G obs :=
  trimmed_paper_preferred_anchor_common_without_splicing_main_theorem
    hC
    (existsNamedContextSplicingConstruction_of_forall_template_parent_binary hB)

/-- Preferred anchor-common conclusion package with splicing supplied by
parentwise local binary targets for every template. -/
theorem trimmed_paper_preferred_anchor_common_without_splicing_conclusion_package_of_forall_template_parent_binary
    (hC : ExistsPaperPreferredAnchorCommonAllPiecesWithoutSplicing G obs)
    (hB : ForallTemplateParentBinaryNamedContextSplicingLocalTarget α) :
    PaperConstructiveLearningConclusionPackage G obs :=
  trimmed_paper_preferred_anchor_common_without_splicing_conclusion_package
    hC
    (existsNamedContextSplicingConstruction_of_forall_template_parent_binary hB)

/-- Bridge from without-splicing preferred pieces plus parentwise local binary
targets for every template to the complete all-pieces checklist. -/
theorem trimmed_paper_preferred_anchor_common_all_pieces_of_without_splicing_forall_template_parent_binary
    (hC : ExistsPaperPreferredAnchorCommonAllPiecesWithoutSplicing G obs)
    (hB : ForallTemplateParentBinaryNamedContextSplicingLocalTarget α) :
    ExistsPaperPreferredAnchorCommonAllPieces G obs :=
  trimmed_paper_preferred_anchor_common_all_pieces_of_without_splicing
    hC
    (existsNamedContextSplicingConstruction_of_forall_template_parent_binary hB)

/-- Preferred anchor-common theorem with splicing supplied by parentwise local
left and right targets for every template. -/
theorem trimmed_paper_preferred_anchor_common_without_splicing_main_theorem_of_forall_template_parent_left_right
    (hC : ExistsPaperPreferredAnchorCommonAllPiecesWithoutSplicing G obs)
    (hL : ForallTemplateParentLeftNamedContextSplicingLocalTarget α)
    (hR : ForallTemplateParentRightNamedContextSplicingLocalTarget α) :
    PaperConstructiveIdentificationConclusion G obs :=
  trimmed_paper_preferred_anchor_common_without_splicing_main_theorem
    hC
    (existsNamedContextSplicingConstruction_of_forall_template_parent_left_right
      hL hR)

end

end ParentChoiceTopLevel

end MCFG
