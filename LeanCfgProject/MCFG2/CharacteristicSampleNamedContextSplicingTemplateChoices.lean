/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG2.CharacteristicSampleNamedContextSplicingTemplateTargets

/-!
# CharacteristicSampleNamedContextSplicingTemplateChoices.lean

One-hundred-twenty-eighth clean Lean experiment for the fixed-observation MCFG
project.

`CharacteristicSampleNamedContextSplicingTemplateTargets.lean` introduced
template-level constructors such as

```lean
TemplateBinaryNamedContextSplicingConstructor body
```

and their universal version

```lean
NamedContextTemplateBinarySplicingConstructor α.
```

This file separates the next proof task into two levels:

```text
for each fixed binary template body, construct a template-level splicing object;
then choose such an object uniformly for all body.
```

The file uses `Classical.choice` only as a packaging device for moving from
pointwise `Nonempty` data to a universal constructor.

No new mathematical principle is introduced here.

No theorem here uses `sorry`.
-/

namespace MCFG

universe u v w

section TemplateLevelExistence

variable {α : Type u}

/-- Existence of a template-level left splicing constructor for one fixed binary
template. -/
def ExistsTemplateLeftNamedContextSplicingConstructor
    {e dB dC : Nat}
    (body : TemplateTuple α e dB dC) : Prop :=
  Nonempty (TemplateLeftNamedContextSplicingConstructor body)

/-- Existence of a template-level right splicing constructor for one fixed binary
template. -/
def ExistsTemplateRightNamedContextSplicingConstructor
    {e dB dC : Nat}
    (body : TemplateTuple α e dB dC) : Prop :=
  Nonempty (TemplateRightNamedContextSplicingConstructor body)

/-- Existence of a template-level binary splicing constructor for one fixed
binary template. -/
def ExistsTemplateBinaryNamedContextSplicingConstructor
    {e dB dC : Nat}
    (body : TemplateTuple α e dB dC) : Prop :=
  Nonempty (TemplateBinaryNamedContextSplicingConstructor body)

/-- A template-level binary constructor gives a template-level left constructor
for the same body. -/
theorem existsTemplateLeftNamedContextSplicingConstructor_of_binary
    {e dB dC : Nat}
    {body : TemplateTuple α e dB dC}
    (h : ExistsTemplateBinaryNamedContextSplicingConstructor body) :
    ExistsTemplateLeftNamedContextSplicingConstructor body :=
  match h with
  | ⟨B⟩ => ⟨B.toLeftConstructor⟩

/-- A template-level binary constructor gives a template-level right constructor
for the same body. -/
theorem existsTemplateRightNamedContextSplicingConstructor_of_binary
    {e dB dC : Nat}
    {body : TemplateTuple α e dB dC}
    (h : ExistsTemplateBinaryNamedContextSplicingConstructor body) :
    ExistsTemplateRightNamedContextSplicingConstructor body :=
  match h with
  | ⟨B⟩ => ⟨B.toRightConstructor⟩

end TemplateLevelExistence


section UniversalTemplateChoices

variable {α : Type u}

/-- Pointwise existence of template-level left splicing constructors for every
binary template. -/
def ForallTemplateLeftNamedContextSplicingConstructor
    (α : Type u) : Prop :=
  ∀ {e dB dC : Nat}
    (body : TemplateTuple α e dB dC),
      ExistsTemplateLeftNamedContextSplicingConstructor body

/-- Pointwise existence of template-level right splicing constructors for every
binary template. -/
def ForallTemplateRightNamedContextSplicingConstructor
    (α : Type u) : Prop :=
  ∀ {e dB dC : Nat}
    (body : TemplateTuple α e dB dC),
      ExistsTemplateRightNamedContextSplicingConstructor body

/-- Pointwise existence of template-level binary splicing constructors for every
binary template. -/
def ForallTemplateBinaryNamedContextSplicingConstructor
    (α : Type u) : Prop :=
  ∀ {e dB dC : Nat}
    (body : TemplateTuple α e dB dC),
      ExistsTemplateBinaryNamedContextSplicingConstructor body

/-- Binary pointwise template construction implies left pointwise template
construction. -/
theorem forallTemplateLeftNamedContextSplicingConstructor_of_binary
    (h : ForallTemplateBinaryNamedContextSplicingConstructor α) :
    ForallTemplateLeftNamedContextSplicingConstructor α := by
  intro e dB dC body
  exact existsTemplateLeftNamedContextSplicingConstructor_of_binary
    (h body)

/-- Binary pointwise template construction implies right pointwise template
construction. -/
theorem forallTemplateRightNamedContextSplicingConstructor_of_binary
    (h : ForallTemplateBinaryNamedContextSplicingConstructor α) :
    ForallTemplateRightNamedContextSplicingConstructor α := by
  intro e dB dC body
  exact existsTemplateRightNamedContextSplicingConstructor_of_binary
    (h body)

noncomputable section

/-- Choose a universal template-level left constructor from pointwise nonempty
left template constructors. -/
def namedContextTemplateLeftSplicingConstructor_of_forall
    (h : ForallTemplateLeftNamedContextSplicingConstructor α) :
    NamedContextTemplateLeftSplicingConstructor α where
  templateLeft := by
    intro e dB dC body
    exact Classical.choice (h body)

/-- Choose a universal template-level right constructor from pointwise nonempty
right template constructors. -/
def namedContextTemplateRightSplicingConstructor_of_forall
    (h : ForallTemplateRightNamedContextSplicingConstructor α) :
    NamedContextTemplateRightSplicingConstructor α where
  templateRight := by
    intro e dB dC body
    exact Classical.choice (h body)

/-- Choose a universal template-level binary constructor from pointwise nonempty
binary template constructors. -/
def namedContextTemplateBinarySplicingConstructor_of_forall
    (h : ForallTemplateBinaryNamedContextSplicingConstructor α) :
    NamedContextTemplateBinarySplicingConstructor α where
  templateBinary := by
    intro e dB dC body
    exact Classical.choice (h body)

/-- Pointwise left and right template construction gives the universal
template-level left constructor. -/
theorem existsNamedContextTemplateLeftSplicingConstructor_of_forall
    (h : ForallTemplateLeftNamedContextSplicingConstructor α) :
    ExistsNamedContextTemplateLeftSplicingConstructor α :=
  ⟨namedContextTemplateLeftSplicingConstructor_of_forall h⟩

/-- Pointwise right template construction gives the universal template-level
right constructor. -/
theorem existsNamedContextTemplateRightSplicingConstructor_of_forall
    (h : ForallTemplateRightNamedContextSplicingConstructor α) :
    ExistsNamedContextTemplateRightSplicingConstructor α :=
  ⟨namedContextTemplateRightSplicingConstructor_of_forall h⟩

/-- Pointwise binary template construction gives the universal template-level
binary constructor. -/
theorem existsNamedContextTemplateBinarySplicingConstructor_of_forall
    (h : ForallTemplateBinaryNamedContextSplicingConstructor α) :
    ExistsNamedContextTemplateBinarySplicingConstructor α :=
  ⟨namedContextTemplateBinarySplicingConstructor_of_forall h⟩

/-- Pointwise binary template construction gives the old named-context splicing
construction. -/
theorem existsNamedContextSplicingConstruction_of_forall_template_binary
    (h : ForallTemplateBinaryNamedContextSplicingConstructor α) :
    ExistsNamedContextSplicingConstruction α :=
  existsNamedContextSplicingConstruction_of_template_binary
    (existsNamedContextTemplateBinarySplicingConstructor_of_forall h)

/-- Pointwise left and right template construction gives the old named-context
splicing construction. -/
theorem existsNamedContextSplicingConstruction_of_forall_template_left_right
    (hL : ForallTemplateLeftNamedContextSplicingConstructor α)
    (hR : ForallTemplateRightNamedContextSplicingConstructor α) :
    ExistsNamedContextSplicingConstruction α :=
  existsNamedContextSplicingConstruction_of_template_left_right
    (existsNamedContextTemplateLeftSplicingConstructor_of_forall hL)
    (existsNamedContextTemplateRightSplicingConstructor_of_forall hR)

end

end UniversalTemplateChoices


section TemplateChoiceTopLevel

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}

noncomputable section

/-- Preferred anchor-common theorem with splicing supplied by pointwise
template-level binary constructors. -/
theorem trimmed_paper_preferred_anchor_common_without_splicing_main_theorem_of_forall_template_binary
    (hC : ExistsPaperPreferredAnchorCommonAllPiecesWithoutSplicing G obs)
    (hB : ForallTemplateBinaryNamedContextSplicingConstructor α) :
    PaperConstructiveIdentificationConclusion G obs :=
  trimmed_paper_preferred_anchor_common_without_splicing_main_theorem
    hC
    (existsNamedContextSplicingConstruction_of_forall_template_binary hB)

/-- Preferred anchor-common conclusion package with splicing supplied by
pointwise template-level binary constructors. -/
theorem trimmed_paper_preferred_anchor_common_without_splicing_conclusion_package_of_forall_template_binary
    (hC : ExistsPaperPreferredAnchorCommonAllPiecesWithoutSplicing G obs)
    (hB : ForallTemplateBinaryNamedContextSplicingConstructor α) :
    PaperConstructiveLearningConclusionPackage G obs :=
  trimmed_paper_preferred_anchor_common_without_splicing_conclusion_package
    hC
    (existsNamedContextSplicingConstruction_of_forall_template_binary hB)

/-- Bridge from without-splicing preferred pieces plus pointwise template-level
binary constructors to the complete all-pieces checklist. -/
theorem trimmed_paper_preferred_anchor_common_all_pieces_of_without_splicing_forall_template_binary
    (hC : ExistsPaperPreferredAnchorCommonAllPiecesWithoutSplicing G obs)
    (hB : ForallTemplateBinaryNamedContextSplicingConstructor α) :
    ExistsPaperPreferredAnchorCommonAllPieces G obs :=
  trimmed_paper_preferred_anchor_common_all_pieces_of_without_splicing
    hC
    (existsNamedContextSplicingConstruction_of_forall_template_binary hB)

/-- Preferred anchor-common theorem with splicing supplied by pointwise
template-level left and right constructors. -/
theorem trimmed_paper_preferred_anchor_common_without_splicing_main_theorem_of_forall_template_left_right
    (hC : ExistsPaperPreferredAnchorCommonAllPiecesWithoutSplicing G obs)
    (hL : ForallTemplateLeftNamedContextSplicingConstructor α)
    (hR : ForallTemplateRightNamedContextSplicingConstructor α) :
    PaperConstructiveIdentificationConclusion G obs :=
  trimmed_paper_preferred_anchor_common_without_splicing_main_theorem
    hC
    (existsNamedContextSplicingConstruction_of_forall_template_left_right
      hL hR)

end

end TemplateChoiceTopLevel

end MCFG
