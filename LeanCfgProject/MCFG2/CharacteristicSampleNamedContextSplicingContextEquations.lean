/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG2.CharacteristicSampleNamedContextSplicingContextFamilies

/-!
# CharacteristicSampleNamedContextSplicingContextEquations.lean

One-hundred-thirty-first clean Lean experiment for the fixed-observation MCFG
project.

This file splits parentwise child-context families into:

```text
context functions
+
namedFill equation proofs.
```

No new mathematical principle is introduced here.

No theorem here uses `sorry`.
-/

namespace MCFG

universe u v w

section ParentwiseContextFunctionsAndEquations

variable {α : Type u}

/-- Left child-context function alone, without the namedFill equation. -/
structure ParentwiseLeftSplicingContextFunctions
    {e dB dC : Nat}
    (body : TemplateTuple α e dB dC) where
  leftContext :
    (parent : NamedSentenceContext α e) →
      Tuple α dC → NamedSentenceContext α dB

/-- Right child-context function alone, without the namedFill equation. -/
structure ParentwiseRightSplicingContextFunctions
    {e dB dC : Nat}
    (body : TemplateTuple α e dB dC) where
  rightContext :
    (parent : NamedSentenceContext α e) →
      Tuple α dB → NamedSentenceContext α dC

/-- Both left and right child-context functions, without equations. -/
structure ParentwiseBinarySplicingContextFunctions
    {e dB dC : Nat}
    (body : TemplateTuple α e dB dC) where
  leftFunctions : ParentwiseLeftSplicingContextFunctions body
  rightFunctions : ParentwiseRightSplicingContextFunctions body

/-- The namedFill equation for a chosen left child-context function. -/
structure ParentwiseLeftSplicingContextEquations
    {e dB dC : Nat}
    {body : TemplateTuple α e dB dC}
    (F : ParentwiseLeftSplicingContextFunctions body) where
  left_fill_eq :
    ∀ (parent : NamedSentenceContext α e)
      (y : Tuple α dC) (x : Tuple α dB),
      namedFill dB (F.leftContext parent y) x =
        namedFill e parent (evalTemplateTuple body x y)

/-- The namedFill equation for a chosen right child-context function. -/
structure ParentwiseRightSplicingContextEquations
    {e dB dC : Nat}
    {body : TemplateTuple α e dB dC}
    (F : ParentwiseRightSplicingContextFunctions body) where
  right_fill_eq :
    ∀ (parent : NamedSentenceContext α e)
      (u : Tuple α dB) (v : Tuple α dC),
      namedFill dC (F.rightContext parent u) v =
        namedFill e parent (evalTemplateTuple body u v)

/-- The two namedFill equations for chosen left/right context functions. -/
structure ParentwiseBinarySplicingContextEquations
    {e dB dC : Nat}
    {body : TemplateTuple α e dB dC}
    (F : ParentwiseBinarySplicingContextFunctions body) where
  leftEquations :
    ParentwiseLeftSplicingContextEquations F.leftFunctions
  rightEquations :
    ParentwiseRightSplicingContextEquations F.rightFunctions

namespace ParentwiseLeftSplicingContextFunctions

variable {e dB dC : Nat}
variable {body : TemplateTuple α e dB dC}

/-- Add the left equation to obtain the previous left context family. -/
def withEquations
    (F : ParentwiseLeftSplicingContextFunctions body)
    (E : ParentwiseLeftSplicingContextEquations F) :
    ParentwiseLeftSplicingContextFamily body where
  leftContext := F.leftContext
  left_fill_eq := E.left_fill_eq

end ParentwiseLeftSplicingContextFunctions


namespace ParentwiseRightSplicingContextFunctions

variable {e dB dC : Nat}
variable {body : TemplateTuple α e dB dC}

/-- Add the right equation to obtain the previous right context family. -/
def withEquations
    (F : ParentwiseRightSplicingContextFunctions body)
    (E : ParentwiseRightSplicingContextEquations F) :
    ParentwiseRightSplicingContextFamily body where
  rightContext := F.rightContext
  right_fill_eq := E.right_fill_eq

end ParentwiseRightSplicingContextFunctions


namespace ParentwiseBinarySplicingContextFunctions

variable {e dB dC : Nat}
variable {body : TemplateTuple α e dB dC}

/-- Add both equations to obtain the previous binary context family. -/
def withEquations
    (F : ParentwiseBinarySplicingContextFunctions body)
    (E : ParentwiseBinarySplicingContextEquations F) :
    ParentwiseBinarySplicingContextFamily body where
  leftFamily := F.leftFunctions.withEquations E.leftEquations
  rightFamily := F.rightFunctions.withEquations E.rightEquations

/-- The completed binary context family gives a template-level binary
constructor. -/
def toTemplateBinaryConstructor
    (F : ParentwiseBinarySplicingContextFunctions body)
    (E : ParentwiseBinarySplicingContextEquations F) :
    TemplateBinaryNamedContextSplicingConstructor body :=
  (F.withEquations E).toTemplateBinaryConstructor

end ParentwiseBinarySplicingContextFunctions

end ParentwiseContextFunctionsAndEquations


section UniversalContextFunctionTargets

variable {α : Type u}

/-- For every binary template, there are left context functions together with
their namedFill equations. -/
def ForallTemplateParentwiseLeftSplicingContextFunctionsWithEquations
    (α : Type u) : Prop :=
  ∀ {e dB dC : Nat}
    (body : TemplateTuple α e dB dC),
      ∃ F : ParentwiseLeftSplicingContextFunctions body,
        Nonempty (ParentwiseLeftSplicingContextEquations F)

/-- For every binary template, there are right context functions together with
their namedFill equations. -/
def ForallTemplateParentwiseRightSplicingContextFunctionsWithEquations
    (α : Type u) : Prop :=
  ∀ {e dB dC : Nat}
    (body : TemplateTuple α e dB dC),
      ∃ F : ParentwiseRightSplicingContextFunctions body,
        Nonempty (ParentwiseRightSplicingContextEquations F)

/-- For every binary template, there are left/right context functions together
with both namedFill equations. -/
def ForallTemplateParentwiseBinarySplicingContextFunctionsWithEquations
    (α : Type u) : Prop :=
  ∀ {e dB dC : Nat}
    (body : TemplateTuple α e dB dC),
      ∃ F : ParentwiseBinarySplicingContextFunctions body,
        Nonempty (ParentwiseBinarySplicingContextEquations F)

/-- Binary context functions with equations give left context functions with
equations. -/
theorem forallTemplateParentwiseLeftSplicingContextFunctionsWithEquations_of_binary
    (h : ForallTemplateParentwiseBinarySplicingContextFunctionsWithEquations α) :
    ForallTemplateParentwiseLeftSplicingContextFunctionsWithEquations α := by
  intro e dB dC body
  rcases h body with ⟨F, hE⟩
  rcases hE with ⟨E⟩
  exact ⟨F.leftFunctions, ⟨E.leftEquations⟩⟩

/-- Binary context functions with equations give right context functions with
equations. -/
theorem forallTemplateParentwiseRightSplicingContextFunctionsWithEquations_of_binary
    (h : ForallTemplateParentwiseBinarySplicingContextFunctionsWithEquations α) :
    ForallTemplateParentwiseRightSplicingContextFunctionsWithEquations α := by
  intro e dB dC body
  rcases h body with ⟨F, hE⟩
  rcases hE with ⟨E⟩
  exact ⟨F.rightFunctions, ⟨E.rightEquations⟩⟩

/-- Left context functions with equations give the previous left context-family
interface. -/
theorem forallTemplateParentwiseLeftSplicingContextFamily_of_functions_equations
    (h : ForallTemplateParentwiseLeftSplicingContextFunctionsWithEquations α) :
    ForallTemplateParentwiseLeftSplicingContextFamily α := by
  intro e dB dC body
  rcases h body with ⟨F, hE⟩
  rcases hE with ⟨E⟩
  exact ⟨F.withEquations E⟩

/-- Right context functions with equations give the previous right context-family
interface. -/
theorem forallTemplateParentwiseRightSplicingContextFamily_of_functions_equations
    (h : ForallTemplateParentwiseRightSplicingContextFunctionsWithEquations α) :
    ForallTemplateParentwiseRightSplicingContextFamily α := by
  intro e dB dC body
  rcases h body with ⟨F, hE⟩
  rcases hE with ⟨E⟩
  exact ⟨F.withEquations E⟩

/-- Binary context functions with equations give the previous binary
context-family interface. -/
theorem forallTemplateParentwiseBinarySplicingContextFamily_of_functions_equations
    (h : ForallTemplateParentwiseBinarySplicingContextFunctionsWithEquations α) :
    ForallTemplateParentwiseBinarySplicingContextFamily α := by
  intro e dB dC body
  rcases h body with ⟨F, hE⟩
  rcases hE with ⟨E⟩
  exact ⟨F.withEquations E⟩

/-- Binary context functions with equations give named-context splicing
construction. -/
theorem existsNamedContextSplicingConstruction_of_context_functions_equations
    (h : ForallTemplateParentwiseBinarySplicingContextFunctionsWithEquations α) :
    ExistsNamedContextSplicingConstruction α :=
  existsNamedContextSplicingConstruction_of_contextFamilies
    (forallTemplateParentwiseBinarySplicingContextFamily_of_functions_equations h)

/-- Separate left/right context functions with equations give named-context
splicing construction. -/
theorem existsNamedContextSplicingConstruction_of_left_right_context_functions_equations
    (hL : ForallTemplateParentwiseLeftSplicingContextFunctionsWithEquations α)
    (hR : ForallTemplateParentwiseRightSplicingContextFunctionsWithEquations α) :
    ExistsNamedContextSplicingConstruction α :=
  existsNamedContextSplicingConstruction_of_left_right_contextFamilies
    (forallTemplateParentwiseLeftSplicingContextFamily_of_functions_equations hL)
    (forallTemplateParentwiseRightSplicingContextFamily_of_functions_equations hR)

end UniversalContextFunctionTargets


section ContextEquationTopLevel

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}

/-- Preferred anchor-common theorem with splicing supplied by explicit
left/right context functions plus namedFill equations. -/
theorem trimmed_paper_preferred_anchor_common_without_splicing_main_theorem_of_context_functions_equations
    (hC : ExistsPaperPreferredAnchorCommonAllPiecesWithoutSplicing G obs)
    (hB :
      ForallTemplateParentwiseBinarySplicingContextFunctionsWithEquations α) :
    PaperConstructiveIdentificationConclusion G obs :=
  trimmed_paper_preferred_anchor_common_without_splicing_main_theorem
    hC
    (existsNamedContextSplicingConstruction_of_context_functions_equations hB)

/-- Preferred anchor-common conclusion package with splicing supplied by explicit
left/right context functions plus namedFill equations. -/
theorem trimmed_paper_preferred_anchor_common_without_splicing_conclusion_package_of_context_functions_equations
    (hC : ExistsPaperPreferredAnchorCommonAllPiecesWithoutSplicing G obs)
    (hB :
      ForallTemplateParentwiseBinarySplicingContextFunctionsWithEquations α) :
    PaperConstructiveLearningConclusionPackage G obs :=
  trimmed_paper_preferred_anchor_common_without_splicing_conclusion_package
    hC
    (existsNamedContextSplicingConstruction_of_context_functions_equations hB)

/-- Preferred anchor-common theorem with splicing supplied by separate left and
right context functions plus namedFill equations. -/
theorem trimmed_paper_preferred_anchor_common_without_splicing_main_theorem_of_left_right_context_functions_equations
    (hC : ExistsPaperPreferredAnchorCommonAllPiecesWithoutSplicing G obs)
    (hL :
      ForallTemplateParentwiseLeftSplicingContextFunctionsWithEquations α)
    (hR :
      ForallTemplateParentwiseRightSplicingContextFunctionsWithEquations α) :
    PaperConstructiveIdentificationConclusion G obs :=
  trimmed_paper_preferred_anchor_common_without_splicing_main_theorem
    hC
    (existsNamedContextSplicingConstruction_of_left_right_context_functions_equations
      hL hR)

end ContextEquationTopLevel

end MCFG
