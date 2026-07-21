/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG2.CharacteristicSamplePreferredAllPieces

/-!
# CharacteristicSampleNamedContextSplicingConstruction.lean

One-hundred-twenty-third clean Lean experiment for the fixed-observation MCFG
project.

`CharacteristicSamplePreferredAllPieces.lean` reduced the preferred
anchor-common route to the complete checklist

```lean
PaperPreferredAnchorCommonAllPieces
```

whose fields include

```lean
splicingConstructor : NamedContextSplicingConstructor α.
```

This file starts the next phase by isolating that one ingredient.

The new record

```lean
NamedContextSplicingConstructionData
```

is a paper-facing name for a constructed `NamedContextSplicingConstructor`.
The companion record

```lean
PaperPreferredAnchorCommonAllPiecesWithoutSplicing
```

keeps all other preferred anchor-common ingredients, but leaves the splicing
constructor out.

Thus the theorem in this file says:

```text
all preferred anchor-common pieces except splicing
+
a named-context splicing construction
⇒ the paper-facing identification conclusion.
```

No new mathematical principle is introduced here; the point is to make the
splicing constructor the next isolated construction target.

No theorem here uses `sorry`.
-/

namespace MCFG

universe u v w

section NamedContextSplicingConstructionData

variable {α : Type u}

/-- Paper-facing construction data for the named-context splicing constructor. -/
structure NamedContextSplicingConstructionData where
  splicingConstructor : NamedContextSplicingConstructor α

namespace NamedContextSplicingConstructionData

/-- Convert named-context splicing construction data to the preferred splicing
target used by the global-assumption layer. -/
def toPreferredSplicingConstructorTarget
    (S : NamedContextSplicingConstructionData (α := α)) :
    PaperPreferredSplicingConstructorTarget (α := α) where
  splicingConstructor := S.splicingConstructor

/-- Convert named-context splicing construction data to the generic splicing
construction assumption. -/
def toSplicingConstructionAssumption
    (S : NamedContextSplicingConstructionData (α := α)) :
    TrimmedPresentationSplicingConstructionAssumption (α := α) where
  splicingConstructor := S.splicingConstructor

end NamedContextSplicingConstructionData

/-- Existence of a named-context splicing construction. -/
def ExistsNamedContextSplicingConstruction (α : Type u) : Prop :=
  Nonempty (NamedContextSplicingConstructionData (α := α))

/-- Existence of named-context splicing construction gives the preferred
splicing-constructor target. -/
theorem existsPreferredSplicingConstructorTarget_of_namedContextSplicing
    (h : ExistsNamedContextSplicingConstruction α) :
    Nonempty (PaperPreferredSplicingConstructorTarget (α := α)) :=
  match h with
  | ⟨S⟩ => ⟨S.toPreferredSplicingConstructorTarget⟩

/-- Existence of named-context splicing construction gives the generic splicing
construction assumption. -/
theorem existsSplicingConstructionAssumption_of_namedContextSplicing
    (h : ExistsNamedContextSplicingConstruction α) :
    Nonempty (TrimmedPresentationSplicingConstructionAssumption (α := α)) :=
  match h with
  | ⟨S⟩ => ⟨S.toSplicingConstructionAssumption⟩

end NamedContextSplicingConstructionData


section PreferredAllPiecesWithoutSplicing

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}

/-- Preferred anchor-common checklist with every item except the named-context
splicing constructor.

This is useful because the splicing constructor is now the next isolated
construction target. -/
structure PaperPreferredAnchorCommonAllPiecesWithoutSplicing where
  fanoutBound : Nat
  presentation : TrimmedOutputTypePresentation G obs
  data : TrimmedPresentationPreCoreData presentation fanoutBound
  builder : TrimmedPresentationGrammarRuleBuilder data
  fanout : G.FanoutAtMost fanoutBound
  promise : FixedNamedTupleSubstitutable fanoutBound obs G.StringLanguage
  commonTransport : TrimmedPresentationAnchorCommonContextTransport data

namespace PaperPreferredAnchorCommonAllPiecesWithoutSplicing

/-- Add a named-context splicing construction to recover the complete preferred
all-pieces checklist. -/
def withSplicing
    (C : PaperPreferredAnchorCommonAllPiecesWithoutSplicing
      (G := G) (obs := obs))
    (S : NamedContextSplicingConstructionData (α := α)) :
    PaperPreferredAnchorCommonAllPieces
      (G := G) (obs := obs) where
  fanoutBound := C.fanoutBound
  presentation := C.presentation
  data := C.data
  builder := C.builder
  splicingConstructor := S.splicingConstructor
  fanout := C.fanout
  promise := C.promise
  commonTransport := C.commonTransport

/-- Add a raw named-context splicing constructor to recover the complete
preferred all-pieces checklist. -/
def withSplicingConstructor
    (C : PaperPreferredAnchorCommonAllPiecesWithoutSplicing
      (G := G) (obs := obs))
    (S : NamedContextSplicingConstructor α) :
    PaperPreferredAnchorCommonAllPieces
      (G := G) (obs := obs) :=
  C.withSplicing
    ({ splicingConstructor := S } :
      NamedContextSplicingConstructionData (α := α))

/-- Without-splicing pieces plus splicing construction give existence of the
complete preferred all-pieces checklist. -/
theorem existsAllPieces
    (C : PaperPreferredAnchorCommonAllPiecesWithoutSplicing
      (G := G) (obs := obs))
    (S : NamedContextSplicingConstructionData (α := α)) :
    ExistsPaperPreferredAnchorCommonAllPieces G obs :=
  ⟨C.withSplicing S⟩

/-- Without-splicing pieces plus splicing construction give the paper-facing
main theorem. -/
theorem main_theorem
    (C : PaperPreferredAnchorCommonAllPiecesWithoutSplicing
      (G := G) (obs := obs))
    (S : NamedContextSplicingConstructionData (α := α)) :
    PaperConstructiveIdentificationConclusion G obs :=
  trimmed_paper_preferred_anchor_common_all_pieces_main_theorem
    (C.existsAllPieces S)

/-- Without-splicing pieces plus splicing construction give the paper-facing
conclusion package. -/
theorem conclusion_package
    (C : PaperPreferredAnchorCommonAllPiecesWithoutSplicing
      (G := G) (obs := obs))
    (S : NamedContextSplicingConstructionData (α := α)) :
    PaperConstructiveLearningConclusionPackage G obs :=
  trimmed_paper_preferred_anchor_common_all_pieces_conclusion_package
    (C.existsAllPieces S)

end PaperPreferredAnchorCommonAllPiecesWithoutSplicing

end PreferredAllPiecesWithoutSplicing


section PreferredWithoutSplicingExistentials

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}

/-- Existence of all preferred anchor-common pieces except the named-context
splicing constructor. -/
def ExistsPaperPreferredAnchorCommonAllPiecesWithoutSplicing
    (G : WorkingMCFG N α) (obs : α → M) : Prop :=
  Nonempty
    (PaperPreferredAnchorCommonAllPiecesWithoutSplicing
      (G := G) (obs := obs))

/-- Without-splicing preferred pieces plus a named-context splicing construction
give all preferred pieces. -/
theorem existsPaperPreferredAnchorCommonAllPieces_of_withoutSplicing
    (hC : ExistsPaperPreferredAnchorCommonAllPiecesWithoutSplicing G obs)
    (hS : ExistsNamedContextSplicingConstruction α) :
    ExistsPaperPreferredAnchorCommonAllPieces G obs :=
  match hC with
  | ⟨C⟩ =>
      match hS with
      | ⟨S⟩ => C.existsAllPieces S

/-- Without-splicing preferred pieces plus a named-context splicing construction
give the paper-facing main theorem. -/
theorem paperPreferredAnchorCommonWithoutSplicing_main_theorem
    (hC : ExistsPaperPreferredAnchorCommonAllPiecesWithoutSplicing G obs)
    (hS : ExistsNamedContextSplicingConstruction α) :
    PaperConstructiveIdentificationConclusion G obs :=
  trimmed_paper_preferred_anchor_common_all_pieces_main_theorem
    (existsPaperPreferredAnchorCommonAllPieces_of_withoutSplicing
      hC hS)

/-- Without-splicing preferred pieces plus a named-context splicing construction
give the paper-facing conclusion package. -/
theorem paperPreferredAnchorCommonWithoutSplicing_conclusion_package
    (hC : ExistsPaperPreferredAnchorCommonAllPiecesWithoutSplicing G obs)
    (hS : ExistsNamedContextSplicingConstruction α) :
    PaperConstructiveLearningConclusionPackage G obs :=
  trimmed_paper_preferred_anchor_common_all_pieces_conclusion_package
    (existsPaperPreferredAnchorCommonAllPieces_of_withoutSplicing
      hC hS)

end PreferredWithoutSplicingExistentials


section NamedContextSplicingConstructionTopLevel

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}

/-- Stable top-level theorem isolating the named-context splicing construction
as one independent ingredient. -/
theorem trimmed_paper_preferred_anchor_common_without_splicing_main_theorem
    (hC : ExistsPaperPreferredAnchorCommonAllPiecesWithoutSplicing G obs)
    (hS : ExistsNamedContextSplicingConstruction α) :
    PaperConstructiveIdentificationConclusion G obs :=
  paperPreferredAnchorCommonWithoutSplicing_main_theorem hC hS

/-- Stable top-level conclusion-package theorem isolating the named-context
splicing construction as one independent ingredient. -/
theorem trimmed_paper_preferred_anchor_common_without_splicing_conclusion_package
    (hC : ExistsPaperPreferredAnchorCommonAllPiecesWithoutSplicing G obs)
    (hS : ExistsNamedContextSplicingConstruction α) :
    PaperConstructiveLearningConclusionPackage G obs :=
  paperPreferredAnchorCommonWithoutSplicing_conclusion_package hC hS

/-- Stable bridge: adding a named-context splicing construction to the
without-splicing checklist gives the complete all-pieces checklist. -/
theorem trimmed_paper_preferred_anchor_common_all_pieces_of_without_splicing
    (hC : ExistsPaperPreferredAnchorCommonAllPiecesWithoutSplicing G obs)
    (hS : ExistsNamedContextSplicingConstruction α) :
    ExistsPaperPreferredAnchorCommonAllPieces G obs :=
  existsPaperPreferredAnchorCommonAllPieces_of_withoutSplicing hC hS

end NamedContextSplicingConstructionTopLevel

end MCFG
