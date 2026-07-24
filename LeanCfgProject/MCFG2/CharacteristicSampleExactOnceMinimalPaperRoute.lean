/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG2.CharacteristicSampleNamedContextSplicingExactOnceIntegration

/-!
# CharacteristicSampleExactOnceMinimalPaperRoute.lean

A smaller corrected paper-facing route after concrete exact-once named-context
splicing has been integrated.

The previous corrected endpoint used
`PaperPreferredAnchorCommonAllPiecesWithoutSplicing`.  That record still stored
an `AnchorCommonContextTransport` field, although the exact-once integration
actually used only the already-built positive grammar-rule sample.

This file removes that redundant transport assumption.  The remaining data are:

* a fanout bound;
* a trimmed output-type presentation;
* pre-core data;
* a positive grammar-rule sample builder;
* the fanout bound proof;
* the fixed-observation substitutability promise.

Together with `BinaryRulesExactlyOnce` (or `ExactWorkingConditions`), these data
produce the reachable characteristic-sample and Gold-identification conclusions.
No theorem in this file uses the false unrestricted
`NamedContextSplicingConstructor` interface.
-/

namespace MCFG

universe u v w

section ExactOnceMinimalPieces

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}

/-- Minimal corrected paper-facing data after exact-once splicing has been
constructed.  In particular, no unrestricted splicing constructor and no
anchor-common transport witness are stored here. -/
structure PaperExactOnceMinimalPieces where
  fanoutBound : Nat
  presentation : TrimmedOutputTypePresentation G obs
  data : TrimmedPresentationPreCoreData presentation fanoutBound
  builder : TrimmedPresentationGrammarRuleBuilder data
  fanout : G.FanoutAtMost fanoutBound
  promise : FixedNamedTupleSubstitutable fanoutBound obs G.StringLanguage

namespace PaperExactOnceMinimalPieces

/-- The finite positive sample supplied by the grammar-rule builder. -/
noncomputable def sample
    (C : PaperExactOnceMinimalPieces (G := G) (obs := obs)) :
    Finset (Word α) :=
  C.builder.sample

/-- The builder sample viewed as the trimmed-presentation sample data needed by
the exact-once integration. -/
def sampleData
    (C : PaperExactOnceMinimalPieces (G := G) (obs := obs)) :
    TrimmedPresentationSampleData C.data C.sample :=
  C.builder.toWitnessSample.toSampleData

/-- The finite sample is positive. -/
theorem sample_positive
    (C : PaperExactOnceMinimalPieces (G := G) (obs := obs)) :
    (C.sample : Set (Word α)) ⊆ G.StringLanguage :=
  C.builder.sample_positive

/-- Concrete exact-once splicing turns the stored sample data into the ordinary
reachable characteristic blueprint. -/
noncomputable def toExactReachableBlueprint
    (C : PaperExactOnceMinimalPieces (G := G) (obs := obs))
    (hexact : G.BinaryRulesExactlyOnce) :
    ReachableCharacteristicBlueprint
      G C.sample obs C.fanoutBound :=
  C.sampleData.toExactReachableBlueprint hexact

/-- The stored finite positive sample is characteristic for the reachable
learner. -/
theorem characteristic_sample
    (C : PaperExactOnceMinimalPieces (G := G) (obs := obs))
    (hexact : G.BinaryRulesExactlyOnce) :
    CharacteristicSample
      (reachableHypLanguage obs C.fanoutBound)
      (reachableSampleLearner (α := α))
      C.sample
      G.StringLanguage :=
  C.sampleData.exact_characteristic_sample
    hexact C.fanout C.promise

/-- Exact reconstruction holds for every positive finite superset of the stored
sample. -/
theorem exact_for_positive_superset
    (C : PaperExactOnceMinimalPieces (G := G) (obs := obs))
    (hexact : G.BinaryRulesExactlyOnce)
    {K : Finset (Word α)}
    (hSK : (C.sample : Set (Word α)) ⊆ (K : Set (Word α)))
    (hKpos : (K : Set (Word α)) ⊆ G.StringLanguage) :
    ReachableSampleStringLanguage K obs C.fanoutBound =
      G.StringLanguage :=
  C.sampleData.exact_reconstruction_for_positive_superset
    hexact C.fanout C.promise hSK hKpos

/-- Eventual exact reconstruction on every positive text. -/
theorem prefix_exact_eventually
    (C : PaperExactOnceMinimalPieces (G := G) (obs := obs))
    (hexact : G.BinaryRulesExactlyOnce) :
    ∀ Ttxt : TextFor G.StringLanguage,
      ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
        ReachableSampleStringLanguage
          (Ttxt.prefixSample n) obs C.fanoutBound =
          G.StringLanguage :=
  C.sampleData.exact_prefix_reconstruction
    hexact C.fanout C.promise

/-- Gold-style identification of the target by the reachable learner. -/
theorem identifies_from_positive_text
    (C : PaperExactOnceMinimalPieces (G := G) (obs := obs))
    (hexact : G.BinaryRulesExactlyOnce) :
    ∀ Ttxt : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs C.fanoutBound)
        (reachableSampleLearner (α := α))
        Ttxt :=
  C.sampleData.exact_identifies_from_positive_text
    hexact C.fanout C.promise

/-- Paper-facing finite positive characteristic-sample conclusion. -/
theorem paper_characteristic_sample_theorem
    (C : PaperExactOnceMinimalPieces (G := G) (obs := obs))
    (hexact : G.BinaryRulesExactlyOnce) :
    PaperConstructiveCharacteristicSampleConclusion G obs := by
  change ExistsBoundedPositiveCharacteristicSample G obs
  exact ⟨C.fanoutBound, C.sample, C.sample_positive,
    C.characteristic_sample hexact⟩

/-- Paper-facing eventual prefix-exact conclusion. -/
theorem paper_prefix_exact_theorem
    (C : PaperExactOnceMinimalPieces (G := G) (obs := obs))
    (hexact : G.BinaryRulesExactlyOnce) :
    PaperConstructivePrefixExactConclusion G obs := by
  change ExistsBoundedPrefixExactIdentification G obs
  exact ⟨C.fanoutBound, C.prefix_exact_eventually hexact⟩

/-- Corrected paper-facing identification theorem from the minimal pieces. -/
theorem paper_main_theorem
    (C : PaperExactOnceMinimalPieces (G := G) (obs := obs))
    (hexact : G.BinaryRulesExactlyOnce) :
    PaperConstructiveIdentificationConclusion G obs := by
  change ExistsBoundedReachableIdentification G obs
  exact ⟨C.fanoutBound, C.identifies_from_positive_text hexact⟩

/-- Complete corrected learning conclusion package from the minimal pieces. -/
theorem paper_conclusion_package
    (C : PaperExactOnceMinimalPieces (G := G) (obs := obs))
    (hexact : G.BinaryRulesExactlyOnce) :
    PaperConstructiveLearningConclusionPackage G obs :=
  ⟨C.paper_characteristic_sample_theorem hexact,
    C.paper_prefix_exact_theorem hexact,
    C.paper_main_theorem hexact⟩

/-- Version using the paper's exact working-condition package. -/
theorem exact_working_paper_main_theorem
    (C : PaperExactOnceMinimalPieces (G := G) (obs := obs))
    (hworking : G.ExactWorkingConditions) :
    PaperConstructiveIdentificationConclusion G obs :=
  C.paper_main_theorem hworking.2

/-- Full conclusion package using the paper's exact working conditions. -/
theorem exact_working_paper_conclusion_package
    (C : PaperExactOnceMinimalPieces (G := G) (obs := obs))
    (hworking : G.ExactWorkingConditions) :
    PaperConstructiveLearningConclusionPackage G obs :=
  C.paper_conclusion_package hworking.2

end PaperExactOnceMinimalPieces

end ExactOnceMinimalPieces


section ExactOnceMinimalExistentials

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}

/-- Existence of the corrected minimal data package. -/
def ExistsPaperExactOnceMinimalPieces
    (G : WorkingMCFG N α) (obs : α → M) : Prop :=
  Nonempty (PaperExactOnceMinimalPieces (G := G) (obs := obs))

/-- Stable corrected endpoint from minimal pieces and exact-once rules. -/
theorem trimmed_paper_exact_once_minimal_main_theorem
    (hC : ExistsPaperExactOnceMinimalPieces G obs)
    (hexact : G.BinaryRulesExactlyOnce) :
    PaperConstructiveIdentificationConclusion G obs :=
  match hC with
  | ⟨C⟩ => C.paper_main_theorem hexact

/-- Stable corrected full conclusion package from minimal pieces. -/
theorem trimmed_paper_exact_once_minimal_conclusion_package
    (hC : ExistsPaperExactOnceMinimalPieces G obs)
    (hexact : G.BinaryRulesExactlyOnce) :
    PaperConstructiveLearningConclusionPackage G obs :=
  match hC with
  | ⟨C⟩ => C.paper_conclusion_package hexact

/-- Stable corrected endpoint phrased with exact working conditions. -/
theorem trimmed_paper_exact_working_minimal_main_theorem
    (hC : ExistsPaperExactOnceMinimalPieces G obs)
    (hworking : G.ExactWorkingConditions) :
    PaperConstructiveIdentificationConclusion G obs :=
  trimmed_paper_exact_once_minimal_main_theorem hC hworking.2

/-- Stable corrected full conclusion package phrased with exact working
conditions. -/
theorem trimmed_paper_exact_working_minimal_conclusion_package
    (hC : ExistsPaperExactOnceMinimalPieces G obs)
    (hworking : G.ExactWorkingConditions) :
    PaperConstructiveLearningConclusionPackage G obs :=
  trimmed_paper_exact_once_minimal_conclusion_package hC hworking.2

end ExactOnceMinimalExistentials

end MCFG
