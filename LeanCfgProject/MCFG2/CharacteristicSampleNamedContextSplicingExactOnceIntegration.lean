/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG2.CharacteristicSampleNamedContextSplicingExactOnceConstruction
import LeanCfgProject.MCFG2.CharacteristicSampleNamedContextSplicingConstruction

/-!
# CharacteristicSampleNamedContextSplicingExactOnceIntegration.lean

Correct integration of concrete named-context splicing into the reachable
learning theorem.

The old `NamedContextSplicingConstructor` quantified over arbitrary templates
and is not generally inhabited.  This file bypasses that false interface.  For
a grammar whose listed binary rules satisfy `BinaryRulesExactlyOnce`, the
concrete constructor from
`CharacteristicSampleNamedContextSplicingExactOnceConstruction.lean` supplies
the filling witnesses required by the already verified characteristic-sample
and Gold-identification chain.

No theorem here uses `sorry`, `admit`, or `axiom`.
-/

namespace MCFG

universe u v w

section ExactSampleIntegration

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}
variable {f : Nat}
variable {T : TrimmedOutputTypePresentation G obs}
variable {D : TrimmedPresentationPreCoreData T f}
variable {S : Finset (Word α)}

namespace TrimmedPresentationSampleData

/-- Concrete exact-once filling witnesses for the pre-core attached to `D`. -/
def exactFillingWitnessFamily
    (H : TrimmedPresentationSampleData D S)
    (hexact : G.BinaryRulesExactlyOnce) :
    BinaryFillingWitnessFamily G D.toReachablePreCore :=
  (ExactSplicing.exact_namedContextSplicingConstructor α)
    .toFillingWitnessFamily hexact G D.toReachablePreCore

/-- Build the ordinary reachable characteristic blueprint without using the
false universal splicing-constructor assumption. -/
def toExactReachableBlueprint
    (H : TrimmedPresentationSampleData D S)
    (hexact : G.BinaryRulesExactlyOnce) :
    ReachableCharacteristicBlueprint G S obs f :=
  H.toReachablePreCoreFiniteSample.toBlueprint
    (H.exactFillingWitnessFamily hexact)

/-- Exact-once sample data gives a characteristic sample for the reachable
learner. -/
theorem exact_characteristic_sample
    (H : TrimmedPresentationSampleData D S)
    (hexact : G.BinaryRulesExactlyOnce)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    CharacteristicSample
      (reachableHypLanguage obs f)
      (reachableSampleLearner (α := α))
      S
      G.StringLanguage :=
  (H.toExactReachableBlueprint hexact).characteristic_sample hfan hL

/-- Exact-once sample data gives exact reconstruction on every positive finite
superset. -/
theorem exact_reconstruction_for_positive_superset
    (H : TrimmedPresentationSampleData D S)
    (hexact : G.BinaryRulesExactlyOnce)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage)
    {K : Finset (Word α)}
    (hSK : (S : Set (Word α)) ⊆ (K : Set (Word α)))
    (hKpos : (K : Set (Word α)) ⊆ G.StringLanguage) :
    ReachableSampleStringLanguage K obs f = G.StringLanguage :=
  (H.toExactReachableBlueprint hexact)
    .exact_for_positive_superset hfan hL hSK hKpos

/-- Exact-once sample data gives eventual prefix-exact reconstruction. -/
theorem exact_prefix_reconstruction
    (H : TrimmedPresentationSampleData D S)
    (hexact : G.BinaryRulesExactlyOnce)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    ∀ Ttxt : TextFor G.StringLanguage,
      ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
        ReachableSampleStringLanguage (Ttxt.prefixSample n) obs f =
          G.StringLanguage :=
  (H.toExactReachableBlueprint hexact).prefix_exact_eventually hfan hL

/-- Exact-once sample data gives Gold identification for the reachable learner. -/
theorem exact_identifies_from_positive_text
    (H : TrimmedPresentationSampleData D S)
    (hexact : G.BinaryRulesExactlyOnce)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    ∀ Ttxt : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        Ttxt :=
  (H.toExactReachableBlueprint hexact).identifies_from_positive_text hfan hL

end TrimmedPresentationSampleData

end ExactSampleIntegration


section PreferredExactOnceIntegration

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}

namespace PaperPreferredAnchorCommonAllPiecesWithoutSplicing

/-- The finite sample already constructed by the stored grammar-rule builder. -/
def exactSample
    (C : PaperPreferredAnchorCommonAllPiecesWithoutSplicing
      (G := G) (obs := obs)) :
    Finset (Word α) :=
  C.builder.sample

/-- The builder's witness sample, viewed as trimmed-presentation sample data. -/
def exactSampleData
    (C : PaperPreferredAnchorCommonAllPiecesWithoutSplicing
      (G := G) (obs := obs)) :
    TrimmedPresentationSampleData C.data C.exactSample :=
  C.builder.toWitnessSample.toSampleData

/-- The concrete exact-once filling witnesses for all listed binary rules. -/
def exactFillingWitnessFamily
    (C : PaperPreferredAnchorCommonAllPiecesWithoutSplicing
      (G := G) (obs := obs))
    (hexact : G.BinaryRulesExactlyOnce) :
    BinaryFillingWitnessFamily G C.data.toReachablePreCore :=
  C.exactSampleData.exactFillingWitnessFamily hexact

/-- The corrected characteristic blueprint.  It is built from the stored
finite sample and the concrete exact-once splicing construction, with no use of
`NamedContextSplicingConstructor`. -/
def toExactReachableBlueprint
    (C : PaperPreferredAnchorCommonAllPiecesWithoutSplicing
      (G := G) (obs := obs))
    (hexact : G.BinaryRulesExactlyOnce) :
    ReachableCharacteristicBlueprint
      G C.exactSample obs C.fanoutBound :=
  C.exactSampleData.toExactReachableBlueprint hexact

/-- The corrected preferred route supplies a finite positive characteristic
sample at the stored fanout bound. -/
theorem exact_characteristic_sample
    (C : PaperPreferredAnchorCommonAllPiecesWithoutSplicing
      (G := G) (obs := obs))
    (hexact : G.BinaryRulesExactlyOnce) :
    CharacteristicSample
      (reachableHypLanguage obs C.fanoutBound)
      (reachableSampleLearner (α := α))
      C.exactSample
      G.StringLanguage :=
  C.exactSampleData.exact_characteristic_sample
    hexact C.fanout C.promise

/-- The corrected preferred route gives eventual prefix-exact reconstruction. -/
theorem exact_prefix_reconstruction
    (C : PaperPreferredAnchorCommonAllPiecesWithoutSplicing
      (G := G) (obs := obs))
    (hexact : G.BinaryRulesExactlyOnce) :
    ∀ Ttxt : TextFor G.StringLanguage,
      ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
        ReachableSampleStringLanguage
          (Ttxt.prefixSample n) obs C.fanoutBound =
          G.StringLanguage :=
  C.exactSampleData.exact_prefix_reconstruction
    hexact C.fanout C.promise

/-- The corrected preferred route gives Gold identification at the stored
fanout bound. -/
theorem exact_identifies_from_positive_text
    (C : PaperPreferredAnchorCommonAllPiecesWithoutSplicing
      (G := G) (obs := obs))
    (hexact : G.BinaryRulesExactlyOnce) :
    ∀ Ttxt : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs C.fanoutBound)
        (reachableSampleLearner (α := α))
        Ttxt :=
  C.exactSampleData.exact_identifies_from_positive_text
    hexact C.fanout C.promise

/-- Paper-facing finite positive characteristic-sample conclusion. -/
theorem exact_paper_characteristic_sample_theorem
    (C : PaperPreferredAnchorCommonAllPiecesWithoutSplicing
      (G := G) (obs := obs))
    (hexact : G.BinaryRulesExactlyOnce) :
    PaperConstructiveCharacteristicSampleConclusion G obs := by
  show ExistsBoundedPositiveCharacteristicSample G obs
  exact ⟨C.fanoutBound, C.exactSample, C.builder.sample_positive,
    C.exact_characteristic_sample hexact⟩

/-- Paper-facing eventual prefix-exact conclusion. -/
theorem exact_paper_prefix_exact_theorem
    (C : PaperPreferredAnchorCommonAllPiecesWithoutSplicing
      (G := G) (obs := obs))
    (hexact : G.BinaryRulesExactlyOnce) :
    PaperConstructivePrefixExactConclusion G obs := by
  show ExistsBoundedPrefixExactIdentification G obs
  exact ⟨C.fanoutBound, C.exact_prefix_reconstruction hexact⟩

/-- Paper-facing corrected theorem.  The impossible universal splicing premise
has disappeared; the only splicing-related premise is exact-once linearity of
the grammar's listed binary rules. -/
theorem exact_paper_main_theorem
    (C : PaperPreferredAnchorCommonAllPiecesWithoutSplicing
      (G := G) (obs := obs))
    (hexact : G.BinaryRulesExactlyOnce) :
    PaperConstructiveIdentificationConclusion G obs := by
  show ExistsBoundedReachableIdentification G obs
  exact ⟨C.fanoutBound, C.exact_identifies_from_positive_text hexact⟩

/-- Complete corrected paper-facing conclusion package. -/
theorem exact_paper_conclusion_package
    (C : PaperPreferredAnchorCommonAllPiecesWithoutSplicing
      (G := G) (obs := obs))
    (hexact : G.BinaryRulesExactlyOnce) :
    PaperConstructiveLearningConclusionPackage G obs :=
  ⟨C.exact_paper_characteristic_sample_theorem hexact,
    C.exact_paper_prefix_exact_theorem hexact,
    C.exact_paper_main_theorem hexact⟩

/-- Version using the paper's exact working-condition package. -/
theorem exact_working_paper_main_theorem
    (C : PaperPreferredAnchorCommonAllPiecesWithoutSplicing
      (G := G) (obs := obs))
    (hworking : G.ExactWorkingConditions) :
    PaperConstructiveIdentificationConclusion G obs :=
  C.exact_paper_main_theorem hworking.2

end PaperPreferredAnchorCommonAllPiecesWithoutSplicing

end PreferredExactOnceIntegration


section PreferredExactOnceTopLevel

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}

/-- Stable corrected endpoint from the previous without-splicing checklist and
exact-once linearity. -/
theorem trimmed_paper_preferred_anchor_common_exact_once_main_theorem
    (hC : ExistsPaperPreferredAnchorCommonAllPiecesWithoutSplicing G obs)
    (hexact : G.BinaryRulesExactlyOnce) :
    PaperConstructiveIdentificationConclusion G obs :=
  match hC with
  | ⟨C⟩ => C.exact_paper_main_theorem hexact

/-- Stable corrected full conclusion package. -/
theorem trimmed_paper_preferred_anchor_common_exact_once_conclusion_package
    (hC : ExistsPaperPreferredAnchorCommonAllPiecesWithoutSplicing G obs)
    (hexact : G.BinaryRulesExactlyOnce) :
    PaperConstructiveLearningConclusionPackage G obs :=
  match hC with
  | ⟨C⟩ => C.exact_paper_conclusion_package hexact

/-- Stable corrected endpoint phrased with exact working conditions. -/
theorem trimmed_paper_preferred_anchor_common_exact_working_main_theorem
    (hC : ExistsPaperPreferredAnchorCommonAllPiecesWithoutSplicing G obs)
    (hworking : G.ExactWorkingConditions) :
    PaperConstructiveIdentificationConclusion G obs :=
  trimmed_paper_preferred_anchor_common_exact_once_main_theorem
    hC hworking.2

/-- Full corrected conclusion package phrased with exact working conditions. -/
theorem trimmed_paper_preferred_anchor_common_exact_working_conclusion_package
    (hC : ExistsPaperPreferredAnchorCommonAllPiecesWithoutSplicing G obs)
    (hworking : G.ExactWorkingConditions) :
    PaperConstructiveLearningConclusionPackage G obs :=
  trimmed_paper_preferred_anchor_common_exact_once_conclusion_package
    hC hworking.2

end PreferredExactOnceTopLevel

end MCFG
