import LeanCfgProject.MCFG.FI_v2_1_SampleGeneratedPackageToSemanticsExact

/-!
# FI v2.1 Lean experiment: Gold wrapper for the semantics bridge

This layer gives a learner-like interface for the bridge from generated sample
consistency packages to canonical learner grammar packages.  For every finite
sample, the learner returns both the generated grammar shell and a canonical
package whose learner-side word language is the generated shell's string
language.
-/

namespace FIv21

universe u v w

section SampleGeneratedPackageToSemanticsGold

variable {N : Type w} {α : Type u}
variable [DecidableEq α]
variable {M : Type v} [Monoid M] [Fintype M]

/-- Learner-like map from finite samples to exact sample-generated semantics
bridges. -/
structure SampleGeneratedPackageSemanticsBridgeLearner
    (G : WorkingMCFG N α) (obs : α → M) where
  exactBridge :
    (K : Finset (Word α)) → SampleGeneratedPackageSemanticsBridgeExact G obs K

namespace SampleGeneratedPackageSemanticsBridgeLearner

/-- Bridge at sample `K`. -/
def bridge
    {G : WorkingMCFG N α} {obs : α → M}
    (L : SampleGeneratedPackageSemanticsBridgeLearner G obs)
    (K : Finset (Word α)) :
    SampleGeneratedPackageSemanticsBridge G obs K :=
  (L.exactBridge K).bridge

/-- Generated consistency package at sample `K`. -/
def package
    {G : WorkingMCFG N α} {obs : α → M}
    (L : SampleGeneratedPackageSemanticsBridgeLearner G obs)
    (K : Finset (Word α)) :
    SampleGeneratedConsistencyPackage G obs K :=
  (L.exactBridge K).package

/-- Generated rule-list package at sample `K`. -/
noncomputable def ruleLists
    {G : WorkingMCFG N α} {obs : α → M}
    (L : SampleGeneratedPackageSemanticsBridgeLearner G obs)
    (K : Finset (Word α)) :
    SampleGeneratedRuleListPackage G obs K :=
  (L.exactBridge K).ruleLists

/-- Generated working grammar shell at sample `K`. -/
noncomputable def grammar
    {G : WorkingMCFG N α} {obs : α → M}
    (L : SampleGeneratedPackageSemanticsBridgeLearner G obs)
    (K : Finset (Word α)) :
    WorkingMCFG (SampleGeneratedGrammarNonterminal
      (L.ruleLists K).ruleSkeleton.skeleton) α :=
  (L.exactBridge K).grammar

/-- Generated learner-side word language at sample `K`. -/
noncomputable def wordLanguage
    {G : WorkingMCFG N α} {obs : α → M}
    (L : SampleGeneratedPackageSemanticsBridgeLearner G obs)
    (K : Finset (Word α)) : Set (Word α) :=
  (L.exactBridge K).wordLanguage

/-- Canonical learner package at sample `K`. -/
noncomputable def canonicalPackage
    {G : WorkingMCFG N α} {obs : α → M}
    (L : SampleGeneratedPackageSemanticsBridgeLearner G obs)
    (K : Finset (Word α)) :
    CanonicalLearnerGrammarPackage G obs K :=
  (L.exactBridge K).toCanonicalLearnerGrammarPackage

/-- The generated grammar shell is semantically well-formed. -/
theorem grammar_semanticWorkingConditions
    {G : WorkingMCFG N α} {obs : α → M}
    (L : SampleGeneratedPackageSemanticsBridgeLearner G obs)
    (K : Finset (Word α)) :
    (L.grammar K).SemanticWorkingConditions := by
  exact (L.exactBridge K).grammar_semanticWorkingConditions

/-- Each output language contains its input finite sample. -/
theorem positiveForWordLanguage
    {G : WorkingMCFG N α} {obs : α → M}
    (L : SampleGeneratedPackageSemanticsBridgeLearner G obs)
    (K : Finset (Word α)) :
    PositiveForLanguage K (L.wordLanguage K) := by
  exact (L.exactBridge K).positiveForWordLanguage

/-- Pointwise sample generation. -/
theorem sample_word_generated
    {G : WorkingMCFG N α} {obs : α → M}
    (L : SampleGeneratedPackageSemanticsBridgeLearner G obs)
    (K : Finset (Word α)) {x : Word α} (hx : x ∈ K) :
    x ∈ L.wordLanguage K := by
  exact (L.exactBridge K).sample_word_generated hx

/-- Pointwise sample generation through the canonical package view. -/
theorem canonicalPackage_sample_word_generated
    {G : WorkingMCFG N α} {obs : α → M}
    (L : SampleGeneratedPackageSemanticsBridgeLearner G obs)
    (K : Finset (Word α)) {x : Word α} (hx : x ∈ K) :
    x ∈ (L.canonicalPackage K).wordLanguage := by
  exact (L.canonicalPackage K).sample_word_generated x hx

end SampleGeneratedPackageSemanticsBridgeLearner

/-- Gold-style summary for the sample-generated semantics bridge. -/
structure SampleGeneratedPackageSemanticsBridgeGoldSummary
    (G : WorkingMCFG N α) (obs : α → M) where
  learner : SampleGeneratedPackageSemanticsBridgeLearner G obs
  characteristicSample : Finset (Word α)

namespace SampleGeneratedPackageSemanticsBridgeGoldSummary

/-- Canonical package at sample `K`. -/
noncomputable def canonicalPackage
    {G : WorkingMCFG N α} {obs : α → M}
    (S : SampleGeneratedPackageSemanticsBridgeGoldSummary G obs)
    (K : Finset (Word α)) :
    CanonicalLearnerGrammarPackage G obs K :=
  S.learner.canonicalPackage K

/-- Generated word language at sample `K`. -/
noncomputable def wordLanguage
    {G : WorkingMCFG N α} {obs : α → M}
    (S : SampleGeneratedPackageSemanticsBridgeGoldSummary G obs)
    (K : Finset (Word α)) : Set (Word α) :=
  S.learner.wordLanguage K

/-- Each finite sample is positive for the generated word language. -/
theorem positiveForWordLanguage
    {G : WorkingMCFG N α} {obs : α → M}
    (S : SampleGeneratedPackageSemanticsBridgeGoldSummary G obs)
    (K : Finset (Word α)) :
    PositiveForLanguage K (S.wordLanguage K) := by
  exact S.learner.positiveForWordLanguage K

/-- Pointwise sample generation through the canonical package view. -/
theorem canonicalPackage_sample_word_generated
    {G : WorkingMCFG N α} {obs : α → M}
    (S : SampleGeneratedPackageSemanticsBridgeGoldSummary G obs)
    (K : Finset (Word α)) {x : Word α} (hx : x ∈ K) :
    x ∈ (S.canonicalPackage K).wordLanguage := by
  exact S.learner.canonicalPackage_sample_word_generated K hx

end SampleGeneratedPackageSemanticsBridgeGoldSummary

/-- Build a bridge learner from exact bridge packages. -/
def SampleGeneratedPackageSemanticsBridgeLearner.ofExactBridges
    {G : WorkingMCFG N α} {obs : α → M}
    (E : (K : Finset (Word α)) →
      SampleGeneratedPackageSemanticsBridgeExact G obs K) :
    SampleGeneratedPackageSemanticsBridgeLearner G obs :=
  { exactBridge := E }

/-- Build a bridge learner from the previous generated consistency-package
learner. -/
def SampleGeneratedPackageSemanticsBridgeLearner.ofConsistencyPackageLearner
    {G : WorkingMCFG N α} {obs : α → M}
    (L : SampleGeneratedConsistencyPackageLearner G obs) :
    SampleGeneratedPackageSemanticsBridgeLearner G obs :=
  { exactBridge := fun K =>
      SampleGeneratedPackageSemanticsBridgeExact.ofConsistencyPackageExact
        (L.exactPackage K) }

end SampleGeneratedPackageToSemanticsGold

end FIv21
