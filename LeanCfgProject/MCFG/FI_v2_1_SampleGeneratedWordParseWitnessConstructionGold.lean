import LeanCfgProject.MCFG.FI_v2_1_SampleGeneratedWordParseWitnessConstructionExact

/-!
# FI v2.1 Lean experiment: Gold wrapper for word-parse witness construction

This file supplies the learner-like wrapper for the constructor layer: a learner
returns the generated grammar shell together with the constructor interface that
turns prefix-node enumerations for sample words into sample inclusion in the
output grammar.
-/

namespace FIv21

universe u v w

section SampleGeneratedWordParseWitnessConstructionGold

variable {N : Type w} {α : Type u}
variable [DecidableEq α]
variable {M : Type v} [Monoid M] [Fintype M]

/-- Learner-like map from finite samples to word-parse-construction exact
packages. -/
structure SampleGeneratedWordParseWitnessConstructionLearner
    (G : WorkingMCFG N α) (obs : α → M) where
  exactPackage :
    (K : Finset (Word α)) →
      SampleGeneratedWordParseWitnessConstructionExact G obs K

namespace SampleGeneratedWordParseWitnessConstructionLearner

/-- Rule skeleton after seeing finite sample `K`. -/
def ruleSkeleton
    {G : WorkingMCFG N α} {obs : α → M}
    (L : SampleGeneratedWordParseWitnessConstructionLearner G obs)
    (K : Finset (Word α)) : SampleGeneratedRuleSkeleton G obs K :=
  (L.exactPackage K).ruleSkeleton

/-- Rule lists after seeing finite sample `K`. -/
noncomputable def ruleLists
    {G : WorkingMCFG N α} {obs : α → M}
    (L : SampleGeneratedWordParseWitnessConstructionLearner G obs)
    (K : Finset (Word α)) : SampleGeneratedRuleListPackage G obs K :=
  (L.exactPackage K).ruleLists

/-- Output grammar after seeing finite sample `K`. -/
noncomputable def grammar
    {G : WorkingMCFG N α} {obs : α → M}
    (L : SampleGeneratedWordParseWitnessConstructionLearner G obs)
    (K : Finset (Word α)) :
    WorkingMCFG (SampleGeneratedGrammarNonterminal
      (L.ruleLists K).ruleSkeleton.skeleton) α :=
  (L.exactPackage K).toWorkingMCFG

/-- Output grammar is semantically well-formed. -/
theorem grammar_semanticWorkingConditions
    {G : WorkingMCFG N α} {obs : α → M}
    (L : SampleGeneratedWordParseWitnessConstructionLearner G obs)
    (K : Finset (Word α)) :
    (L.grammar K).SemanticWorkingConditions := by
  exact (L.exactPackage K).semanticWorkingConditions

/-- A word-construction witness gives membership in the learner's output grammar. -/
theorem wordConstruction_mem_stringLanguage
    {G : WorkingMCFG N α} {obs : α → M}
    (L : SampleGeneratedWordParseWitnessConstructionLearner G obs)
    (K : Finset (Word α)) {w : Word α}
    (C : SampleGeneratedWordParseWitnessConstruction (M := M) (L.ruleSkeleton K) w) :
    w ∈ (L.grammar K).StringLanguage := by
  exact (L.exactPackage K).wordConstruction_mem_stringLanguage (M := M) C

/-- A sample-level construction gives sample inclusion in the learner's output
grammar. -/
theorem sampleConstruction_subset_stringLanguage
    {G : WorkingMCFG N α} {obs : α → M}
    (L : SampleGeneratedWordParseWitnessConstructionLearner G obs)
    (K : Finset (Word α))
    (C : SampleGeneratedSampleParseWitnessConstruction (M := M) (L.ruleSkeleton K)) :
    ∀ w : Word α, w ∈ K → w ∈ (L.grammar K).StringLanguage := by
  exact (L.exactPackage K).sampleConstruction_subset_stringLanguage (M := M) C

end SampleGeneratedWordParseWitnessConstructionLearner

/-- Concrete constructor learner for a fixed fanout bound. -/
noncomputable def enumeratedSampleGeneratedWordParseWitnessConstructionLearner
    (G : WorkingMCFG N α) (obs : α → M)
    (f : Nat) (hfanout : 1 ≤ f) (hG : G.SemanticWorkingConditions) :
    SampleGeneratedWordParseWitnessConstructionLearner G obs :=
  { exactPackage := fun K =>
      enumeratedSampleGeneratedWordParseWitnessConstructionExact G obs K f hfanout hG }

/-- Gold-style summary for word-parse witness construction. -/
structure SampleGeneratedWordParseWitnessConstructionGoldSummary
    (G : WorkingMCFG N α) (obs : α → M) where
  learner : SampleGeneratedWordParseWitnessConstructionLearner G obs
  characteristicSample : Finset (Word α)

namespace SampleGeneratedWordParseWitnessConstructionGoldSummary

/-- Output grammar after finite sample `K`. -/
noncomputable def grammar
    {G : WorkingMCFG N α} {obs : α → M}
    (S : SampleGeneratedWordParseWitnessConstructionGoldSummary G obs)
    (K : Finset (Word α)) :
    WorkingMCFG (SampleGeneratedGrammarNonterminal
      (S.learner.ruleLists K).ruleSkeleton.skeleton) α :=
  S.learner.grammar K

/-- Output grammar is semantically well-formed. -/
theorem grammar_semanticWorkingConditions
    {G : WorkingMCFG N α} {obs : α → M}
    (S : SampleGeneratedWordParseWitnessConstructionGoldSummary G obs)
    (K : Finset (Word α)) :
    (S.grammar K).SemanticWorkingConditions := by
  exact S.learner.grammar_semanticWorkingConditions K

/-- A word-construction witness gives membership in the summary's output grammar. -/
theorem wordConstruction_mem_stringLanguage
    {G : WorkingMCFG N α} {obs : α → M}
    (S : SampleGeneratedWordParseWitnessConstructionGoldSummary G obs)
    (K : Finset (Word α)) {w : Word α}
    (C : SampleGeneratedWordParseWitnessConstruction (M := M)
      (S.learner.ruleSkeleton K) w) :
    w ∈ (S.grammar K).StringLanguage := by
  exact S.learner.wordConstruction_mem_stringLanguage (M := M) K C

/-- Sample-level construction gives sample inclusion in the summary's output
grammar. -/
theorem sampleConstruction_subset_stringLanguage
    {G : WorkingMCFG N α} {obs : α → M}
    (S : SampleGeneratedWordParseWitnessConstructionGoldSummary G obs)
    (K : Finset (Word α))
    (C : SampleGeneratedSampleParseWitnessConstruction (M := M)
      (S.learner.ruleSkeleton K)) :
    ∀ w : Word α, w ∈ K → w ∈ (S.grammar K).StringLanguage := by
  exact S.learner.sampleConstruction_subset_stringLanguage (M := M) K C

end SampleGeneratedWordParseWitnessConstructionGoldSummary

/-- Concrete enumerated Gold-style constructor summary. -/
noncomputable def enumeratedSampleGeneratedWordParseWitnessConstructionGoldSummary
    (G : WorkingMCFG N α) (obs : α → M)
    (f : Nat) (hfanout : 1 ≤ f) (hG : G.SemanticWorkingConditions)
    (CS : Finset (Word α)) :
    SampleGeneratedWordParseWitnessConstructionGoldSummary G obs :=
  { learner := enumeratedSampleGeneratedWordParseWitnessConstructionLearner
      G obs f hfanout hG
    characteristicSample := CS }

end SampleGeneratedWordParseWitnessConstructionGold

end FIv21
