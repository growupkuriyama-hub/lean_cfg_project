import LeanCfgProject.MCFG.FI_v2_1_SampleGeneratedLinearParseConstructionExact

/-!
# FI v2.1 Lean experiment: Gold wrapper for constructed left-linear parses

This file provides the learner-like wrapper for the word-indexed linear parse
construction layer.  It is still below the final reconstruction theorem, but it
packages the generated `WorkingMCFG` shell together with the interface that a
constructed prefix-chain parse generates its indexed word.
-/

namespace FIv21

universe u v w

section SampleGeneratedLinearParseConstructionGold

variable {N : Type w} {α : Type u}
variable [DecidableEq α]
variable {M : Type v} [Monoid M] [Fintype M]

/-- Learner-like map from finite samples to constructed-linear-parse exact
packages. -/
structure SampleGeneratedLinearParseConstructionLearner
    (G : WorkingMCFG N α) (obs : α → M) where
  exactPackage :
    (K : Finset (Word α)) →
      SampleGeneratedLinearParseConstructionExact G obs K

namespace SampleGeneratedLinearParseConstructionLearner

/-- Rule skeleton after seeing finite sample `K`. -/
def ruleSkeleton
    {G : WorkingMCFG N α} {obs : α → M}
    (L : SampleGeneratedLinearParseConstructionLearner G obs)
    (K : Finset (Word α)) : SampleGeneratedRuleSkeleton G obs K :=
  (L.exactPackage K).ruleSkeleton

/-- Rule lists after seeing finite sample `K`. -/
noncomputable def ruleLists
    {G : WorkingMCFG N α} {obs : α → M}
    (L : SampleGeneratedLinearParseConstructionLearner G obs)
    (K : Finset (Word α)) : SampleGeneratedRuleListPackage G obs K :=
  (L.exactPackage K).ruleLists

/-- Output grammar after seeing finite sample `K`. -/
noncomputable def grammar
    {G : WorkingMCFG N α} {obs : α → M}
    (L : SampleGeneratedLinearParseConstructionLearner G obs)
    (K : Finset (Word α)) :
    WorkingMCFG (SampleGeneratedGrammarNonterminal
      (L.ruleLists K).ruleSkeleton.skeleton) α :=
  (L.exactPackage K).toWorkingMCFG

/-- Every output grammar is semantically well-formed. -/
theorem grammar_semanticWorkingConditions
    {G : WorkingMCFG N α} {obs : α → M}
    (L : SampleGeneratedLinearParseConstructionLearner G obs)
    (K : Finset (Word α)) :
    (L.grammar K).SemanticWorkingConditions := by
  exact (L.exactPackage K).semanticWorkingConditions

/-- A constructed word parse for sample `K` generates the indexed word in the
learner's output grammar for `K`. -/
theorem constructed_word_mem_stringLanguage
    {G : WorkingMCFG N α} {obs : α → M}
    (L : SampleGeneratedLinearParseConstructionLearner G obs)
    (K : Finset (Word α)) {w : Word α}
    (P : SampleGeneratedWordLinearParseConstruction
      (M := M) (L.ruleSkeleton K) w) :
    w ∈ (L.grammar K).StringLanguage := by
  exact (L.exactPackage K).word_mem_stringLanguage (M := M) P

end SampleGeneratedLinearParseConstructionLearner

/-- Concrete constructed-linear-parse learner for a fixed fanout bound. -/
noncomputable def enumeratedSampleGeneratedLinearParseConstructionLearner
    (G : WorkingMCFG N α) (obs : α → M)
    (f : Nat) (hfanout : 1 ≤ f) (hG : G.SemanticWorkingConditions) :
    SampleGeneratedLinearParseConstructionLearner G obs :=
  { exactPackage := fun K =>
      enumeratedSampleGeneratedLinearParseConstructionExact G obs K f hfanout hG }

/-- Gold-style summary for constructed left-linear generated grammar shells. -/
structure SampleGeneratedLinearParseConstructionGoldSummary
    (G : WorkingMCFG N α) (obs : α → M) where
  learner : SampleGeneratedLinearParseConstructionLearner G obs
  characteristicSample : Finset (Word α)

namespace SampleGeneratedLinearParseConstructionGoldSummary

/-- Output grammar after finite sample `K`. -/
noncomputable def grammar
    {G : WorkingMCFG N α} {obs : α → M}
    (S : SampleGeneratedLinearParseConstructionGoldSummary G obs)
    (K : Finset (Word α)) :
    WorkingMCFG (SampleGeneratedGrammarNonterminal
      (S.learner.ruleLists K).ruleSkeleton.skeleton) α :=
  S.learner.grammar K

/-- Output grammar is semantically well-formed. -/
theorem grammar_semanticWorkingConditions
    {G : WorkingMCFG N α} {obs : α → M}
    (S : SampleGeneratedLinearParseConstructionGoldSummary G obs)
    (K : Finset (Word α)) :
    (S.grammar K).SemanticWorkingConditions := by
  exact S.learner.grammar_semanticWorkingConditions K

/-- A constructed word parse for sample `K` gives membership in the summary's
output grammar. -/
theorem constructed_word_mem_stringLanguage
    {G : WorkingMCFG N α} {obs : α → M}
    (S : SampleGeneratedLinearParseConstructionGoldSummary G obs)
    (K : Finset (Word α)) {w : Word α}
    (P : SampleGeneratedWordLinearParseConstruction
      (M := M) (S.learner.ruleSkeleton K) w) :
    w ∈ (S.grammar K).StringLanguage := by
  exact S.learner.constructed_word_mem_stringLanguage (M := M) K P

end SampleGeneratedLinearParseConstructionGoldSummary

/-- Concrete enumerated Gold-style constructed-linear-parse summary. -/
noncomputable def enumeratedSampleGeneratedLinearParseConstructionGoldSummary
    (G : WorkingMCFG N α) (obs : α → M)
    (f : Nat) (hfanout : 1 ≤ f) (hG : G.SemanticWorkingConditions)
    (CS : Finset (Word α)) :
    SampleGeneratedLinearParseConstructionGoldSummary G obs :=
  { learner := enumeratedSampleGeneratedLinearParseConstructionLearner
      G obs f hfanout hG
    characteristicSample := CS }

end SampleGeneratedLinearParseConstructionGold

end FIv21
