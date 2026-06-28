import LeanCfgProject.MCFG.FI_v2_1_SampleGeneratedLinearParseExact

/-!
# FI v2.1 Lean experiment: Gold wrapper for left-linear generated parses

This file provides the learner-like wrapper for the left-linear parse layer.
The layer is below the final reconstruction theorem, but it is now a genuine
sample-indexed generated `WorkingMCFG` shell equipped with a left-to-right parse
certificate interface.
-/

namespace FIv21

universe u v w

section SampleGeneratedLinearParseGold

variable {N : Type w} {α : Type u}
variable [DecidableEq α]
variable {M : Type v} [Monoid M] [Fintype M]

/-- Learner-like map from finite samples to left-linear parse exact packages. -/
structure SampleGeneratedLinearParseLearner
    (G : WorkingMCFG N α) (obs : α → M) where
  exactPackage :
    (K : Finset (Word α)) → SampleGeneratedLinearParseExact G obs K

namespace SampleGeneratedLinearParseLearner

/-- Rule lists after seeing finite sample `K`. -/
noncomputable def ruleLists
    {G : WorkingMCFG N α} {obs : α → M}
    (L : SampleGeneratedLinearParseLearner G obs)
    (K : Finset (Word α)) : SampleGeneratedRuleListPackage G obs K :=
  (L.exactPackage K).ruleLists

/-- Output grammar after seeing finite sample `K`. -/
noncomputable def grammar
    {G : WorkingMCFG N α} {obs : α → M}
    (L : SampleGeneratedLinearParseLearner G obs)
    (K : Finset (Word α)) :
    WorkingMCFG (SampleGeneratedGrammarNonterminal
      (L.ruleLists K).ruleSkeleton.skeleton) α :=
  (L.exactPackage K).toWorkingMCFG

/-- Every output grammar is semantically well-formed. -/
theorem grammar_semanticWorkingConditions
    {G : WorkingMCFG N α} {obs : α → M}
    (L : SampleGeneratedLinearParseLearner G obs)
    (K : Finset (Word α)) :
    (L.grammar K).SemanticWorkingConditions := by
  exact (L.exactPackage K).semanticWorkingConditions

end SampleGeneratedLinearParseLearner

/-- Concrete left-linear parse learner for a fixed fanout bound. -/
noncomputable def enumeratedSampleGeneratedLinearParseLearner
    (G : WorkingMCFG N α) (obs : α → M)
    (f : Nat) (hfanout : 1 ≤ f) (hG : G.SemanticWorkingConditions) :
    SampleGeneratedLinearParseLearner G obs :=
  { exactPackage := fun K =>
      enumeratedSampleGeneratedLinearParseExact G obs K f hfanout hG }

/-- Gold-style summary for left-linear generated grammar shells. -/
structure SampleGeneratedLinearParseGoldSummary
    (G : WorkingMCFG N α) (obs : α → M) where
  learner : SampleGeneratedLinearParseLearner G obs
  characteristicSample : Finset (Word α)

namespace SampleGeneratedLinearParseGoldSummary

/-- Output grammar after finite sample `K`. -/
noncomputable def grammar
    {G : WorkingMCFG N α} {obs : α → M}
    (S : SampleGeneratedLinearParseGoldSummary G obs)
    (K : Finset (Word α)) :
    WorkingMCFG (SampleGeneratedGrammarNonterminal
      (S.learner.ruleLists K).ruleSkeleton.skeleton) α :=
  S.learner.grammar K

/-- Output grammar is semantically well-formed. -/
theorem grammar_semanticWorkingConditions
    {G : WorkingMCFG N α} {obs : α → M}
    (S : SampleGeneratedLinearParseGoldSummary G obs)
    (K : Finset (Word α)) :
    (S.grammar K).SemanticWorkingConditions := by
  exact S.learner.grammar_semanticWorkingConditions K

end SampleGeneratedLinearParseGoldSummary

/-- Concrete enumerated Gold-style left-linear parse summary. -/
noncomputable def enumeratedSampleGeneratedLinearParseGoldSummary
    (G : WorkingMCFG N α) (obs : α → M)
    (f : Nat) (hfanout : 1 ≤ f) (hG : G.SemanticWorkingConditions)
    (CS : Finset (Word α)) :
    SampleGeneratedLinearParseGoldSummary G obs :=
  { learner := enumeratedSampleGeneratedLinearParseLearner
      G obs f hfanout hG
    characteristicSample := CS }

end SampleGeneratedLinearParseGold

end FIv21
