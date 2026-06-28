import LeanCfgProject.MCFG.FI_v2_1_SampleGeneratedConcatEnumerationExact

/-!
# FI v2.1 Lean experiment: Gold wrapper for terminal+concat generated grammars

This file provides the learner-like wrapper for the terminal+binary-concat
enumerated generated grammar shells.  As before, this is not yet the full
canonical reconstruction theorem; it is a concrete output-grammar generator whose
rule lists now include both singleton terminal rules and middle-concatenation
binary rules generated from the finite subword-decomposition list.
-/

namespace FIv21

universe u v w

section SampleGeneratedConcatEnumerationGold

variable {N : Type w} {α : Type u}
variable [DecidableEq α]
variable {M : Type v} [Monoid M] [Fintype M]

/-- Learner-like map from samples to terminal+concat-enumerated generated
working grammars. -/
structure SampleGeneratedConcatEnumerationLearner
    (G : WorkingMCFG N α) (obs : α → M) where
  exactPackage :
    (K : Finset (Word α)) → SampleGeneratedConcatEnumerationExact G obs K

namespace SampleGeneratedConcatEnumerationLearner

/-- Rule lists after seeing finite sample `K`. -/
noncomputable def ruleLists
    {G : WorkingMCFG N α} {obs : α → M}
    (L : SampleGeneratedConcatEnumerationLearner G obs)
    (K : Finset (Word α)) : SampleGeneratedRuleListPackage G obs K :=
  (L.exactPackage K).ruleLists

/-- Output grammar after seeing finite sample `K`. -/
noncomputable def grammar
    {G : WorkingMCFG N α} {obs : α → M}
    (L : SampleGeneratedConcatEnumerationLearner G obs)
    (K : Finset (Word α)) :
    WorkingMCFG (SampleGeneratedGrammarNonterminal
      (L.ruleLists K).ruleSkeleton.skeleton) α :=
  (L.exactPackage K).toWorkingMCFG

/-- Every output grammar is semantically well-formed. -/
theorem grammar_semanticWorkingConditions
    {G : WorkingMCFG N α} {obs : α → M}
    (L : SampleGeneratedConcatEnumerationLearner G obs)
    (K : Finset (Word α)) :
    (L.grammar K).SemanticWorkingConditions := by
  exact (L.exactPackage K).semanticWorkingConditions

end SampleGeneratedConcatEnumerationLearner

/-- Concrete terminal+concat-enumerated learner for a fixed fanout bound. -/
noncomputable def enumeratedSampleGeneratedConcatEnumerationLearner
    (G : WorkingMCFG N α) (obs : α → M)
    (f : Nat) (hfanout : 1 ≤ f) (hG : G.SemanticWorkingConditions) :
    SampleGeneratedConcatEnumerationLearner G obs :=
  { exactPackage := fun K =>
      enumeratedSampleGeneratedConcatEnumerationExact G obs K f hfanout hG }

/-- Gold-style summary for the terminal+concat-enumerated generated grammar
shell. -/
structure SampleGeneratedConcatEnumerationGoldSummary
    (G : WorkingMCFG N α) (obs : α → M) where
  learner : SampleGeneratedConcatEnumerationLearner G obs
  characteristicSample : Finset (Word α)

namespace SampleGeneratedConcatEnumerationGoldSummary

/-- Output grammar after finite sample `K`. -/
noncomputable def grammar
    {G : WorkingMCFG N α} {obs : α → M}
    (S : SampleGeneratedConcatEnumerationGoldSummary G obs)
    (K : Finset (Word α)) :
    WorkingMCFG (SampleGeneratedGrammarNonterminal
      (S.learner.ruleLists K).ruleSkeleton.skeleton) α :=
  S.learner.grammar K

/-- Output grammar is semantically well-formed. -/
theorem grammar_semanticWorkingConditions
    {G : WorkingMCFG N α} {obs : α → M}
    (S : SampleGeneratedConcatEnumerationGoldSummary G obs)
    (K : Finset (Word α)) :
    (S.grammar K).SemanticWorkingConditions := by
  exact S.learner.grammar_semanticWorkingConditions K

end SampleGeneratedConcatEnumerationGoldSummary

/-- Concrete enumerated Gold-style concat-enumeration summary. -/
noncomputable def enumeratedSampleGeneratedConcatEnumerationGoldSummary
    (G : WorkingMCFG N α) (obs : α → M)
    (f : Nat) (hfanout : 1 ≤ f) (hG : G.SemanticWorkingConditions)
    (CS : Finset (Word α)) :
    SampleGeneratedConcatEnumerationGoldSummary G obs :=
  { learner := enumeratedSampleGeneratedConcatEnumerationLearner
      G obs f hfanout hG
    characteristicSample := CS }

end SampleGeneratedConcatEnumerationGold

end FIv21
