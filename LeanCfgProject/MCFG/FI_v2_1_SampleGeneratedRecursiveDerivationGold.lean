import LeanCfgProject.MCFG.FI_v2_1_SampleGeneratedRecursiveDerivationExact

/-!
# FI v2.1 Lean experiment: Gold wrapper for recursive generated derivations

This file gives the learner-like wrapper for the recursively certified
terminal+concat generated grammar shells.  This remains below the full canonical
reconstruction theorem, but it is now a genuine generated `WorkingMCFG` shell
with recursive parse-tree certificates that imply membership in its string
language.
-/

namespace FIv21

universe u v w

section SampleGeneratedRecursiveDerivationGold

variable {N : Type w} {α : Type u}
variable [DecidableEq α]
variable {M : Type v} [Monoid M] [Fintype M]

/-- Learner-like map from finite samples to recursive-derivation exact packages. -/
structure SampleGeneratedRecursiveDerivationLearner
    (G : WorkingMCFG N α) (obs : α → M) where
  exactPackage :
    (K : Finset (Word α)) → SampleGeneratedRecursiveDerivationExact G obs K

namespace SampleGeneratedRecursiveDerivationLearner

/-- Rule lists after seeing finite sample `K`. -/
noncomputable def ruleLists
    {G : WorkingMCFG N α} {obs : α → M}
    (L : SampleGeneratedRecursiveDerivationLearner G obs)
    (K : Finset (Word α)) : SampleGeneratedRuleListPackage G obs K :=
  (L.exactPackage K).ruleLists

/-- Output grammar after seeing finite sample `K`. -/
noncomputable def grammar
    {G : WorkingMCFG N α} {obs : α → M}
    (L : SampleGeneratedRecursiveDerivationLearner G obs)
    (K : Finset (Word α)) :
    WorkingMCFG (SampleGeneratedGrammarNonterminal
      (L.ruleLists K).ruleSkeleton.skeleton) α :=
  (L.exactPackage K).toWorkingMCFG

/-- Every output grammar is semantically well-formed. -/
theorem grammar_semanticWorkingConditions
    {G : WorkingMCFG N α} {obs : α → M}
    (L : SampleGeneratedRecursiveDerivationLearner G obs)
    (K : Finset (Word α)) :
    (L.grammar K).SemanticWorkingConditions := by
  exact (L.exactPackage K).semanticWorkingConditions

end SampleGeneratedRecursiveDerivationLearner

/-- Concrete recursive-derivation learner for a fixed fanout bound. -/
noncomputable def enumeratedSampleGeneratedRecursiveDerivationLearner
    (G : WorkingMCFG N α) (obs : α → M)
    (f : Nat) (hfanout : 1 ≤ f) (hG : G.SemanticWorkingConditions) :
    SampleGeneratedRecursiveDerivationLearner G obs :=
  { exactPackage := fun K =>
      enumeratedSampleGeneratedRecursiveDerivationExact G obs K f hfanout hG }

/-- Gold-style summary for recursive generated grammar shells. -/
structure SampleGeneratedRecursiveDerivationGoldSummary
    (G : WorkingMCFG N α) (obs : α → M) where
  learner : SampleGeneratedRecursiveDerivationLearner G obs
  characteristicSample : Finset (Word α)

namespace SampleGeneratedRecursiveDerivationGoldSummary

/-- Output grammar after finite sample `K`. -/
noncomputable def grammar
    {G : WorkingMCFG N α} {obs : α → M}
    (S : SampleGeneratedRecursiveDerivationGoldSummary G obs)
    (K : Finset (Word α)) :
    WorkingMCFG (SampleGeneratedGrammarNonterminal
      (S.learner.ruleLists K).ruleSkeleton.skeleton) α :=
  S.learner.grammar K

/-- Output grammar is semantically well-formed. -/
theorem grammar_semanticWorkingConditions
    {G : WorkingMCFG N α} {obs : α → M}
    (S : SampleGeneratedRecursiveDerivationGoldSummary G obs)
    (K : Finset (Word α)) :
    (S.grammar K).SemanticWorkingConditions := by
  exact S.learner.grammar_semanticWorkingConditions K

end SampleGeneratedRecursiveDerivationGoldSummary

/-- Concrete enumerated Gold-style recursive-derivation summary. -/
noncomputable def enumeratedSampleGeneratedRecursiveDerivationGoldSummary
    (G : WorkingMCFG N α) (obs : α → M)
    (f : Nat) (hfanout : 1 ≤ f) (hG : G.SemanticWorkingConditions)
    (CS : Finset (Word α)) :
    SampleGeneratedRecursiveDerivationGoldSummary G obs :=
  { learner := enumeratedSampleGeneratedRecursiveDerivationLearner
      G obs f hfanout hG
    characteristicSample := CS }

end SampleGeneratedRecursiveDerivationGold

end FIv21
