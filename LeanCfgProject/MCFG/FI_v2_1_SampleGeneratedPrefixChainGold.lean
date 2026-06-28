import LeanCfgProject.MCFG.FI_v2_1_SampleGeneratedPrefixChainExact

/-!
# FI v2.1 Lean experiment: Gold wrapper for prefix-chain generated parses

This file provides the learner-like wrapper for the prefix-chain layer.  It is
still below the full reconstruction theorem, but it packages the generated
`WorkingMCFG` shell together with the interface that a finite prefix-chain
certificate generates its indexed word.
-/

namespace FIv21

universe u v w

section SampleGeneratedPrefixChainGold

variable {N : Type w} {α : Type u}
variable [DecidableEq α]
variable {M : Type v} [Monoid M] [Fintype M]

/-- Learner-like map from finite samples to prefix-chain exact packages. -/
structure SampleGeneratedPrefixChainLearner
    (G : WorkingMCFG N α) (obs : α → M) where
  exactPackage :
    (K : Finset (Word α)) →
      SampleGeneratedPrefixChainExact G obs K

namespace SampleGeneratedPrefixChainLearner

/-- Rule skeleton after seeing finite sample `K`. -/
def ruleSkeleton
    {G : WorkingMCFG N α} {obs : α → M}
    (L : SampleGeneratedPrefixChainLearner G obs)
    (K : Finset (Word α)) : SampleGeneratedRuleSkeleton G obs K :=
  (L.exactPackage K).ruleSkeleton

/-- Rule lists after seeing finite sample `K`. -/
noncomputable def ruleLists
    {G : WorkingMCFG N α} {obs : α → M}
    (L : SampleGeneratedPrefixChainLearner G obs)
    (K : Finset (Word α)) : SampleGeneratedRuleListPackage G obs K :=
  (L.exactPackage K).ruleLists

/-- Output grammar after seeing finite sample `K`. -/
noncomputable def grammar
    {G : WorkingMCFG N α} {obs : α → M}
    (L : SampleGeneratedPrefixChainLearner G obs)
    (K : Finset (Word α)) :
    WorkingMCFG (SampleGeneratedGrammarNonterminal
      (L.ruleLists K).ruleSkeleton.skeleton) α :=
  (L.exactPackage K).toWorkingMCFG

/-- Every output grammar is semantically well-formed. -/
theorem grammar_semanticWorkingConditions
    {G : WorkingMCFG N α} {obs : α → M}
    (L : SampleGeneratedPrefixChainLearner G obs)
    (K : Finset (Word α)) :
    (L.grammar K).SemanticWorkingConditions := by
  exact (L.exactPackage K).semanticWorkingConditions

/-- A word prefix-chain for sample `K` generates the indexed word in the
learner's output grammar for `K`. -/
theorem wordPrefixChain_mem_stringLanguage
    {G : WorkingMCFG N α} {obs : α → M}
    (L : SampleGeneratedPrefixChainLearner G obs)
    (K : Finset (Word α)) {w : Word α}
    (P : SampleGeneratedPrefixChain
      (M := M) (L.ruleSkeleton K) w) :
    w ∈ (L.grammar K).StringLanguage := by
  exact (L.exactPackage K).wordPrefixChain_mem_stringLanguage (M := M) P

end SampleGeneratedPrefixChainLearner

/-- Concrete prefix-chain learner for a fixed fanout bound. -/
noncomputable def enumeratedSampleGeneratedPrefixChainLearner
    (G : WorkingMCFG N α) (obs : α → M)
    (f : Nat) (hfanout : 1 ≤ f) (hG : G.SemanticWorkingConditions) :
    SampleGeneratedPrefixChainLearner G obs :=
  { exactPackage := fun K =>
      enumeratedSampleGeneratedPrefixChainExact G obs K f hfanout hG }

/-- Gold-style summary for prefix-chain generated grammar shells. -/
structure SampleGeneratedPrefixChainGoldSummary
    (G : WorkingMCFG N α) (obs : α → M) where
  learner : SampleGeneratedPrefixChainLearner G obs
  characteristicSample : Finset (Word α)

namespace SampleGeneratedPrefixChainGoldSummary

/-- Output grammar after finite sample `K`. -/
noncomputable def grammar
    {G : WorkingMCFG N α} {obs : α → M}
    (S : SampleGeneratedPrefixChainGoldSummary G obs)
    (K : Finset (Word α)) :
    WorkingMCFG (SampleGeneratedGrammarNonterminal
      (S.learner.ruleLists K).ruleSkeleton.skeleton) α :=
  S.learner.grammar K

/-- Output grammar is semantically well-formed. -/
theorem grammar_semanticWorkingConditions
    {G : WorkingMCFG N α} {obs : α → M}
    (S : SampleGeneratedPrefixChainGoldSummary G obs)
    (K : Finset (Word α)) :
    (S.grammar K).SemanticWorkingConditions := by
  exact S.learner.grammar_semanticWorkingConditions K

/-- A word prefix-chain for sample `K` gives membership in the summary's output
grammar. -/
theorem wordPrefixChain_mem_stringLanguage
    {G : WorkingMCFG N α} {obs : α → M}
    (S : SampleGeneratedPrefixChainGoldSummary G obs)
    (K : Finset (Word α)) {w : Word α}
    (P : SampleGeneratedPrefixChain
      (M := M) (S.learner.ruleSkeleton K) w) :
    w ∈ (S.grammar K).StringLanguage := by
  exact S.learner.wordPrefixChain_mem_stringLanguage (M := M) K P

end SampleGeneratedPrefixChainGoldSummary

/-- Concrete enumerated Gold-style prefix-chain summary. -/
noncomputable def enumeratedSampleGeneratedPrefixChainGoldSummary
    (G : WorkingMCFG N α) (obs : α → M)
    (f : Nat) (hfanout : 1 ≤ f) (hG : G.SemanticWorkingConditions)
    (CS : Finset (Word α)) :
    SampleGeneratedPrefixChainGoldSummary G obs :=
  { learner := enumeratedSampleGeneratedPrefixChainLearner
      G obs f hfanout hG
    characteristicSample := CS }

end SampleGeneratedPrefixChainGold

end FIv21
