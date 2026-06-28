import LeanCfgProject.MCFG.FI_v2_1_SampleGeneratedWordParseWitnessExact

/-!
# FI v2.1 Lean experiment: Gold wrapper for word-level parse witnesses

This file provides the learner-like wrapper for word-level parse witnesses.  A
future automatic parse-witness constructor can plug into this layer to obtain
sample inclusion in the generated terminal+concat grammar for every finite
sample.
-/

namespace FIv21

universe u v w

section SampleGeneratedWordParseWitnessGold

variable {N : Type w} {α : Type u}
variable [DecidableEq α]
variable {M : Type v} [Monoid M] [Fintype M]

/-- Learner-like map from finite samples to word-parse exact packages. -/
structure SampleGeneratedWordParseWitnessLearner
    (G : WorkingMCFG N α) (obs : α → M) where
  exactPackage :
    (K : Finset (Word α)) →
      SampleGeneratedWordParseWitnessExact G obs K

namespace SampleGeneratedWordParseWitnessLearner

/-- Rule skeleton after seeing finite sample `K`. -/
def ruleSkeleton
    {G : WorkingMCFG N α} {obs : α → M}
    (L : SampleGeneratedWordParseWitnessLearner G obs)
    (K : Finset (Word α)) : SampleGeneratedRuleSkeleton G obs K :=
  (L.exactPackage K).ruleSkeleton

/-- Rule lists after seeing finite sample `K`. -/
noncomputable def ruleLists
    {G : WorkingMCFG N α} {obs : α → M}
    (L : SampleGeneratedWordParseWitnessLearner G obs)
    (K : Finset (Word α)) : SampleGeneratedRuleListPackage G obs K :=
  (L.exactPackage K).ruleLists

/-- Output grammar after seeing finite sample `K`. -/
noncomputable def grammar
    {G : WorkingMCFG N α} {obs : α → M}
    (L : SampleGeneratedWordParseWitnessLearner G obs)
    (K : Finset (Word α)) :
    WorkingMCFG (SampleGeneratedGrammarNonterminal
      (L.ruleLists K).ruleSkeleton.skeleton) α :=
  (L.exactPackage K).toWorkingMCFG

/-- Every output grammar is semantically well-formed. -/
theorem grammar_semanticWorkingConditions
    {G : WorkingMCFG N α} {obs : α → M}
    (L : SampleGeneratedWordParseWitnessLearner G obs)
    (K : Finset (Word α)) :
    (L.grammar K).SemanticWorkingConditions := by
  exact (L.exactPackage K).semanticWorkingConditions

/-- A word-level parse witness gives membership in the learner's output grammar
for the same finite sample. -/
theorem wordWitness_mem_stringLanguage
    {G : WorkingMCFG N α} {obs : α → M}
    (L : SampleGeneratedWordParseWitnessLearner G obs)
    (K : Finset (Word α)) {w : Word α}
    (W : SampleGeneratedWordParseWitness (M := M) (L.ruleSkeleton K) w) :
    w ∈ (L.grammar K).StringLanguage := by
  exact (L.exactPackage K).wordWitness_mem_stringLanguage (M := M) W

/-- Sample-level parse witnesses imply sample inclusion in the learner's output
grammar. -/
theorem sampleWitnesses_subset_stringLanguage
    {G : WorkingMCFG N α} {obs : α → M}
    (L : SampleGeneratedWordParseWitnessLearner G obs)
    (K : Finset (Word α))
    (P : SampleGeneratedSampleParseWitnesses (M := M) (L.ruleSkeleton K)) :
    ∀ w : Word α, w ∈ K → w ∈ (L.grammar K).StringLanguage := by
  exact (L.exactPackage K).sampleWitnesses_subset_stringLanguage (M := M) P

end SampleGeneratedWordParseWitnessLearner

/-- Concrete word-parse learner for a fixed fanout bound. -/
noncomputable def enumeratedSampleGeneratedWordParseWitnessLearner
    (G : WorkingMCFG N α) (obs : α → M)
    (f : Nat) (hfanout : 1 ≤ f) (hG : G.SemanticWorkingConditions) :
    SampleGeneratedWordParseWitnessLearner G obs :=
  { exactPackage := fun K =>
      enumeratedSampleGeneratedWordParseWitnessExact G obs K f hfanout hG }

/-- Gold-style summary for word-level parse witnesses. -/
structure SampleGeneratedWordParseWitnessGoldSummary
    (G : WorkingMCFG N α) (obs : α → M) where
  learner : SampleGeneratedWordParseWitnessLearner G obs
  characteristicSample : Finset (Word α)

namespace SampleGeneratedWordParseWitnessGoldSummary

/-- Output grammar after finite sample `K`. -/
noncomputable def grammar
    {G : WorkingMCFG N α} {obs : α → M}
    (S : SampleGeneratedWordParseWitnessGoldSummary G obs)
    (K : Finset (Word α)) :
    WorkingMCFG (SampleGeneratedGrammarNonterminal
      (S.learner.ruleLists K).ruleSkeleton.skeleton) α :=
  S.learner.grammar K

/-- Output grammar is semantically well-formed. -/
theorem grammar_semanticWorkingConditions
    {G : WorkingMCFG N α} {obs : α → M}
    (S : SampleGeneratedWordParseWitnessGoldSummary G obs)
    (K : Finset (Word α)) :
    (S.grammar K).SemanticWorkingConditions := by
  exact S.learner.grammar_semanticWorkingConditions K

/-- A word-level parse witness gives membership in the summary's output
grammar. -/
theorem wordWitness_mem_stringLanguage
    {G : WorkingMCFG N α} {obs : α → M}
    (S : SampleGeneratedWordParseWitnessGoldSummary G obs)
    (K : Finset (Word α)) {w : Word α}
    (W : SampleGeneratedWordParseWitness (M := M) (S.learner.ruleSkeleton K) w) :
    w ∈ (S.grammar K).StringLanguage := by
  exact S.learner.wordWitness_mem_stringLanguage (M := M) K W

/-- Sample-level parse witnesses imply sample inclusion in the summary's output
grammar. -/
theorem sampleWitnesses_subset_stringLanguage
    {G : WorkingMCFG N α} {obs : α → M}
    (S : SampleGeneratedWordParseWitnessGoldSummary G obs)
    (K : Finset (Word α))
    (P : SampleGeneratedSampleParseWitnesses (M := M) (S.learner.ruleSkeleton K)) :
    ∀ w : Word α, w ∈ K → w ∈ (S.grammar K).StringLanguage := by
  exact S.learner.sampleWitnesses_subset_stringLanguage (M := M) K P

end SampleGeneratedWordParseWitnessGoldSummary

/-- Concrete enumerated Gold-style word-parse summary. -/
noncomputable def enumeratedSampleGeneratedWordParseWitnessGoldSummary
    (G : WorkingMCFG N α) (obs : α → M)
    (f : Nat) (hfanout : 1 ≤ f) (hG : G.SemanticWorkingConditions)
    (CS : Finset (Word α)) :
    SampleGeneratedWordParseWitnessGoldSummary G obs :=
  { learner := enumeratedSampleGeneratedWordParseWitnessLearner
      G obs f hfanout hG
    characteristicSample := CS }

end SampleGeneratedWordParseWitnessGold

end FIv21
