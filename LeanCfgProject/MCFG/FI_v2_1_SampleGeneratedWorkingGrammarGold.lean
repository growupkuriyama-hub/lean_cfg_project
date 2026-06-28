import LeanCfgProject.MCFG.FI_v2_1_SampleGeneratedWorkingGrammarExact

/-!
# FI v2.1 Lean experiment: Gold wrapper for sample-generated working grammar shells

This file provides the Gold-style wrapper for the new working-grammar shell
layer.  It does not yet claim language identification.  Its purpose is to make
the sample-indexed construction available as a learner-like object whose output
is now an actual syntactic `WorkingMCFG` shell.
-/

namespace FIv21

universe u v w

section SampleGeneratedWorkingGrammarGold

variable {N : Type w} {α : Type u}
variable [DecidableEq α]
variable {M : Type v} [Monoid M] [Fintype M]

/-- A learner-like map sending each finite sample to a sample-generated working
grammar shell package. -/
structure SampleGeneratedWorkingGrammarLearner
    (G : WorkingMCFG N α) (obs : α → M) where
  exactPackage :
    (K : Finset (Word α)) → SampleGeneratedWorkingGrammarExact G obs K

namespace SampleGeneratedWorkingGrammarLearner

/-- The rule-list package output at a finite sample. -/
noncomputable def ruleLists
    {G : WorkingMCFG N α} {obs : α → M}
    (L : SampleGeneratedWorkingGrammarLearner G obs)
    (K : Finset (Word α)) : SampleGeneratedRuleListPackage G obs K :=
  (L.exactPackage K).ruleLists

/-- The actual working grammar shell output at a finite sample. -/
noncomputable def grammar
    {G : WorkingMCFG N α} {obs : α → M}
    (L : SampleGeneratedWorkingGrammarLearner G obs)
    (K : Finset (Word α)) :
    WorkingMCFG (SampleGeneratedGrammarNonterminal (L.ruleLists K).ruleSkeleton.skeleton) α :=
  (L.exactPackage K).toWorkingMCFG

/-- Every learner output satisfies the basic syntactic working conditions. -/
theorem grammar_basicWorkingConditions
    {G : WorkingMCFG N α} {obs : α → M}
    (L : SampleGeneratedWorkingGrammarLearner G obs)
    (K : Finset (Word α)) :
    (L.grammar K).BasicWorkingConditions := by
  exact (L.exactPackage K).basicWorkingConditions

/-- Every sample word has a generated start rule in the learner output. -/
theorem sample_startRule_exists
    {G : WorkingMCFG N α} {obs : α → M}
    (L : SampleGeneratedWorkingGrammarLearner G obs)
    (K : Finset (Word α)) {w : Word α} (hw : w ∈ K) :
    ∃ C : SampleGeneratedStartCandidate (L.ruleLists K).ruleSkeleton.skeleton,
      C ∈ (L.ruleLists K).ruleSkeleton.startCandidates ∧
      C.node.decomposition.sampleWord = w ∧
      startRuleOfCandidate (M := M) C ∈ (L.ruleLists K).startRules := by
  exact (L.exactPackage K).startRule_exists_of_mem hw

end SampleGeneratedWorkingGrammarLearner

/-- Concrete enumerated learner for a fixed fanout bound and semantic working
conditions of the target grammar. -/
noncomputable def enumeratedSampleGeneratedWorkingGrammarLearner
    (G : WorkingMCFG N α) (obs : α → M)
    (f : Nat) (hfanout : 1 ≤ f) (hG : G.SemanticWorkingConditions) :
    SampleGeneratedWorkingGrammarLearner G obs :=
  { exactPackage := fun K =>
      enumeratedSampleGeneratedWorkingGrammarExact G obs K f hfanout hG }

/-- A Gold-style summary package for the sample-generated working grammar shell.

The characteristic sample is only a scheduling/telltale slot here.  The actual
statement guaranteed at each post-threshold sample is syntactic: a generated
working grammar shell exists, is basically well-formed, and has start-rule
coverage for the observed sample words. -/
structure SampleGeneratedWorkingGrammarGoldSummary
    (G : WorkingMCFG N α) (obs : α → M) where
  learner : SampleGeneratedWorkingGrammarLearner G obs
  characteristicSample : Finset (Word α)

namespace SampleGeneratedWorkingGrammarGoldSummary

/-- Output grammar shell after seeing sample `K`. -/
noncomputable def grammar
    {G : WorkingMCFG N α} {obs : α → M}
    (S : SampleGeneratedWorkingGrammarGoldSummary G obs)
    (K : Finset (Word α)) :
    WorkingMCFG (SampleGeneratedGrammarNonterminal
      (S.learner.ruleLists K).ruleSkeleton.skeleton) α :=
  S.learner.grammar K

/-- The output grammar shell is syntactically well-formed in the basic sense. -/
theorem grammar_basicWorkingConditions
    {G : WorkingMCFG N α} {obs : α → M}
    (S : SampleGeneratedWorkingGrammarGoldSummary G obs)
    (K : Finset (Word α)) :
    (S.grammar K).BasicWorkingConditions := by
  exact S.learner.grammar_basicWorkingConditions K

/-- Sample words have generated start rules in the output shell. -/
theorem sample_startRule_exists
    {G : WorkingMCFG N α} {obs : α → M}
    (S : SampleGeneratedWorkingGrammarGoldSummary G obs)
    (K : Finset (Word α)) {w : Word α} (hw : w ∈ K) :
    ∃ C : SampleGeneratedStartCandidate (S.learner.ruleLists K).ruleSkeleton.skeleton,
      C ∈ (S.learner.ruleLists K).ruleSkeleton.startCandidates ∧
      C.node.decomposition.sampleWord = w ∧
      startRuleOfCandidate (M := M) C ∈ (S.learner.ruleLists K).startRules := by
  exact S.learner.sample_startRule_exists K hw

end SampleGeneratedWorkingGrammarGoldSummary

/-- Enumerated Gold-style summary for a fixed target grammar and fanout bound. -/
noncomputable def enumeratedSampleGeneratedWorkingGrammarGoldSummary
    (G : WorkingMCFG N α) (obs : α → M)
    (f : Nat) (hfanout : 1 ≤ f) (hG : G.SemanticWorkingConditions)
    (CS : Finset (Word α)) :
    SampleGeneratedWorkingGrammarGoldSummary G obs :=
  { learner := enumeratedSampleGeneratedWorkingGrammarLearner G obs f hfanout hG
    characteristicSample := CS }

end SampleGeneratedWorkingGrammarGold

end FIv21
