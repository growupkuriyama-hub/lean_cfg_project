import LeanCfgProject.MCFG.FI_v2_1_SampleGeneratedWorkingGrammarDerivationExact

/-!
# FI v2.1 Lean experiment: Gold wrapper for generated working-grammar derivations

This file lifts the derivation-facing working-grammar package to a learner-like
object.  Its output is now an actual `WorkingMCFG` shell equipped with semantic
working conditions and conditional sample-word derivation principles.
-/

namespace FIv21

universe u v w

section SampleGeneratedWorkingGrammarDerivationGold

variable {N : Type w} {α : Type u}
variable [DecidableEq α]
variable {M : Type v} [Monoid M] [Fintype M]

/-- Learner-like map from finite samples to derivation-facing generated working
grammar shells. -/
structure SampleGeneratedWorkingGrammarDerivationLearner
    (G : WorkingMCFG N α) (obs : α → M) where
  exactPackage :
    (K : Finset (Word α)) →
      SampleGeneratedWorkingGrammarDerivationExact G obs K

namespace SampleGeneratedWorkingGrammarDerivationLearner

/-- Rule lists produced after seeing sample `K`. -/
noncomputable def ruleLists
    {G : WorkingMCFG N α} {obs : α → M}
    (L : SampleGeneratedWorkingGrammarDerivationLearner G obs)
    (K : Finset (Word α)) : SampleGeneratedRuleListPackage G obs K :=
  (L.exactPackage K).ruleLists

/-- Generated working grammar shell after seeing sample `K`. -/
noncomputable def grammar
    {G : WorkingMCFG N α} {obs : α → M}
    (L : SampleGeneratedWorkingGrammarDerivationLearner G obs)
    (K : Finset (Word α)) :
    WorkingMCFG (SampleGeneratedGrammarNonterminal
      (L.ruleLists K).ruleSkeleton.skeleton) α :=
  (L.exactPackage K).toWorkingMCFG

/-- Every learner output satisfies the semantic working conditions of the current
MCFG derivation layer. -/
theorem grammar_semanticWorkingConditions
    {G : WorkingMCFG N α} {obs : α → M}
    (L : SampleGeneratedWorkingGrammarDerivationLearner G obs)
    (K : Finset (Word α)) :
    (L.grammar K).SemanticWorkingConditions := by
  exact (L.exactPackage K).semanticWorkingConditions

/-- Listed terminal candidates derive their exposed singleton tuples in the
learner output. -/
theorem terminalCandidate_derives_node_tuple
    {G : WorkingMCFG N α} {obs : α → M}
    (L : SampleGeneratedWorkingGrammarDerivationLearner G obs)
    (K : Finset (Word α))
    {C : SampleGeneratedTerminalCandidate (L.ruleLists K).ruleSkeleton.skeleton}
    (hC : C ∈ (L.ruleLists K).terminalCandidates) :
    DerivesTuple (L.grammar K)
      (SampleGeneratedGrammarNonterminal.node C.node)
      C.node.decomposition.tuple := by
  exact (L.exactPackage K).terminalCandidate_derives_node_tuple hC

/-- Listed binary-concatenation candidates derive their result tuple once their
children are derived. -/
theorem binaryCandidate_derives_result_tuple
    {G : WorkingMCFG N α} {obs : α → M}
    (L : SampleGeneratedWorkingGrammarDerivationLearner G obs)
    (K : Finset (Word α))
    {C : SampleGeneratedConcatCandidate (L.ruleLists K).ruleSkeleton.skeleton}
    (hC : C ∈ (L.ruleLists K).concatCandidates)
    (hLeft : DerivesTuple (L.grammar K)
      (SampleGeneratedGrammarNonterminal.node C.left)
      C.left.decomposition.tuple)
    (hRight : DerivesTuple (L.grammar K)
      (SampleGeneratedGrammarNonterminal.node C.right)
      C.right.decomposition.tuple) :
    DerivesTuple (L.grammar K)
      (SampleGeneratedGrammarNonterminal.node C.result)
      C.result.decomposition.tuple := by
  exact (L.exactPackage K).binaryCandidate_derives_result_tuple
    hC hLeft hRight

/-- Conditional sample-word derivation for a listed start candidate. -/
theorem sample_word_mem_stringLanguage_of_node_derives
    {G : WorkingMCFG N α} {obs : α → M}
    (L : SampleGeneratedWorkingGrammarDerivationLearner G obs)
    (K : Finset (Word α))
    {C : SampleGeneratedStartCandidate (L.ruleLists K).ruleSkeleton.skeleton}
    (hC : C ∈ (L.ruleLists K).ruleSkeleton.startCandidates)
    {w : Word α}
    (hw : DerivesTuple (L.grammar K)
      (SampleGeneratedGrammarNonterminal.node C.node)
      (singletonTuple w)) :
    w ∈ (L.grammar K).StringLanguage := by
  exact (L.exactPackage K).sample_word_mem_stringLanguage_of_node_derives
    hC hw

/-- Every sample word has a generated start rule in the learner output. -/
theorem sample_startRule_exists
    {G : WorkingMCFG N α} {obs : α → M}
    (L : SampleGeneratedWorkingGrammarDerivationLearner G obs)
    (K : Finset (Word α)) {w : Word α} (hw : w ∈ K) :
    ∃ C : SampleGeneratedStartCandidate (L.ruleLists K).ruleSkeleton.skeleton,
      C ∈ (L.ruleLists K).ruleSkeleton.startCandidates ∧
      C.node.decomposition.sampleWord = w ∧
      startRuleOfCandidate (M := M) C ∈ (L.ruleLists K).startRules := by
  exact (L.exactPackage K).startRule_exists_of_mem hw

end SampleGeneratedWorkingGrammarDerivationLearner

/-- Concrete enumerated derivation learner for a fixed fanout bound. -/
noncomputable def enumeratedSampleGeneratedWorkingGrammarDerivationLearner
    (G : WorkingMCFG N α) (obs : α → M)
    (f : Nat) (hfanout : 1 ≤ f) (hG : G.SemanticWorkingConditions) :
    SampleGeneratedWorkingGrammarDerivationLearner G obs :=
  { exactPackage := fun K =>
      enumeratedSampleGeneratedWorkingGrammarDerivationExact
        G obs K f hfanout hG }

/-- Gold-style summary for the derivation-facing generated grammar shell. -/
structure SampleGeneratedWorkingGrammarDerivationGoldSummary
    (G : WorkingMCFG N α) (obs : α → M) where
  learner : SampleGeneratedWorkingGrammarDerivationLearner G obs
  characteristicSample : Finset (Word α)

namespace SampleGeneratedWorkingGrammarDerivationGoldSummary

/-- Output grammar shell after finite sample `K`. -/
noncomputable def grammar
    {G : WorkingMCFG N α} {obs : α → M}
    (S : SampleGeneratedWorkingGrammarDerivationGoldSummary G obs)
    (K : Finset (Word α)) :
    WorkingMCFG (SampleGeneratedGrammarNonterminal
      (S.learner.ruleLists K).ruleSkeleton.skeleton) α :=
  S.learner.grammar K

/-- The output grammar shell is semantically well-formed. -/
theorem grammar_semanticWorkingConditions
    {G : WorkingMCFG N α} {obs : α → M}
    (S : SampleGeneratedWorkingGrammarDerivationGoldSummary G obs)
    (K : Finset (Word α)) :
    (S.grammar K).SemanticWorkingConditions := by
  exact S.learner.grammar_semanticWorkingConditions K

/-- Sample words have generated start rules in the output shell. -/
theorem sample_startRule_exists
    {G : WorkingMCFG N α} {obs : α → M}
    (S : SampleGeneratedWorkingGrammarDerivationGoldSummary G obs)
    (K : Finset (Word α)) {w : Word α} (hw : w ∈ K) :
    ∃ C : SampleGeneratedStartCandidate (S.learner.ruleLists K).ruleSkeleton.skeleton,
      C ∈ (S.learner.ruleLists K).ruleSkeleton.startCandidates ∧
      C.node.decomposition.sampleWord = w ∧
      startRuleOfCandidate (M := M) C ∈ (S.learner.ruleLists K).startRules := by
  exact S.learner.sample_startRule_exists K hw

end SampleGeneratedWorkingGrammarDerivationGoldSummary

/-- Concrete enumerated Gold-style derivation summary. -/
noncomputable def enumeratedSampleGeneratedWorkingGrammarDerivationGoldSummary
    (G : WorkingMCFG N α) (obs : α → M)
    (f : Nat) (hfanout : 1 ≤ f) (hG : G.SemanticWorkingConditions)
    (CS : Finset (Word α)) :
    SampleGeneratedWorkingGrammarDerivationGoldSummary G obs :=
  { learner := enumeratedSampleGeneratedWorkingGrammarDerivationLearner
      G obs f hfanout hG
    characteristicSample := CS }

end SampleGeneratedWorkingGrammarDerivationGold

end FIv21
