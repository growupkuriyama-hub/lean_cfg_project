import LeanCfgProject.MCFG.FI_v2_1_SampleGeneratedPrefixNodeEnumerationExact

/-!
# FI v2.1 Lean experiment: Gold wrapper for prefix-node enumeration

This file provides the learner-like wrapper for the prefix-node enumeration
layer.  It keeps the same conservative meaning as the previous prefix-chain
layer, but exposes the exact finite evidence needed by a future automatic
prefix-node search.
-/

namespace FIv21

universe u v w

section SampleGeneratedPrefixNodeEnumerationGold

variable {N : Type w} {α : Type u}
variable [DecidableEq α]
variable {M : Type v} [Monoid M] [Fintype M]

/-- Learner-like map from finite samples to prefix-node enumeration exact
packages. -/
structure SampleGeneratedPrefixNodeEnumerationLearner
    (G : WorkingMCFG N α) (obs : α → M) where
  exactPackage :
    (K : Finset (Word α)) →
      SampleGeneratedPrefixNodeEnumerationExact G obs K

namespace SampleGeneratedPrefixNodeEnumerationLearner

/-- Rule skeleton after seeing finite sample `K`. -/
def ruleSkeleton
    {G : WorkingMCFG N α} {obs : α → M}
    (L : SampleGeneratedPrefixNodeEnumerationLearner G obs)
    (K : Finset (Word α)) : SampleGeneratedRuleSkeleton G obs K :=
  (L.exactPackage K).ruleSkeleton

/-- Rule lists after seeing finite sample `K`. -/
noncomputable def ruleLists
    {G : WorkingMCFG N α} {obs : α → M}
    (L : SampleGeneratedPrefixNodeEnumerationLearner G obs)
    (K : Finset (Word α)) : SampleGeneratedRuleListPackage G obs K :=
  (L.exactPackage K).ruleLists

/-- Output grammar after seeing finite sample `K`. -/
noncomputable def grammar
    {G : WorkingMCFG N α} {obs : α → M}
    (L : SampleGeneratedPrefixNodeEnumerationLearner G obs)
    (K : Finset (Word α)) :
    WorkingMCFG (SampleGeneratedGrammarNonterminal
      (L.ruleLists K).ruleSkeleton.skeleton) α :=
  (L.exactPackage K).toWorkingMCFG

/-- Every output grammar is semantically well-formed. -/
theorem grammar_semanticWorkingConditions
    {G : WorkingMCFG N α} {obs : α → M}
    (L : SampleGeneratedPrefixNodeEnumerationLearner G obs)
    (K : Finset (Word α)) :
    (L.grammar K).SemanticWorkingConditions := by
  exact (L.exactPackage K).semanticWorkingConditions

/-- A prefix-node enumeration for sample `K` generates the indexed word in the
learner's output grammar for `K`. -/
theorem prefixNodeEnumeration_mem_stringLanguage
    {G : WorkingMCFG N α} {obs : α → M}
    (L : SampleGeneratedPrefixNodeEnumerationLearner G obs)
    (K : Finset (Word α)) {w : Word α}
    (P : SampleGeneratedPrefixNodeEnumeration
      (M := M) (L.ruleSkeleton K) w) :
    w ∈ (L.grammar K).StringLanguage := by
  exact (L.exactPackage K).prefixNodeEnumeration_mem_stringLanguage (M := M) P

end SampleGeneratedPrefixNodeEnumerationLearner

/-- Concrete prefix-node enumeration learner for a fixed fanout bound. -/
noncomputable def enumeratedSampleGeneratedPrefixNodeEnumerationLearner
    (G : WorkingMCFG N α) (obs : α → M)
    (f : Nat) (hfanout : 1 ≤ f) (hG : G.SemanticWorkingConditions) :
    SampleGeneratedPrefixNodeEnumerationLearner G obs :=
  { exactPackage := fun K =>
      enumeratedSampleGeneratedPrefixNodeEnumerationExact G obs K f hfanout hG }

/-- Gold-style summary for prefix-node generated grammar shells. -/
structure SampleGeneratedPrefixNodeEnumerationGoldSummary
    (G : WorkingMCFG N α) (obs : α → M) where
  learner : SampleGeneratedPrefixNodeEnumerationLearner G obs
  characteristicSample : Finset (Word α)

namespace SampleGeneratedPrefixNodeEnumerationGoldSummary

/-- Output grammar after finite sample `K`. -/
noncomputable def grammar
    {G : WorkingMCFG N α} {obs : α → M}
    (S : SampleGeneratedPrefixNodeEnumerationGoldSummary G obs)
    (K : Finset (Word α)) :
    WorkingMCFG (SampleGeneratedGrammarNonterminal
      (S.learner.ruleLists K).ruleSkeleton.skeleton) α :=
  S.learner.grammar K

/-- Output grammar is semantically well-formed. -/
theorem grammar_semanticWorkingConditions
    {G : WorkingMCFG N α} {obs : α → M}
    (S : SampleGeneratedPrefixNodeEnumerationGoldSummary G obs)
    (K : Finset (Word α)) :
    (S.grammar K).SemanticWorkingConditions := by
  exact S.learner.grammar_semanticWorkingConditions K

/-- A prefix-node enumeration for sample `K` gives membership in the summary's
output grammar. -/
theorem prefixNodeEnumeration_mem_stringLanguage
    {G : WorkingMCFG N α} {obs : α → M}
    (S : SampleGeneratedPrefixNodeEnumerationGoldSummary G obs)
    (K : Finset (Word α)) {w : Word α}
    (P : SampleGeneratedPrefixNodeEnumeration
      (M := M) (S.learner.ruleSkeleton K) w) :
    w ∈ (S.grammar K).StringLanguage := by
  exact S.learner.prefixNodeEnumeration_mem_stringLanguage (M := M) K P

end SampleGeneratedPrefixNodeEnumerationGoldSummary

/-- Concrete enumerated Gold-style prefix-node summary. -/
noncomputable def enumeratedSampleGeneratedPrefixNodeEnumerationGoldSummary
    (G : WorkingMCFG N α) (obs : α → M)
    (f : Nat) (hfanout : 1 ≤ f) (hG : G.SemanticWorkingConditions)
    (CS : Finset (Word α)) :
    SampleGeneratedPrefixNodeEnumerationGoldSummary G obs :=
  { learner := enumeratedSampleGeneratedPrefixNodeEnumerationLearner
      G obs f hfanout hG
    characteristicSample := CS }

end SampleGeneratedPrefixNodeEnumerationGold

end FIv21
