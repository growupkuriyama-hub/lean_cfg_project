import LeanCfgProject.MCFG.FI_v2_1_SampleGeneratedLinearParseConstruction

/-!
# FI v2.1 Lean experiment: exact package for constructed left-linear parses

This layer packages the word-indexed linear-parse construction interface.  A
constructed parse for a word is transported to membership of that word in the
terminal+concat generated `WorkingMCFG` shell.
-/

namespace FIv21

universe u v w

section SampleGeneratedLinearParseConstructionExact

variable {N : Type w} {α : Type u}
variable [DecidableEq α]
variable {M : Type v} [Monoid M] [Fintype M]

/-- Exact package for word-indexed constructed left-linear parses. -/
structure SampleGeneratedLinearParseConstructionExact
    (G : WorkingMCFG N α) (obs : α → M) (K : Finset (Word α)) where
  linearExact : SampleGeneratedLinearParseExact G obs K

namespace SampleGeneratedLinearParseConstructionExact

/-- The underlying rule skeleton. -/
def ruleSkeleton
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (E : SampleGeneratedLinearParseConstructionExact G obs K) :
    SampleGeneratedRuleSkeleton G obs K :=
  E.linearExact.ruleSkeleton

/-- The terminal+concat rule-list package. -/
noncomputable def ruleLists
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (E : SampleGeneratedLinearParseConstructionExact G obs K) :
    SampleGeneratedRuleListPackage G obs K :=
  E.linearExact.ruleLists

/-- The generated working grammar shell. -/
noncomputable def toWorkingMCFG
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (E : SampleGeneratedLinearParseConstructionExact G obs K) :
    WorkingMCFG (SampleGeneratedGrammarNonterminal
      E.ruleLists.ruleSkeleton.skeleton) α :=
  E.linearExact.toWorkingMCFG

/-- The generated grammar shell is semantically well-formed. -/
theorem semanticWorkingConditions
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (E : SampleGeneratedLinearParseConstructionExact G obs K) :
    E.toWorkingMCFG.SemanticWorkingConditions := by
  exact E.linearExact.semanticWorkingConditions

/-- A word-indexed constructed parse gives membership of that word in the
generated grammar shell. -/
theorem word_mem_stringLanguage
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (E : SampleGeneratedLinearParseConstructionExact G obs K)
    {w : Word α}
    (P : SampleGeneratedWordLinearParseConstruction (M := M) E.ruleSkeleton w) :
    w ∈ E.toWorkingMCFG.StringLanguage := by
  exact P.word_mem_stringLanguage (M := M)

/-- Singleton endpoint constructions give singleton-word membership. -/
theorem singleton_word_mem_stringLanguage
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (E : SampleGeneratedLinearParseConstructionExact G obs K)
    {X : SampleGeneratedDecompositionNode E.ruleSkeleton.skeleton} {a : α}
    (hX : X ∈ E.ruleSkeleton.decompositionNodes)
    (hmid : X.decomposition.middle = [a]) :
    [a] ∈ E.toWorkingMCFG.StringLanguage := by
  exact E.word_mem_stringLanguage
    (M := M) (singletonWordLinearParseConstruction (M := M) E.ruleSkeleton hX hmid)

/-- Appending a listed singleton endpoint to a constructed prefix gives
membership of the appended word. -/
theorem append_singleton_word_mem_stringLanguage
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (E : SampleGeneratedLinearParseConstructionExact G obs K)
    {u : Word α}
    (P : SampleGeneratedWordLinearParseConstruction (M := M) E.ruleSkeleton u)
    {last result : SampleGeneratedDecompositionNode E.ruleSkeleton.skeleton} {a : α}
    (hLast : last ∈ E.ruleSkeleton.decompositionNodes)
    (hLastMid : last.decomposition.middle = [a])
    (hResult : result ∈ E.ruleSkeleton.decompositionNodes)
    (hmid : result.decomposition.middle =
      P.node.decomposition.middle ++ last.decomposition.middle) :
    u ++ [a] ∈ E.toWorkingMCFG.StringLanguage := by
  exact E.word_mem_stringLanguage (M := M)
    (appendSingletonWordLinearParseConstruction
      (M := M) E.ruleSkeleton P hLast hLastMid hResult hmid)

end SampleGeneratedLinearParseConstructionExact

/-- Concrete exact package using the enumerated subword skeleton and the
terminal+concat generated grammar shell. -/
noncomputable def enumeratedSampleGeneratedLinearParseConstructionExact
    (G : WorkingMCFG N α) (obs : α → M) (K : Finset (Word α))
    (f : Nat) (hfanout : 1 ≤ f) (hG : G.SemanticWorkingConditions) :
    SampleGeneratedLinearParseConstructionExact G obs K :=
  { linearExact :=
      enumeratedSampleGeneratedLinearParseExact G obs K f hfanout hG }

/-- The concrete generated grammar shell is semantically well-formed. -/
theorem enumeratedSampleGeneratedLinearParseConstructionExact_semantic
    (G : WorkingMCFG N α) (obs : α → M) (K : Finset (Word α))
    (f : Nat) (hfanout : 1 ≤ f) (hG : G.SemanticWorkingConditions) :
    (enumeratedSampleGeneratedLinearParseConstructionExact
      G obs K f hfanout hG).toWorkingMCFG.SemanticWorkingConditions := by
  exact (enumeratedSampleGeneratedLinearParseConstructionExact
    G obs K f hfanout hG).semanticWorkingConditions

end SampleGeneratedLinearParseConstructionExact

end FIv21
