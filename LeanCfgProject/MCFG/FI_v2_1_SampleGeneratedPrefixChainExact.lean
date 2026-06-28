import LeanCfgProject.MCFG.FI_v2_1_SampleGeneratedPrefixChain

/-!
# FI v2.1 Lean experiment: exact package for prefix-chain generated parses

This layer packages the prefix-chain interface.  A prefix-chain certificate is
now enough to place its indexed word in the generated terminal+concat
`WorkingMCFG` shell.
-/

namespace FIv21

universe u v w

section SampleGeneratedPrefixChainExact

variable {N : Type w} {α : Type u}
variable [DecidableEq α]
variable {M : Type v} [Monoid M] [Fintype M]

/-- Exact package for prefix-chain generated parses. -/
structure SampleGeneratedPrefixChainExact
    (G : WorkingMCFG N α) (obs : α → M) (K : Finset (Word α)) where
  constructionExact : SampleGeneratedLinearParseConstructionExact G obs K

namespace SampleGeneratedPrefixChainExact

/-- The underlying rule skeleton. -/
def ruleSkeleton
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (E : SampleGeneratedPrefixChainExact G obs K) :
    SampleGeneratedRuleSkeleton G obs K :=
  E.constructionExact.ruleSkeleton

/-- The terminal+concat rule-list package. -/
noncomputable def ruleLists
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (E : SampleGeneratedPrefixChainExact G obs K) :
    SampleGeneratedRuleListPackage G obs K :=
  E.constructionExact.ruleLists

/-- The generated working grammar shell. -/
noncomputable def toWorkingMCFG
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (E : SampleGeneratedPrefixChainExact G obs K) :
    WorkingMCFG (SampleGeneratedGrammarNonterminal
      E.ruleLists.ruleSkeleton.skeleton) α :=
  E.constructionExact.toWorkingMCFG

/-- The generated grammar shell is semantically well-formed. -/
theorem semanticWorkingConditions
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (E : SampleGeneratedPrefixChainExact G obs K) :
    E.toWorkingMCFG.SemanticWorkingConditions := by
  exact E.constructionExact.semanticWorkingConditions

/-- A word prefix-chain gives membership of that word in the generated grammar
shell. -/
theorem wordPrefixChain_mem_stringLanguage
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (E : SampleGeneratedPrefixChainExact G obs K)
    {w : Word α}
    (P : SampleGeneratedPrefixChain (M := M) E.ruleSkeleton w) :
    w ∈ E.toWorkingMCFG.StringLanguage := by
  exact P.word_mem_stringLanguage (M := M)

/-- Singleton word prefix-chains generate their singleton word. -/
theorem singleton_word_mem_stringLanguage
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (E : SampleGeneratedPrefixChainExact G obs K)
    {X : SampleGeneratedDecompositionNode E.ruleSkeleton.skeleton} {a : α}
    (hX : X ∈ E.ruleSkeleton.decompositionNodes)
    (hmid : X.decomposition.middle = [a]) :
    [a] ∈ E.toWorkingMCFG.StringLanguage := by
  exact E.wordPrefixChain_mem_stringLanguage (M := M)
    (singletonPrefixChain (M := M) E.ruleSkeleton hX hmid)

/-- Right-extension word prefix-chains generate the appended word. -/
theorem snoc_word_mem_stringLanguage
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (E : SampleGeneratedPrefixChainExact G obs K)
    {u : Word α}
    (P : SampleGeneratedPrefixChain (M := M) E.ruleSkeleton u)
    {last result : SampleGeneratedDecompositionNode E.ruleSkeleton.skeleton} {a : α}
    (hLast : last ∈ E.ruleSkeleton.decompositionNodes)
    (hLastMid : last.decomposition.middle = [a])
    (hResult : result ∈ E.ruleSkeleton.decompositionNodes)
    (hmid : result.decomposition.middle =
      P.endpoint.decomposition.middle ++ last.decomposition.middle) :
    u ++ [a] ∈ E.toWorkingMCFG.StringLanguage := by
  exact E.wordPrefixChain_mem_stringLanguage (M := M)
    (snocPrefixChain (M := M) E.ruleSkeleton P hLast hLastMid hResult hmid)

end SampleGeneratedPrefixChainExact

/-- Concrete exact package using the enumerated subword skeleton and the
terminal+concat generated grammar shell. -/
noncomputable def enumeratedSampleGeneratedPrefixChainExact
    (G : WorkingMCFG N α) (obs : α → M) (K : Finset (Word α))
    (f : Nat) (hfanout : 1 ≤ f) (hG : G.SemanticWorkingConditions) :
    SampleGeneratedPrefixChainExact G obs K :=
  { constructionExact :=
      enumeratedSampleGeneratedLinearParseConstructionExact G obs K f hfanout hG }

/-- The concrete generated grammar shell is semantically well-formed. -/
theorem enumeratedSampleGeneratedPrefixChainExact_semantic
    (G : WorkingMCFG N α) (obs : α → M) (K : Finset (Word α))
    (f : Nat) (hfanout : 1 ≤ f) (hG : G.SemanticWorkingConditions) :
    (enumeratedSampleGeneratedPrefixChainExact
      G obs K f hfanout hG).toWorkingMCFG.SemanticWorkingConditions := by
  exact (enumeratedSampleGeneratedPrefixChainExact
    G obs K f hfanout hG).semanticWorkingConditions

end SampleGeneratedPrefixChainExact

end FIv21
