import LeanCfgProject.MCFG.FI_v2_1_SampleGeneratedPrefixNodeEnumeration

/-!
# FI v2.1 Lean experiment: exact package for prefix-node enumeration

This layer packages the prefix-node enumeration interface.  A finite list of
listed singleton/result nodes, once folded into a prefix-node enumeration,
places the indexed word in the generated terminal+concat `WorkingMCFG` shell.
-/

namespace FIv21

universe u v w

section SampleGeneratedPrefixNodeEnumerationExact

variable {N : Type w} {α : Type u}
variable [DecidableEq α]
variable {M : Type v} [Monoid M] [Fintype M]

/-- Exact package for prefix-node enumeration generated parses. -/
structure SampleGeneratedPrefixNodeEnumerationExact
    (G : WorkingMCFG N α) (obs : α → M) (K : Finset (Word α)) where
  prefixChainExact : SampleGeneratedPrefixChainExact G obs K

namespace SampleGeneratedPrefixNodeEnumerationExact

/-- The underlying rule skeleton. -/
def ruleSkeleton
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (E : SampleGeneratedPrefixNodeEnumerationExact G obs K) :
    SampleGeneratedRuleSkeleton G obs K :=
  E.prefixChainExact.ruleSkeleton

/-- The terminal+concat rule-list package. -/
noncomputable def ruleLists
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (E : SampleGeneratedPrefixNodeEnumerationExact G obs K) :
    SampleGeneratedRuleListPackage G obs K :=
  E.prefixChainExact.ruleLists

/-- The generated working grammar shell. -/
noncomputable def toWorkingMCFG
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (E : SampleGeneratedPrefixNodeEnumerationExact G obs K) :
    WorkingMCFG (SampleGeneratedGrammarNonterminal
      E.ruleLists.ruleSkeleton.skeleton) α :=
  E.prefixChainExact.toWorkingMCFG

/-- The generated grammar shell is semantically well-formed. -/
theorem semanticWorkingConditions
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (E : SampleGeneratedPrefixNodeEnumerationExact G obs K) :
    E.toWorkingMCFG.SemanticWorkingConditions := by
  exact E.prefixChainExact.semanticWorkingConditions

/-- A prefix-node enumeration for sample `K` generates its indexed word. -/
theorem prefixNodeEnumeration_mem_stringLanguage
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (E : SampleGeneratedPrefixNodeEnumerationExact G obs K)
    {w : Word α}
    (P : SampleGeneratedPrefixNodeEnumeration (M := M) E.ruleSkeleton w) :
    w ∈ E.toWorkingMCFG.StringLanguage := by
  exact P.word_mem_stringLanguage (M := M)

/-- Singleton prefix-node enumerations generate their singleton word. -/
theorem singleton_node_mem_stringLanguage
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (E : SampleGeneratedPrefixNodeEnumerationExact G obs K)
    {a : α}
    (X : SampleGeneratedSingletonPrefixNode (M := M) E.ruleSkeleton a) :
    [a] ∈ E.toWorkingMCFG.StringLanguage := by
  exact E.prefixNodeEnumeration_mem_stringLanguage (M := M)
    (singletonPrefixNodeEnumeration (M := M) E.ruleSkeleton X)

/-- Right-extension prefix-node enumerations generate the appended word. -/
theorem snoc_node_mem_stringLanguage
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (E : SampleGeneratedPrefixNodeEnumerationExact G obs K)
    {u : Word α}
    (P : SampleGeneratedPrefixNodeEnumeration (M := M) E.ruleSkeleton u)
    {a : α}
    (last : SampleGeneratedSingletonPrefixNode (M := M) E.ruleSkeleton a)
    (result : ListedSampleGeneratedDecompositionNode E.ruleSkeleton)
    (hmid : result.middle = P.chain.endpoint.decomposition.middle ++ last.listed.middle) :
    u ++ [a] ∈ E.toWorkingMCFG.StringLanguage := by
  exact E.prefixNodeEnumeration_mem_stringLanguage (M := M)
    (snocPrefixNodeEnumeration (M := M) E.ruleSkeleton P last result hmid)

end SampleGeneratedPrefixNodeEnumerationExact

/-- Concrete exact package using the enumerated subword skeleton and the
terminal+concat generated grammar shell. -/
noncomputable def enumeratedSampleGeneratedPrefixNodeEnumerationExact
    (G : WorkingMCFG N α) (obs : α → M) (K : Finset (Word α))
    (f : Nat) (hfanout : 1 ≤ f) (hG : G.SemanticWorkingConditions) :
    SampleGeneratedPrefixNodeEnumerationExact G obs K :=
  { prefixChainExact :=
      enumeratedSampleGeneratedPrefixChainExact G obs K f hfanout hG }

/-- The concrete generated grammar shell is semantically well-formed. -/
theorem enumeratedSampleGeneratedPrefixNodeEnumerationExact_semantic
    (G : WorkingMCFG N α) (obs : α → M) (K : Finset (Word α))
    (f : Nat) (hfanout : 1 ≤ f) (hG : G.SemanticWorkingConditions) :
    (enumeratedSampleGeneratedPrefixNodeEnumerationExact
      G obs K f hfanout hG).toWorkingMCFG.SemanticWorkingConditions := by
  exact (enumeratedSampleGeneratedPrefixNodeEnumerationExact
    G obs K f hfanout hG).semanticWorkingConditions

end SampleGeneratedPrefixNodeEnumerationExact

end FIv21
