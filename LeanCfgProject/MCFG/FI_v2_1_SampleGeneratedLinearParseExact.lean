import LeanCfgProject.MCFG.FI_v2_1_SampleGeneratedLinearParse

/-!
# FI v2.1 Lean experiment: exact package for left-linear generated parses

This layer packages the left-linear parse certificates.  A linearly parsed
listed node is sent through the already checked recursive derivation bridge and
therefore generates its exposed middle word in the terminal+concat generated
`WorkingMCFG` shell.
-/

namespace FIv21

universe u v w

section SampleGeneratedLinearParseExact

variable {N : Type w} {α : Type u}
variable [DecidableEq α]
variable {M : Type v} [Monoid M] [Fintype M]

/-- Exact package for left-linear terminal/concat parses in a sample-generated
rule skeleton. -/
structure SampleGeneratedLinearParseExact
    (G : WorkingMCFG N α) (obs : α → M) (K : Finset (Word α)) where
  recursiveExact : SampleGeneratedRecursiveDerivationExact G obs K

namespace SampleGeneratedLinearParseExact

/-- The underlying rule skeleton. -/
def ruleSkeleton
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (E : SampleGeneratedLinearParseExact G obs K) :
    SampleGeneratedRuleSkeleton G obs K :=
  E.recursiveExact.ruleSkeleton

/-- The terminal+concat rule lists. -/
noncomputable def ruleLists
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (E : SampleGeneratedLinearParseExact G obs K) :
    SampleGeneratedRuleListPackage G obs K :=
  E.recursiveExact.ruleLists

/-- The generated working grammar shell. -/
noncomputable def toWorkingMCFG
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (E : SampleGeneratedLinearParseExact G obs K) :
    WorkingMCFG (SampleGeneratedGrammarNonterminal
      E.ruleLists.ruleSkeleton.skeleton) α :=
  E.recursiveExact.toWorkingMCFG

/-- The generated grammar shell satisfies semantic working conditions. -/
theorem semanticWorkingConditions
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (E : SampleGeneratedLinearParseExact G obs K) :
    E.toWorkingMCFG.SemanticWorkingConditions := by
  exact E.recursiveExact.semanticWorkingConditions

/-- A left-linear certificate gives tuple derivability in the generated grammar
shell. -/
theorem derives_node_tuple
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (E : SampleGeneratedLinearParseExact G obs K)
    {X : SampleGeneratedDecompositionNode E.ruleSkeleton.skeleton}
    (P : SampleGeneratedLinearParse (M := M) E.ruleSkeleton X) :
    DerivesTuple E.toWorkingMCFG
      (SampleGeneratedGrammarNonterminal.node X)
      X.decomposition.tuple := by
  exact P.derives_node_tuple (M := M)

/-- A left-linear certificate generates the exposed middle word. -/
theorem middle_mem_stringLanguage
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (E : SampleGeneratedLinearParseExact G obs K)
    {X : SampleGeneratedDecompositionNode E.ruleSkeleton.skeleton}
    (P : SampleGeneratedLinearParse (M := M) E.ruleSkeleton X) :
    X.decomposition.middle ∈ E.toWorkingMCFG.StringLanguage := by
  exact P.middle_mem_stringLanguage (M := M)

/-- Singleton-middle nodes are linearly parsed in the exact package. -/
theorem singleton_node_middle_mem_stringLanguage
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (E : SampleGeneratedLinearParseExact G obs K)
    {X : SampleGeneratedDecompositionNode E.ruleSkeleton.skeleton} {a : α}
    (hX : X ∈ E.ruleSkeleton.decompositionNodes)
    (hmid : X.decomposition.middle = [a]) :
    X.decomposition.middle ∈ E.toWorkingMCFG.StringLanguage := by
  exact (singleton_node_linearParse (M := M) E.ruleSkeleton hX hmid)
    .middle_mem_stringLanguage (M := M)

end SampleGeneratedLinearParseExact

/-- Concrete exact package using the enumerated subword decomposition skeleton,
generated terminal/concat candidates, and left-linear parse certificates. -/
noncomputable def enumeratedSampleGeneratedLinearParseExact
    (G : WorkingMCFG N α) (obs : α → M) (K : Finset (Word α))
    (f : Nat) (hfanout : 1 ≤ f) (hG : G.SemanticWorkingConditions) :
    SampleGeneratedLinearParseExact G obs K :=
  { recursiveExact :=
      enumeratedSampleGeneratedRecursiveDerivationExact G obs K f hfanout hG }

/-- The concrete left-linear generated output grammar is semantically
well-formed. -/
theorem enumeratedSampleGeneratedLinearParseExact_semantic
    (G : WorkingMCFG N α) (obs : α → M) (K : Finset (Word α))
    (f : Nat) (hfanout : 1 ≤ f) (hG : G.SemanticWorkingConditions) :
    (enumeratedSampleGeneratedLinearParseExact G obs K f hfanout hG)
      .toWorkingMCFG.SemanticWorkingConditions := by
  exact (enumeratedSampleGeneratedLinearParseExact
    G obs K f hfanout hG).semanticWorkingConditions

end SampleGeneratedLinearParseExact

end FIv21
