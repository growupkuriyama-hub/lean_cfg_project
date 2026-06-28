import LeanCfgProject.MCFG.FI_v2_1_SampleGeneratedRecursiveDerivation

/-!
# FI v2.1 Lean experiment: exact package for recursive generated derivations

This layer packages the recursive derivation certificates introduced in
`SampleGeneratedRecursiveDerivation`.  It exposes the generated grammar shell
and the local exactness bridge: a listed node equipped with a recursive
terminal/concat certificate generates its exposed middle word.
-/

namespace FIv21

universe u v w

section SampleGeneratedRecursiveDerivationExact

variable {N : Type w} {α : Type u}
variable [DecidableEq α]
variable {M : Type v} [Monoid M] [Fintype M]

/-- Exact package for recursive terminal/concat derivations in a
sample-generated rule skeleton. -/
structure SampleGeneratedRecursiveDerivationExact
    (G : WorkingMCFG N α) (obs : α → M) (K : Finset (Word α)) where
  concatExact : SampleGeneratedConcatEnumerationExact G obs K

namespace SampleGeneratedRecursiveDerivationExact

/-- The underlying rule skeleton. -/
def ruleSkeleton
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (E : SampleGeneratedRecursiveDerivationExact G obs K) :
    SampleGeneratedRuleSkeleton G obs K :=
  E.concatExact.ruleSkeleton

/-- The terminal+concat rule-list package. -/
noncomputable def ruleLists
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (E : SampleGeneratedRecursiveDerivationExact G obs K) :
    SampleGeneratedRuleListPackage G obs K :=
  E.concatExact.ruleLists

/-- The generated working grammar shell. -/
noncomputable def toWorkingMCFG
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (E : SampleGeneratedRecursiveDerivationExact G obs K) :
    WorkingMCFG (SampleGeneratedGrammarNonterminal
      E.ruleLists.ruleSkeleton.skeleton) α :=
  E.concatExact.toWorkingMCFG

/-- The generated grammar shell satisfies semantic working conditions. -/
theorem semanticWorkingConditions
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (E : SampleGeneratedRecursiveDerivationExact G obs K) :
    E.toWorkingMCFG.SemanticWorkingConditions := by
  exact E.concatExact.semanticWorkingConditions

/-- A recursive certificate gives tuple derivability in the generated grammar
shell. -/
theorem derives_node_tuple
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (E : SampleGeneratedRecursiveDerivationExact G obs K)
    {X : SampleGeneratedDecompositionNode E.ruleSkeleton.skeleton}
    (D : SampleGeneratedRecursiveDerivation (M := M) E.ruleSkeleton X) :
    DerivesTuple E.toWorkingMCFG
      (SampleGeneratedGrammarNonterminal.node X)
      X.decomposition.tuple := by
  exact D.derives_node_tuple (M := M)

/-- A recursive certificate generates the exposed middle word of its node. -/
theorem middle_mem_stringLanguage
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (E : SampleGeneratedRecursiveDerivationExact G obs K)
    {X : SampleGeneratedDecompositionNode E.ruleSkeleton.skeleton}
    (D : SampleGeneratedRecursiveDerivation (M := M) E.ruleSkeleton X) :
    X.decomposition.middle ∈ E.toWorkingMCFG.StringLanguage := by
  exact D.middle_mem_stringLanguage (M := M)

/-- Singleton-middle nodes are generated in the exact package. -/
theorem singleton_node_middle_mem_stringLanguage
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (E : SampleGeneratedRecursiveDerivationExact G obs K)
    {X : SampleGeneratedDecompositionNode E.ruleSkeleton.skeleton} {a : α}
    (hX : X ∈ E.ruleSkeleton.decompositionNodes)
    (hmid : X.decomposition.middle = [a]) :
    X.decomposition.middle ∈ E.toWorkingMCFG.StringLanguage := by
  exact FIv21.singleton_node_middle_mem_stringLanguage
    (M := M) E.ruleSkeleton hX hmid

end SampleGeneratedRecursiveDerivationExact

/-- Concrete exact package using the enumerated subword decomposition skeleton
and generated terminal/concat candidates. -/
noncomputable def enumeratedSampleGeneratedRecursiveDerivationExact
    (G : WorkingMCFG N α) (obs : α → M) (K : Finset (Word α))
    (f : Nat) (hfanout : 1 ≤ f) (hG : G.SemanticWorkingConditions) :
    SampleGeneratedRecursiveDerivationExact G obs K :=
  { concatExact :=
      enumeratedSampleGeneratedConcatEnumerationExact G obs K f hfanout hG }

/-- The concrete recursive-derivation generated output grammar is semantically
well-formed. -/
theorem enumeratedSampleGeneratedRecursiveDerivationExact_semantic
    (G : WorkingMCFG N α) (obs : α → M) (K : Finset (Word α))
    (f : Nat) (hfanout : 1 ≤ f) (hG : G.SemanticWorkingConditions) :
    (enumeratedSampleGeneratedRecursiveDerivationExact G obs K f hfanout hG)
      .toWorkingMCFG.SemanticWorkingConditions := by
  exact (enumeratedSampleGeneratedRecursiveDerivationExact
    G obs K f hfanout hG).semanticWorkingConditions

end SampleGeneratedRecursiveDerivationExact

end FIv21
