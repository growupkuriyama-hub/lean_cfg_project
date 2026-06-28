import LeanCfgProject.MCFG.FI_v2_1_SampleGeneratedConcatEnumeration

/-!
# FI v2.1 Lean experiment: exact package for terminal+concat generated grammars

This layer packages the generated terminal and binary-concatenation candidate
enumerators.  It exposes the resulting `WorkingMCFG` shell and the main local
exactness bridge: listed singleton child nodes and a listed middle-concatenation
result node give a generated word in the shell's string language.
-/

namespace FIv21

universe u v w

section SampleGeneratedConcatEnumerationExact

variable {N : Type w} {α : Type u}
variable [DecidableEq α]
variable {M : Type v} [Monoid M] [Fintype M]

/-- Exact package for terminal+concat-enumerated generated working grammars. -/
structure SampleGeneratedConcatEnumerationExact
    (G : WorkingMCFG N α) (obs : α → M) (K : Finset (Word α)) where
  ruleSkeleton : SampleGeneratedRuleSkeleton G obs K

namespace SampleGeneratedConcatEnumerationExact

/-- The terminal+concat-enumerated rule-list package. -/
noncomputable def ruleLists
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (E : SampleGeneratedConcatEnumerationExact G obs K) :
    SampleGeneratedRuleListPackage G obs K :=
  terminalConcatEnumeratedRuleListPackage (M := M) E.ruleSkeleton

/-- The generated working grammar shell. -/
noncomputable def toWorkingMCFG
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (E : SampleGeneratedConcatEnumerationExact G obs K) :
    WorkingMCFG (SampleGeneratedGrammarNonterminal
      E.ruleLists.ruleSkeleton.skeleton) α :=
  E.ruleLists.toWorkingMCFG

/-- The terminal+concat-enumerated grammar shell satisfies semantic working
conditions. -/
theorem semanticWorkingConditions
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (E : SampleGeneratedConcatEnumerationExact G obs K) :
    E.toWorkingMCFG.SemanticWorkingConditions := by
  exact E.ruleLists.toWorkingMCFG_semanticWorkingConditions

/-- Local two-singleton generation theorem inside the exact package. -/
theorem two_singletons_mem_stringLanguage
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (E : SampleGeneratedConcatEnumerationExact G obs K)
    {left right result : SampleGeneratedDecompositionNode E.ruleSkeleton.skeleton}
    {a b : α}
    (hLeft : left ∈ E.ruleSkeleton.decompositionNodes)
    (hRight : right ∈ E.ruleSkeleton.decompositionNodes)
    (hResult : result ∈ E.ruleSkeleton.decompositionNodes)
    (hLeftMid : left.decomposition.middle = [a])
    (hRightMid : right.decomposition.middle = [b])
    (hResultMid : result.decomposition.middle = [a] ++ [b])
    (hmid : result.decomposition.middle =
      left.decomposition.middle ++ right.decomposition.middle) :
    ([a] ++ [b] : Word α) ∈ E.toWorkingMCFG.StringLanguage := by
  exact SampleGeneratedRuleListPackage
    .terminalConcatEnumerated_two_singletons_mem_stringLanguage
      (M := M) E.ruleSkeleton hLeft hRight hResult
      hLeftMid hRightMid hResultMid hmid

end SampleGeneratedConcatEnumerationExact

/-- Concrete exact package using the enumerated subword decomposition skeleton
and generated terminal/concat candidates. -/
noncomputable def enumeratedSampleGeneratedConcatEnumerationExact
    (G : WorkingMCFG N α) (obs : α → M) (K : Finset (Word α))
    (f : Nat) (hfanout : 1 ≤ f) (hG : G.SemanticWorkingConditions) :
    SampleGeneratedConcatEnumerationExact G obs K :=
  { ruleSkeleton := enumeratedSampleGeneratedRuleSkeleton G obs K f hfanout hG }

/-- The concrete terminal+concat-enumerated output grammar is semantically
well-formed. -/
theorem enumeratedSampleGeneratedConcatEnumerationExact_semantic
    (G : WorkingMCFG N α) (obs : α → M) (K : Finset (Word α))
    (f : Nat) (hfanout : 1 ≤ f) (hG : G.SemanticWorkingConditions) :
    (enumeratedSampleGeneratedConcatEnumerationExact G obs K f hfanout hG)
      .toWorkingMCFG.SemanticWorkingConditions := by
  exact (enumeratedSampleGeneratedConcatEnumerationExact
    G obs K f hfanout hG).semanticWorkingConditions

end SampleGeneratedConcatEnumerationExact

end FIv21
