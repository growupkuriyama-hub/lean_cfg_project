import LeanCfgProject.MCFG.FI_v2_1_SampleGeneratedWorkingGrammar

/-!
# FI v2.1 Lean experiment: exactness interface for sample-generated working grammar shells

This file packages the working-grammar shell from the previous layer with the
sample-side obligations that will later be proved from concrete rule generation.
It is still an interface layer, but now the interface is attached to an actual
`WorkingMCFG` shell rather than only to abstract candidate data.
-/

namespace FIv21

universe u v w

section SampleGeneratedWorkingGrammarExact

variable {N : Type w} {α : Type u}
variable [DecidableEq α]
variable {M : Type v} [Monoid M] [Fintype M]

/-- Exactness-facing package for a sample-generated working grammar shell.

The field `sampleStartCovered` records the current concrete guarantee: each
positive sample word has a start-rule candidate in the generated start-rule
list.  Later layers can strengthen this to actual derivability in the generated
`WorkingMCFG.StringLanguage`. -/
structure SampleGeneratedWorkingGrammarExact
    (G : WorkingMCFG N α) (obs : α → M) (K : Finset (Word α)) where
  ruleLists : SampleGeneratedRuleListPackage G obs K
  sampleStartCovered :
    ∀ {w : Word α}, w ∈ K →
      ∃ C : SampleGeneratedStartCandidate ruleLists.ruleSkeleton.skeleton,
        C ∈ ruleLists.ruleSkeleton.startCandidates ∧
        C.node.decomposition.sampleWord = w ∧
        startRuleOfCandidate (M := M) C ∈ ruleLists.startRules

namespace SampleGeneratedWorkingGrammarExact

/-- The concrete working grammar shell carried by an exactness-facing package. -/
noncomputable def toWorkingMCFG
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (E : SampleGeneratedWorkingGrammarExact G obs K) :
    WorkingMCFG (SampleGeneratedGrammarNonterminal E.ruleLists.ruleSkeleton.skeleton) α :=
  E.ruleLists.toWorkingMCFG

/-- The carried working grammar shell satisfies the basic syntactic working
conditions. -/
theorem basicWorkingConditions
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (E : SampleGeneratedWorkingGrammarExact G obs K) :
    E.toWorkingMCFG.BasicWorkingConditions := by
  exact E.ruleLists.toWorkingMCFG_basicWorkingConditions

/-- The package exposes the start-rule coverage statement for every sample word. -/
theorem startRule_exists_of_mem
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (E : SampleGeneratedWorkingGrammarExact G obs K)
    {w : Word α} (hw : w ∈ K) :
    ∃ C : SampleGeneratedStartCandidate E.ruleLists.ruleSkeleton.skeleton,
      C ∈ E.ruleLists.ruleSkeleton.startCandidates ∧
      C.node.decomposition.sampleWord = w ∧
      startRuleOfCandidate (M := M) C ∈ E.ruleLists.startRules := by
  exact E.sampleStartCovered hw

end SampleGeneratedWorkingGrammarExact

/-- Exactness-facing package obtained from the concrete enumerated rule-list
package.  At this stage terminal and binary rule candidates are still empty, but
start-rule coverage for every sample word is already proved. -/
noncomputable def enumeratedSampleGeneratedWorkingGrammarExact
    (G : WorkingMCFG N α) (obs : α → M) (K : Finset (Word α))
    (f : Nat) (hfanout : 1 ≤ f) (hG : G.SemanticWorkingConditions) :
    SampleGeneratedWorkingGrammarExact G obs K :=
  { ruleLists := enumeratedSampleGeneratedRuleListPackage G obs K f hfanout hG
    sampleStartCovered := by
      intro w hw
      exact enumeratedRuleListPackage_startRule_exists_of_mem
        G obs K f hfanout hG hw }

/-- The enumerated exact package carries a syntactically well-formed working
grammar shell. -/
theorem enumeratedSampleGeneratedWorkingGrammarExact_basic
    (G : WorkingMCFG N α) (obs : α → M) (K : Finset (Word α))
    (f : Nat) (hfanout : 1 ≤ f) (hG : G.SemanticWorkingConditions) :
    (enumeratedSampleGeneratedWorkingGrammarExact G obs K f hfanout hG)
      .toWorkingMCFG.BasicWorkingConditions := by
  exact (enumeratedSampleGeneratedWorkingGrammarExact G obs K f hfanout hG)
    .basicWorkingConditions

end SampleGeneratedWorkingGrammarExact

end FIv21
