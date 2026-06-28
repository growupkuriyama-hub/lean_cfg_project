import LeanCfgProject.MCFG.FI_v2_1_SampleGeneratedWorkingGrammarDerivation

/-!
# FI v2.1 Lean experiment: exactness package for generated working-grammar derivations

This file packages the derivation-facing lemmas for the sample-generated
`WorkingMCFG` shell.  It does not yet assert that all positive sample words are
derived automatically; rather, it isolates the exact remaining local obligation:
show that the node reached by a generated start rule derives the desired
singleton tuple.
-/

namespace FIv21

universe u v w

section SampleGeneratedWorkingGrammarDerivationExact

variable {N : Type w} {α : Type u}
variable [DecidableEq α]
variable {M : Type v} [Monoid M] [Fintype M]

/-- Derivation-facing exact package for the sample-generated working grammar
shell. -/
structure SampleGeneratedWorkingGrammarDerivationExact
    (G : WorkingMCFG N α) (obs : α → M) (K : Finset (Word α)) where
  working : SampleGeneratedWorkingGrammarExact G obs K

namespace SampleGeneratedWorkingGrammarDerivationExact

/-- The rule-list package carried by the derivation-facing exact package. -/
noncomputable def ruleLists
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (E : SampleGeneratedWorkingGrammarDerivationExact G obs K) :
    SampleGeneratedRuleListPackage G obs K :=
  E.working.ruleLists

/-- The concrete generated working grammar shell. -/
noncomputable def toWorkingMCFG
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (E : SampleGeneratedWorkingGrammarDerivationExact G obs K) :
    WorkingMCFG (SampleGeneratedGrammarNonterminal E.ruleLists.ruleSkeleton.skeleton) α :=
  E.working.toWorkingMCFG

/-- The generated grammar shell satisfies the semantic working conditions of the
current derivation layer. -/
theorem semanticWorkingConditions
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (E : SampleGeneratedWorkingGrammarDerivationExact G obs K) :
    E.toWorkingMCFG.SemanticWorkingConditions := by
  exact E.ruleLists.toWorkingMCFG_semanticWorkingConditions

/-- Listed terminal candidates derive their exposed singleton tuples. -/
theorem terminalCandidate_derives_node_tuple
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (E : SampleGeneratedWorkingGrammarDerivationExact G obs K)
    {C : SampleGeneratedTerminalCandidate E.ruleLists.ruleSkeleton.skeleton}
    (hC : C ∈ E.ruleLists.terminalCandidates) :
    DerivesTuple E.toWorkingMCFG
      (SampleGeneratedGrammarNonterminal.node C.node)
      C.node.decomposition.tuple := by
  exact E.ruleLists.terminalCandidate_derives_node_tuple (M := M) hC

/-- Listed binary-concatenation candidates derive their result tuple once their
children are derived. -/
theorem binaryCandidate_derives_result_tuple
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (E : SampleGeneratedWorkingGrammarDerivationExact G obs K)
    {C : SampleGeneratedConcatCandidate E.ruleLists.ruleSkeleton.skeleton}
    (hC : C ∈ E.ruleLists.concatCandidates)
    (hLeft : DerivesTuple E.toWorkingMCFG
      (SampleGeneratedGrammarNonterminal.node C.left)
      C.left.decomposition.tuple)
    (hRight : DerivesTuple E.toWorkingMCFG
      (SampleGeneratedGrammarNonterminal.node C.right)
      C.right.decomposition.tuple) :
    DerivesTuple E.toWorkingMCFG
      (SampleGeneratedGrammarNonterminal.node C.result)
      C.result.decomposition.tuple := by
  exact E.ruleLists.binaryCandidate_derives_result_tuple (M := M)
    hC hLeft hRight

/-- A generated start candidate lifts a child-node derivation to the generated
root. -/
theorem startCandidate_lifts_node_derivation
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (E : SampleGeneratedWorkingGrammarDerivationExact G obs K)
    {C : SampleGeneratedStartCandidate E.ruleLists.ruleSkeleton.skeleton}
    (hC : C ∈ E.ruleLists.ruleSkeleton.startCandidates)
    {x : Tuple α 1}
    (hx : DerivesTuple E.toWorkingMCFG
      (SampleGeneratedGrammarNonterminal.node C.node) x) :
    DerivesTuple E.toWorkingMCFG SampleGeneratedGrammarNonterminal.root x := by
  exact E.ruleLists.startCandidate_lifts_node_derivation (M := M) hC hx

/-- Conditional sample-word generation: once the start candidate's child node
derives the singleton tuple for `w`, the generated grammar shell derives `w`. -/
theorem sample_word_mem_stringLanguage_of_node_derives
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (E : SampleGeneratedWorkingGrammarDerivationExact G obs K)
    {C : SampleGeneratedStartCandidate E.ruleLists.ruleSkeleton.skeleton}
    (hC : C ∈ E.ruleLists.ruleSkeleton.startCandidates)
    {w : Word α}
    (hw : DerivesTuple E.toWorkingMCFG
      (SampleGeneratedGrammarNonterminal.node C.node)
      (singletonTuple w)) :
    w ∈ E.toWorkingMCFG.StringLanguage := by
  exact E.ruleLists.mem_stringLanguage_of_startCandidate_node_derives
    (M := M) hC hw

/-- The underlying start-rule coverage statement from the previous exact layer. -/
theorem startRule_exists_of_mem
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (E : SampleGeneratedWorkingGrammarDerivationExact G obs K)
    {w : Word α} (hw : w ∈ K) :
    ∃ C : SampleGeneratedStartCandidate E.ruleLists.ruleSkeleton.skeleton,
      C ∈ E.ruleLists.ruleSkeleton.startCandidates ∧
      C.node.decomposition.sampleWord = w ∧
      startRuleOfCandidate (M := M) C ∈ E.ruleLists.startRules := by
  exact E.working.startRule_exists_of_mem hw

end SampleGeneratedWorkingGrammarDerivationExact

/-- Concrete enumerated derivation-facing exact package. -/
noncomputable def enumeratedSampleGeneratedWorkingGrammarDerivationExact
    (G : WorkingMCFG N α) (obs : α → M) (K : Finset (Word α))
    (f : Nat) (hfanout : 1 ≤ f) (hG : G.SemanticWorkingConditions) :
    SampleGeneratedWorkingGrammarDerivationExact G obs K :=
  { working := enumeratedSampleGeneratedWorkingGrammarExact G obs K f hfanout hG }

/-- The enumerated derivation-facing grammar shell is semantically well-formed. -/
theorem enumeratedSampleGeneratedWorkingGrammarDerivationExact_semantic
    (G : WorkingMCFG N α) (obs : α → M) (K : Finset (Word α))
    (f : Nat) (hfanout : 1 ≤ f) (hG : G.SemanticWorkingConditions) :
    (enumeratedSampleGeneratedWorkingGrammarDerivationExact G obs K f hfanout hG)
      .toWorkingMCFG.SemanticWorkingConditions := by
  exact (enumeratedSampleGeneratedWorkingGrammarDerivationExact
    G obs K f hfanout hG).semanticWorkingConditions

end SampleGeneratedWorkingGrammarDerivationExact

end FIv21
