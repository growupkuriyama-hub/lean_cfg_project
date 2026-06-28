import LeanCfgProject.MCFG.FI_v2_1_SampleGeneratedWorkingGrammarDerivationGold

/-!
# FI v2.1 Lean experiment: terminal-rule enumeration from sample decompositions

The previous layers built an actual sample-generated `WorkingMCFG` shell and
proved that listed terminal/start/binary candidates feed into ordinary
`DerivesTuple` semantics.  This layer removes one remaining manual input: it
constructs terminal-rule candidates automatically from listed decomposition
nodes whose exposed middle is a singleton word.

This is still deliberately modest.  It handles the terminal/length-one case,
not the full recursive decomposition of arbitrary sample words.  Nevertheless,
for a sampled singleton word `[a]`, the enumerated package now contains both a
start candidate and a terminal candidate, and therefore derives `[a]` in the
sample-generated grammar shell.
-/

namespace FIv21

universe u v w

section SampleGeneratedTerminalEnumeration

variable {N : Type w} {α : Type u}
variable [DecidableEq α]
variable {M : Type v} [Monoid M] [Fintype M]

/-- Canonical terminal candidate attached to a decomposition node whose exposed
middle is exactly `[a]`. -/
def terminalCandidateOfSingletonNode
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {S : SampleGeneratedLearnerGrammarSkeleton G obs K}
    (X : SampleGeneratedDecompositionNode S) (a : α)
    (hmid : X.decomposition.middle = [a]) :
    SampleGeneratedTerminalCandidate S :=
  { node := X
    terminal := a
    middle_eq := hmid }

/-- Try to read a terminal candidate from a listed decomposition node.  The
candidate is produced exactly when the exposed middle has length one. -/
def terminalCandidateOfNode?
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {S : SampleGeneratedLearnerGrammarSkeleton G obs K}
    (X : SampleGeneratedDecompositionNode S) :
    Option (SampleGeneratedTerminalCandidate S) :=
  match hmid : X.decomposition.middle with
  | [a] => some (terminalCandidateOfSingletonNode (M := M) X a hmid)
  | _ => none

/-- If the exposed middle is `[a]`, the optional terminal-candidate extractor
returns the corresponding singleton candidate. -/
theorem terminalCandidateOfNode?_eq_some_of_middle_eq
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {S : SampleGeneratedLearnerGrammarSkeleton G obs K}
    (X : SampleGeneratedDecompositionNode S) {a : α}
    (hmid : X.decomposition.middle = [a]) :
    terminalCandidateOfNode? (M := M) X =
      some (terminalCandidateOfSingletonNode (M := M) X a hmid) := by
  cases hmid
  simp [terminalCandidateOfNode?, terminalCandidateOfSingletonNode]

/-- Terminal candidates obtained by scanning a finite list of decomposition
nodes. -/
def terminalCandidatesOfNodes
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {S : SampleGeneratedLearnerGrammarSkeleton G obs K}
    (Xs : List (SampleGeneratedDecompositionNode S)) :
    List (SampleGeneratedTerminalCandidate S) :=
  Xs.filterMap (terminalCandidateOfNode? (M := M))

/-- A listed singleton-middle node contributes its canonical terminal candidate
to the enumerated terminal-candidate list. -/
theorem terminalCandidate_mem_of_node_mem
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {S : SampleGeneratedLearnerGrammarSkeleton G obs K}
    {Xs : List (SampleGeneratedDecompositionNode S)}
    {X : SampleGeneratedDecompositionNode S} {a : α}
    (hX : X ∈ Xs) (hmid : X.decomposition.middle = [a]) :
    terminalCandidateOfSingletonNode (M := M) X a hmid ∈
      terminalCandidatesOfNodes (M := M) Xs := by
  unfold terminalCandidatesOfNodes
  exact List.mem_filterMap.mpr
    ⟨X, hX, terminalCandidateOfNode?_eq_some_of_middle_eq (M := M) X hmid⟩

namespace SampleGeneratedRuleSkeleton

/-- Automatically generated terminal candidates for a sample-generated rule
skeleton: scan all listed decomposition nodes and keep the singleton-middle
ones. -/
def generatedTerminalCandidates
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (R : SampleGeneratedRuleSkeleton G obs K) :
    List (SampleGeneratedTerminalCandidate R.skeleton) :=
  terminalCandidatesOfNodes (M := M) R.decompositionNodes

/-- A singleton-middle decomposition node contributes a generated terminal
candidate. -/
theorem generatedTerminalCandidate_mem_of_node_mem
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (R : SampleGeneratedRuleSkeleton G obs K)
    {X : SampleGeneratedDecompositionNode R.skeleton} {a : α}
    (hX : X ∈ R.decompositionNodes) (hmid : X.decomposition.middle = [a]) :
    terminalCandidateOfSingletonNode (M := M) X a hmid ∈
      R.generatedTerminalCandidates := by
  exact terminalCandidate_mem_of_node_mem (M := M) hX hmid

end SampleGeneratedRuleSkeleton

/-- A rule-list package in which terminal candidates are generated from the
listed decomposition nodes.  Binary concatenation candidates remain empty in
this layer; they are handled separately in the later concatenation-enumeration
layer. -/
noncomputable def terminalEnumeratedRuleListPackage
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (R : SampleGeneratedRuleSkeleton G obs K) :
    SampleGeneratedRuleListPackage G obs K :=
  { ruleSkeleton := R
    terminalCandidates := R.generatedTerminalCandidates (M := M)
    concatCandidates := [] }

namespace SampleGeneratedRuleListPackage

/-- The terminal-enumerated package contains the canonical terminal candidate
for every listed singleton-middle decomposition node. -/
theorem terminalEnumerated_terminalCandidate_mem
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (R : SampleGeneratedRuleSkeleton G obs K)
    {X : SampleGeneratedDecompositionNode R.skeleton} {a : α}
    (hX : X ∈ R.decompositionNodes) (hmid : X.decomposition.middle = [a]) :
    terminalCandidateOfSingletonNode (M := M) X a hmid ∈
      (terminalEnumeratedRuleListPackage (M := M) R).terminalCandidates := by
  exact R.generatedTerminalCandidate_mem_of_node_mem (M := M) hX hmid

/-- A listed singleton-middle decomposition node derives its exposed singleton
tuple in the terminal-enumerated grammar shell. -/
theorem terminalEnumerated_node_derives_singleton
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (R : SampleGeneratedRuleSkeleton G obs K)
    {X : SampleGeneratedDecompositionNode R.skeleton} {a : α}
    (hX : X ∈ R.decompositionNodes) (hmid : X.decomposition.middle = [a]) :
    DerivesTuple (terminalEnumeratedRuleListPackage (M := M) R).toWorkingMCFG
      (SampleGeneratedGrammarNonterminal.node X)
      (singletonTuple [a]) := by
  let C : SampleGeneratedTerminalCandidate R.skeleton :=
    terminalCandidateOfSingletonNode (M := M) X a hmid
  have hC : C ∈ (terminalEnumeratedRuleListPackage (M := M) R).terminalCandidates :=
    terminalEnumerated_terminalCandidate_mem (M := M) R hX hmid
  have hD : DerivesTuple (terminalEnumeratedRuleListPackage (M := M) R).toWorkingMCFG
      (SampleGeneratedGrammarNonterminal.node C.node)
      C.node.decomposition.tuple :=
    (terminalEnumeratedRuleListPackage (M := M) R)
      .terminalCandidate_derives_node_tuple (M := M) hC
  have hTuple : X.decomposition.tuple = singletonTuple [a] := by
    simp [SubwordSampleDecomposition.tuple, singletonTuple, hmid]
  simpa [C, terminalCandidateOfSingletonNode, hTuple] using hD

/-- A singleton sample word is generated by the terminal-enumerated grammar shell
because the whole-word decomposition supplies both the start candidate and the
terminal candidate. -/
theorem terminalEnumerated_singleton_sample_mem_stringLanguage
    (G : WorkingMCFG N α) (obs : α → M) (K : Finset (Word α))
    (f : Nat) (hfanout : 1 ≤ f) (hG : G.SemanticWorkingConditions)
    {a : α} (ha : ([a] : Word α) ∈ K) :
    ([a] : Word α) ∈
      (terminalEnumeratedRuleListPackage (M := M)
        (enumeratedSampleGeneratedRuleSkeleton G obs K f hfanout hG))
        .toWorkingMCFG.StringLanguage := by
  let R := enumeratedSampleGeneratedRuleSkeleton G obs K f hfanout hG
  let P := terminalEnumeratedRuleListPackage (M := M) R
  rcases exists_enumeratedSubwordDecomposition_of_mem (α := α) (K := K) ha with
    ⟨S, hS, _hWord, _hLeft, hMid, _hRight⟩
  let X : SampleGeneratedDecompositionNode R.skeleton :=
    { decomposition := S, mem := hS }
  have hX : X ∈ R.decompositionNodes := decompositionNode_mem_decompositionNodes R X
  let Cstart : SampleGeneratedStartCandidate R.skeleton := { node := X }
  have hStart : Cstart ∈ R.startCandidates := R.startCandidate_mem_of_node_mem hX
  have hNode : DerivesTuple P.toWorkingMCFG
      (SampleGeneratedGrammarNonterminal.node X)
      (singletonTuple ([a] : Word α)) := by
    exact terminalEnumerated_node_derives_singleton (M := M) R hX hMid
  exact P.mem_stringLanguage_of_startCandidate_node_derives
    (M := M) hStart hNode

end SampleGeneratedRuleListPackage

/-- Concrete terminal-enumerated rule-list package. -/
noncomputable def enumeratedTerminalRuleListPackage
    (G : WorkingMCFG N α) (obs : α → M) (K : Finset (Word α))
    (f : Nat) (hfanout : 1 ≤ f) (hG : G.SemanticWorkingConditions) :
    SampleGeneratedRuleListPackage G obs K :=
  terminalEnumeratedRuleListPackage (M := M)
    (enumeratedSampleGeneratedRuleSkeleton G obs K f hfanout hG)

/-- Singleton sample words are generated by the concrete terminal-enumerated
working grammar shell. -/
theorem enumeratedTerminalRuleListPackage_singleton_sample_mem_stringLanguage
    (G : WorkingMCFG N α) (obs : α → M) (K : Finset (Word α))
    (f : Nat) (hfanout : 1 ≤ f) (hG : G.SemanticWorkingConditions)
    {a : α} (ha : ([a] : Word α) ∈ K) :
    ([a] : Word α) ∈
      (enumeratedTerminalRuleListPackage G obs K f hfanout hG).toWorkingMCFG.StringLanguage := by
  exact SampleGeneratedRuleListPackage
    .terminalEnumerated_singleton_sample_mem_stringLanguage
      (M := M) G obs K f hfanout hG ha

end SampleGeneratedTerminalEnumeration

end FIv21
