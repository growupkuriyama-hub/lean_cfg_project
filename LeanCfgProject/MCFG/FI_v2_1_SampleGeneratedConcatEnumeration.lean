import LeanCfgProject.MCFG.FI_v2_1_SampleGeneratedTerminalEnumerationGold

/-!
# FI v2.1 Lean experiment: binary-concatenation enumeration for sample-generated grammars

The previous terminal-enumeration layer generated terminal candidates from listed
sample decompositions whose exposed middle is a singleton word.  This file adds
the next constructive step: generate binary-concatenation candidates from listed
decomposition nodes whenever the exposed middle of one node is the concatenation
of the exposed middles of two other nodes.

The construction is still intentionally local and conservative.  It does not yet
prove that every nonempty sample word has a complete parse tree.  Instead, it
builds the finite candidate list and proves the key membership and derivation
bridge: if the two child nodes are derivable, then the listed concatenation
candidate derives the result node in the generated `WorkingMCFG` shell.
-/

namespace FIv21

universe u v w

section SampleGeneratedConcatEnumeration

variable {N : Type w} {α : Type u}
variable [DecidableEq α]
variable {M : Type v} [Monoid M] [Fintype M]

/-- Canonical binary-concatenation candidate attached to three listed
subword-decomposition nodes whose exposed middles satisfy
`result.middle = left.middle ++ right.middle`. -/
def concatCandidateOfMiddleEq
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {S : SampleGeneratedLearnerGrammarSkeleton G obs K}
    (left right result : SampleGeneratedDecompositionNode S)
    (hmid : result.decomposition.middle =
      left.decomposition.middle ++ right.decomposition.middle) :
    SampleGeneratedConcatCandidate S :=
  { left := left
    right := right
    result := result
    middle_eq := hmid }

/-- Try to generate a binary-concatenation candidate from an ordered triple of
listed decomposition nodes. -/
def concatCandidateOfTriple?
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {S : SampleGeneratedLearnerGrammarSkeleton G obs K}
    (left right result : SampleGeneratedDecompositionNode S) :
    Option (SampleGeneratedConcatCandidate S) :=
  if hmid : result.decomposition.middle =
      left.decomposition.middle ++ right.decomposition.middle then
    some (concatCandidateOfMiddleEq (M := M) left right result hmid)
  else
    none

/-- If the exposed-middle equality holds, the optional extractor returns the
canonical concatenation candidate. -/
theorem concatCandidateOfTriple?_eq_some_of_middle_eq
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {S : SampleGeneratedLearnerGrammarSkeleton G obs K}
    (left right result : SampleGeneratedDecompositionNode S)
    (hmid : result.decomposition.middle =
      left.decomposition.middle ++ right.decomposition.middle) :
    concatCandidateOfTriple? (M := M) left right result =
      some (concatCandidateOfMiddleEq (M := M) left right result hmid) := by
  unfold concatCandidateOfTriple?
  simp [hmid, concatCandidateOfMiddleEq]

/-- Binary-concatenation candidates obtained by scanning all ordered triples of
listed decomposition nodes. -/
def concatCandidatesOfNodes
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {S : SampleGeneratedLearnerGrammarSkeleton G obs K}
    (Xs : List (SampleGeneratedDecompositionNode S)) :
    List (SampleGeneratedConcatCandidate S) :=
  Xs.bind (fun left =>
    Xs.bind (fun right =>
      Xs.filterMap (fun result =>
        concatCandidateOfTriple? (M := M) left right result)))

/-- Any listed triple satisfying the exposed-middle equality contributes the
corresponding concatenation candidate to the generated list. -/
theorem concatCandidate_mem_of_nodes_mem
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {S : SampleGeneratedLearnerGrammarSkeleton G obs K}
    {Xs : List (SampleGeneratedDecompositionNode S)}
    {left right result : SampleGeneratedDecompositionNode S}
    (hLeft : left ∈ Xs) (hRight : right ∈ Xs) (hResult : result ∈ Xs)
    (hmid : result.decomposition.middle =
      left.decomposition.middle ++ right.decomposition.middle) :
    concatCandidateOfMiddleEq (M := M) left right result hmid ∈
      concatCandidatesOfNodes (M := M) Xs := by
  unfold concatCandidatesOfNodes
  exact List.mem_bind.mpr
    ⟨left, hLeft,
      List.mem_bind.mpr
        ⟨right, hRight,
          List.mem_filterMap.mpr
            ⟨result, hResult,
              concatCandidateOfTriple?_eq_some_of_middle_eq
                (M := M) left right result hmid⟩⟩⟩

namespace SampleGeneratedRuleSkeleton

/-- Automatically generated binary-concatenation candidates for a
sample-generated rule skeleton: scan all ordered triples of listed decomposition
nodes and keep the triples whose exposed middles concatenate. -/
def generatedConcatCandidates
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (R : SampleGeneratedRuleSkeleton G obs K) :
    List (SampleGeneratedConcatCandidate R.skeleton) :=
  concatCandidatesOfNodes (M := M) R.decompositionNodes

/-- A listed triple of decomposition nodes satisfying the exposed-middle
equality contributes a generated concatenation candidate. -/
theorem generatedConcatCandidate_mem_of_nodes_mem
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (R : SampleGeneratedRuleSkeleton G obs K)
    {left right result : SampleGeneratedDecompositionNode R.skeleton}
    (hLeft : left ∈ R.decompositionNodes)
    (hRight : right ∈ R.decompositionNodes)
    (hResult : result ∈ R.decompositionNodes)
    (hmid : result.decomposition.middle =
      left.decomposition.middle ++ right.decomposition.middle) :
    concatCandidateOfMiddleEq (M := M) left right result hmid ∈
      R.generatedConcatCandidates := by
  exact concatCandidate_mem_of_nodes_mem (M := M) hLeft hRight hResult hmid

end SampleGeneratedRuleSkeleton

/-- A rule-list package in which terminal candidates are generated from
singleton-middle nodes and binary-concatenation candidates are generated from
middle-concatenating triples of nodes. -/
noncomputable def terminalConcatEnumeratedRuleListPackage
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (R : SampleGeneratedRuleSkeleton G obs K) :
    SampleGeneratedRuleListPackage G obs K :=
  { ruleSkeleton := R
    terminalCandidates := R.generatedTerminalCandidates (M := M)
    concatCandidates := R.generatedConcatCandidates (M := M) }

namespace SampleGeneratedRuleListPackage

/-- The terminal+concat-enumerated package contains the canonical terminal
candidate for every listed singleton-middle decomposition node. -/
theorem terminalConcatEnumerated_terminalCandidate_mem
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (R : SampleGeneratedRuleSkeleton G obs K)
    {X : SampleGeneratedDecompositionNode R.skeleton} {a : α}
    (hX : X ∈ R.decompositionNodes) (hmid : X.decomposition.middle = [a]) :
    terminalCandidateOfSingletonNode (M := M) X a hmid ∈
      (terminalConcatEnumeratedRuleListPackage (M := M) R).terminalCandidates := by
  exact R.generatedTerminalCandidate_mem_of_node_mem (M := M) hX hmid

/-- The terminal+concat-enumerated package contains the canonical concatenation
candidate for every listed middle-concatenating triple of decomposition nodes. -/
theorem terminalConcatEnumerated_concatCandidate_mem
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (R : SampleGeneratedRuleSkeleton G obs K)
    {left right result : SampleGeneratedDecompositionNode R.skeleton}
    (hLeft : left ∈ R.decompositionNodes)
    (hRight : right ∈ R.decompositionNodes)
    (hResult : result ∈ R.decompositionNodes)
    (hmid : result.decomposition.middle =
      left.decomposition.middle ++ right.decomposition.middle) :
    concatCandidateOfMiddleEq (M := M) left right result hmid ∈
      (terminalConcatEnumeratedRuleListPackage (M := M) R).concatCandidates := by
  exact R.generatedConcatCandidate_mem_of_nodes_mem
    (M := M) hLeft hRight hResult hmid

/-- If two listed child nodes are already derivable, the generated
middle-concatenation candidate derives the listed result node. -/
theorem terminalConcatEnumerated_binary_derives_result_tuple
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (R : SampleGeneratedRuleSkeleton G obs K)
    {left right result : SampleGeneratedDecompositionNode R.skeleton}
    (hLeft : left ∈ R.decompositionNodes)
    (hRight : right ∈ R.decompositionNodes)
    (hResult : result ∈ R.decompositionNodes)
    (hmid : result.decomposition.middle =
      left.decomposition.middle ++ right.decomposition.middle)
    (hDL : DerivesTuple (terminalConcatEnumeratedRuleListPackage (M := M) R).toWorkingMCFG
      (SampleGeneratedGrammarNonterminal.node left) left.decomposition.tuple)
    (hDR : DerivesTuple (terminalConcatEnumeratedRuleListPackage (M := M) R).toWorkingMCFG
      (SampleGeneratedGrammarNonterminal.node right) right.decomposition.tuple) :
    DerivesTuple (terminalConcatEnumeratedRuleListPackage (M := M) R).toWorkingMCFG
      (SampleGeneratedGrammarNonterminal.node result) result.decomposition.tuple := by
  let C : SampleGeneratedConcatCandidate R.skeleton :=
    concatCandidateOfMiddleEq (M := M) left right result hmid
  have hC : C ∈ (terminalConcatEnumeratedRuleListPackage (M := M) R).concatCandidates :=
    terminalConcatEnumerated_concatCandidate_mem
      (M := M) R hLeft hRight hResult hmid
  exact (terminalConcatEnumeratedRuleListPackage (M := M) R)
    .binaryCandidate_derives_result_tuple (M := M) hC hDL hDR

/-- A listed singleton-middle node still derives its exposed singleton tuple in
the terminal+concat-enumerated grammar shell. -/
theorem terminalConcatEnumerated_node_derives_singleton
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (R : SampleGeneratedRuleSkeleton G obs K)
    {X : SampleGeneratedDecompositionNode R.skeleton} {a : α}
    (hX : X ∈ R.decompositionNodes) (hmid : X.decomposition.middle = [a]) :
    DerivesTuple (terminalConcatEnumeratedRuleListPackage (M := M) R).toWorkingMCFG
      (SampleGeneratedGrammarNonterminal.node X)
      (singletonTuple [a]) := by
  let C : SampleGeneratedTerminalCandidate R.skeleton :=
    terminalCandidateOfSingletonNode (M := M) X a hmid
  have hC : C ∈ (terminalConcatEnumeratedRuleListPackage (M := M) R).terminalCandidates :=
    terminalConcatEnumerated_terminalCandidate_mem (M := M) R hX hmid
  have hD : DerivesTuple (terminalConcatEnumeratedRuleListPackage (M := M) R).toWorkingMCFG
      (SampleGeneratedGrammarNonterminal.node C.node)
      C.node.decomposition.tuple :=
    (terminalConcatEnumeratedRuleListPackage (M := M) R)
      .terminalCandidate_derives_node_tuple (M := M) hC
  have hTuple : X.decomposition.tuple = singletonTuple [a] := by
    simp [SubwordSampleDecomposition.tuple, singletonTuple, hmid]
  simpa [C, terminalCandidateOfSingletonNode, hTuple] using hD

/-- If two singleton child nodes and a listed concatenation result node are
present, then the result node derives the concatenated singleton tuple. -/
theorem terminalConcatEnumerated_two_singletons_derive_result
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (R : SampleGeneratedRuleSkeleton G obs K)
    {left right result : SampleGeneratedDecompositionNode R.skeleton}
    {a b : α}
    (hLeft : left ∈ R.decompositionNodes)
    (hRight : right ∈ R.decompositionNodes)
    (hResult : result ∈ R.decompositionNodes)
    (hLeftMid : left.decomposition.middle = [a])
    (hRightMid : right.decomposition.middle = [b])
    (hResultMid : result.decomposition.middle = [a] ++ [b])
    (hmid : result.decomposition.middle =
      left.decomposition.middle ++ right.decomposition.middle) :
    DerivesTuple (terminalConcatEnumeratedRuleListPackage (M := M) R).toWorkingMCFG
      (SampleGeneratedGrammarNonterminal.node result)
      (singletonTuple ([a] ++ [b])) := by
  have hDL : DerivesTuple (terminalConcatEnumeratedRuleListPackage (M := M) R).toWorkingMCFG
      (SampleGeneratedGrammarNonterminal.node left)
      left.decomposition.tuple := by
    have hD := terminalConcatEnumerated_node_derives_singleton
      (M := M) R hLeft hLeftMid
    have hTuple : left.decomposition.tuple = singletonTuple [a] := by
      simp [SubwordSampleDecomposition.tuple, singletonTuple, hLeftMid]
    simpa [hTuple] using hD
  have hDR : DerivesTuple (terminalConcatEnumeratedRuleListPackage (M := M) R).toWorkingMCFG
      (SampleGeneratedGrammarNonterminal.node right)
      right.decomposition.tuple := by
    have hD := terminalConcatEnumerated_node_derives_singleton
      (M := M) R hRight hRightMid
    have hTuple : right.decomposition.tuple = singletonTuple [b] := by
      simp [SubwordSampleDecomposition.tuple, singletonTuple, hRightMid]
    simpa [hTuple] using hD
  have hDres := terminalConcatEnumerated_binary_derives_result_tuple
    (M := M) R hLeft hRight hResult hmid hDL hDR
  have hTupleRes : result.decomposition.tuple = singletonTuple ([a] ++ [b]) := by
    simp [SubwordSampleDecomposition.tuple, singletonTuple, hResultMid]
  simpa [hTupleRes] using hDres

/-- If the concatenation result node is also listed as a start candidate, the
terminal+concat-enumerated grammar shell generates the concatenated word. -/
theorem terminalConcatEnumerated_two_singletons_mem_stringLanguage
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (R : SampleGeneratedRuleSkeleton G obs K)
    {left right result : SampleGeneratedDecompositionNode R.skeleton}
    {a b : α}
    (hLeft : left ∈ R.decompositionNodes)
    (hRight : right ∈ R.decompositionNodes)
    (hResult : result ∈ R.decompositionNodes)
    (hLeftMid : left.decomposition.middle = [a])
    (hRightMid : right.decomposition.middle = [b])
    (hResultMid : result.decomposition.middle = [a] ++ [b])
    (hmid : result.decomposition.middle =
      left.decomposition.middle ++ right.decomposition.middle) :
    ([a] ++ [b] : Word α) ∈
      (terminalConcatEnumeratedRuleListPackage (M := M) R).toWorkingMCFG.StringLanguage := by
  let Cstart : SampleGeneratedStartCandidate R.skeleton := { node := result }
  have hStart : Cstart ∈ R.startCandidates := by
    exact R.startCandidate_mem_of_node_mem hResult
  have hNode : DerivesTuple (terminalConcatEnumeratedRuleListPackage (M := M) R).toWorkingMCFG
      (SampleGeneratedGrammarNonterminal.node result)
      (singletonTuple ([a] ++ [b])) :=
    terminalConcatEnumerated_two_singletons_derive_result
      (M := M) R hLeft hRight hResult hLeftMid hRightMid hResultMid hmid
  exact (terminalConcatEnumeratedRuleListPackage (M := M) R)
    .mem_stringLanguage_of_startCandidate_node_derives (M := M) hStart hNode

end SampleGeneratedRuleListPackage

/-- Concrete terminal+concat-enumerated rule-list package. -/
noncomputable def enumeratedTerminalConcatRuleListPackage
    (G : WorkingMCFG N α) (obs : α → M) (K : Finset (Word α))
    (f : Nat) (hfanout : 1 ≤ f) (hG : G.SemanticWorkingConditions) :
    SampleGeneratedRuleListPackage G obs K :=
  terminalConcatEnumeratedRuleListPackage (M := M)
    (enumeratedSampleGeneratedRuleSkeleton G obs K f hfanout hG)

/-- The concrete terminal+concat-enumerated grammar shell is semantically
well-formed. -/
theorem enumeratedTerminalConcatRuleListPackage_semantic
    (G : WorkingMCFG N α) (obs : α → M) (K : Finset (Word α))
    (f : Nat) (hfanout : 1 ≤ f) (hG : G.SemanticWorkingConditions) :
    (enumeratedTerminalConcatRuleListPackage G obs K f hfanout hG)
      .toWorkingMCFG.SemanticWorkingConditions := by
  exact (enumeratedTerminalConcatRuleListPackage G obs K f hfanout hG)
    .toWorkingMCFG_semanticWorkingConditions

end SampleGeneratedConcatEnumeration

end FIv21
