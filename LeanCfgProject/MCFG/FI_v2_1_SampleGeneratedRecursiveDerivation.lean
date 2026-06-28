import LeanCfgProject.MCFG.FI_v2_1_SampleGeneratedConcatEnumerationGold

/-!
# FI v2.1 Lean experiment: recursive derivations for sample-generated grammars

The previous layer generated terminal candidates from singleton-middle nodes and
binary-concatenation candidates from triples of listed subword-decomposition
nodes.  This file adds the next derivation-facing layer: a finite parse-tree
certificate whose leaves are generated terminal candidates and whose internal
nodes are generated concatenation candidates.

The main theorem states that every such recursive certificate yields an ordinary
`DerivesTuple` derivation in the terminal+concat generated `WorkingMCFG` shell,
and hence, after applying the generated start rule, the exposed middle word lies
in the generated grammar's string language.
-/

namespace FIv21

universe u v w

section SampleGeneratedRecursiveDerivation

variable {N : Type w} {α : Type u}
variable [DecidableEq α]
variable {M : Type v} [Monoid M] [Fintype M]

/-- Recursive derivation certificate for a listed sample-generated decomposition
node.  A certificate is either a singleton terminal leaf, or a binary
concatenation step combining two already-certified child nodes whose exposed
middles concatenate to the result node's exposed middle.

This is still a certificate over the generated rule skeleton, not a claim that
all sample words automatically have such a certificate. -/
inductive SampleGeneratedRecursiveDerivation
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (R : SampleGeneratedRuleSkeleton G obs K) :
    SampleGeneratedDecompositionNode R.skeleton → Prop where
  | terminal
      {X : SampleGeneratedDecompositionNode R.skeleton} {a : α}
      (hX : X ∈ R.decompositionNodes)
      (hmid : X.decomposition.middle = [a]) :
      SampleGeneratedRecursiveDerivation R X
  | concat
      {left right result : SampleGeneratedDecompositionNode R.skeleton}
      (hLeft : left ∈ R.decompositionNodes)
      (hRight : right ∈ R.decompositionNodes)
      (hResult : result ∈ R.decompositionNodes)
      (hmid : result.decomposition.middle =
        left.decomposition.middle ++ right.decomposition.middle)
      (hDL : SampleGeneratedRecursiveDerivation R left)
      (hDR : SampleGeneratedRecursiveDerivation R right) :
      SampleGeneratedRecursiveDerivation R result

namespace SampleGeneratedRecursiveDerivation

/-- The target node of a recursive certificate is listed by the rule skeleton. -/
theorem node_mem
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {R : SampleGeneratedRuleSkeleton G obs K}
    {X : SampleGeneratedDecompositionNode R.skeleton}
    (D : SampleGeneratedRecursiveDerivation (M := M) R X) :
    X ∈ R.decompositionNodes := by
  cases D with
  | terminal hX _ => exact hX
  | concat _ _ hResult _ _ _ => exact hResult

/-- The exposed tuple of a listed subword-decomposition node is the singleton
tuple of its exposed middle word. -/
theorem node_tuple_eq_singleton_middle
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {R : SampleGeneratedRuleSkeleton G obs K}
    (X : SampleGeneratedDecompositionNode R.skeleton) :
    X.decomposition.tuple = singletonTuple X.decomposition.middle := by
  simp [SubwordSampleDecomposition.tuple, singletonTuple]

/-- A recursive certificate yields an ordinary tuple derivation of the node's
exposed tuple in the terminal+concat generated grammar shell. -/
theorem derives_node_tuple
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {R : SampleGeneratedRuleSkeleton G obs K}
    {X : SampleGeneratedDecompositionNode R.skeleton}
    (D : SampleGeneratedRecursiveDerivation (M := M) R X) :
    DerivesTuple (terminalConcatEnumeratedRuleListPackage (M := M) R).toWorkingMCFG
      (SampleGeneratedGrammarNonterminal.node X)
      X.decomposition.tuple := by
  induction D with
  | terminal hX hmid =>
      have hD := SampleGeneratedRuleListPackage
        .terminalConcatEnumerated_node_derives_singleton
          (M := M) R hX hmid
      simpa [SubwordSampleDecomposition.tuple, singletonTuple, hmid] using hD
  | concat hLeft hRight hResult hmid _ _ ihLeft ihRight =>
      exact SampleGeneratedRuleListPackage
        .terminalConcatEnumerated_binary_derives_result_tuple
          (M := M) R hLeft hRight hResult hmid ihLeft ihRight

/-- A recursive certificate also yields a derivation of the singleton tuple of
the node's exposed middle word. -/
theorem derives_singleton_middle
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {R : SampleGeneratedRuleSkeleton G obs K}
    {X : SampleGeneratedDecompositionNode R.skeleton}
    (D : SampleGeneratedRecursiveDerivation (M := M) R X) :
    DerivesTuple (terminalConcatEnumeratedRuleListPackage (M := M) R).toWorkingMCFG
      (SampleGeneratedGrammarNonterminal.node X)
      (singletonTuple X.decomposition.middle) := by
  have hD := D.derives_node_tuple (M := M)
  have hTuple : X.decomposition.tuple = singletonTuple X.decomposition.middle :=
    node_tuple_eq_singleton_middle (M := M) X
  simpa [hTuple] using hD

/-- Applying the generated start rule to a recursively derived node puts the
node's exposed middle in the generated grammar's string language. -/
theorem middle_mem_stringLanguage
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {R : SampleGeneratedRuleSkeleton G obs K}
    {X : SampleGeneratedDecompositionNode R.skeleton}
    (D : SampleGeneratedRecursiveDerivation (M := M) R X) :
    X.decomposition.middle ∈
      (terminalConcatEnumeratedRuleListPackage (M := M) R).toWorkingMCFG.StringLanguage := by
  let Cstart : SampleGeneratedStartCandidate R.skeleton := { node := X }
  have hStart : Cstart ∈ R.startCandidates := by
    exact R.startCandidate_mem_of_node_mem D.node_mem
  have hNode : DerivesTuple
      (terminalConcatEnumeratedRuleListPackage (M := M) R).toWorkingMCFG
      (SampleGeneratedGrammarNonterminal.node X)
      (singletonTuple X.decomposition.middle) :=
    D.derives_singleton_middle (M := M)
  exact (terminalConcatEnumeratedRuleListPackage (M := M) R)
    .mem_stringLanguage_of_startCandidate_node_derives (M := M) hStart hNode

end SampleGeneratedRecursiveDerivation

/-- Convenience theorem: a listed singleton-middle node has a recursive
certificate and therefore its exposed middle is generated by the grammar shell. -/
theorem singleton_node_middle_mem_stringLanguage
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (R : SampleGeneratedRuleSkeleton G obs K)
    {X : SampleGeneratedDecompositionNode R.skeleton} {a : α}
    (hX : X ∈ R.decompositionNodes)
    (hmid : X.decomposition.middle = [a]) :
    X.decomposition.middle ∈
      (terminalConcatEnumeratedRuleListPackage (M := M) R).toWorkingMCFG.StringLanguage := by
  exact (SampleGeneratedRecursiveDerivation.terminal
    (R := R) (M := M) hX hmid).middle_mem_stringLanguage (M := M)

/-- Convenience theorem: if two certified child nodes concatenate to a listed
result node, then the result middle is generated by the grammar shell. -/
theorem concat_node_middle_mem_stringLanguage
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (R : SampleGeneratedRuleSkeleton G obs K)
    {left right result : SampleGeneratedDecompositionNode R.skeleton}
    (hLeft : left ∈ R.decompositionNodes)
    (hRight : right ∈ R.decompositionNodes)
    (hResult : result ∈ R.decompositionNodes)
    (hmid : result.decomposition.middle =
      left.decomposition.middle ++ right.decomposition.middle)
    (hDL : SampleGeneratedRecursiveDerivation (M := M) R left)
    (hDR : SampleGeneratedRecursiveDerivation (M := M) R right) :
    result.decomposition.middle ∈
      (terminalConcatEnumeratedRuleListPackage (M := M) R).toWorkingMCFG.StringLanguage := by
  exact (SampleGeneratedRecursiveDerivation.concat
    (R := R) (M := M) hLeft hRight hResult hmid hDL hDR)
      .middle_mem_stringLanguage (M := M)

end SampleGeneratedRecursiveDerivation

end FIv21
