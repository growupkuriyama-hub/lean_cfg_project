import LeanCfgProject.MCFG.FI_v2_1_SampleGeneratedRecursiveDerivationGold

/-!
# FI v2.1 Lean experiment: left-linear parse certificates for sample-generated grammars

The previous layer introduced general recursive terminal/concat derivation
certificates.  This file adds a more implementation-facing specialization:
left-linear parse certificates.  A listed decomposition node is linearly
parseable if it is a singleton terminal node, or if it is obtained by appending
one singleton terminal node to an already linearly parseable prefix node.

This is still certificate-driven rather than a full parser.  The point is to
isolate the next constructive interface: once a finite chain of listed subword
nodes witnesses a left-to-right decomposition of a sample word, the generated
terminal+concat `WorkingMCFG` shell derives that word.
-/

namespace FIv21

universe u v w

section SampleGeneratedLinearParse

variable {N : Type w} {α : Type u}
variable [DecidableEq α]
variable {M : Type v} [Monoid M] [Fintype M]

/-- A left-linear parse certificate over a sample-generated rule skeleton.

Leaves are singleton-middle terminal nodes.  The `appendTerminal` constructor
extends an already parsed prefix by a listed singleton terminal node.  The
result node must be listed and must expose the concatenation of the prefix and
last singleton middles.

The generated concat-candidate enumeration scans all listed triples, so every
constructor instance below corresponds to an actual generated binary rule. -/
inductive SampleGeneratedLinearParse
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (R : SampleGeneratedRuleSkeleton G obs K) :
    SampleGeneratedDecompositionNode R.skeleton → Prop where
  | terminal
      {X : SampleGeneratedDecompositionNode R.skeleton} {a : α}
      (hX : X ∈ R.decompositionNodes)
      (hmid : X.decomposition.middle = [a]) :
      SampleGeneratedLinearParse R X
  | appendTerminal
      {prefix last result : SampleGeneratedDecompositionNode R.skeleton}
      {a : α}
      (hPrefix : SampleGeneratedLinearParse R prefix)
      (hLast : last ∈ R.decompositionNodes)
      (hLastMid : last.decomposition.middle = [a])
      (hResult : result ∈ R.decompositionNodes)
      (hmid : result.decomposition.middle =
        prefix.decomposition.middle ++ last.decomposition.middle) :
      SampleGeneratedLinearParse R result

namespace SampleGeneratedLinearParse

/-- The target node of a linear parse certificate is listed by the rule
skeleton. -/
theorem node_mem
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {R : SampleGeneratedRuleSkeleton G obs K}
    {X : SampleGeneratedDecompositionNode R.skeleton}
    (P : SampleGeneratedLinearParse (M := M) R X) :
    X ∈ R.decompositionNodes := by
  cases P with
  | terminal hX _ => exact hX
  | appendTerminal _ _ _ hResult _ => exact hResult

/-- Every left-linear certificate is, in particular, a recursive terminal/concat
certificate from the previous layer. -/
theorem toRecursive
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {R : SampleGeneratedRuleSkeleton G obs K}
    {X : SampleGeneratedDecompositionNode R.skeleton}
    (P : SampleGeneratedLinearParse (M := M) R X) :
    SampleGeneratedRecursiveDerivation (M := M) R X := by
  induction P with
  | terminal hX hmid =>
      exact SampleGeneratedRecursiveDerivation.terminal (R := R) (M := M) hX hmid
  | appendTerminal hPrefix hLast hLastMid hResult hmid ihPrefix =>
      have hPrefixMem := hPrefix.node_mem (M := M)
      have hLastRec : SampleGeneratedRecursiveDerivation (M := M) R last :=
        SampleGeneratedRecursiveDerivation.terminal (R := R) (M := M) hLast hLastMid
      exact SampleGeneratedRecursiveDerivation.concat
        (R := R) (M := M) hPrefixMem hLast hResult hmid ihPrefix hLastRec

/-- A left-linear certificate yields an ordinary tuple derivation in the
terminal+concat generated grammar shell. -/
theorem derives_node_tuple
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {R : SampleGeneratedRuleSkeleton G obs K}
    {X : SampleGeneratedDecompositionNode R.skeleton}
    (P : SampleGeneratedLinearParse (M := M) R X) :
    DerivesTuple (terminalConcatEnumeratedRuleListPackage (M := M) R).toWorkingMCFG
      (SampleGeneratedGrammarNonterminal.node X)
      X.decomposition.tuple := by
  have hRec := P.toRecursive (M := M)
  exact hRec.derives_node_tuple (M := M)

/-- A left-linear certificate derives the singleton tuple of the exposed middle
word. -/
theorem derives_singleton_middle
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {R : SampleGeneratedRuleSkeleton G obs K}
    {X : SampleGeneratedDecompositionNode R.skeleton}
    (P : SampleGeneratedLinearParse (M := M) R X) :
    DerivesTuple (terminalConcatEnumeratedRuleListPackage (M := M) R).toWorkingMCFG
      (SampleGeneratedGrammarNonterminal.node X)
      (singletonTuple X.decomposition.middle) := by
  have hRec := P.toRecursive (M := M)
  exact hRec.derives_singleton_middle (M := M)

/-- A left-linear certificate puts the exposed middle in the generated grammar's
string language. -/
theorem middle_mem_stringLanguage
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {R : SampleGeneratedRuleSkeleton G obs K}
    {X : SampleGeneratedDecompositionNode R.skeleton}
    (P : SampleGeneratedLinearParse (M := M) R X) :
    X.decomposition.middle ∈
      (terminalConcatEnumeratedRuleListPackage (M := M) R).toWorkingMCFG.StringLanguage := by
  have hRec := P.toRecursive (M := M)
  exact hRec.middle_mem_stringLanguage (M := M)

end SampleGeneratedLinearParse

/-- Singleton-middle nodes have a left-linear parse certificate. -/
theorem singleton_node_linearParse
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (R : SampleGeneratedRuleSkeleton G obs K)
    {X : SampleGeneratedDecompositionNode R.skeleton} {a : α}
    (hX : X ∈ R.decompositionNodes)
    (hmid : X.decomposition.middle = [a]) :
    SampleGeneratedLinearParse (M := M) R X :=
  SampleGeneratedLinearParse.terminal (R := R) (M := M) hX hmid

/-- Appending a listed singleton terminal node to a linearly parsed prefix gives
a linearly parsed result whenever the exposed middles concatenate. -/
theorem append_terminal_linearParse
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (R : SampleGeneratedRuleSkeleton G obs K)
    {prefix last result : SampleGeneratedDecompositionNode R.skeleton}
    {a : α}
    (hPrefix : SampleGeneratedLinearParse (M := M) R prefix)
    (hLast : last ∈ R.decompositionNodes)
    (hLastMid : last.decomposition.middle = [a])
    (hResult : result ∈ R.decompositionNodes)
    (hmid : result.decomposition.middle =
      prefix.decomposition.middle ++ last.decomposition.middle) :
    SampleGeneratedLinearParse (M := M) R result :=
  SampleGeneratedLinearParse.appendTerminal
    (R := R) (M := M) hPrefix hLast hLastMid hResult hmid

/-- Convenience theorem: a left-linear certificate immediately gives membership
of the exposed middle in the generated grammar shell. -/
theorem linearParse_middle_mem_stringLanguage
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (R : SampleGeneratedRuleSkeleton G obs K)
    {X : SampleGeneratedDecompositionNode R.skeleton}
    (P : SampleGeneratedLinearParse (M := M) R X) :
    X.decomposition.middle ∈
      (terminalConcatEnumeratedRuleListPackage (M := M) R).toWorkingMCFG.StringLanguage := by
  exact P.middle_mem_stringLanguage (M := M)

end SampleGeneratedLinearParse

end FIv21
