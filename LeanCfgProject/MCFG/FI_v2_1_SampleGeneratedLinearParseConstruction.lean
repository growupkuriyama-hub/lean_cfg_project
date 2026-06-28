import LeanCfgProject.MCFG.FI_v2_1_SampleGeneratedLinearParseGold

/-!
# FI v2.1 Lean experiment: constructing left-linear parse certificates

The previous layer introduced left-linear parse certificates and showed that
such a certificate gives membership in the string language of the generated
terminal+concat `WorkingMCFG` shell.  This file adds the next implementation-
facing step: package a left-linear certificate together with the word it parses,
and provide constructors for singleton words and for appending one terminal on
the right.

This is still certificate-driven.  It does not yet search the finite subword
node list automatically.  The point is to isolate the exact induction principle
needed for the next layer: once a prefix-chain of listed decomposition nodes is
available, it can be folded into a generated grammar derivation.
-/

namespace FIv21

universe u v w

section SampleGeneratedLinearParseConstruction

variable {N : Type w} {α : Type u}
variable [DecidableEq α]
variable {M : Type v} [Monoid M] [Fintype M]

/-- A constructed left-linear parse chain ending at a listed decomposition node.

The chain stores the endpoint node and a `SampleGeneratedLinearParse` certificate
for that endpoint.  It is the lightweight object manipulated by the construction
lemmas below. -/
structure SampleGeneratedLinearParseChain
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (R : SampleGeneratedRuleSkeleton G obs K) where
  node : SampleGeneratedDecompositionNode R.skeleton
  parse : SampleGeneratedLinearParse (M := M) R node

namespace SampleGeneratedLinearParseChain

/-- The endpoint node of a constructed linear parse chain is listed. -/
theorem node_mem
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {R : SampleGeneratedRuleSkeleton G obs K}
    (C : SampleGeneratedLinearParseChain (M := M) R) :
    C.node ∈ R.decompositionNodes := by
  exact C.parse.node_mem (M := M)

/-- A constructed chain derives its endpoint tuple in the generated grammar. -/
theorem derives_node_tuple
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {R : SampleGeneratedRuleSkeleton G obs K}
    (C : SampleGeneratedLinearParseChain (M := M) R) :
    DerivesTuple (terminalConcatEnumeratedRuleListPackage (M := M) R).toWorkingMCFG
      (SampleGeneratedGrammarNonterminal.node C.node)
      C.node.decomposition.tuple := by
  exact C.parse.derives_node_tuple (M := M)

/-- A constructed chain generates the exposed middle word of its endpoint. -/
theorem middle_mem_stringLanguage
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {R : SampleGeneratedRuleSkeleton G obs K}
    (C : SampleGeneratedLinearParseChain (M := M) R) :
    C.node.decomposition.middle ∈
      (terminalConcatEnumeratedRuleListPackage (M := M) R).toWorkingMCFG.StringLanguage := by
  exact C.parse.middle_mem_stringLanguage (M := M)

end SampleGeneratedLinearParseChain

/-- Construct a linear parse chain from a singleton-middle node. -/
def singletonLinearParseChain
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (R : SampleGeneratedRuleSkeleton G obs K)
    {X : SampleGeneratedDecompositionNode R.skeleton} {a : α}
    (hX : X ∈ R.decompositionNodes)
    (hmid : X.decomposition.middle = [a]) :
    SampleGeneratedLinearParseChain (M := M) R :=
  { node := X
    parse := singleton_node_linearParse (M := M) R hX hmid }

/-- Append one listed singleton-terminal node to an already constructed chain. -/
def appendSingletonLinearParseChain
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (R : SampleGeneratedRuleSkeleton G obs K)
    (C : SampleGeneratedLinearParseChain (M := M) R)
    {last result : SampleGeneratedDecompositionNode R.skeleton} {a : α}
    (hLast : last ∈ R.decompositionNodes)
    (hLastMid : last.decomposition.middle = [a])
    (hResult : result ∈ R.decompositionNodes)
    (hmid : result.decomposition.middle =
      C.node.decomposition.middle ++ last.decomposition.middle) :
    SampleGeneratedLinearParseChain (M := M) R :=
  { node := result
    parse := append_terminal_linearParse
      (M := M) R C.parse hLast hLastMid hResult hmid }

/-- A constructed linear parse for a specific word: the endpoint node exposes
that word as its middle, and the endpoint has a left-linear parse certificate. -/
structure SampleGeneratedWordLinearParseConstruction
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (R : SampleGeneratedRuleSkeleton G obs K) (w : Word α) where
  node : SampleGeneratedDecompositionNode R.skeleton
  middle_eq : node.decomposition.middle = w
  parse : SampleGeneratedLinearParse (M := M) R node

namespace SampleGeneratedWordLinearParseConstruction

/-- Forget a word-indexed construction to its endpoint chain. -/
def toChain
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {R : SampleGeneratedRuleSkeleton G obs K} {w : Word α}
    (P : SampleGeneratedWordLinearParseConstruction (M := M) R w) :
    SampleGeneratedLinearParseChain (M := M) R :=
  { node := P.node
    parse := P.parse }

/-- The endpoint node of a word-indexed construction is listed. -/
theorem node_mem
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {R : SampleGeneratedRuleSkeleton G obs K} {w : Word α}
    (P : SampleGeneratedWordLinearParseConstruction (M := M) R w) :
    P.node ∈ R.decompositionNodes := by
  exact P.parse.node_mem (M := M)

/-- A word-indexed construction derives its endpoint tuple. -/
theorem derives_node_tuple
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {R : SampleGeneratedRuleSkeleton G obs K} {w : Word α}
    (P : SampleGeneratedWordLinearParseConstruction (M := M) R w) :
    DerivesTuple (terminalConcatEnumeratedRuleListPackage (M := M) R).toWorkingMCFG
      (SampleGeneratedGrammarNonterminal.node P.node)
      P.node.decomposition.tuple := by
  exact P.parse.derives_node_tuple (M := M)

/-- A word-indexed construction places the indexed word in the generated string
language. -/
theorem word_mem_stringLanguage
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {R : SampleGeneratedRuleSkeleton G obs K} {w : Word α}
    (P : SampleGeneratedWordLinearParseConstruction (M := M) R w) :
    w ∈ (terminalConcatEnumeratedRuleListPackage (M := M) R).toWorkingMCFG.StringLanguage := by
  have h := P.parse.middle_mem_stringLanguage (M := M)
  simpa [P.middle_eq] using h

end SampleGeneratedWordLinearParseConstruction

/-- Construct a word-indexed left-linear parse for a singleton word. -/
def singletonWordLinearParseConstruction
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (R : SampleGeneratedRuleSkeleton G obs K)
    {X : SampleGeneratedDecompositionNode R.skeleton} {a : α}
    (hX : X ∈ R.decompositionNodes)
    (hmid : X.decomposition.middle = [a]) :
    SampleGeneratedWordLinearParseConstruction (M := M) R [a] :=
  { node := X
    middle_eq := hmid
    parse := singleton_node_linearParse (M := M) R hX hmid }

/-- Append a listed singleton-terminal node to a word-indexed construction.

This is the fold step used by the later sample-word construction: if a prefix
word has already been parsed and the result node exposes the concatenation of
the prefix node and a listed singleton node, then the longer word is parsed. -/
def appendSingletonWordLinearParseConstruction
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (R : SampleGeneratedRuleSkeleton G obs K)
    {u : Word α}
    (P : SampleGeneratedWordLinearParseConstruction (M := M) R u)
    {last result : SampleGeneratedDecompositionNode R.skeleton} {a : α}
    (hLast : last ∈ R.decompositionNodes)
    (hLastMid : last.decomposition.middle = [a])
    (hResult : result ∈ R.decompositionNodes)
    (hmid : result.decomposition.middle =
      P.node.decomposition.middle ++ last.decomposition.middle) :
    SampleGeneratedWordLinearParseConstruction (M := M) R (u ++ [a]) :=
  { node := result
    middle_eq := by
      calc
        result.decomposition.middle
            = P.node.decomposition.middle ++ last.decomposition.middle := hmid
        _ = u ++ [a] := by rw [P.middle_eq, hLastMid]
    parse := append_terminal_linearParse
      (M := M) R P.parse hLast hLastMid hResult hmid }

/-- Convenience theorem: a singleton construction generates the singleton word. -/
theorem singletonWordLinearParseConstruction_mem_stringLanguage
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (R : SampleGeneratedRuleSkeleton G obs K)
    {X : SampleGeneratedDecompositionNode R.skeleton} {a : α}
    (hX : X ∈ R.decompositionNodes)
    (hmid : X.decomposition.middle = [a]) :
    [a] ∈ (terminalConcatEnumeratedRuleListPackage (M := M) R).toWorkingMCFG.StringLanguage := by
  exact (singletonWordLinearParseConstruction (M := M) R hX hmid)
    .word_mem_stringLanguage (M := M)

/-- Convenience theorem: an appended construction generates the appended word. -/
theorem appendSingletonWordLinearParseConstruction_mem_stringLanguage
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (R : SampleGeneratedRuleSkeleton G obs K)
    {u : Word α}
    (P : SampleGeneratedWordLinearParseConstruction (M := M) R u)
    {last result : SampleGeneratedDecompositionNode R.skeleton} {a : α}
    (hLast : last ∈ R.decompositionNodes)
    (hLastMid : last.decomposition.middle = [a])
    (hResult : result ∈ R.decompositionNodes)
    (hmid : result.decomposition.middle =
      P.node.decomposition.middle ++ last.decomposition.middle) :
    u ++ [a] ∈
      (terminalConcatEnumeratedRuleListPackage (M := M) R).toWorkingMCFG.StringLanguage := by
  exact (appendSingletonWordLinearParseConstruction
    (M := M) R P hLast hLastMid hResult hmid).word_mem_stringLanguage (M := M)

end SampleGeneratedLinearParseConstruction

end FIv21
