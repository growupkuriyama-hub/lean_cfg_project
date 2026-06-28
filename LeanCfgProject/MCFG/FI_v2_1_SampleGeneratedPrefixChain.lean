import LeanCfgProject.MCFG.FI_v2_1_SampleGeneratedLinearParseConstructionGold

/-!
# FI v2.1 Lean experiment: prefix-chain packages for generated sample parses

The previous layer packaged word-indexed left-linear parse constructions.  This
file adds the next implementation-facing wrapper: a prefix-chain package.  The
package records the endpoint node and generated parse via the already checked
word-linear construction, while providing singleton and right-extension
constructors that correspond to the intended prefix-chain fold.

This is still certificate-driven.  It does not yet automatically find all prefix
nodes for a word, but it isolates the exact object that the later automatic
prefix-chain enumeration should produce.
-/

namespace FIv21

universe u v w

section SampleGeneratedPrefixChain

variable {N : Type w} {α : Type u}
variable [DecidableEq α]
variable {M : Type v} [Monoid M] [Fintype M]

/-- A prefix-chain package for a generated sample parse of word `w`.

Internally this is represented by the word-indexed left-linear construction from
the previous layer.  The current layer gives it prefix-chain-facing names and
constructors, preparing the next step where prefix nodes will be enumerated from
sample words. -/
structure SampleGeneratedPrefixChain
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (R : SampleGeneratedRuleSkeleton G obs K) (w : Word α) where
  construction : SampleGeneratedWordLinearParseConstruction (M := M) R w

namespace SampleGeneratedPrefixChain

/-- Endpoint node of a prefix-chain package. -/
def endpoint
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {R : SampleGeneratedRuleSkeleton G obs K} {w : Word α}
    (P : SampleGeneratedPrefixChain (M := M) R w) :
    SampleGeneratedDecompositionNode R.skeleton :=
  P.construction.node

/-- The endpoint node is listed in the rule skeleton. -/
theorem endpoint_mem
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {R : SampleGeneratedRuleSkeleton G obs K} {w : Word α}
    (P : SampleGeneratedPrefixChain (M := M) R w) :
    P.endpoint ∈ R.decompositionNodes := by
  exact P.construction.node_mem (M := M)

/-- The endpoint exposes the indexed word as its middle. -/
theorem endpoint_middle_eq
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {R : SampleGeneratedRuleSkeleton G obs K} {w : Word α}
    (P : SampleGeneratedPrefixChain (M := M) R w) :
    P.endpoint.decomposition.middle = w := by
  exact P.construction.middle_eq

/-- The underlying word-linear parse construction. -/
def toWordLinearParseConstruction
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {R : SampleGeneratedRuleSkeleton G obs K} {w : Word α}
    (P : SampleGeneratedPrefixChain (M := M) R w) :
    SampleGeneratedWordLinearParseConstruction (M := M) R w :=
  P.construction

/-- The underlying constructed parse chain. -/
def toLinearParseChain
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {R : SampleGeneratedRuleSkeleton G obs K} {w : Word α}
    (P : SampleGeneratedPrefixChain (M := M) R w) :
    SampleGeneratedLinearParseChain (M := M) R :=
  P.construction.toChain

/-- The underlying left-linear parse certificate. -/
theorem linearParse
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {R : SampleGeneratedRuleSkeleton G obs K} {w : Word α}
    (P : SampleGeneratedPrefixChain (M := M) R w) :
    SampleGeneratedLinearParse (M := M) R P.endpoint := by
  exact P.construction.parse

/-- A prefix-chain package derives its endpoint tuple in the generated
terminal+concat `WorkingMCFG` shell. -/
theorem derives_endpoint_tuple
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {R : SampleGeneratedRuleSkeleton G obs K} {w : Word α}
    (P : SampleGeneratedPrefixChain (M := M) R w) :
    DerivesTuple (terminalConcatEnumeratedRuleListPackage (M := M) R).toWorkingMCFG
      (SampleGeneratedGrammarNonterminal.node P.endpoint)
      P.endpoint.decomposition.tuple := by
  exact P.construction.derives_node_tuple (M := M)

/-- A prefix-chain package places its indexed word in the generated grammar's
string language. -/
theorem word_mem_stringLanguage
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {R : SampleGeneratedRuleSkeleton G obs K} {w : Word α}
    (P : SampleGeneratedPrefixChain (M := M) R w) :
    w ∈ (terminalConcatEnumeratedRuleListPackage (M := M) R).toWorkingMCFG.StringLanguage := by
  exact P.construction.word_mem_stringLanguage (M := M)

end SampleGeneratedPrefixChain

/-- Construct a prefix-chain package for a singleton word. -/
def singletonPrefixChain
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (R : SampleGeneratedRuleSkeleton G obs K)
    {X : SampleGeneratedDecompositionNode R.skeleton} {a : α}
    (hX : X ∈ R.decompositionNodes)
    (hmid : X.decomposition.middle = [a]) :
    SampleGeneratedPrefixChain (M := M) R [a] :=
  { construction := singletonWordLinearParseConstruction (M := M) R hX hmid }

/-- Extend a prefix-chain package by one listed singleton node on the right. -/
def snocPrefixChain
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (R : SampleGeneratedRuleSkeleton G obs K)
    {u : Word α}
    (P : SampleGeneratedPrefixChain (M := M) R u)
    {last result : SampleGeneratedDecompositionNode R.skeleton} {a : α}
    (hLast : last ∈ R.decompositionNodes)
    (hLastMid : last.decomposition.middle = [a])
    (hResult : result ∈ R.decompositionNodes)
    (hmid : result.decomposition.middle =
      P.endpoint.decomposition.middle ++ last.decomposition.middle) :
    SampleGeneratedPrefixChain (M := M) R (u ++ [a]) :=
  { construction :=
      appendSingletonWordLinearParseConstruction
        (M := M) R P.construction hLast hLastMid hResult hmid }

/-- Singleton prefix-chain packages generate their singleton word. -/
theorem singletonPrefixChain_mem_stringLanguage
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (R : SampleGeneratedRuleSkeleton G obs K)
    {X : SampleGeneratedDecompositionNode R.skeleton} {a : α}
    (hX : X ∈ R.decompositionNodes)
    (hmid : X.decomposition.middle = [a]) :
    [a] ∈ (terminalConcatEnumeratedRuleListPackage (M := M) R).toWorkingMCFG.StringLanguage := by
  exact (singletonPrefixChain (M := M) R hX hmid).word_mem_stringLanguage (M := M)

/-- Right-extension prefix-chain packages generate the appended word. -/
theorem snocPrefixChain_mem_stringLanguage
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (R : SampleGeneratedRuleSkeleton G obs K)
    {u : Word α}
    (P : SampleGeneratedPrefixChain (M := M) R u)
    {last result : SampleGeneratedDecompositionNode R.skeleton} {a : α}
    (hLast : last ∈ R.decompositionNodes)
    (hLastMid : last.decomposition.middle = [a])
    (hResult : result ∈ R.decompositionNodes)
    (hmid : result.decomposition.middle =
      P.endpoint.decomposition.middle ++ last.decomposition.middle) :
    u ++ [a] ∈
      (terminalConcatEnumeratedRuleListPackage (M := M) R).toWorkingMCFG.StringLanguage := by
  exact (snocPrefixChain (M := M) R P hLast hLastMid hResult hmid)
    .word_mem_stringLanguage (M := M)

end SampleGeneratedPrefixChain

end FIv21
