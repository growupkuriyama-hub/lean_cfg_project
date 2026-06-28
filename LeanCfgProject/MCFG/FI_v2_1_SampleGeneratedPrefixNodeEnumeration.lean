import LeanCfgProject.MCFG.FI_v2_1_SampleGeneratedPrefixChainGold

/-!
# FI v2.1 Lean experiment: prefix-node enumeration witnesses

The previous layer packaged prefix chains abstractly: if a left-linear chain of
listed decomposition nodes is supplied, the generated terminal+concat grammar
shell generates the indexed word.  This file adds the next implementation-facing
interface: the individual listed nodes used by such a chain are packaged as
finite-enumeration witnesses.

This is still deliberately certificate-driven.  It does not yet search a word's
prefixes automatically.  Instead, it isolates the precise finite evidence the
next automatic prefix-node enumerator should construct: a listed singleton node
for the first letter, and listed singleton/result nodes for each right-extension
step.
-/

namespace FIv21

universe u v w

section SampleGeneratedPrefixNodeEnumeration

variable {N : Type w} {α : Type u}
variable [DecidableEq α]
variable {M : Type v} [Monoid M] [Fintype M]

/-- A decomposition node together with explicit membership in the finite node
list of a generated rule skeleton. -/
structure ListedSampleGeneratedDecompositionNode
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (R : SampleGeneratedRuleSkeleton G obs K) where
  node : SampleGeneratedDecompositionNode R.skeleton
  mem : node ∈ R.decompositionNodes

namespace ListedSampleGeneratedDecompositionNode

/-- The underlying listed decomposition node. -/
def toNode
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {R : SampleGeneratedRuleSkeleton G obs K}
    (X : ListedSampleGeneratedDecompositionNode R) :
    SampleGeneratedDecompositionNode R.skeleton :=
  X.node

/-- The exposed middle word of a listed node. -/
def middle
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {R : SampleGeneratedRuleSkeleton G obs K}
    (X : ListedSampleGeneratedDecompositionNode R) : Word α :=
  X.node.decomposition.middle

/-- The tuple exposed by a listed node. -/
def tuple
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {R : SampleGeneratedRuleSkeleton G obs K}
    (X : ListedSampleGeneratedDecompositionNode R) : Tuple α 1 :=
  X.node.decomposition.tuple

/-- The context exposed by a listed node. -/
def context
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {R : SampleGeneratedRuleSkeleton G obs K}
    (X : ListedSampleGeneratedDecompositionNode R) : NamedSentenceContext α 1 :=
  X.node.decomposition.context

/-- Listed nodes have their tuple nonterminal in the generated nonterminal list. -/
theorem tuple_mem_nonterminals
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {R : SampleGeneratedRuleSkeleton G obs K}
    (X : ListedSampleGeneratedDecompositionNode R) :
    X.node.tupleNonterminal ∈ R.nonterminals := by
  exact X.node.tuple_mem_nonterminals

/-- Listed nodes have their context nonterminal in the generated nonterminal
list. -/
theorem context_mem_nonterminals
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {R : SampleGeneratedRuleSkeleton G obs K}
    (X : ListedSampleGeneratedDecompositionNode R) :
    X.node.contextNonterminal ∈ R.nonterminals := by
  exact X.node.context_mem_nonterminals

/-- Listed nodes have their typed nonterminal in the generated nonterminal list. -/
theorem typed_mem_nonterminals
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {R : SampleGeneratedRuleSkeleton G obs K}
    (X : ListedSampleGeneratedDecompositionNode R) :
    X.node.typedNonterminal ∈ R.nonterminals := by
  exact X.node.typed_mem_nonterminals

/-- A listed node contributes the corresponding start candidate. -/
theorem startCandidate_mem
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {R : SampleGeneratedRuleSkeleton G obs K}
    (X : ListedSampleGeneratedDecompositionNode R) :
    ({ node := X.node } : SampleGeneratedStartCandidate R.skeleton) ∈
      R.startCandidates := by
  exact R.startCandidate_mem_of_node_mem X.mem

/-- The node's context is licensed by the sample named distribution. -/
theorem context_mem_sampleDistribution
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {R : SampleGeneratedRuleSkeleton G obs K}
    (X : ListedSampleGeneratedDecompositionNode R) :
    X.context ∈ SampleNamedDistribution K X.tuple := by
  exact X.node.context_mem_sampleDistribution

end ListedSampleGeneratedDecompositionNode

/-- A singleton prefix-node witness: a listed node whose exposed middle is a
single terminal. -/
structure SampleGeneratedSingletonPrefixNode
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (R : SampleGeneratedRuleSkeleton G obs K) (a : α) where
  listed : ListedSampleGeneratedDecompositionNode R
  middle_eq : listed.middle = [a]

namespace SampleGeneratedSingletonPrefixNode

/-- The singleton node as a terminal-rule candidate. -/
def toTerminalCandidate
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {R : SampleGeneratedRuleSkeleton G obs K} {a : α}
    (X : SampleGeneratedSingletonPrefixNode R a) :
    SampleGeneratedTerminalCandidate R.skeleton :=
  { node := X.listed.node
    terminal := a
    middle_eq := X.middle_eq }

/-- Singleton prefix-node witnesses generate singleton prefix chains. -/
def toPrefixChain
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {R : SampleGeneratedRuleSkeleton G obs K} {a : α}
    (X : SampleGeneratedSingletonPrefixNode R a) :
    SampleGeneratedPrefixChain (M := M) R [a] :=
  singletonPrefixChain (M := M) R X.listed.mem X.middle_eq

/-- The singleton node generates the singleton word in the generated grammar. -/
theorem mem_stringLanguage
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {R : SampleGeneratedRuleSkeleton G obs K} {a : α}
    (X : SampleGeneratedSingletonPrefixNode (M := M) R a) :
    [a] ∈ (terminalConcatEnumeratedRuleListPackage (M := M) R).toWorkingMCFG.StringLanguage := by
  exact X.toPrefixChain.word_mem_stringLanguage (M := M)

end SampleGeneratedSingletonPrefixNode

/-- One right-extension step in a prefix-node enumeration.  It records the
already parsed prefix chain, a listed singleton node to append, and a listed
result node whose middle is the concatenation of the two. -/
structure SampleGeneratedPrefixNodeStep
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (R : SampleGeneratedRuleSkeleton G obs K)
    (u : Word α) (a : α) where
  prefix : SampleGeneratedPrefixChain (M := M) R u
  last : SampleGeneratedSingletonPrefixNode (M := M) R a
  result : ListedSampleGeneratedDecompositionNode R
  result_middle_eq :
    result.middle = prefix.endpoint.decomposition.middle ++ last.listed.middle

namespace SampleGeneratedPrefixNodeStep

/-- The concatenation candidate associated with a prefix extension step. -/
def toConcatCandidate
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {R : SampleGeneratedRuleSkeleton G obs K} {u : Word α} {a : α}
    (S : SampleGeneratedPrefixNodeStep (M := M) R u a) :
    SampleGeneratedConcatCandidate R.skeleton :=
  { left := S.prefix.endpoint
    right := S.last.listed.node
    result := S.result.node
    middle_eq := S.result_middle_eq }

/-- A prefix-node step extends the prefix chain by one terminal. -/
def extendPrefixChain
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {R : SampleGeneratedRuleSkeleton G obs K} {u : Word α} {a : α}
    (S : SampleGeneratedPrefixNodeStep (M := M) R u a) :
    SampleGeneratedPrefixChain (M := M) R (u ++ [a]) :=
  snocPrefixChain (M := M) R S.prefix
    S.last.listed.mem S.last.middle_eq S.result.mem S.result_middle_eq

/-- The word obtained by one right-extension step is generated by the generated
terminal+concat grammar. -/
theorem mem_stringLanguage
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {R : SampleGeneratedRuleSkeleton G obs K} {u : Word α} {a : α}
    (S : SampleGeneratedPrefixNodeStep (M := M) R u a) :
    u ++ [a] ∈
      (terminalConcatEnumeratedRuleListPackage (M := M) R).toWorkingMCFG.StringLanguage := by
  exact S.extendPrefixChain.word_mem_stringLanguage (M := M)

end SampleGeneratedPrefixNodeStep

/-- A prefix-node enumeration package for a word: it is a prefix-chain together
with explicit evidence that its endpoint is one of the listed decomposition
nodes. -/
structure SampleGeneratedPrefixNodeEnumeration
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (R : SampleGeneratedRuleSkeleton G obs K) (w : Word α) where
  chain : SampleGeneratedPrefixChain (M := M) R w
  endpoint_mem : chain.endpoint ∈ R.decompositionNodes

namespace SampleGeneratedPrefixNodeEnumeration

/-- Endpoint as a listed node. -/
def endpoint
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {R : SampleGeneratedRuleSkeleton G obs K} {w : Word α}
    (E : SampleGeneratedPrefixNodeEnumeration (M := M) R w) :
    ListedSampleGeneratedDecompositionNode R :=
  { node := E.chain.endpoint
    mem := E.endpoint_mem }

/-- The endpoint exposes the indexed word. -/
theorem endpoint_middle_eq
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {R : SampleGeneratedRuleSkeleton G obs K} {w : Word α}
    (E : SampleGeneratedPrefixNodeEnumeration (M := M) R w) :
    E.endpoint.middle = w := by
  exact E.chain.endpoint_middle_eq

/-- Prefix-node enumerations generate their indexed word. -/
theorem word_mem_stringLanguage
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {R : SampleGeneratedRuleSkeleton G obs K} {w : Word α}
    (E : SampleGeneratedPrefixNodeEnumeration (M := M) R w) :
    w ∈ (terminalConcatEnumeratedRuleListPackage (M := M) R).toWorkingMCFG.StringLanguage := by
  exact E.chain.word_mem_stringLanguage (M := M)

end SampleGeneratedPrefixNodeEnumeration

/-- Start a prefix-node enumeration from a listed singleton node. -/
def singletonPrefixNodeEnumeration
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (R : SampleGeneratedRuleSkeleton G obs K) {a : α}
    (X : SampleGeneratedSingletonPrefixNode (M := M) R a) :
    SampleGeneratedPrefixNodeEnumeration (M := M) R [a] :=
  { chain := X.toPrefixChain
    endpoint_mem := by
      simpa [SampleGeneratedPrefixChain.endpoint,
        SampleGeneratedSingletonPrefixNode.toPrefixChain,
        singletonPrefixChain,
        singletonWordLinearParseConstruction] using X.listed.mem }

/-- Extend a prefix-node enumeration by one listed singleton node and a listed
result node. -/
def snocPrefixNodeEnumeration
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (R : SampleGeneratedRuleSkeleton G obs K)
    {u : Word α} (E : SampleGeneratedPrefixNodeEnumeration (M := M) R u)
    {a : α}
    (last : SampleGeneratedSingletonPrefixNode (M := M) R a)
    (result : ListedSampleGeneratedDecompositionNode R)
    (hmid : result.middle = E.chain.endpoint.decomposition.middle ++ last.listed.middle) :
    SampleGeneratedPrefixNodeEnumeration (M := M) R (u ++ [a]) :=
  { chain :=
      (SampleGeneratedPrefixNodeStep.extendPrefixChain (M := M)
        { prefix := E.chain
          last := last
          result := result
          result_middle_eq := hmid })
    endpoint_mem := by
      simpa [SampleGeneratedPrefixChain.endpoint,
        SampleGeneratedPrefixNodeStep.extendPrefixChain,
        snocPrefixChain,
        appendSingletonWordLinearParseConstruction] using result.mem }

/-- Singleton prefix-node enumerations generate their singleton word. -/
theorem singletonPrefixNodeEnumeration_mem_stringLanguage
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (R : SampleGeneratedRuleSkeleton G obs K) {a : α}
    (X : SampleGeneratedSingletonPrefixNode (M := M) R a) :
    [a] ∈ (terminalConcatEnumeratedRuleListPackage (M := M) R).toWorkingMCFG.StringLanguage := by
  exact (singletonPrefixNodeEnumeration (M := M) R X).word_mem_stringLanguage (M := M)

/-- Right-extension prefix-node enumerations generate the appended word. -/
theorem snocPrefixNodeEnumeration_mem_stringLanguage
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (R : SampleGeneratedRuleSkeleton G obs K)
    {u : Word α} (E : SampleGeneratedPrefixNodeEnumeration (M := M) R u)
    {a : α}
    (last : SampleGeneratedSingletonPrefixNode (M := M) R a)
    (result : ListedSampleGeneratedDecompositionNode R)
    (hmid : result.middle = E.chain.endpoint.decomposition.middle ++ last.listed.middle) :
    u ++ [a] ∈
      (terminalConcatEnumeratedRuleListPackage (M := M) R).toWorkingMCFG.StringLanguage := by
  exact (snocPrefixNodeEnumeration (M := M) R E last result hmid)
    .word_mem_stringLanguage (M := M)

end SampleGeneratedPrefixNodeEnumeration

end FIv21
