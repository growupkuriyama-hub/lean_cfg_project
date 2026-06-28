import LeanCfgProject.MCFG.FI_v2_1_CanonicalLearnerNonterminalGold

/-!
# FI v2.1 Lean experiment: sample-generated learner grammar skeleton

This file is the next vertical step after the canonical learner-nonterminal
layer.  We still do not construct the full `WorkingMCFG` learner.  Instead we
package the finite nonterminal universe generated from the sample, together with
its decomposition nodes and same-context/same-type unit candidates.

The point of this layer is implementation-facing: a future concrete learner
grammar can use these objects as its start node, tuple/context/typed nodes, and
unit-edge skeleton.
-/

namespace FIv21

universe u v w

section SampleGeneratedLearnerGrammarSkeleton

variable {N : Type w} {α : Type u}
variable [DecidableEq α]
variable {M : Type v} [Monoid M] [Fintype M]

/-- A learner-grammar skeleton generated from a finite positive sample through
subword-context enumeration and same-context/same-type unit-edge filtering.

This is not yet a full `WorkingMCFG`.  It is the finite, sample-generated
nonterminal-and-unit-edge substrate on which the later concrete grammar
construction should be layered. -/
structure SampleGeneratedLearnerGrammarSkeleton
    (G : WorkingMCFG N α) (obs : α → M) (K : Finset (Word α)) where
  data : SubwordUnitEdgeEnumerationData G obs K

namespace SampleGeneratedLearnerGrammarSkeleton

/-- The finite support underlying the skeleton. -/
noncomputable def support
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (S : SampleGeneratedLearnerGrammarSkeleton G obs K) : FiniteLearnerSupport α :=
  S.data.support

/-- The finite nonterminal list of the skeleton. -/
noncomputable def nonterminals
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (S : SampleGeneratedLearnerGrammarSkeleton G obs K) :
    List (CanonicalLearnerNonterminal α M) :=
  S.data.learnerNonterminals

/-- The future start node of the sample-generated learner. -/
def root : CanonicalLearnerNonterminal α M :=
  CanonicalLearnerNonterminal.root

/-- The arity map intended for the skeleton nonterminals. -/
def arity (A : CanonicalLearnerNonterminal α M) : Nat :=
  A.arity

/-- Forget the skeleton to the previous subword-unit-edge enumeration data. -/
def toSubwordUnitEdgeEnumerationData
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (S : SampleGeneratedLearnerGrammarSkeleton G obs K) :
    SubwordUnitEdgeEnumerationData G obs K :=
  S.data

/-- Forget the skeleton to the finite learner-hypothesis object at this sample. -/
noncomputable def toFiniteLearnerHypothesis
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (S : SampleGeneratedLearnerGrammarSkeleton G obs K) :
    FiniteLearnerHypothesis α M :=
  S.data.toSubwordContextDecompositionData.toFiniteLearnerHypothesis

/-- The root nonterminal is listed in the generated finite nonterminal list. -/
theorem root_mem_nonterminals
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (S : SampleGeneratedLearnerGrammarSkeleton G obs K) :
    root (α := α) (M := M) ∈ S.nonterminals := by
  exact root_mem_supportCanonicalNonterminals (M := M) obs S.data.support

/-- The support sample is exactly the original sample. -/
theorem support_sample_eq
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (S : SampleGeneratedLearnerGrammarSkeleton G obs K) :
    S.support.sample = K := by
  exact S.data.support_sample_eq

end SampleGeneratedLearnerGrammarSkeleton

/-- A listed subword decomposition, viewed as a node package of the generated
learner skeleton. -/
structure SampleGeneratedDecompositionNode
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (S : SampleGeneratedLearnerGrammarSkeleton G obs K) where
  decomposition : SubwordSampleDecomposition (α := α) K
  mem : decomposition ∈ S.data.subwordDecompositions

namespace SampleGeneratedDecompositionNode

/-- Tuple nonterminal associated with a listed subword decomposition. -/
def tupleNonterminal
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {S : SampleGeneratedLearnerGrammarSkeleton G obs K}
    (X : SampleGeneratedDecompositionNode S) : CanonicalLearnerNonterminal α M :=
  CanonicalLearnerNonterminal.tuple 1 X.decomposition.tuple

/-- Context nonterminal associated with a listed subword decomposition. -/
def contextNonterminal
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {S : SampleGeneratedLearnerGrammarSkeleton G obs K}
    (X : SampleGeneratedDecompositionNode S) : CanonicalLearnerNonterminal α M :=
  CanonicalLearnerNonterminal.context 1 X.decomposition.context

/-- Typed nonterminal associated with a listed subword decomposition. -/
def typedNonterminal
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {S : SampleGeneratedLearnerGrammarSkeleton G obs K}
    (X : SampleGeneratedDecompositionNode S) : CanonicalLearnerNonterminal α M :=
  CanonicalLearnerNonterminal.typed 1 (tupleType obs X.decomposition.tuple)

/-- The tuple nonterminal of a listed decomposition is listed by the skeleton. -/
theorem tuple_mem_nonterminals
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {S : SampleGeneratedLearnerGrammarSkeleton G obs K}
    (X : SampleGeneratedDecompositionNode S) :
    X.tupleNonterminal ∈ S.nonterminals := by
  exact S.data.tupleNonterminal_mem_of_subword_mem X.mem

/-- The context nonterminal of a listed decomposition is listed by the skeleton. -/
theorem context_mem_nonterminals
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {S : SampleGeneratedLearnerGrammarSkeleton G obs K}
    (X : SampleGeneratedDecompositionNode S) :
    X.contextNonterminal ∈ S.nonterminals := by
  exact S.data.contextNonterminal_mem_of_subword_mem X.mem

/-- The typed nonterminal of a listed decomposition is listed by the skeleton. -/
theorem typed_mem_nonterminals
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {S : SampleGeneratedLearnerGrammarSkeleton G obs K}
    (X : SampleGeneratedDecompositionNode S) :
    X.typedNonterminal ∈ S.nonterminals := by
  exact S.data.typedNonterminal_mem_of_subword_mem X.mem

/-- Listed decomposition contexts are licensed by the sample distribution. -/
theorem context_mem_sampleDistribution
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {S : SampleGeneratedLearnerGrammarSkeleton G obs K}
    (X : SampleGeneratedDecompositionNode S) :
    X.decomposition.context ∈ SampleNamedDistribution K X.decomposition.tuple := by
  exact S.data.subword_context_mem_sampleDistribution X.mem

/-- The filled word of a listed decomposition belongs to the skeleton support
sample. -/
theorem filled_mem_support_sample
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {S : SampleGeneratedLearnerGrammarSkeleton G obs K}
    (X : SampleGeneratedDecompositionNode S) :
    namedFill 1 X.decomposition.context X.decomposition.tuple ∈ S.support.sample := by
  simpa [SampleGeneratedLearnerGrammarSkeleton.support] using
    S.data.toSubwordContextDecompositionData.subword_filled_mem_support_sample X.mem

end SampleGeneratedDecompositionNode

/-- Source membership for an ordered pair drawn from a decomposition list. -/
theorem subwordDecompositionPairs_src_mem
    {K : Finset (Word α)}
    {Ss : List (SubwordSampleDecomposition (α := α) K)}
    {P : SubwordDecompositionPair (α := α) K}
    (hP : P ∈ subwordDecompositionPairs (α := α) Ss) :
    P.src ∈ Ss := by
  unfold subwordDecompositionPairs at hP
  rcases List.mem_bind.mp hP with ⟨S, hS, hmap⟩
  rcases List.mem_map.mp hmap with ⟨T, _hT, hEq⟩
  cases hEq
  exact hS

/-- Target membership for an ordered pair drawn from a decomposition list. -/
theorem subwordDecompositionPairs_tgt_mem
    {K : Finset (Word α)}
    {Ss : List (SubwordSampleDecomposition (α := α) K)}
    {P : SubwordDecompositionPair (α := α) K}
    (hP : P ∈ subwordDecompositionPairs (α := α) Ss) :
    P.tgt ∈ Ss := by
  unfold subwordDecompositionPairs at hP
  rcases List.mem_bind.mp hP with ⟨S, _hS, hmap⟩
  rcases List.mem_map.mp hmap with ⟨T, hT, hEq⟩
  cases hEq
  exact hT

/-- A same-context/same-type filtered pair has its source in the original
subword-decomposition list. -/
theorem typedSameContextSubwordPairs_src_mem
    {K : Finset (Word α)} {obs : α → M}
    {Ss : List (SubwordSampleDecomposition (α := α) K)}
    {P : SubwordDecompositionPair (α := α) K}
    (hP : P ∈ typedSameContextSubwordPairs (α := α) obs Ss) :
    P.src ∈ Ss := by
  exact subwordDecompositionPairs_src_mem
    (typedSameContextSubwordPairs_mem_pairs (α := α) hP)

/-- A same-context/same-type filtered pair has its target in the original
subword-decomposition list. -/
theorem typedSameContextSubwordPairs_tgt_mem
    {K : Finset (Word α)} {obs : α → M}
    {Ss : List (SubwordSampleDecomposition (α := α) K)}
    {P : SubwordDecompositionPair (α := α) K}
    (hP : P ∈ typedSameContextSubwordPairs (α := α) obs Ss) :
    P.tgt ∈ Ss := by
  exact subwordDecompositionPairs_tgt_mem
    (typedSameContextSubwordPairs_mem_pairs (α := α) hP)

/-- A unit-edge candidate in the generated skeleton, represented by a filtered
same-context/same-type pair. -/
structure SampleGeneratedUnitCandidate
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (S : SampleGeneratedLearnerGrammarSkeleton G obs K) where
  pair : SubwordDecompositionPair (α := α) K
  pair_mem : pair ∈ typedSameContextSubwordPairs (α := α) obs S.data.subwordDecompositions

namespace SampleGeneratedUnitCandidate

/-- Source tuple nonterminal of a generated unit candidate. -/
def srcNonterminal
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {S : SampleGeneratedLearnerGrammarSkeleton G obs K}
    (U : SampleGeneratedUnitCandidate S) : CanonicalLearnerNonterminal α M :=
  CanonicalLearnerNonterminal.tuple 1 U.pair.src.tuple

/-- Target tuple nonterminal of a generated unit candidate. -/
def tgtNonterminal
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {S : SampleGeneratedLearnerGrammarSkeleton G obs K}
    (U : SampleGeneratedUnitCandidate S) : CanonicalLearnerNonterminal α M :=
  CanonicalLearnerNonterminal.tuple 1 U.pair.tgt.tuple

/-- The source decomposition of a unit candidate is listed. -/
theorem src_mem_decompositions
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {S : SampleGeneratedLearnerGrammarSkeleton G obs K}
    (U : SampleGeneratedUnitCandidate S) :
    U.pair.src ∈ S.data.subwordDecompositions := by
  exact typedSameContextSubwordPairs_src_mem (α := α) (obs := obs) U.pair_mem

/-- The target decomposition of a unit candidate is listed. -/
theorem tgt_mem_decompositions
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {S : SampleGeneratedLearnerGrammarSkeleton G obs K}
    (U : SampleGeneratedUnitCandidate S) :
    U.pair.tgt ∈ S.data.subwordDecompositions := by
  exact typedSameContextSubwordPairs_tgt_mem (α := α) (obs := obs) U.pair_mem

/-- The source nonterminal of a unit candidate is listed by the skeleton. -/
theorem src_mem_nonterminals
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {S : SampleGeneratedLearnerGrammarSkeleton G obs K}
    (U : SampleGeneratedUnitCandidate S) :
    U.srcNonterminal ∈ S.nonterminals := by
  exact S.data.tupleNonterminal_mem_of_subword_mem U.src_mem_decompositions

/-- The target nonterminal of a unit candidate is listed by the skeleton. -/
theorem tgt_mem_nonterminals
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {S : SampleGeneratedLearnerGrammarSkeleton G obs K}
    (U : SampleGeneratedUnitCandidate S) :
    U.tgtNonterminal ∈ S.nonterminals := by
  exact S.data.tupleNonterminal_mem_of_subword_mem U.tgt_mem_decompositions

/-- A generated unit candidate gives learner unit reachability. -/
theorem unitReach
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {S : SampleGeneratedLearnerGrammarSkeleton G obs K}
    (U : SampleGeneratedUnitCandidate S) :
    S.data.toSubwordContextDecompositionData.toSampleExtractedRuleLists.UnitReach
      U.pair.src.tuple U.pair.tgt.tuple := by
  exact S.data.typedPair_unitReach U.pair_mem

/-- A generated unit candidate has the same observed context and tuple type. -/
theorem property
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {S : SampleGeneratedLearnerGrammarSkeleton G obs K}
    (U : SampleGeneratedUnitCandidate S) :
    SubwordUnitEdgePredicate (α := α) obs U.pair := by
  exact typedSameContextSubwordPairs_property (α := α) U.pair_mem

end SampleGeneratedUnitCandidate

/-- Build a skeleton from subword-unit-edge enumeration data. -/
noncomputable def sampleGeneratedLearnerGrammarSkeletonOfData
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (D : SubwordUnitEdgeEnumerationData G obs K) :
    SampleGeneratedLearnerGrammarSkeleton G obs K :=
  { data := D }

/-- Concrete skeleton obtained from the enumerated subword-context and unit-edge
construction. -/
noncomputable def enumeratedSampleGeneratedLearnerGrammarSkeleton
    (G : WorkingMCFG N α) (obs : α → M) (K : Finset (Word α))
    (f : Nat) (hfanout : 1 ≤ f) (hG : G.SemanticWorkingConditions) :
    SampleGeneratedLearnerGrammarSkeleton G obs K :=
  { data := enumeratedSubwordUnitEdgeEnumerationData G obs K f hfanout hG }

/-- Every sampled word in the concrete enumerated skeleton has a listed
decomposition node whose tuple, context, and typed nonterminals are all listed. -/
theorem enumeratedSkeleton_sample_word_node
    (G : WorkingMCFG N α) (obs : α → M) (K : Finset (Word α))
    (f : Nat) (hfanout : 1 ≤ f) (hG : G.SemanticWorkingConditions)
    {w : Word α} (hw : w ∈ K) :
    ∃ X : SampleGeneratedDecompositionNode
        (enumeratedSampleGeneratedLearnerGrammarSkeleton G obs K f hfanout hG),
      X.decomposition.sampleWord = w ∧
      X.tupleNonterminal ∈
        (enumeratedSampleGeneratedLearnerGrammarSkeleton G obs K f hfanout hG).nonterminals ∧
      X.contextNonterminal ∈
        (enumeratedSampleGeneratedLearnerGrammarSkeleton G obs K f hfanout hG).nonterminals ∧
      X.typedNonterminal ∈
        (enumeratedSampleGeneratedLearnerGrammarSkeleton G obs K f hfanout hG).nonterminals ∧
      X.decomposition.context ∈ SampleNamedDistribution K X.decomposition.tuple := by
  rcases SubwordUnitEdgeEnumerationData.enumerated_sample_word_nonterminals
      G obs K f hfanout hG hw with
    ⟨S, hS, hWord, hTuple, hContext, hTyped⟩
  let X : SampleGeneratedDecompositionNode
      (enumeratedSampleGeneratedLearnerGrammarSkeleton G obs K f hfanout hG) :=
    { decomposition := S, mem := hS }
  refine ⟨X, hWord, ?_, ?_, ?_, ?_⟩
  · exact hTuple
  · exact hContext
  · exact hTyped
  · exact X.context_mem_sampleDistribution

end SampleGeneratedLearnerGrammarSkeleton

end FIv21
