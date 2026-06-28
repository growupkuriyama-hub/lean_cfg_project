import LeanCfgProject.MCFG.FI_v2_1_SampleGeneratedLearnerGrammarSkeleton

/-!
# FI v2.1 Lean experiment: exactness wrapper for sample-generated skeletons

This layer attaches the previously checked canonical-nonterminal exactness
certificate to a concrete sample-generated learner-grammar skeleton.
-/

namespace FIv21

universe u v w

section SampleGeneratedLearnerGrammarSkeletonExact

variable {N : Type w} {α : Type u}
variable [DecidableEq α]
variable {M : Type v} [Monoid M] [Fintype M]

/-- Exactness certificate for a sample-generated learner-grammar skeleton.  The
semantic content is inherited from the canonical-nonterminal layer; the new
payload is that the same data is now viewed as a learner-grammar skeleton. -/
structure SampleGeneratedLearnerGrammarSkeletonExactForLanguage
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (S : SampleGeneratedLearnerGrammarSkeleton G obs K) (L : Set (Word α)) where
  base : CanonicalLearnerNonterminalExactForLanguage S.data L

namespace SampleGeneratedLearnerGrammarSkeletonExactForLanguage

/-- Forget to the canonical-nonterminal exactness layer. -/
def toCanonicalLearnerNonterminalExact
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {S : SampleGeneratedLearnerGrammarSkeleton G obs K} {L : Set (Word α)}
    (C : SampleGeneratedLearnerGrammarSkeletonExactForLanguage S L) :
    CanonicalLearnerNonterminalExactForLanguage S.data L :=
  C.base

/-- Forget further to the subword-unit-edge exactness layer. -/
def toSubwordUnitEdgeEnumerationExact
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {S : SampleGeneratedLearnerGrammarSkeleton G obs K} {L : Set (Word α)}
    (C : SampleGeneratedLearnerGrammarSkeletonExactForLanguage S L) :
    SubwordUnitEdgeEnumerationExactForLanguage S.data L :=
  C.base.toSubwordUnitEdgeExact

/-- Exact skeletons still expose the finite nonterminal list. -/
theorem root_mem_nonterminals
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {S : SampleGeneratedLearnerGrammarSkeleton G obs K} {L : Set (Word α)}
    (_C : SampleGeneratedLearnerGrammarSkeletonExactForLanguage S L) :
    SampleGeneratedLearnerGrammarSkeleton.root (α := α) (M := M) ∈ S.nonterminals := by
  exact S.root_mem_nonterminals

/-- Exact skeletons preserve tuple-node membership for listed decompositions. -/
theorem decomposition_tuple_mem
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {S : SampleGeneratedLearnerGrammarSkeleton G obs K} {L : Set (Word α)}
    (_C : SampleGeneratedLearnerGrammarSkeletonExactForLanguage S L)
    (X : SampleGeneratedDecompositionNode S) :
    X.tupleNonterminal ∈ S.nonterminals := by
  exact X.tuple_mem_nonterminals

/-- Exact skeletons preserve context-node membership for listed decompositions. -/
theorem decomposition_context_mem
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {S : SampleGeneratedLearnerGrammarSkeleton G obs K} {L : Set (Word α)}
    (_C : SampleGeneratedLearnerGrammarSkeletonExactForLanguage S L)
    (X : SampleGeneratedDecompositionNode S) :
    X.contextNonterminal ∈ S.nonterminals := by
  exact X.context_mem_nonterminals

/-- Exact skeletons preserve typed-node membership for listed decompositions. -/
theorem decomposition_typed_mem
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {S : SampleGeneratedLearnerGrammarSkeleton G obs K} {L : Set (Word α)}
    (_C : SampleGeneratedLearnerGrammarSkeletonExactForLanguage S L)
    (X : SampleGeneratedDecompositionNode S) :
    X.typedNonterminal ∈ S.nonterminals := by
  exact X.typed_mem_nonterminals

/-- Exact skeletons preserve unit-candidate reachability. -/
theorem unitCandidate_reach
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {S : SampleGeneratedLearnerGrammarSkeleton G obs K} {L : Set (Word α)}
    (_C : SampleGeneratedLearnerGrammarSkeletonExactForLanguage S L)
    (U : SampleGeneratedUnitCandidate S) :
    S.data.toSubwordContextDecompositionData.toSampleExtractedRuleLists.UnitReach
      U.pair.src.tuple U.pair.tgt.tuple := by
  exact U.unitReach

/-- Exact concrete enumerated skeletons still represent every sampled word by
listed skeleton nodes. -/
theorem enumerated_sample_word_node_exact
    (G : WorkingMCFG N α) (obs : α → M) (K : Finset (Word α))
    (f : Nat) (hfanout : 1 ≤ f) (hG : G.SemanticWorkingConditions)
    {L : Set (Word α)}
    (_C : SampleGeneratedLearnerGrammarSkeletonExactForLanguage
      (enumeratedSampleGeneratedLearnerGrammarSkeleton G obs K f hfanout hG) L)
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
  exact enumeratedSkeleton_sample_word_node G obs K f hfanout hG hw

end SampleGeneratedLearnerGrammarSkeletonExactForLanguage

/-- Grammar-target abbreviation. -/
abbrev SampleGeneratedLearnerGrammarSkeletonExactForGrammar
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (S : SampleGeneratedLearnerGrammarSkeleton G obs K) :=
  SampleGeneratedLearnerGrammarSkeletonExactForLanguage S G.StringLanguage

end SampleGeneratedLearnerGrammarSkeletonExact

end FIv21
