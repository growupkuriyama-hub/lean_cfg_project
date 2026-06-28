import LeanCfgProject.MCFG.FI_v2_1_SampleGeneratedLearnerGrammarSkeletonExact

/-!
# FI v2.1 Lean experiment: Gold wrapper for sample-generated skeletons

This layer packages learners that return sample-generated learner-grammar
skeletons.  It is still not the full concrete learner grammar, but the Gold
pipeline now runs through a concrete skeleton object carrying sample-generated
nonterminals and unit candidates.
-/

namespace FIv21

universe u v w

section SampleGeneratedLearnerGrammarSkeletonGold

variable {N : Type w} {α : Type u}
variable [DecidableEq α]
variable {M : Type v} [Monoid M] [Fintype M]

/-- A learner returning a sample-generated grammar skeleton for each finite
sample. -/
def SampleGeneratedLearnerGrammarSkeletonLearner
    (G : WorkingMCFG N α) (obs : α → M) :=
  (K : Finset (Word α)) → SampleGeneratedLearnerGrammarSkeleton G obs K

namespace SampleGeneratedLearnerGrammarSkeletonLearner

/-- Forget a skeleton learner to the canonical-nonterminal learner. -/
def toCanonicalLearnerNonterminalLearner
    {G : WorkingMCFG N α} {obs : α → M}
    (A : SampleGeneratedLearnerGrammarSkeletonLearner G obs) :
    CanonicalLearnerNonterminalLearner G obs :=
  fun K => (A K).data

/-- The finite nonterminal list returned by a skeleton learner at a sample. -/
noncomputable def nonterminals
    {G : WorkingMCFG N α} {obs : α → M}
    (A : SampleGeneratedLearnerGrammarSkeletonLearner G obs)
    (K : Finset (Word α)) : List (CanonicalLearnerNonterminal α M) :=
  (A K).nonterminals

/-- Forget to the finite-hypothesis learner. -/
noncomputable def toFiniteHypothesisLearner
    {G : WorkingMCFG N α} {obs : α → M}
    (A : SampleGeneratedLearnerGrammarSkeletonLearner G obs) :
    FiniteHypothesisLearner α M :=
  A.toCanonicalLearnerNonterminalLearner.toFiniteHypothesisLearner

end SampleGeneratedLearnerGrammarSkeletonLearner

/-- The concrete enumerated skeleton learner. -/
noncomputable def enumeratedSampleGeneratedLearnerGrammarSkeletonLearner
    (G : WorkingMCFG N α) (obs : α → M)
    (f : Nat) (hfanout : 1 ≤ f) (hG : G.SemanticWorkingConditions) :
    SampleGeneratedLearnerGrammarSkeletonLearner G obs :=
  fun K => enumeratedSampleGeneratedLearnerGrammarSkeleton G obs K f hfanout hG

/-- Characteristic sample certificate for skeleton learners. -/
structure SampleGeneratedLearnerGrammarSkeletonCharacteristicSample
    {G : WorkingMCFG N α} {obs : α → M}
    (A : SampleGeneratedLearnerGrammarSkeletonLearner G obs) (L : Set (Word α)) where
  sample : Finset (Word α)
  positive : PositiveForLanguage sample L
  exact_after_extending :
    ∀ K : Finset (Word α),
      SampleExtends sample K →
      PositiveForLanguage K L →
        SampleGeneratedLearnerGrammarSkeletonExactForLanguage (A K) L

namespace SampleGeneratedLearnerGrammarSkeletonCharacteristicSample

/-- Forget to the canonical-nonterminal characteristic-sample layer. -/
def toCanonicalLearnerNonterminalCharacteristicSample
    {G : WorkingMCFG N α} {obs : α → M}
    {A : SampleGeneratedLearnerGrammarSkeletonLearner G obs} {L : Set (Word α)}
    (C : SampleGeneratedLearnerGrammarSkeletonCharacteristicSample A L) :
    CanonicalLearnerNonterminalCharacteristicSample
      A.toCanonicalLearnerNonterminalLearner L :=
  { sample := C.sample
    positive := C.positive
    exact_after_extending := by
      intro K hExt hPos
      exact (C.exact_after_extending K hExt hPos).toCanonicalLearnerNonterminalExact }

/-- Skeleton learners identify in the limit once their characteristic-sample
exactness certificate is available. -/
theorem identifiesInLimit
    {G : WorkingMCFG N α} {obs : α → M}
    {A : SampleGeneratedLearnerGrammarSkeletonLearner G obs} {L : Set (Word α)}
    (C : SampleGeneratedLearnerGrammarSkeletonCharacteristicSample A L) :
    FiniteHypothesisIdentifiesInLimit A.toFiniteHypothesisLearner L := by
  exact C.toCanonicalLearnerNonterminalCharacteristicSample.identifiesInLimit

/-- Pointwise context-membership form of limiting identification. -/
theorem eventuallyCorrectContexts
    {G : WorkingMCFG N α} {obs : α → M}
    {A : SampleGeneratedLearnerGrammarSkeletonLearner G obs} {L : Set (Word α)}
    (C : SampleGeneratedLearnerGrammarSkeletonCharacteristicSample A L) :
    FiniteHypothesisEventuallyCorrectContexts A.toFiniteHypothesisLearner L := by
  exact C.toCanonicalLearnerNonterminalCharacteristicSample.eventuallyCorrectContexts

/-- After the threshold, listed skeleton decomposition nodes still provide
listed tuple/context/typed nonterminals. -/
theorem decomposition_node_nonterminals_after
    {G : WorkingMCFG N α} {obs : α → M}
    {A : SampleGeneratedLearnerGrammarSkeletonLearner G obs} {L : Set (Word α)}
    (C : SampleGeneratedLearnerGrammarSkeletonCharacteristicSample A L)
    {K : Finset (Word α)}
    (hExt : SampleExtends C.sample K)
    (hPos : PositiveForLanguage K L)
    (X : SampleGeneratedDecompositionNode (A K)) :
    X.tupleNonterminal ∈ (A K).nonterminals ∧
    X.contextNonterminal ∈ (A K).nonterminals ∧
    X.typedNonterminal ∈ (A K).nonterminals ∧
    X.decomposition.context ∈ SampleNamedDistribution K X.decomposition.tuple := by
  have Cexact := C.exact_after_extending K hExt hPos
  exact ⟨Cexact.decomposition_tuple_mem X,
    Cexact.decomposition_context_mem X,
    Cexact.decomposition_typed_mem X,
    X.context_mem_sampleDistribution⟩

/-- After the threshold, unit candidates still provide learner unit reachability. -/
theorem unitCandidate_reach_after
    {G : WorkingMCFG N α} {obs : α → M}
    {A : SampleGeneratedLearnerGrammarSkeletonLearner G obs} {L : Set (Word α)}
    (C : SampleGeneratedLearnerGrammarSkeletonCharacteristicSample A L)
    {K : Finset (Word α)}
    (hExt : SampleExtends C.sample K)
    (hPos : PositiveForLanguage K L)
    (U : SampleGeneratedUnitCandidate (A K)) :
    (A K).data.toSubwordContextDecompositionData.toSampleExtractedRuleLists.UnitReach
      U.pair.src.tuple U.pair.tgt.tuple := by
  have Cexact := C.exact_after_extending K hExt hPos
  exact Cexact.unitCandidate_reach U

/-- For the concrete enumerated skeleton learner, every sampled word gives a
listed skeleton decomposition node after the threshold. -/
theorem enumerated_sample_word_node_after
    {G : WorkingMCFG N α} {obs : α → M} {L : Set (Word α)}
    {f : Nat} {hfanout : 1 ≤ f} {hG : G.SemanticWorkingConditions}
    (C : SampleGeneratedLearnerGrammarSkeletonCharacteristicSample
      (enumeratedSampleGeneratedLearnerGrammarSkeletonLearner G obs f hfanout hG) L)
    {K : Finset (Word α)}
    (hExt : SampleExtends C.sample K)
    (hPos : PositiveForLanguage K L)
    {w : Word α} (hw : w ∈ K) :
    ∃ X : SampleGeneratedDecompositionNode
        ((enumeratedSampleGeneratedLearnerGrammarSkeletonLearner G obs f hfanout hG) K),
      X.decomposition.sampleWord = w ∧
      X.tupleNonterminal ∈
        ((enumeratedSampleGeneratedLearnerGrammarSkeletonLearner G obs f hfanout hG) K).nonterminals ∧
      X.contextNonterminal ∈
        ((enumeratedSampleGeneratedLearnerGrammarSkeletonLearner G obs f hfanout hG) K).nonterminals ∧
      X.typedNonterminal ∈
        ((enumeratedSampleGeneratedLearnerGrammarSkeletonLearner G obs f hfanout hG) K).nonterminals ∧
      X.decomposition.context ∈ SampleNamedDistribution K X.decomposition.tuple := by
  exact SampleGeneratedLearnerGrammarSkeletonExactForLanguage.enumerated_sample_word_node_exact
    G obs K f hfanout hG (C.exact_after_extending K hExt hPos) hw

end SampleGeneratedLearnerGrammarSkeletonCharacteristicSample

/-- Grammar-target characteristic-sample abbreviation. -/
abbrev GrammarSampleGeneratedLearnerGrammarSkeletonCharacteristicSample
    {G : WorkingMCFG N α} {obs : α → M}
    (A : SampleGeneratedLearnerGrammarSkeletonLearner G obs) :=
  SampleGeneratedLearnerGrammarSkeletonCharacteristicSample A G.StringLanguage

/-- Grammar-target abbreviation for the concrete enumerated skeleton learner. -/
abbrev GrammarEnumeratedSampleGeneratedLearnerGrammarSkeletonCharacteristicSample
    {G : WorkingMCFG N α} {obs : α → M}
    (f : Nat) (hfanout : 1 ≤ f) (hG : G.SemanticWorkingConditions) :=
  SampleGeneratedLearnerGrammarSkeletonCharacteristicSample
    (enumeratedSampleGeneratedLearnerGrammarSkeletonLearner G obs f hfanout hG)
    G.StringLanguage

end SampleGeneratedLearnerGrammarSkeletonGold

end FIv21
