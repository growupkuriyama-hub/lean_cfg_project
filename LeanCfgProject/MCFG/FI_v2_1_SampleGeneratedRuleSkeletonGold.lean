import LeanCfgProject.MCFG.FI_v2_1_SampleGeneratedRuleSkeletonExact

/-!
# FI v2.1 Lean experiment: Gold wrapper for sample-generated rule skeletons

This layer packages learners returning sample-generated rule skeletons.  The
Gold pipeline now runs through an object carrying sample-generated nonterminals,
start-rule candidates, unit-edge candidates, and certified singleton/binary rule
candidate interfaces.
-/

namespace FIv21

universe u v w

section SampleGeneratedRuleSkeletonGold

variable {N : Type w} {α : Type u}
variable [DecidableEq α]
variable {M : Type v} [Monoid M] [Fintype M]

/-- A learner returning a sample-generated rule skeleton for each finite sample. -/
def SampleGeneratedRuleSkeletonLearner
    (G : WorkingMCFG N α) (obs : α → M) :=
  (K : Finset (Word α)) → SampleGeneratedRuleSkeleton G obs K

namespace SampleGeneratedRuleSkeletonLearner

/-- Forget a rule-skeleton learner to the learner-grammar skeleton layer. -/
def toSampleGeneratedLearnerGrammarSkeletonLearner
    {G : WorkingMCFG N α} {obs : α → M}
    (A : SampleGeneratedRuleSkeletonLearner G obs) :
    SampleGeneratedLearnerGrammarSkeletonLearner G obs :=
  fun K => (A K).skeleton

/-- Forget further to the canonical-nonterminal learner. -/
def toCanonicalLearnerNonterminalLearner
    {G : WorkingMCFG N α} {obs : α → M}
    (A : SampleGeneratedRuleSkeletonLearner G obs) :
    CanonicalLearnerNonterminalLearner G obs :=
  A.toSampleGeneratedLearnerGrammarSkeletonLearner.toCanonicalLearnerNonterminalLearner

/-- Forget to the finite-hypothesis learner. -/
noncomputable def toFiniteHypothesisLearner
    {G : WorkingMCFG N α} {obs : α → M}
    (A : SampleGeneratedRuleSkeletonLearner G obs) :
    FiniteHypothesisLearner α M :=
  A.toCanonicalLearnerNonterminalLearner.toFiniteHypothesisLearner

end SampleGeneratedRuleSkeletonLearner

/-- The concrete enumerated rule-skeleton learner. -/
noncomputable def enumeratedSampleGeneratedRuleSkeletonLearner
    (G : WorkingMCFG N α) (obs : α → M)
    (f : Nat) (hfanout : 1 ≤ f) (hG : G.SemanticWorkingConditions) :
    SampleGeneratedRuleSkeletonLearner G obs :=
  fun K => enumeratedSampleGeneratedRuleSkeleton G obs K f hfanout hG

/-- Characteristic-sample certificate for rule-skeleton learners. -/
structure SampleGeneratedRuleSkeletonCharacteristicSample
    {G : WorkingMCFG N α} {obs : α → M}
    (A : SampleGeneratedRuleSkeletonLearner G obs) (L : Set (Word α)) where
  sample : Finset (Word α)
  positive : PositiveForLanguage sample L
  exact_after_extending :
    ∀ K : Finset (Word α),
      SampleExtends sample K →
      PositiveForLanguage K L →
        SampleGeneratedRuleSkeletonExactForLanguage (A K) L

namespace SampleGeneratedRuleSkeletonCharacteristicSample

/-- Forget to the learner-grammar skeleton characteristic-sample layer. -/
def toSampleGeneratedLearnerGrammarSkeletonCharacteristicSample
    {G : WorkingMCFG N α} {obs : α → M}
    {A : SampleGeneratedRuleSkeletonLearner G obs} {L : Set (Word α)}
    (C : SampleGeneratedRuleSkeletonCharacteristicSample A L) :
    SampleGeneratedLearnerGrammarSkeletonCharacteristicSample
      A.toSampleGeneratedLearnerGrammarSkeletonLearner L :=
  { sample := C.sample
    positive := C.positive
    exact_after_extending := by
      intro K hExt hPos
      exact (C.exact_after_extending K hExt hPos).toSampleGeneratedLearnerGrammarSkeletonExact }

/-- Rule-skeleton learners identify in the limit once their characteristic
sample exactness certificate is available. -/
theorem identifiesInLimit
    {G : WorkingMCFG N α} {obs : α → M}
    {A : SampleGeneratedRuleSkeletonLearner G obs} {L : Set (Word α)}
    (C : SampleGeneratedRuleSkeletonCharacteristicSample A L) :
    FiniteHypothesisIdentifiesInLimit A.toFiniteHypothesisLearner L := by
  exact C.toSampleGeneratedLearnerGrammarSkeletonCharacteristicSample.identifiesInLimit

/-- Pointwise context-membership form of limiting identification. -/
theorem eventuallyCorrectContexts
    {G : WorkingMCFG N α} {obs : α → M}
    {A : SampleGeneratedRuleSkeletonLearner G obs} {L : Set (Word α)}
    (C : SampleGeneratedRuleSkeletonCharacteristicSample A L) :
    FiniteHypothesisEventuallyCorrectContexts A.toFiniteHypothesisLearner L := by
  exact C.toSampleGeneratedLearnerGrammarSkeletonCharacteristicSample.eventuallyCorrectContexts

/-- After the threshold, listed start candidates still have listed children. -/
theorem startCandidate_child_after
    {G : WorkingMCFG N α} {obs : α → M}
    {A : SampleGeneratedRuleSkeletonLearner G obs} {L : Set (Word α)}
    (C : SampleGeneratedRuleSkeletonCharacteristicSample A L)
    {K : Finset (Word α)}
    (hExt : SampleExtends C.sample K)
    (hPos : PositiveForLanguage K L)
    {SC : SampleGeneratedStartCandidate (A K).skeleton}
    (hSC : SC ∈ (A K).startCandidates) :
    SC.child ∈ (A K).nonterminals := by
  exact (C.exact_after_extending K hExt hPos).startCandidate_child_mem hSC

/-- After the threshold, unit candidates still have listed endpoints and unit
reachability. -/
theorem unitCandidate_nodes_and_reach_after
    {G : WorkingMCFG N α} {obs : α → M}
    {A : SampleGeneratedRuleSkeletonLearner G obs} {L : Set (Word α)}
    (C : SampleGeneratedRuleSkeletonCharacteristicSample A L)
    {K : Finset (Word α)}
    (hExt : SampleExtends C.sample K)
    (hPos : PositiveForLanguage K L)
    {UC : SampleGeneratedUnitRuleCandidate (A K).skeleton}
    (hUC : UC ∈ (A K).unitCandidates) :
    UC.src ∈ (A K).nonterminals ∧
    UC.tgt ∈ (A K).nonterminals ∧
    (A K).skeleton.data.toSubwordContextDecompositionData.toSampleExtractedRuleLists.UnitReach
      UC.unit.pair.src.tuple UC.unit.pair.tgt.tuple := by
  exact (C.exact_after_extending K hExt hPos).unitCandidate_nodes_and_reach hUC

/-- For the concrete enumerated rule-skeleton learner, every sampled word gives
a listed start candidate after the threshold. -/
theorem enumerated_sample_word_start_candidate_after
    {G : WorkingMCFG N α} {obs : α → M} {L : Set (Word α)}
    {f : Nat} {hfanout : 1 ≤ f} {hG : G.SemanticWorkingConditions}
    (C : SampleGeneratedRuleSkeletonCharacteristicSample
      (enumeratedSampleGeneratedRuleSkeletonLearner G obs f hfanout hG) L)
    {K : Finset (Word α)}
    (hExt : SampleExtends C.sample K)
    (hPos : PositiveForLanguage K L)
    {w : Word α} (hw : w ∈ K) :
    ∃ SC : SampleGeneratedStartCandidate
        ((enumeratedSampleGeneratedRuleSkeletonLearner G obs f hfanout hG) K).skeleton,
      SC.node.decomposition.sampleWord = w ∧
      SC.child ∈
        ((enumeratedSampleGeneratedRuleSkeletonLearner G obs f hfanout hG) K).nonterminals ∧
      SC.node.decomposition.context ∈
        SampleNamedDistribution K SC.node.decomposition.tuple := by
  exact SampleGeneratedRuleSkeletonExactForLanguage.enumerated_sample_word_start_candidate_exact
    G obs K f hfanout hG (C.exact_after_extending K hExt hPos) hw

end SampleGeneratedRuleSkeletonCharacteristicSample

/-- Grammar-target abbreviation for rule-skeleton characteristic samples. -/
abbrev GrammarSampleGeneratedRuleSkeletonCharacteristicSample
    {G : WorkingMCFG N α} {obs : α → M}
    (A : SampleGeneratedRuleSkeletonLearner G obs) :=
  SampleGeneratedRuleSkeletonCharacteristicSample A G.StringLanguage

end SampleGeneratedRuleSkeletonGold

end FIv21
