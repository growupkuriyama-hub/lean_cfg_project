import LeanCfgProject.MCFG.FI_v2_1_SampleGeneratedRuleSkeleton

/-!
# FI v2.1 Lean experiment: exactness wrapper for sample-generated rule skeletons

This layer attaches the previously checked skeleton exactness certificate to the
new rule-skeleton view.  Its main purpose is to ensure that exactness can now be
carried while referring to start, terminal, concatenation, and unit candidates.
-/

namespace FIv21

universe u v w

section SampleGeneratedRuleSkeletonExact

variable {N : Type w} {α : Type u}
variable [DecidableEq α]
variable {M : Type v} [Monoid M] [Fintype M]

/-- Exactness certificate for a sample-generated rule skeleton.  The semantic
content is inherited from the learner-grammar skeleton layer. -/
structure SampleGeneratedRuleSkeletonExactForLanguage
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (R : SampleGeneratedRuleSkeleton G obs K) (L : Set (Word α)) where
  base : SampleGeneratedLearnerGrammarSkeletonExactForLanguage R.skeleton L

namespace SampleGeneratedRuleSkeletonExactForLanguage

/-- Forget to the previous learner-grammar skeleton exactness layer. -/
def toSampleGeneratedLearnerGrammarSkeletonExact
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {R : SampleGeneratedRuleSkeleton G obs K} {L : Set (Word α)}
    (C : SampleGeneratedRuleSkeletonExactForLanguage R L) :
    SampleGeneratedLearnerGrammarSkeletonExactForLanguage R.skeleton L :=
  C.base

/-- Forget further to the canonical-nonterminal exactness layer. -/
def toCanonicalLearnerNonterminalExact
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {R : SampleGeneratedRuleSkeleton G obs K} {L : Set (Word α)}
    (C : SampleGeneratedRuleSkeletonExactForLanguage R L) :
    CanonicalLearnerNonterminalExactForLanguage R.skeleton.data L :=
  C.base.toCanonicalLearnerNonterminalExact

/-- Exact rule skeletons still list the root nonterminal. -/
theorem root_mem_nonterminals
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {R : SampleGeneratedRuleSkeleton G obs K} {L : Set (Word α)}
    (_C : SampleGeneratedRuleSkeletonExactForLanguage R L) :
    SampleGeneratedLearnerGrammarSkeleton.root (α := α) (M := M) ∈
      R.nonterminals := by
  exact R.root_mem_nonterminals

/-- Exact rule skeletons preserve start-candidate child membership. -/
theorem startCandidate_child_mem
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {R : SampleGeneratedRuleSkeleton G obs K} {L : Set (Word α)}
    (_C : SampleGeneratedRuleSkeletonExactForLanguage R L)
    {SC : SampleGeneratedStartCandidate R.skeleton}
    (hSC : SC ∈ R.startCandidates) :
    SC.child ∈ R.nonterminals := by
  exact R.startCandidate_child_mem hSC

/-- Exact rule skeletons preserve terminal-candidate well-typedness. -/
theorem terminalCandidate_wellTyped
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {R : SampleGeneratedRuleSkeleton G obs K} {L : Set (Word α)}
    (_C : SampleGeneratedRuleSkeletonExactForLanguage R L)
    (TC : SampleGeneratedTerminalCandidate R.skeleton) :
    TC.toTerminalRule.WellTyped (canonicalLearnerArity (α := α) (M := M)) := by
  exact TC.wellTyped

/-- Exact rule skeletons preserve concatenation-candidate endpoint membership. -/
theorem concatCandidate_nodes
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {R : SampleGeneratedRuleSkeleton G obs K} {L : Set (Word α)}
    (_C : SampleGeneratedRuleSkeletonExactForLanguage R L)
    (BC : SampleGeneratedConcatCandidate R.skeleton) :
    BC.left.tupleNonterminal ∈ R.nonterminals ∧
    BC.right.tupleNonterminal ∈ R.nonterminals ∧
    BC.result.tupleNonterminal ∈ R.nonterminals ∧
    BC.toBinaryRule.Nondeleting := by
  exact ⟨BC.left_mem_nonterminals, BC.right_mem_nonterminals,
    BC.result_mem_nonterminals, BC.nondeleting⟩

/-- Exact rule skeletons preserve unit-candidate endpoint membership and unit
reachability. -/
theorem unitCandidate_nodes_and_reach
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {R : SampleGeneratedRuleSkeleton G obs K} {L : Set (Word α)}
    (_C : SampleGeneratedRuleSkeletonExactForLanguage R L)
    {UC : SampleGeneratedUnitRuleCandidate R.skeleton}
    (hUC : UC ∈ R.unitCandidates) :
    UC.src ∈ R.nonterminals ∧
    UC.tgt ∈ R.nonterminals ∧
    R.skeleton.data.toSubwordContextDecompositionData.toSampleExtractedRuleLists.UnitReach
      UC.unit.pair.src.tuple UC.unit.pair.tgt.tuple := by
  exact R.unitCandidate_nodes_and_reach hUC

/-- Exact concrete enumerated rule skeletons still represent every sampled word
by a start candidate. -/
theorem enumerated_sample_word_start_candidate_exact
    (G : WorkingMCFG N α) (obs : α → M) (K : Finset (Word α))
    (f : Nat) (hfanout : 1 ≤ f) (hG : G.SemanticWorkingConditions)
    {L : Set (Word α)}
    (_C : SampleGeneratedRuleSkeletonExactForLanguage
      (enumeratedSampleGeneratedRuleSkeleton G obs K f hfanout hG) L)
    {w : Word α} (hw : w ∈ K) :
    ∃ SC : SampleGeneratedStartCandidate
        (enumeratedSampleGeneratedRuleSkeleton G obs K f hfanout hG).skeleton,
      SC.node.decomposition.sampleWord = w ∧
      SC.child ∈
        (enumeratedSampleGeneratedRuleSkeleton G obs K f hfanout hG).nonterminals ∧
      SC.node.decomposition.context ∈
        SampleNamedDistribution K SC.node.decomposition.tuple := by
  exact enumeratedRuleSkeleton_sample_word_start_candidate G obs K f hfanout hG hw

end SampleGeneratedRuleSkeletonExactForLanguage

/-- Grammar-target abbreviation. -/
abbrev SampleGeneratedRuleSkeletonExactForGrammar
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (R : SampleGeneratedRuleSkeleton G obs K) :=
  SampleGeneratedRuleSkeletonExactForLanguage R G.StringLanguage

end SampleGeneratedRuleSkeletonExact

end FIv21
