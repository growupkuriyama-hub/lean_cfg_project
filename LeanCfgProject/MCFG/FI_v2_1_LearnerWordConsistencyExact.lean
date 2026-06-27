import LeanCfgProject.MCFG.FI_v2_1_LearnerWordConsistencySkeleton

/-!
# FI v2.1 Lean experiment: exact extraction with learner-side word consistency

This forty-fifth layer combines the target-side exact/context/word/start
certificate with a learner-side sample-word consistency obligation.  The latter
is still parameterized by a proposed learner-side word language, since the full
canonical learner grammar is not yet part of the formalization.
-/

namespace FIv21

universe u v w

section LearnerWordConsistencyExact

variable {N : Type w} {α : Type u}
variable [DecidableEq α]
variable {M : Type v} [Monoid M] [Fintype M]

/-- Exact concrete extraction for a grammar target, together with an abstract
learner-side statement that the extracted learner explains the external sample
words. -/
structure ConcreteExtractedSampleExactStartLearnerWordForGrammar
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (E : ConcreteExtractedSampleData G obs K) (LH : Set (Word α)) : Prop where
  exact_start : ConcreteExtractedSampleExactContextWordStartForGrammar E
  learner_word : ConcreteExtractedSampleLearnerWordConsistent E LH

namespace ConcreteExtractedSampleExactStartLearnerWordForGrammar

/-- Forget the learner-side word-consistency field. -/
def toExactContextWordStart
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {E : ConcreteExtractedSampleData G obs K} {LH : Set (Word α)}
    (C : ConcreteExtractedSampleExactStartLearnerWordForGrammar E LH) :
    ConcreteExtractedSampleExactContextWordStartForGrammar E :=
  C.exact_start

/-- Keep only the learner-side sample-word consistency field. -/
theorem learnerWordConsistent
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {E : ConcreteExtractedSampleData G obs K} {LH : Set (Word α)}
    (C : ConcreteExtractedSampleExactStartLearnerWordForGrammar E LH) :
    ConcreteExtractedSampleLearnerWordConsistent E LH := by
  exact C.learner_word

/-- Exact equality of extracted and target named-context distributions. -/
theorem approxDistribution_exact
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {E : ConcreteExtractedSampleData G obs K} {LH : Set (Word α)}
    (C : ConcreteExtractedSampleExactStartLearnerWordForGrammar E LH)
    {d : Nat} (x : Tuple α d) :
    E.ApproxDistribution x = NamedDistribution G.StringLanguage x := by
  exact C.exact_start.approxDistribution_exact x

/-- Exact context-membership form. -/
theorem licensed_iff_target_context
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {E : ConcreteExtractedSampleData G obs K} {LH : Set (Word α)}
    (C : ConcreteExtractedSampleExactStartLearnerWordForGrammar E LH)
    {d : Nat} (x : Tuple α d) (c : NamedSentenceContext α d) :
    c ∈ E.ApproxDistribution x ↔ c ∈ NamedDistribution G.StringLanguage x := by
  exact C.exact_start.licensed_iff_target_context x c

/-- Target-side start-symbol derivation witness for a sampled word. -/
theorem sample_word_start_derives
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {E : ConcreteExtractedSampleData G obs K} {LH : Set (Word α)}
    (C : ConcreteExtractedSampleExactStartLearnerWordForGrammar E LH)
    (w : Word α) (hw : w ∈ K) :
    ∃ h : 1 = G.arity G.start,
      DerivesTuple G G.start (castTuple h (singletonTuple w)) := by
  exact C.exact_start.sample_word_start_derives w hw

/-- Target-side membership of a sampled word. -/
theorem sample_word_in_target
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {E : ConcreteExtractedSampleData G obs K} {LH : Set (Word α)}
    (C : ConcreteExtractedSampleExactStartLearnerWordForGrammar E LH)
    (w : Word α) (hw : w ∈ K) :
    w ∈ G.StringLanguage := by
  exact C.exact_start.sample_word_in_stringLanguage w hw

/-- Learner-side generation of a sampled word, relative to the proposed learner
word language `LH`. -/
theorem sample_word_generated_by_learner
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {E : ConcreteExtractedSampleData G obs K} {LH : Set (Word α)}
    (C : ConcreteExtractedSampleExactStartLearnerWordForGrammar E LH)
    (w : Word α) (hw : w ∈ K) :
    w ∈ LH := by
  exact ConcreteExtractedSampleLearnerWordConsistent.sample_word_generated
    C.learner_word w hw

/-- Positivity for the external sample, recovered from the target-side start
witnesses. -/
theorem positiveSample
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {E : ConcreteExtractedSampleData G obs K} {LH : Set (Word α)}
    (C : ConcreteExtractedSampleExactStartLearnerWordForGrammar E LH) :
    PositiveSample G K := by
  exact C.exact_start.positiveSample

end ConcreteExtractedSampleExactStartLearnerWordForGrammar

end LearnerWordConsistencyExact

end FIv21
