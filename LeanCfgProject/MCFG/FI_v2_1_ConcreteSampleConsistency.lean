import LeanCfgProject.MCFG.FI_v2_1_ConcreteExtractedSampleGold

/-!
# FI v2.1 Lean experiment: sample-context consistency for concrete extractions

This thirty-fifth layer records the most basic sample-consistency property of
concrete extracted sample data.

The learner's transported-context approximation is defined so that every
context actually observed in the finite sample is licensed for the tuple where
it was observed.  This is weaker than full sample generation by a canonical MCFG
hypothesis, but it is the distributional sample-consistency statement that is
available at the current stage of the formalization.
-/

namespace FIv21

universe u v w

section ConcreteSampleConsistency

variable {N : Type w} {α : Type u}
variable [DecidableEq α]
variable {M : Type v} [Monoid M] [Fintype M]

/-- Sample-context consistency for concrete extracted sample data.

Every named context observed in the finite sample is licensed by the extracted
finite hypothesis for the tuple where it was observed. -/
structure ConcreteExtractedSampleContextConsistency
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (E : ConcreteExtractedSampleData G obs K) : Prop where
  sample_contexts_licensed :
    ∀ {d : Nat} (x : Tuple α d) (c : NamedSentenceContext α d),
      c ∈ SampleNamedDistribution K x → c ∈ E.ApproxDistribution x

namespace ConcreteExtractedSampleContextConsistency

/-- Concrete extracted sample data is automatically sample-context consistent:
observed sample contexts are licensed by reflexive unit reachability. -/
theorem holds
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (E : ConcreteExtractedSampleData G obs K) :
    ConcreteExtractedSampleContextConsistency E := by
  refine ⟨?_⟩
  intro d x c hc
  have hsample : E.toFiniteLearnerHypothesis.sampleSet = K :=
    E.finiteHypothesis_sampleSet
  have hcH : c ∈ SampleNamedDistribution
      E.toFiniteLearnerHypothesis.sampleSet x := by
    simpa [hsample] using hc
  have hlic : c ∈ E.toFiniteLearnerHypothesis.ApproxDistribution x := by
    exact sample_context_subset_learnerApproxDistribution
      E.toFiniteLearnerHypothesis.sampleSet
      E.toFiniteLearnerHypothesis.obs
      E.toFiniteLearnerHypothesis.f
      x hcH
  simpa [ConcreteExtractedSampleData.ApproxDistribution,
    RelativeSampleExtraction.ApproxDistribution] using hlic

/-- Sample-context consistency can be stated as an inclusion of the sample
named distribution into the extracted approximation. -/
theorem sampleDistribution_subset_approxDistribution
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {E : ConcreteExtractedSampleData G obs K}
    (C : ConcreteExtractedSampleContextConsistency E)
    {d : Nat} (x : Tuple α d) :
    SampleNamedDistribution K x ⊆ E.ApproxDistribution x := by
  intro c hc
  exact C.sample_contexts_licensed x c hc

/-- If the extracted approximation is sound for a target language, then every
sample-observed context is a true target context. -/
theorem sample_context_sound_for_language
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {E : ConcreteExtractedSampleData G obs K}
    (C : ConcreteExtractedSampleContextConsistency E)
    {L : Set (Word α)}
    (hK : PositiveForLanguage E.toFiniteLearnerHypothesis.sampleSet L)
    (hL : FixedNamedTupleSubstitutable E.f obs L)
    {d : Nat} (x : Tuple α d) (c : NamedSentenceContext α d)
    (hc : c ∈ SampleNamedDistribution K x) :
    c ∈ NamedDistribution L x := by
  have hlic : c ∈ E.ApproxDistribution x :=
    C.sample_contexts_licensed x c hc
  exact E.approxDistribution_sound_for_language hK hL x hlic

/-- The automatic consistency certificate gives the same sample-context
soundness statement. -/
theorem automatic_sample_context_sound_for_language
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (E : ConcreteExtractedSampleData G obs K)
    {L : Set (Word α)}
    (hK : PositiveForLanguage E.toFiniteLearnerHypothesis.sampleSet L)
    (hL : FixedNamedTupleSubstitutable E.f obs L)
    {d : Nat} (x : Tuple α d) (c : NamedSentenceContext α d)
    (hc : c ∈ SampleNamedDistribution K x) :
    c ∈ NamedDistribution L x := by
  exact sample_context_sound_for_language (holds E) hK hL x c hc

end ConcreteExtractedSampleContextConsistency

end ConcreteSampleConsistency

end FIv21
