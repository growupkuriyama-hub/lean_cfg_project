import LeanCfgProject.MCFG.FI_v2_1_ConcreteSampleConsistency

/-!
# FI v2.1 Lean experiment: exactness plus sample-context consistency

This thirty-sixth layer combines concrete extracted-sample exactness with the
automatic sample-context consistency certificate from the previous layer.
-/

namespace FIv21

universe u v w

section ConcreteSampleConsistencyExact

variable {N : Type w} {α : Type u}
variable [DecidableEq α]
variable {M : Type v} [Monoid M] [Fintype M]

/-- Exact and sample-context-consistent concrete extracted data. -/
structure ConcreteExtractedSampleExactAndConsistentForLanguage
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (E : ConcreteExtractedSampleData G obs K) (L : Set (Word α)) : Prop where
  exact : ConcreteExtractedSampleExactForLanguage E L
  consistent : ConcreteExtractedSampleContextConsistency E

namespace ConcreteExtractedSampleExactAndConsistentForLanguage

/-- Any exact concrete extraction is automatically sample-context consistent. -/
def ofExact
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {E : ConcreteExtractedSampleData G obs K} {L : Set (Word α)}
    (C : ConcreteExtractedSampleExactForLanguage E L) :
    ConcreteExtractedSampleExactAndConsistentForLanguage E L :=
  { exact := C
    consistent := ConcreteExtractedSampleContextConsistency.holds E }

/-- Positivity projection. -/
theorem positive
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {E : ConcreteExtractedSampleData G obs K} {L : Set (Word α)}
    (C : ConcreteExtractedSampleExactAndConsistentForLanguage E L) :
    PositiveForLanguage E.toFiniteLearnerHypothesis.sampleSet L := by
  exact C.exact.positive

/-- Fixed-substitutability projection. -/
theorem substitutable
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {E : ConcreteExtractedSampleData G obs K} {L : Set (Word α)}
    (C : ConcreteExtractedSampleExactAndConsistentForLanguage E L) :
    FixedNamedTupleSubstitutable E.f obs L := by
  exact C.exact.substitutable

/-- Exact equality of extracted and target distributions. -/
theorem approxDistribution_exact
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {E : ConcreteExtractedSampleData G obs K} {L : Set (Word α)}
    (C : ConcreteExtractedSampleExactAndConsistentForLanguage E L)
    {d : Nat} (x : Tuple α d) :
    E.ApproxDistribution x = NamedDistribution L x := by
  exact C.exact.approxDistribution_exact x

/-- Exact context-membership form. -/
theorem licensed_iff_target_context
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {E : ConcreteExtractedSampleData G obs K} {L : Set (Word α)}
    (C : ConcreteExtractedSampleExactAndConsistentForLanguage E L)
    {d : Nat} (x : Tuple α d) (c : NamedSentenceContext α d) :
    c ∈ E.ApproxDistribution x ↔ c ∈ NamedDistribution L x := by
  exact C.exact.licensed_iff_target_context x c

/-- Every sample-observed context belongs to the exact target distribution. -/
theorem sample_context_in_target_distribution
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {E : ConcreteExtractedSampleData G obs K} {L : Set (Word α)}
    (C : ConcreteExtractedSampleExactAndConsistentForLanguage E L)
    {d : Nat} (x : Tuple α d) (c : NamedSentenceContext α d)
    (hc : c ∈ SampleNamedDistribution K x) :
    c ∈ NamedDistribution L x := by
  have hlic : c ∈ E.ApproxDistribution x :=
    C.consistent.sample_contexts_licensed x c hc
  exact (C.licensed_iff_target_context x c).1 hlic

end ConcreteExtractedSampleExactAndConsistentForLanguage

/-- Grammar-target abbreviation. -/
abbrev ConcreteExtractedSampleExactAndConsistentForGrammar
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (E : ConcreteExtractedSampleData G obs K) :=
  ConcreteExtractedSampleExactAndConsistentForLanguage E G.StringLanguage

end ConcreteSampleConsistencyExact

end FIv21
