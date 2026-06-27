import LeanCfgProject.MCFG.FI_v2_1_ConcreteExtractedSampleData

/-!
# FI v2.1 Lean experiment: exactness for concrete extracted sample data

This thirty-third layer specializes the relative exactness interface to the
more implementation-facing `ConcreteExtractedSampleData` structure.
-/

namespace FIv21

universe u v w

section ConcreteExtractedSampleExact

variable {N : Type w} {α : Type u}
variable [DecidableEq α]
variable {M : Type v} [Monoid M] [Fintype M]

/-- Exactness of concrete extracted data for an abstract target language. -/
structure ConcreteExtractedSampleExactForLanguage
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (E : ConcreteExtractedSampleData G obs K) (L : Set (Word α)) : Prop where
  relativeExact : RelativeSampleExtractionExactForLanguage
    E.toRelativeSampleExtraction L

namespace ConcreteExtractedSampleExactForLanguage

/-- Forget to the finite-hypothesis exactness certificate. -/
theorem hypExact
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {E : ConcreteExtractedSampleData G obs K} {L : Set (Word α)}
    (C : ConcreteExtractedSampleExactForLanguage E L) :
    FiniteLearnerHypothesis.ExactForLanguage
      E.toFiniteLearnerHypothesis L := by
  exact C.relativeExact.hypExact

/-- Positivity part of exactness. -/
theorem positive
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {E : ConcreteExtractedSampleData G obs K} {L : Set (Word α)}
    (C : ConcreteExtractedSampleExactForLanguage E L) :
    PositiveForLanguage E.toFiniteLearnerHypothesis.sampleSet L := by
  exact C.relativeExact.positive

/-- Fixed-substitutability part of exactness. -/
theorem substitutable
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {E : ConcreteExtractedSampleData G obs K} {L : Set (Word α)}
    (C : ConcreteExtractedSampleExactForLanguage E L) :
    FixedNamedTupleSubstitutable E.f obs L := by
  exact C.relativeExact.substitutable

/-- Completeness part of exactness. -/
theorem complete
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {E : ConcreteExtractedSampleData G obs K} {L : Set (Word α)}
    (C : ConcreteExtractedSampleExactForLanguage E L) :
    E.toFiniteLearnerHypothesis.CompleteForLanguage L := by
  exact C.relativeExact.complete

/-- Exact equality of the concrete extracted approximation and the target
distribution. -/
theorem approxDistribution_exact
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {E : ConcreteExtractedSampleData G obs K} {L : Set (Word α)}
    (C : ConcreteExtractedSampleExactForLanguage E L)
    {d : Nat} (x : Tuple α d) :
    E.ApproxDistribution x = NamedDistribution L x := by
  exact C.relativeExact.approxDistribution_exact x

/-- Pointwise context-membership exactness. -/
theorem licensed_iff_target_context
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {E : ConcreteExtractedSampleData G obs K} {L : Set (Word α)}
    (C : ConcreteExtractedSampleExactForLanguage E L)
    {d : Nat} (x : Tuple α d) (c : NamedSentenceContext α d) :
    c ∈ E.ApproxDistribution x ↔ c ∈ NamedDistribution L x := by
  exact C.relativeExact.licensed_iff_target_context x c

/-- Soundness half of exactness. -/
theorem approxDistribution_subset_target
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {E : ConcreteExtractedSampleData G obs K} {L : Set (Word α)}
    (C : ConcreteExtractedSampleExactForLanguage E L)
    {d : Nat} (x : Tuple α d) :
    E.ApproxDistribution x ⊆ NamedDistribution L x := by
  exact C.relativeExact.approxDistribution_subset_target x

/-- Completeness half of exactness. -/
theorem target_subset_approxDistribution
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {E : ConcreteExtractedSampleData G obs K} {L : Set (Word α)}
    (C : ConcreteExtractedSampleExactForLanguage E L)
    {d : Nat} (x : Tuple α d) :
    NamedDistribution L x ⊆ E.ApproxDistribution x := by
  exact C.relativeExact.target_subset_approxDistribution x

end ConcreteExtractedSampleExactForLanguage

/-- Grammar-target exactness abbreviation for concrete extracted data. -/
abbrev ConcreteExtractedSampleExactForGrammar
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (E : ConcreteExtractedSampleData G obs K) :=
  ConcreteExtractedSampleExactForLanguage E G.StringLanguage

end ConcreteExtractedSampleExact

end FIv21
