import LeanCfgProject.MCFG.FI_v2_1_RelativeSampleExtraction

/-!
# FI v2.1 Lean experiment: exactness for relative sample extractions

This thirtieth layer packages the exactness condition for the
sample-extraction interface introduced in the previous file.

The condition is deliberately distributional: the finite learner hypothesis
obtained from the sample extraction has exactly the target named-context
distributions.  This is the level already supported by the reconstruction and
Gold-stabilization layers.
-/

namespace FIv21

universe u v w

section RelativeSampleExtractionExact

variable {N : Type w} {α : Type u}
variable [DecidableEq α]
variable {M : Type v} [Monoid M] [Fintype M]

/-- Exactness of a relative sample-extraction certificate for a target language.

This simply reuses the already-checked exactness interface for finite learner
hypotheses after forgetting the grammar-side refined-rule enumeration. -/
structure RelativeSampleExtractionExactForLanguage
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (E : RelativeSampleExtraction G obs K) (L : Set (Word α)) : Prop where
  hypExact : FiniteLearnerHypothesis.ExactForLanguage
    E.toFiniteLearnerHypothesis L

namespace RelativeSampleExtractionExactForLanguage

/-- Positivity part of exactness. -/
theorem positive
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {E : RelativeSampleExtraction G obs K} {L : Set (Word α)}
    (C : RelativeSampleExtractionExactForLanguage E L) :
    PositiveForLanguage E.toFiniteLearnerHypothesis.sampleSet L :=
  C.hypExact.positive

/-- Fixed-substitutability part of exactness. -/
theorem substitutable
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {E : RelativeSampleExtraction G obs K} {L : Set (Word α)}
    (C : RelativeSampleExtractionExactForLanguage E L) :
    FixedNamedTupleSubstitutable E.f obs L :=
  C.hypExact.substitutable

/-- Completeness part of exactness. -/
theorem complete
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {E : RelativeSampleExtraction G obs K} {L : Set (Word α)}
    (C : RelativeSampleExtractionExactForLanguage E L) :
    E.toFiniteLearnerHypothesis.CompleteForLanguage L :=
  C.hypExact.complete

/-- Exact equality between the extracted approximation and the target
distribution. -/
theorem approxDistribution_exact
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {E : RelativeSampleExtraction G obs K} {L : Set (Word α)}
    (C : RelativeSampleExtractionExactForLanguage E L)
    {d : Nat} (x : Tuple α d) :
    E.ApproxDistribution x = NamedDistribution L x := by
  exact FiniteLearnerHypothesis.ExactForLanguage.approxDistribution_exact
    C.hypExact x

/-- Pointwise context-membership form of exactness. -/
theorem licensed_iff_target_context
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {E : RelativeSampleExtraction G obs K} {L : Set (Word α)}
    (C : RelativeSampleExtractionExactForLanguage E L)
    {d : Nat} (x : Tuple α d) (c : NamedSentenceContext α d) :
    c ∈ E.ApproxDistribution x ↔ c ∈ NamedDistribution L x := by
  rw [C.approxDistribution_exact x]

/-- Exactness implies soundness of the extracted approximation. -/
theorem approxDistribution_subset_target
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {E : RelativeSampleExtraction G obs K} {L : Set (Word α)}
    (C : RelativeSampleExtractionExactForLanguage E L)
    {d : Nat} (x : Tuple α d) :
    E.ApproxDistribution x ⊆ NamedDistribution L x := by
  intro c hc
  exact (C.licensed_iff_target_context x c).1 hc

/-- Exactness implies completeness of the extracted approximation. -/
theorem target_subset_approxDistribution
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {E : RelativeSampleExtraction G obs K} {L : Set (Word α)}
    (C : RelativeSampleExtractionExactForLanguage E L)
    {d : Nat} (x : Tuple α d) :
    NamedDistribution L x ⊆ E.ApproxDistribution x := by
  intro c hc
  exact (C.licensed_iff_target_context x c).2 hc

end RelativeSampleExtractionExactForLanguage

/-- Exactness of a relative sample extraction for the string language of a
working grammar. -/
abbrev RelativeSampleExtractionExactForGrammar
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (E : RelativeSampleExtraction G obs K) :=
  RelativeSampleExtractionExactForLanguage E G.StringLanguage

end RelativeSampleExtractionExact

end FIv21
