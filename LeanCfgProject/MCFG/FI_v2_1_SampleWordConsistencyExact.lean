import LeanCfgProject.MCFG.FI_v2_1_SampleWordConsistencySkeleton

/-!
# FI v2.1 Lean experiment: exactness with sample-word consistency

This thirty-ninth layer combines the earlier exact/context-consistency package
with the new sample-word consistency skeleton.
-/

namespace FIv21

universe u v w

section SampleWordConsistencyExact

variable {N : Type w} {α : Type u}
variable [DecidableEq α]
variable {M : Type v} [Monoid M] [Fintype M]

/-- Exact concrete extracted data, together with both sample-context consistency
and sample-word consistency. -/
structure ConcreteExtractedSampleExactContextWordForLanguage
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (E : ConcreteExtractedSampleData G obs K) (L : Set (Word α)) : Prop where
  exact_and_context : ConcreteExtractedSampleExactAndConsistentForLanguage E L
  word_consistent : ConcreteExtractedSampleWordConsistencyForLanguage E L

namespace ConcreteExtractedSampleExactContextWordForLanguage

/-- Exact/context-consistent data automatically has the word-consistency
component. -/
def ofExactAndContext
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {E : ConcreteExtractedSampleData G obs K} {L : Set (Word α)}
    (C : ConcreteExtractedSampleExactAndConsistentForLanguage E L) :
    ConcreteExtractedSampleExactContextWordForLanguage E L :=
  { exact_and_context := C
    word_consistent :=
      ConcreteExtractedSampleWordConsistencyForLanguage.ofExactAndConsistentForLanguage C }

/-- Exactness alone is enough, since context and word consistency are automatic
at this interface level. -/
def ofExact
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {E : ConcreteExtractedSampleData G obs K} {L : Set (Word α)}
    (C : ConcreteExtractedSampleExactForLanguage E L) :
    ConcreteExtractedSampleExactContextWordForLanguage E L :=
  ofExactAndContext
    (ConcreteExtractedSampleExactAndConsistentForLanguage.ofExact C)

/-- Positivity for the finite hypothesis sample. -/
theorem positive_for_hypothesis_sample
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {E : ConcreteExtractedSampleData G obs K} {L : Set (Word α)}
    (C : ConcreteExtractedSampleExactContextWordForLanguage E L) :
    PositiveForLanguage E.toFiniteLearnerHypothesis.sampleSet L := by
  exact C.exact_and_context.positive

/-- Positivity for the external sample `K`. -/
theorem positive_for_external_sample
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {E : ConcreteExtractedSampleData G obs K} {L : Set (Word α)}
    (C : ConcreteExtractedSampleExactContextWordForLanguage E L) :
    PositiveForLanguage K L := by
  exact C.word_consistent.positive

/-- Pointwise target membership for an external sample word. -/
theorem sample_word_in_target
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {E : ConcreteExtractedSampleData G obs K} {L : Set (Word α)}
    (C : ConcreteExtractedSampleExactContextWordForLanguage E L)
    (w : Word α) (hw : w ∈ K) :
    w ∈ L := by
  exact C.word_consistent.sample_word_in_target w hw

/-- Exact equality of the extracted approximation and the target distribution. -/
theorem approxDistribution_exact
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {E : ConcreteExtractedSampleData G obs K} {L : Set (Word α)}
    (C : ConcreteExtractedSampleExactContextWordForLanguage E L)
    {d : Nat} (x : Tuple α d) :
    E.ApproxDistribution x = NamedDistribution L x := by
  exact C.exact_and_context.approxDistribution_exact x

/-- Sample-observed contexts are target contexts. -/
theorem sample_context_in_target_distribution
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {E : ConcreteExtractedSampleData G obs K} {L : Set (Word α)}
    (C : ConcreteExtractedSampleExactContextWordForLanguage E L)
    {d : Nat} (x : Tuple α d) (c : NamedSentenceContext α d)
    (hc : c ∈ SampleNamedDistribution K x) :
    c ∈ NamedDistribution L x := by
  exact C.exact_and_context.sample_context_in_target_distribution x c hc

end ConcreteExtractedSampleExactContextWordForLanguage

/-- Grammar-target abbreviation. -/
abbrev ConcreteExtractedSampleExactContextWordForGrammar
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (E : ConcreteExtractedSampleData G obs K) :=
  ConcreteExtractedSampleExactContextWordForLanguage E G.StringLanguage

namespace ConcreteExtractedSampleExactContextWordForGrammar

/-- In the grammar-target case, every external sample word has a start-symbol
witness in the target grammar. -/
theorem sample_word_start_derives
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {E : ConcreteExtractedSampleData G obs K}
    (C : ConcreteExtractedSampleExactContextWordForGrammar E)
    (w : Word α) (hw : w ∈ K) :
    ∃ h : 1 = G.arity G.start,
      DerivesTuple G G.start (castTuple h (singletonTuple w)) := by
  exact start_derives_of_mem_StringLanguage G w
    (C.sample_word_in_target w hw)

end ConcreteExtractedSampleExactContextWordForGrammar

end SampleWordConsistencyExact

end FIv21
