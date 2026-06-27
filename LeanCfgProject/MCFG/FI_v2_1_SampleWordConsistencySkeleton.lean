import LeanCfgProject.MCFG.FI_v2_1_ConcreteSampleConsistencyGold

/-!
# FI v2.1 Lean experiment: sample-word consistency skeleton

This thirty-eighth layer moves from sample-context consistency toward the more
familiar sample-word consistency statement.

The current development still does not define a full canonical learner grammar,
so we do not claim that an extracted grammar generates every sampled word.
Instead, this file isolates the semantic skeleton that is already available:
all sampled words belong to the target language, and in the grammar-target case
this can be unpacked into a start-symbol derivation witness.
-/

namespace FIv21

universe u v w

section SampleWordConsistencySkeleton

variable {N : Type w} {α : Type u}
variable [DecidableEq α]
variable {M : Type v} [Monoid M] [Fintype M]

/-- Sample-word consistency for an abstract target language.

This is just positivity, repackaged under the name used by the learner-facing
interface: every externally sampled word is a target word. -/
structure SampleWordLanguageConsistency
    (K : Finset (Word α)) (L : Set (Word α)) : Prop where
  sample_words_in_target : PositiveForLanguage K L

namespace SampleWordLanguageConsistency

/-- Build sample-word consistency from the already used positivity predicate. -/
def ofPositive
    {K : Finset (Word α)} {L : Set (Word α)}
    (hK : PositiveForLanguage K L) :
    SampleWordLanguageConsistency K L :=
  { sample_words_in_target := hK }

/-- Forget sample-word consistency back to positivity. -/
theorem positive
    {K : Finset (Word α)} {L : Set (Word α)}
    (C : SampleWordLanguageConsistency K L) :
    PositiveForLanguage K L := by
  exact C.sample_words_in_target

/-- Pointwise target membership for a sampled word. -/
theorem sample_word_in_target
    {K : Finset (Word α)} {L : Set (Word α)}
    (C : SampleWordLanguageConsistency K L)
    (w : Word α) (hw : w ∈ K) :
    w ∈ L := by
  exact C.sample_words_in_target w hw

end SampleWordLanguageConsistency

/-- Grammar-target sample-word consistency. -/
abbrev SampleWordStartConsistency
    (G : WorkingMCFG N α) (K : Finset (Word α)) : Prop :=
  SampleWordLanguageConsistency K G.StringLanguage

namespace SampleWordStartConsistency

/-- A grammar-target sample word has a start-symbol derivation witness. -/
theorem sample_word_start_derives
    {G : WorkingMCFG N α} {K : Finset (Word α)}
    (C : SampleWordStartConsistency G K)
    (w : Word α) (hw : w ∈ K) :
    ∃ h : 1 = G.arity G.start,
      DerivesTuple G G.start (castTuple h (singletonTuple w)) := by
  exact start_derives_of_mem_StringLanguage G w
    (C.sample_words_in_target w hw)

/-- Positivity for a grammar target is the same data as this skeleton. -/
def ofPositiveSample
    {G : WorkingMCFG N α} {K : Finset (Word α)}
    (hK : PositiveSample G K) :
    SampleWordStartConsistency G K :=
  SampleWordLanguageConsistency.ofPositive
    (positiveForLanguage_of_positiveSample G K hK)

end SampleWordStartConsistency

/-- Sample-word consistency carried by concrete extracted sample data. -/
structure ConcreteExtractedSampleWordConsistencyForLanguage
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (E : ConcreteExtractedSampleData G obs K) (L : Set (Word α)) : Prop where
  words : SampleWordLanguageConsistency K L

namespace ConcreteExtractedSampleWordConsistencyForLanguage

/-- Exact and context-consistent extraction implies sample-word consistency for
its external sample `K`.

The exactness certificate gives positivity for the finite hypothesis sample,
and `ConcreteExtractedSampleData` records that this sample is exactly `K`. -/
def ofExactAndConsistentForLanguage
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {E : ConcreteExtractedSampleData G obs K} {L : Set (Word α)}
    (C : ConcreteExtractedSampleExactAndConsistentForLanguage E L) :
    ConcreteExtractedSampleWordConsistencyForLanguage E L :=
  { words :=
      { sample_words_in_target := by
          intro w hw
          have hsample : E.toFiniteLearnerHypothesis.sampleSet = K :=
            E.finiteHypothesis_sampleSet
          have hwH : w ∈ E.toFiniteLearnerHypothesis.sampleSet := by
            simpa [hsample] using hw
          exact C.positive w hwH } }

/-- Forget to plain positivity for the external sample. -/
theorem positive
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {E : ConcreteExtractedSampleData G obs K} {L : Set (Word α)}
    (C : ConcreteExtractedSampleWordConsistencyForLanguage E L) :
    PositiveForLanguage K L := by
  exact C.words.positive

/-- Pointwise target membership for an externally sampled word. -/
theorem sample_word_in_target
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {E : ConcreteExtractedSampleData G obs K} {L : Set (Word α)}
    (C : ConcreteExtractedSampleWordConsistencyForLanguage E L)
    (w : Word α) (hw : w ∈ K) :
    w ∈ L := by
  exact C.words.sample_word_in_target w hw

end ConcreteExtractedSampleWordConsistencyForLanguage

/-- Grammar-target sample-word consistency for concrete extracted data. -/
abbrev ConcreteExtractedSampleWordConsistencyForGrammar
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (E : ConcreteExtractedSampleData G obs K) : Prop :=
  ConcreteExtractedSampleWordConsistencyForLanguage E G.StringLanguage

namespace ConcreteExtractedSampleWordConsistencyForGrammar

/-- In the grammar-target case, every externally sampled word has a start-symbol
witness in the target grammar. -/
theorem sample_word_start_derives
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {E : ConcreteExtractedSampleData G obs K}
    (C : ConcreteExtractedSampleWordConsistencyForGrammar E)
    (w : Word α) (hw : w ∈ K) :
    ∃ h : 1 = G.arity G.start,
      DerivesTuple G G.start (castTuple h (singletonTuple w)) := by
  exact start_derives_of_mem_StringLanguage G w
    (C.sample_word_in_target w hw)

/-- Exact and context-consistent grammar extraction implies grammar-target
sample-word consistency. -/
def ofExactAndConsistentForGrammar
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {E : ConcreteExtractedSampleData G obs K}
    (C : ConcreteExtractedSampleExactAndConsistentForGrammar E) :
    ConcreteExtractedSampleWordConsistencyForGrammar E :=
  ConcreteExtractedSampleWordConsistencyForLanguage.ofExactAndConsistentForLanguage C

end ConcreteExtractedSampleWordConsistencyForGrammar

end SampleWordConsistencySkeleton

end FIv21
