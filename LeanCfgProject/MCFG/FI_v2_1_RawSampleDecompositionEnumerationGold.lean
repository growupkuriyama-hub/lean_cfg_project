import LeanCfgProject.MCFG.FI_v2_1_RawSampleDecompositionEnumerationExact

/-!
# FI v2.1 Lean experiment: Gold wrapper for enumerated sample-word decompositions

This file pushes the elementary sample-word enumeration through the Gold-style
raw-decomposition learner interface.  The key point is simple but useful: for
the concrete sample-word-only learner, every word in the current positive sample
is represented by an explicit listed one-hole raw decomposition.
-/

namespace FIv21

universe u v w

section RawSampleDecompositionEnumerationGold

variable {N : Type w} {α : Type u}
variable [DecidableEq α]
variable {M : Type v} [Monoid M] [Fintype M]

namespace RawSampleDecompositionCharacteristicSample

/-- For the sample-word-only learner, every observed sample word is covered by a
listed raw decomposition after the characteristic-sample threshold.  The
threshold hypotheses are kept in the statement so this theorem can be used in
the same shape as the other Gold-style consequences. -/
theorem sampleWordOnly_covers_sample_after
    {G : WorkingMCFG N α} {obs : α → M} {L : Set (Word α)}
    {f : Nat} {hG : G.SemanticWorkingConditions}
    (C : RawSampleDecompositionCharacteristicSample
      (sampleWordOnlyRawSampleDecompositionLearner G obs f hG) L)
    {K : Finset (Word α)}
    (_hExt : SampleExtends C.sample K)
    (_hPos : PositiveForLanguage K L)
    {w : Word α} (hw : w ∈ K) :
    ∃ R : RawSampleDecomposition (α := α) K,
      R ∈ ((sampleWordOnlyRawSampleDecompositionLearner G obs f hG) K).decompositions ∧
      R.sampleWord = w ∧
      namedFill R.d R.context R.tuple = w := by
  exact sampleWordOnlyRawSampleDecompositionLearner_covers_sample G obs f hG K hw

/-- For the sample-word-only learner, every observed sample word has a listed
decomposition whose tuple and context are supported and whose context is
sample-licensed. -/
theorem sampleWordOnly_supported_sample_word_after
    {G : WorkingMCFG N α} {obs : α → M} {L : Set (Word α)}
    {f : Nat} {hG : G.SemanticWorkingConditions}
    (C : RawSampleDecompositionCharacteristicSample
      (sampleWordOnlyRawSampleDecompositionLearner G obs f hG) L)
    {K : Finset (Word α)}
    (_hExt : SampleExtends C.sample K)
    (_hPos : PositiveForLanguage K L)
    {w : Word α} (hw : w ∈ K) :
    ∃ R : RawSampleDecomposition (α := α) K,
      R ∈ ((sampleWordOnlyRawSampleDecompositionLearner G obs f hG) K).decompositions ∧
      R.sampleWord = w ∧
      (((sampleWordOnlyRawSampleDecompositionLearner G obs f hG) K).support.SupportsTuple R.tuple) ∧
      (((sampleWordOnlyRawSampleDecompositionLearner G obs f hG) K).support.SupportsContext R.context) ∧
      R.context ∈ SampleNamedDistribution K R.tuple := by
  exact sampleWordOnlyRawSampleDecompositionData_supported_sample_word G obs K f hG hw

end RawSampleDecompositionCharacteristicSample

/-- Grammar-target abbreviation for characteristic samples of the sample-word-only
raw-decomposition learner. -/
abbrev GrammarSampleWordOnlyRawSampleDecompositionCharacteristicSample
    {G : WorkingMCFG N α} {obs : α → M}
    (f : Nat) (hG : G.SemanticWorkingConditions) :=
  RawSampleDecompositionCharacteristicSample
    (sampleWordOnlyRawSampleDecompositionLearner G obs f hG) G.StringLanguage

end RawSampleDecompositionEnumerationGold

end FIv21
