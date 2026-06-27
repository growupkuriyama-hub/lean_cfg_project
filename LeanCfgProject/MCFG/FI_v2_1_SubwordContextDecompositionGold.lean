import LeanCfgProject.MCFG.FI_v2_1_SubwordContextDecompositionExact

/-!
# FI v2.1 Lean experiment: Gold wrapper for subword-context decompositions

This file packages learners that return subword-context decomposition data and
forgets them to the already checked raw-decomposition learner interface.  It
also records the concrete fact that the whole-word subword learner represents
every word in the current positive sample by a listed two-sided decomposition.
-/

namespace FIv21

universe u v w

section SubwordContextDecompositionGold

variable {N : Type w} {α : Type u}
variable [DecidableEq α]
variable {M : Type v} [Monoid M] [Fintype M]

/-- A learner mapping each finite sample to subword-context decomposition data. -/
abbrev SubwordContextDecompositionLearner
    (G : WorkingMCFG N α) (obs : α → M) :=
  (K : Finset (Word α)) → SubwordContextDecompositionData G obs K

/-- Forget a subword-context learner to a raw-decomposition learner. -/
noncomputable def SubwordContextDecompositionLearner.toRawSampleDecompositionLearner
    {G : WorkingMCFG N α} {obs : α → M}
    (A : SubwordContextDecompositionLearner G obs) :
    RawSampleDecompositionLearner G obs :=
  fun K => (A K).toRawSampleDecompositionData

/-- Forget a subword-context learner to the finite-hypothesis learner. -/
noncomputable def SubwordContextDecompositionLearner.toFiniteHypothesisLearner
    {G : WorkingMCFG N α} {obs : α → M}
    (A : SubwordContextDecompositionLearner G obs) :
    FiniteHypothesisLearner α M :=
  A.toRawSampleDecompositionLearner.toFiniteHypothesisLearner

/-- Characteristic sample certificate for a subword-context decomposition
learner. -/
structure SubwordContextDecompositionCharacteristicSample
    {G : WorkingMCFG N α} {obs : α → M}
    (A : SubwordContextDecompositionLearner G obs) (L : Set (Word α)) where
  sample : Finset (Word α)
  positive : PositiveForLanguage sample L
  exact_after_extending :
    ∀ K : Finset (Word α),
      SampleExtends sample K →
      PositiveForLanguage K L →
        SubwordContextDecompositionExactForLanguage (A K) L

namespace SubwordContextDecompositionCharacteristicSample

/-- Forget to the raw-decomposition characteristic-sample interface. -/
noncomputable def toRawSampleDecompositionCharacteristicSample
    {G : WorkingMCFG N α} {obs : α → M}
    {A : SubwordContextDecompositionLearner G obs} {L : Set (Word α)}
    (C : SubwordContextDecompositionCharacteristicSample A L) :
    RawSampleDecompositionCharacteristicSample
      A.toRawSampleDecompositionLearner L :=
  { sample := C.sample
    positive := C.positive
    exact_after_extending := by
      intro K hExt hPos
      exact (C.exact_after_extending K hExt hPos).toRawExact }

/-- Subword-context characteristic samples identify the target at the transported
named-context distribution level. -/
theorem identifiesInLimit
    {G : WorkingMCFG N α} {obs : α → M}
    {A : SubwordContextDecompositionLearner G obs} {L : Set (Word α)}
    (C : SubwordContextDecompositionCharacteristicSample A L) :
    FiniteHypothesisIdentifiesInLimit A.toFiniteHypothesisLearner L := by
  exact C.toRawSampleDecompositionCharacteristicSample.identifiesInLimit

/-- Pointwise context-membership form of limiting identification. -/
theorem eventuallyCorrectContexts
    {G : WorkingMCFG N α} {obs : α → M}
    {A : SubwordContextDecompositionLearner G obs} {L : Set (Word α)}
    (C : SubwordContextDecompositionCharacteristicSample A L) :
    FiniteHypothesisEventuallyCorrectContexts A.toFiniteHypothesisLearner L := by
  exact C.toRawSampleDecompositionCharacteristicSample.eventuallyCorrectContexts

/-- After the threshold, listed subword decompositions provide supported tuples. -/
theorem supportsTuple_of_subword_mem_after
    {G : WorkingMCFG N α} {obs : α → M}
    {A : SubwordContextDecompositionLearner G obs} {L : Set (Word α)}
    (C : SubwordContextDecompositionCharacteristicSample A L)
    {K : Finset (Word α)}
    (hExt : SampleExtends C.sample K)
    (hPos : PositiveForLanguage K L)
    {S : SubwordSampleDecomposition (α := α) K}
    (hS : S ∈ (A K).subwordDecompositions) :
    (A K).support.SupportsTuple S.tuple := by
  exact (C.exact_after_extending K hExt hPos).supportsTuple_of_subword_mem hS

/-- After the threshold, listed subword decompositions provide supported
contexts. -/
theorem supportsContext_of_subword_mem_after
    {G : WorkingMCFG N α} {obs : α → M}
    {A : SubwordContextDecompositionLearner G obs} {L : Set (Word α)}
    (C : SubwordContextDecompositionCharacteristicSample A L)
    {K : Finset (Word α)}
    (hExt : SampleExtends C.sample K)
    (hPos : PositiveForLanguage K L)
    {S : SubwordSampleDecomposition (α := α) K}
    (hS : S ∈ (A K).subwordDecompositions) :
    (A K).support.SupportsContext S.context := by
  exact (C.exact_after_extending K hExt hPos).supportsContext_of_subword_mem hS

/-- Whole-word subword learner: every observed sample word has a listed subword
decomposition after the characteristic-sample threshold. -/
theorem wholeWord_supported_sample_word_after
    {G : WorkingMCFG N α} {obs : α → M} {L : Set (Word α)}
    {f : Nat} {hG : G.SemanticWorkingConditions}
    (C : SubwordContextDecompositionCharacteristicSample
      (wholeWordSubwordContextDecompositionLearner G obs f hG) L)
    {K : Finset (Word α)}
    (_hExt : SampleExtends C.sample K)
    (_hPos : PositiveForLanguage K L)
    {w : Word α} (hw : w ∈ K) :
    ∃ S : SubwordSampleDecomposition (α := α) K,
      S ∈ ((wholeWordSubwordContextDecompositionLearner G obs f hG) K).subwordDecompositions ∧
      S.sampleWord = w ∧
      (((wholeWordSubwordContextDecompositionLearner G obs f hG) K).support.SupportsTuple S.tuple) ∧
      (((wholeWordSubwordContextDecompositionLearner G obs f hG) K).support.SupportsContext S.context) ∧
      S.context ∈ SampleNamedDistribution K S.tuple := by
  exact wholeWordSubwordContextDecompositionData_supported_sample_word G obs K f hG hw

end SubwordContextDecompositionCharacteristicSample

/-- Grammar-target characteristic sample abbreviation for subword-context
learners. -/
abbrev GrammarSubwordContextDecompositionCharacteristicSample
    {G : WorkingMCFG N α} {obs : α → M}
    (A : SubwordContextDecompositionLearner G obs) :=
  SubwordContextDecompositionCharacteristicSample A G.StringLanguage

/-- Grammar-target characteristic sample abbreviation for the whole-word subword
learner. -/
abbrev GrammarWholeWordSubwordContextDecompositionCharacteristicSample
    {G : WorkingMCFG N α} {obs : α → M}
    (f : Nat) (hG : G.SemanticWorkingConditions) :=
  SubwordContextDecompositionCharacteristicSample
    (wholeWordSubwordContextDecompositionLearner G obs f hG) G.StringLanguage

end SubwordContextDecompositionGold

end FIv21
