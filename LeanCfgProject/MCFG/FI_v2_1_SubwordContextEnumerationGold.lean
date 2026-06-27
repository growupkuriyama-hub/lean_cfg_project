import LeanCfgProject.MCFG.FI_v2_1_SubwordContextEnumerationExact

/-!
# FI v2.1 Lean experiment: Gold wrapper for subword-context enumeration

This file packages learners that return the new enumerated subword-context data
and forgets them to the previous subword-context learner interface.  The main
point is that the enumerated learner has an actual finite list of two-sided cut
candidates for every sample word, not merely an externally supplied list.
-/

namespace FIv21

universe u v w

section SubwordContextEnumerationGold

variable {N : Type w} {α : Type u}
variable [DecidableEq α]
variable {M : Type v} [Monoid M] [Fintype M]

/-- A learner mapping each finite sample to enumerated subword-context data. -/
abbrev SubwordContextEnumerationLearner
    (G : WorkingMCFG N α) (obs : α → M) :=
  (K : Finset (Word α)) → SubwordContextDecompositionData G obs K

/-- Forget an enumeration learner to the previous subword-context learner. -/
noncomputable def SubwordContextEnumerationLearner.toSubwordContextDecompositionLearner
    {G : WorkingMCFG N α} {obs : α → M}
    (A : SubwordContextEnumerationLearner G obs) :
    SubwordContextDecompositionLearner G obs :=
  A

/-- Forget an enumeration learner to the finite-hypothesis learner. -/
noncomputable def SubwordContextEnumerationLearner.toFiniteHypothesisLearner
    {G : WorkingMCFG N α} {obs : α → M}
    (A : SubwordContextEnumerationLearner G obs) :
    FiniteHypothesisLearner α M :=
  A.toSubwordContextDecompositionLearner.toFiniteHypothesisLearner

/-- Characteristic sample certificate for an enumerated subword-context learner. -/
structure SubwordContextEnumerationCharacteristicSample
    {G : WorkingMCFG N α} {obs : α → M}
    (A : SubwordContextEnumerationLearner G obs) (L : Set (Word α)) where
  sample : Finset (Word α)
  positive : PositiveForLanguage sample L
  exact_after_extending :
    ∀ K : Finset (Word α),
      SampleExtends sample K →
      PositiveForLanguage K L →
        SubwordContextEnumerationExactForLanguage (A K) L

namespace SubwordContextEnumerationCharacteristicSample

/-- Forget to the previous subword-context characteristic-sample interface. -/
noncomputable def toSubwordContextDecompositionCharacteristicSample
    {G : WorkingMCFG N α} {obs : α → M}
    {A : SubwordContextEnumerationLearner G obs} {L : Set (Word α)}
    (C : SubwordContextEnumerationCharacteristicSample A L) :
    SubwordContextDecompositionCharacteristicSample
      A.toSubwordContextDecompositionLearner L :=
  { sample := C.sample
    positive := C.positive
    exact_after_extending := by
      intro K hExt hPos
      exact (C.exact_after_extending K hExt hPos).toSubwordExact }

/-- Enumerated subword-context characteristic samples identify the target at the
finite-hypothesis distribution level. -/
theorem identifiesInLimit
    {G : WorkingMCFG N α} {obs : α → M}
    {A : SubwordContextEnumerationLearner G obs} {L : Set (Word α)}
    (C : SubwordContextEnumerationCharacteristicSample A L) :
    FiniteHypothesisIdentifiesInLimit A.toFiniteHypothesisLearner L := by
  exact C.toSubwordContextDecompositionCharacteristicSample.identifiesInLimit

/-- Pointwise context-membership form of limiting identification. -/
theorem eventuallyCorrectContexts
    {G : WorkingMCFG N α} {obs : α → M}
    {A : SubwordContextEnumerationLearner G obs} {L : Set (Word α)}
    (C : SubwordContextEnumerationCharacteristicSample A L) :
    FiniteHypothesisEventuallyCorrectContexts A.toFiniteHypothesisLearner L := by
  exact C.toSubwordContextDecompositionCharacteristicSample.eventuallyCorrectContexts

/-- After the threshold, listed enumerated subword decompositions support their
tuples. -/
theorem supportsTuple_of_subword_mem_after
    {G : WorkingMCFG N α} {obs : α → M}
    {A : SubwordContextEnumerationLearner G obs} {L : Set (Word α)}
    (C : SubwordContextEnumerationCharacteristicSample A L)
    {K : Finset (Word α)}
    (hExt : SampleExtends C.sample K)
    (hPos : PositiveForLanguage K L)
    {S : SubwordSampleDecomposition (α := α) K}
    (hS : S ∈ (A K).subwordDecompositions) :
    (A K).support.SupportsTuple S.tuple := by
  exact (C.exact_after_extending K hExt hPos).supportsTuple_of_subword_mem hS

/-- The concrete enumerated learner represents every observed sample word by a
listed and supported subword decomposition after the threshold. -/
theorem enumerated_supported_sample_word_after
    {G : WorkingMCFG N α} {obs : α → M} {L : Set (Word α)}
    {f : Nat} {hG : G.SemanticWorkingConditions}
    (C : SubwordContextEnumerationCharacteristicSample
      (enumeratedSubwordContextDecompositionLearner G obs f hG) L)
    {K : Finset (Word α)}
    (_hExt : SampleExtends C.sample K)
    (_hPos : PositiveForLanguage K L)
    {w : Word α} (hw : w ∈ K) :
    ∃ S : SubwordSampleDecomposition (α := α) K,
      S ∈ ((enumeratedSubwordContextDecompositionLearner G obs f hG) K).subwordDecompositions ∧
      S.sampleWord = w ∧
      (((enumeratedSubwordContextDecompositionLearner G obs f hG) K).support.SupportsTuple S.tuple) ∧
      (((enumeratedSubwordContextDecompositionLearner G obs f hG) K).support.SupportsContext S.context) ∧
      S.context ∈ SampleNamedDistribution K S.tuple := by
  exact enumeratedSubwordContextDecompositionData_supported_sample_word G obs K f hG hw

end SubwordContextEnumerationCharacteristicSample

/-- Grammar-target characteristic sample abbreviation for subword-context
enumeration learners. -/
abbrev GrammarSubwordContextEnumerationCharacteristicSample
    {G : WorkingMCFG N α} {obs : α → M}
    (A : SubwordContextEnumerationLearner G obs) :=
  SubwordContextEnumerationCharacteristicSample A G.StringLanguage

/-- Grammar-target characteristic sample abbreviation for the concrete
enumerated subword-context learner. -/
abbrev GrammarEnumeratedSubwordContextEnumerationCharacteristicSample
    {G : WorkingMCFG N α} {obs : α → M}
    (f : Nat) (hG : G.SemanticWorkingConditions) :=
  SubwordContextEnumerationCharacteristicSample
    (enumeratedSubwordContextDecompositionLearner G obs f hG) G.StringLanguage

end SubwordContextEnumerationGold

end FIv21
