import LeanCfgProject.MCFG.FI_v2_1_SampleWordConsistencyExact

/-!
# FI v2.1 Lean experiment: Gold wrapper with sample-word consistency

This fortieth layer records a characteristic-sample interface whose post-
threshold concrete extractions are exact, sample-context consistent, and
sample-word consistent.  The word-consistency component is automatic from
exactness, but the explicit package is useful for stating the canonical
learner's intended sample-consistency obligations.
-/

namespace FIv21

universe u v w

section SampleWordConsistencyGold

variable {N : Type w} {α : Type u}
variable [DecidableEq α]
variable {M : Type v} [Monoid M] [Fintype M]

/-- Characteristic sample certificate whose post-threshold extractions are
exact, context-consistent, and word-consistent. -/
structure ConcreteWordConsistentCharacteristicSample
    {G : WorkingMCFG N α} {obs : α → M}
    (A : ConcreteExtractedSampleLearner G obs) (L : Set (Word α)) where
  sample : Finset (Word α)
  positive : PositiveForLanguage sample L
  exact_context_word_after_extending :
    ∀ K : Finset (Word α),
      SampleExtends sample K →
      PositiveForLanguage K L →
        ConcreteExtractedSampleExactContextWordForLanguage (A K) L

namespace ConcreteWordConsistentCharacteristicSample

/-- Forget word consistency and keep the previous context-consistent
characteristic-sample interface. -/
def toConcreteSampleConsistentCharacteristicSample
    {G : WorkingMCFG N α} {obs : α → M}
    {A : ConcreteExtractedSampleLearner G obs} {L : Set (Word α)}
    (C : ConcreteWordConsistentCharacteristicSample A L) :
    ConcreteSampleConsistentCharacteristicSample A L :=
  { sample := C.sample
    positive := C.positive
    exact_and_consistent_after_extending := by
      intro K hExt hPos
      exact (C.exact_context_word_after_extending K hExt hPos).exact_and_context }

/-- Limiting identification follows by forgetting the word-consistency field. -/
theorem identifiesInLimit
    {G : WorkingMCFG N α} {obs : α → M}
    {A : ConcreteExtractedSampleLearner G obs} {L : Set (Word α)}
    (C : ConcreteWordConsistentCharacteristicSample A L) :
    FiniteHypothesisIdentifiesInLimit A.toFiniteHypothesisLearner L := by
  exact ConcreteSampleConsistentCharacteristicSample.identifiesInLimit
    C.toConcreteSampleConsistentCharacteristicSample

/-- Pointwise limiting context correctness follows as before. -/
theorem eventuallyCorrectContexts
    {G : WorkingMCFG N α} {obs : α → M}
    {A : ConcreteExtractedSampleLearner G obs} {L : Set (Word α)}
    (C : ConcreteWordConsistentCharacteristicSample A L) :
    FiniteHypothesisEventuallyCorrectContexts A.toFiniteHypothesisLearner L := by
  exact ConcreteSampleConsistentCharacteristicSample.eventuallyCorrectContexts
    C.toConcreteSampleConsistentCharacteristicSample

/-- The previous context-consistent characteristic sample can be promoted to the
word-consistent one, since the word component follows automatically from
exactness and the sample-equality field of the extraction data. -/
def ofConcreteSampleConsistentCharacteristicSample
    {G : WorkingMCFG N α} {obs : α → M}
    {A : ConcreteExtractedSampleLearner G obs} {L : Set (Word α)}
    (C : ConcreteSampleConsistentCharacteristicSample A L) :
    ConcreteWordConsistentCharacteristicSample A L :=
  { sample := C.sample
    positive := C.positive
    exact_context_word_after_extending := by
      intro K hExt hPos
      exact ConcreteExtractedSampleExactContextWordForLanguage.ofExactAndContext
        (C.exact_and_consistent_after_extending K hExt hPos) }

end ConcreteWordConsistentCharacteristicSample

/-- Grammar-target abbreviation. -/
abbrev GrammarConcreteWordConsistentCharacteristicSample
    {G : WorkingMCFG N α} {obs : α → M}
    (A : ConcreteExtractedSampleLearner G obs) :=
  ConcreteWordConsistentCharacteristicSample A G.StringLanguage

/-- Grammar-target identification from the word-consistent characteristic sample. -/
theorem GrammarConcreteWordConsistentCharacteristicSample.identifiesInLimit
    {G : WorkingMCFG N α} {obs : α → M}
    {A : ConcreteExtractedSampleLearner G obs}
    (C : GrammarConcreteWordConsistentCharacteristicSample A) :
    FiniteHypothesisIdentifiesGrammarInLimit A.toFiniteHypothesisLearner G := by
  exact ConcreteWordConsistentCharacteristicSample.identifiesInLimit C

/-- Grammar-target pointwise context correctness. -/
theorem GrammarConcreteWordConsistentCharacteristicSample.eventuallyCorrectContexts
    {G : WorkingMCFG N α} {obs : α → M}
    {A : ConcreteExtractedSampleLearner G obs}
    (C : GrammarConcreteWordConsistentCharacteristicSample A) :
    FiniteHypothesisEventuallyCorrectContexts
      A.toFiniteHypothesisLearner G.StringLanguage := by
  exact ConcreteWordConsistentCharacteristicSample.eventuallyCorrectContexts C

end SampleWordConsistencyGold

end FIv21
