import LeanCfgProject.MCFG.FI_v2_1_ConcreteSampleConsistencyExact

/-!
# FI v2.1 Lean experiment: Gold wrapper with sample-context consistency

This thirty-seventh layer packages characteristic samples whose post-threshold
extractions are both exact and sample-context-consistent.  The consistency part
is automatic, but keeping it in the interface records explicitly that the
learner explains the contexts it actually observed in the positive sample.
-/

namespace FIv21

universe u v w

section ConcreteSampleConsistencyGold

variable {N : Type w} {α : Type u}
variable [DecidableEq α]
variable {M : Type v} [Monoid M] [Fintype M]

/-- Characteristic sample certificate with exactness and sample-context
consistency after every positive extension. -/
structure ConcreteSampleConsistentCharacteristicSample
    {G : WorkingMCFG N α} {obs : α → M}
    (A : ConcreteExtractedSampleLearner G obs) (L : Set (Word α)) where
  sample : Finset (Word α)
  positive : PositiveForLanguage sample L
  exact_and_consistent_after_extending :
    ∀ K : Finset (Word α),
      SampleExtends sample K →
      PositiveForLanguage K L →
        ConcreteExtractedSampleExactAndConsistentForLanguage (A K) L

namespace ConcreteSampleConsistentCharacteristicSample

/-- Forget consistency and keep the earlier concrete extracted-sample
characteristic sample. -/
def toConcreteExtractedSampleCharacteristicSample
    {G : WorkingMCFG N α} {obs : α → M}
    {A : ConcreteExtractedSampleLearner G obs} {L : Set (Word α)}
    (C : ConcreteSampleConsistentCharacteristicSample A L) :
    ConcreteExtractedSampleCharacteristicSample A L :=
  { sample := C.sample
    positive := C.positive
    exact_after_extending := by
      intro K hExt hPos
      exact (C.exact_and_consistent_after_extending K hExt hPos).exact }

/-- Limiting identification follows by forgetting the consistency component. -/
theorem identifiesInLimit
    {G : WorkingMCFG N α} {obs : α → M}
    {A : ConcreteExtractedSampleLearner G obs} {L : Set (Word α)}
    (C : ConcreteSampleConsistentCharacteristicSample A L) :
    FiniteHypothesisIdentifiesInLimit A.toFiniteHypothesisLearner L := by
  exact ConcreteExtractedSampleCharacteristicSample.identifiesInLimit
    C.toConcreteExtractedSampleCharacteristicSample

/-- Pointwise limiting context correctness follows as before. -/
theorem eventuallyCorrectContexts
    {G : WorkingMCFG N α} {obs : α → M}
    {A : ConcreteExtractedSampleLearner G obs} {L : Set (Word α)}
    (C : ConcreteSampleConsistentCharacteristicSample A L) :
    FiniteHypothesisEventuallyCorrectContexts A.toFiniteHypothesisLearner L := by
  exact ConcreteExtractedSampleCharacteristicSample.eventuallyCorrectContexts
    C.toConcreteExtractedSampleCharacteristicSample

/-- Exactness alone is enough to build the stronger consistency-aware
characteristic sample, because sample-context consistency is automatic. -/
def ofConcreteExtractedSampleCharacteristicSample
    {G : WorkingMCFG N α} {obs : α → M}
    {A : ConcreteExtractedSampleLearner G obs} {L : Set (Word α)}
    (C : ConcreteExtractedSampleCharacteristicSample A L) :
    ConcreteSampleConsistentCharacteristicSample A L :=
  { sample := C.sample
    positive := C.positive
    exact_and_consistent_after_extending := by
      intro K hExt hPos
      exact ConcreteExtractedSampleExactAndConsistentForLanguage.ofExact
        (C.exact_after_extending K hExt hPos) }

end ConcreteSampleConsistentCharacteristicSample

/-- Grammar-target abbreviation. -/
abbrev GrammarConcreteSampleConsistentCharacteristicSample
    {G : WorkingMCFG N α} {obs : α → M}
    (A : ConcreteExtractedSampleLearner G obs) :=
  ConcreteSampleConsistentCharacteristicSample A G.StringLanguage

/-- Grammar-target identification from a consistency-aware characteristic
sample. -/
theorem GrammarConcreteSampleConsistentCharacteristicSample.identifiesInLimit
    {G : WorkingMCFG N α} {obs : α → M}
    {A : ConcreteExtractedSampleLearner G obs}
    (C : GrammarConcreteSampleConsistentCharacteristicSample A) :
    FiniteHypothesisIdentifiesGrammarInLimit A.toFiniteHypothesisLearner G := by
  exact ConcreteSampleConsistentCharacteristicSample.identifiesInLimit C

/-- Grammar-target pointwise context correctness. -/
theorem GrammarConcreteSampleConsistentCharacteristicSample.eventuallyCorrectContexts
    {G : WorkingMCFG N α} {obs : α → M}
    {A : ConcreteExtractedSampleLearner G obs}
    (C : GrammarConcreteSampleConsistentCharacteristicSample A) :
    FiniteHypothesisEventuallyCorrectContexts
      A.toFiniteHypothesisLearner G.StringLanguage := by
  exact ConcreteSampleConsistentCharacteristicSample.eventuallyCorrectContexts C

end ConcreteSampleConsistencyGold

end FIv21
