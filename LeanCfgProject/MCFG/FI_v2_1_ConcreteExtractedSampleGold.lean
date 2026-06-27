import LeanCfgProject.MCFG.FI_v2_1_ConcreteExtractedSampleExact

/-!
# FI v2.1 Lean experiment: Gold wrapper for concrete extracted sample data

This thirty-fourth layer packages the implementation-facing concrete extracted
sample data as a learner and reuses the already-checked relative extraction Gold
wrapper.
-/

namespace FIv21

universe u v w

section ConcreteExtractedSampleGold

variable {N : Type w} {α : Type u}
variable [DecidableEq α]
variable {M : Type v} [Monoid M] [Fintype M]

/-- A concrete extracted-sample learner: each finite sample is mapped to
concrete extracted data using exactly that sample. -/
abbrev ConcreteExtractedSampleLearner
    (G : WorkingMCFG N α) (obs : α → M) :=
  (K : Finset (Word α)) → ConcreteExtractedSampleData G obs K

/-- Forget a concrete extracted-sample learner to the relative extraction
learner interface. -/
def ConcreteExtractedSampleLearner.toRelativeSampleExtractionLearner
    {G : WorkingMCFG N α} {obs : α → M}
    (A : ConcreteExtractedSampleLearner G obs) :
    RelativeSampleExtractionLearner G obs :=
  fun K => (A K).toRelativeSampleExtraction

/-- Forget a concrete extracted-sample learner to the finite-hypothesis learner
interface. -/
def ConcreteExtractedSampleLearner.toFiniteHypothesisLearner
    {G : WorkingMCFG N α} {obs : α → M}
    (A : ConcreteExtractedSampleLearner G obs) :
    FiniteHypothesisLearner α M :=
  (A.toRelativeSampleExtractionLearner).toFiniteHypothesisLearner

/-- Characteristic sample certificate for a concrete extracted-sample learner. -/
structure ConcreteExtractedSampleCharacteristicSample
    {G : WorkingMCFG N α} {obs : α → M}
    (A : ConcreteExtractedSampleLearner G obs) (L : Set (Word α)) where
  sample : Finset (Word α)
  positive : PositiveForLanguage sample L
  exact_after_extending :
    ∀ K : Finset (Word α),
      SampleExtends sample K →
      PositiveForLanguage K L →
        ConcreteExtractedSampleExactForLanguage (A K) L

namespace ConcreteExtractedSampleCharacteristicSample

/-- Forget a concrete characteristic sample to the relative extraction
characteristic-sample interface. -/
def toRelativeSampleExtractionCharacteristicSample
    {G : WorkingMCFG N α} {obs : α → M}
    {A : ConcreteExtractedSampleLearner G obs} {L : Set (Word α)}
    (C : ConcreteExtractedSampleCharacteristicSample A L) :
    RelativeSampleExtractionCharacteristicSample
      A.toRelativeSampleExtractionLearner L :=
  { sample := C.sample
    positive := C.positive
    exact_after_extending := by
      intro K hExt hPos
      exact (C.exact_after_extending K hExt hPos).relativeExact }

/-- Concrete extracted-sample characteristic samples identify the target at the
transported-context distribution level. -/
theorem identifiesInLimit
    {G : WorkingMCFG N α} {obs : α → M}
    {A : ConcreteExtractedSampleLearner G obs} {L : Set (Word α)}
    (C : ConcreteExtractedSampleCharacteristicSample A L) :
    FiniteHypothesisIdentifiesInLimit A.toFiniteHypothesisLearner L := by
  exact RelativeSampleExtractionCharacteristicSample.identifiesInLimit
    C.toRelativeSampleExtractionCharacteristicSample

/-- Pointwise context-membership form of limiting identification. -/
theorem eventuallyCorrectContexts
    {G : WorkingMCFG N α} {obs : α → M}
    {A : ConcreteExtractedSampleLearner G obs} {L : Set (Word α)}
    (C : ConcreteExtractedSampleCharacteristicSample A L) :
    FiniteHypothesisEventuallyCorrectContexts A.toFiniteHypothesisLearner L := by
  exact RelativeSampleExtractionCharacteristicSample.eventuallyCorrectContexts
    C.toRelativeSampleExtractionCharacteristicSample

end ConcreteExtractedSampleCharacteristicSample

/-- Grammar-target characteristic sample abbreviation for a concrete extracted
sample learner. -/
abbrev GrammarConcreteExtractedSampleCharacteristicSample
    {G : WorkingMCFG N α} {obs : α → M}
    (A : ConcreteExtractedSampleLearner G obs) :=
  ConcreteExtractedSampleCharacteristicSample A G.StringLanguage

/-- Grammar-target limiting identification for concrete extracted-sample
learners. -/
theorem GrammarConcreteExtractedSampleCharacteristicSample.identifiesInLimit
    {G : WorkingMCFG N α} {obs : α → M}
    {A : ConcreteExtractedSampleLearner G obs}
    (C : GrammarConcreteExtractedSampleCharacteristicSample A) :
    FiniteHypothesisIdentifiesGrammarInLimit A.toFiniteHypothesisLearner G := by
  exact ConcreteExtractedSampleCharacteristicSample.identifiesInLimit C

/-- Grammar-target pointwise context form. -/
theorem GrammarConcreteExtractedSampleCharacteristicSample.eventuallyCorrectContexts
    {G : WorkingMCFG N α} {obs : α → M}
    {A : ConcreteExtractedSampleLearner G obs}
    (C : GrammarConcreteExtractedSampleCharacteristicSample A) :
    FiniteHypothesisEventuallyCorrectContexts
      A.toFiniteHypothesisLearner G.StringLanguage := by
  exact ConcreteExtractedSampleCharacteristicSample.eventuallyCorrectContexts C

end ConcreteExtractedSampleGold

end FIv21
