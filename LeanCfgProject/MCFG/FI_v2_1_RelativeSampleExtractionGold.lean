import LeanCfgProject.MCFG.FI_v2_1_RelativeSampleExtractionExact

/-!
# FI v2.1 Lean experiment: Gold wrapper for relative sample extraction

This thirty-first layer connects the relative sample-extraction interface to
Gold-style identification.

A relative sample-extraction learner maps each finite positive sample `K` to a
certificate whose internal finite support has sample component `K`, whose unit
edges are sample-safe, and whose grammar-side refined rule enumeration is a
finite-monoid concrete enumeration.  If such a learner has a finite
characteristic sample after which all extracted finite hypotheses are exact,
then the previously proved finite-hypothesis Gold theorem applies immediately.
-/

namespace FIv21

universe u v w

section RelativeSampleExtractionGold

variable {N : Type w} {α : Type u}
variable [DecidableEq α]
variable {M : Type v} [Monoid M] [Fintype M]

/-- A sample-indexed relative extraction learner for a fixed grammar and
observation. -/
abbrev RelativeSampleExtractionLearner
    (G : WorkingMCFG N α) (obs : α → M) :=
  (K : Finset (Word α)) → RelativeSampleExtraction G obs K

/-- Forget the grammar-side refined-rule certificates and keep only the finite
hypothesis returned for each sample. -/
def RelativeSampleExtractionLearner.toFiniteHypothesisLearner
    {G : WorkingMCFG N α} {obs : α → M}
    (A : RelativeSampleExtractionLearner G obs) :
    FiniteHypothesisLearner α M :=
  fun K => (A K).toFiniteLearnerHypothesis

/-- Characteristic-sample certificate for a relative extraction learner. -/
structure RelativeSampleExtractionCharacteristicSample
    {G : WorkingMCFG N α} {obs : α → M}
    (A : RelativeSampleExtractionLearner G obs) (L : Set (Word α)) where
  sample : Finset (Word α)
  positive : PositiveForLanguage sample L
  exact_after_extending :
    ∀ K : Finset (Word α),
      SampleExtends sample K →
      PositiveForLanguage K L →
        RelativeSampleExtractionExactForLanguage (A K) L

namespace RelativeSampleExtractionCharacteristicSample

/-- Forget a relative-extraction characteristic sample to the finite-hypothesis
characteristic-sample interface. -/
def toFiniteHypothesisCharacteristicSample
    {G : WorkingMCFG N α} {obs : α → M}
    {A : RelativeSampleExtractionLearner G obs} {L : Set (Word α)}
    (C : RelativeSampleExtractionCharacteristicSample A L) :
    FiniteHypothesisCharacteristicSample
      (A.toFiniteHypothesisLearner) L :=
  { sample := C.sample
    positive := C.positive
    exact_after_extending := by
      intro K hExt hPos
      exact (C.exact_after_extending K hExt hPos).hypExact }

/-- Relative sample-extraction characteristic samples identify the target at
the transported-context distribution level. -/
theorem identifiesInLimit
    {G : WorkingMCFG N α} {obs : α → M}
    {A : RelativeSampleExtractionLearner G obs} {L : Set (Word α)}
    (C : RelativeSampleExtractionCharacteristicSample A L) :
    FiniteHypothesisIdentifiesInLimit A.toFiniteHypothesisLearner L := by
  exact FiniteHypothesisCharacteristicSample.identifiesInLimit
    C.toFiniteHypothesisCharacteristicSample

/-- Pointwise context-membership form of the limiting identification theorem. -/
theorem eventuallyCorrectContexts
    {G : WorkingMCFG N α} {obs : α → M}
    {A : RelativeSampleExtractionLearner G obs} {L : Set (Word α)}
    (C : RelativeSampleExtractionCharacteristicSample A L) :
    FiniteHypothesisEventuallyCorrectContexts A.toFiniteHypothesisLearner L := by
  exact FiniteHypothesisCharacteristicSample.eventuallyCorrectContexts
    C.toFiniteHypothesisCharacteristicSample

end RelativeSampleExtractionCharacteristicSample

/-- Grammar-target abbreviation for relative extraction characteristic samples. -/
abbrev GrammarRelativeSampleExtractionCharacteristicSample
    {G : WorkingMCFG N α} {obs : α → M}
    (A : RelativeSampleExtractionLearner G obs) :=
  RelativeSampleExtractionCharacteristicSample A G.StringLanguage

/-- Grammar-target limiting identification for relative sample extraction. -/
theorem GrammarRelativeSampleExtractionCharacteristicSample.identifiesInLimit
    {G : WorkingMCFG N α} {obs : α → M}
    {A : RelativeSampleExtractionLearner G obs}
    (C : GrammarRelativeSampleExtractionCharacteristicSample A) :
    FiniteHypothesisIdentifiesGrammarInLimit A.toFiniteHypothesisLearner G := by
  exact RelativeSampleExtractionCharacteristicSample.identifiesInLimit C

/-- Grammar-target pointwise context version. -/
theorem GrammarRelativeSampleExtractionCharacteristicSample.eventuallyCorrectContexts
    {G : WorkingMCFG N α} {obs : α → M}
    {A : RelativeSampleExtractionLearner G obs}
    (C : GrammarRelativeSampleExtractionCharacteristicSample A) :
    FiniteHypothesisEventuallyCorrectContexts
      A.toFiniteHypothesisLearner G.StringLanguage := by
  exact RelativeSampleExtractionCharacteristicSample.eventuallyCorrectContexts C

end RelativeSampleExtractionGold

end FIv21
