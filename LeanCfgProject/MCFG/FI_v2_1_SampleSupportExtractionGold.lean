import LeanCfgProject.MCFG.FI_v2_1_SampleSupportExtractionExact

/-!
# FI v2.1 Lean experiment: Gold wrapper for minimal sample-support extraction

This file packages a learner returning `SampleSupportExtraction` data.  This is
a genuine sample-to-support learner at the minimal level: the support records the
input finite sample exactly, with empty tuple/context/unit-edge lists.  Exactness
is still supplied by a characteristic-sample certificate.
-/

namespace FIv21

universe u v w

section SampleSupportExtractionGold

variable {N : Type w} {α : Type u}
variable [DecidableEq α]
variable {M : Type v} [Monoid M] [Fintype M]

/-- A learner mapping each finite sample to minimal sample-support extraction
data. -/
abbrev SampleSupportExtractionLearner
    (G : WorkingMCFG N α) (obs : α → M) :=
  (K : Finset (Word α)) → SampleSupportExtraction G obs K

/-- Forget a minimal support-extraction learner to the previous sample-extracted
rule-list learner. -/
noncomputable def SampleSupportExtractionLearner.toSampleExtractedRuleListLearner
    {G : WorkingMCFG N α} {obs : α → M}
    (A : SampleSupportExtractionLearner G obs) :
    SampleExtractedRuleListLearner G obs :=
  fun K => (A K).toSampleExtractedRuleLists

/-- Forget to the concrete extracted-sample learner interface. -/
noncomputable def SampleSupportExtractionLearner.toConcreteExtractedSampleLearner
    {G : WorkingMCFG N α} {obs : α → M}
    (A : SampleSupportExtractionLearner G obs) :
    ConcreteExtractedSampleLearner G obs :=
  A.toSampleExtractedRuleListLearner.toConcreteExtractedSampleLearner

/-- Forget to the finite-hypothesis learner interface. -/
noncomputable def SampleSupportExtractionLearner.toFiniteHypothesisLearner
    {G : WorkingMCFG N α} {obs : α → M}
    (A : SampleSupportExtractionLearner G obs) :
    FiniteHypothesisLearner α M :=
  A.toSampleExtractedRuleListLearner.toFiniteHypothesisLearner

/-- Characteristic sample certificate for a minimal support-extraction learner. -/
structure SampleSupportExtractionCharacteristicSample
    {G : WorkingMCFG N α} {obs : α → M}
    (A : SampleSupportExtractionLearner G obs) (L : Set (Word α)) where
  sample : Finset (Word α)
  positive : PositiveForLanguage sample L
  exact_after_extending :
    ∀ K : Finset (Word α),
      SampleExtends sample K →
      PositiveForLanguage K L →
        SampleSupportExtractionExactForLanguage (A K) L

namespace SampleSupportExtractionCharacteristicSample

/-- Forget to the previous sample-extracted rule-list characteristic-sample
interface. -/
noncomputable def toSampleExtractedRuleListCharacteristicSample
    {G : WorkingMCFG N α} {obs : α → M}
    {A : SampleSupportExtractionLearner G obs} {L : Set (Word α)}
    (C : SampleSupportExtractionCharacteristicSample A L) :
    SampleExtractedRuleListCharacteristicSample
      A.toSampleExtractedRuleListLearner L :=
  { sample := C.sample
    positive := C.positive
    exact_after_extending := by
      intro K hExt hPos
      exact (C.exact_after_extending K hExt hPos).extractedExact }

/-- Minimal support-extraction characteristic samples identify the target at the
transported-context distribution level. -/
theorem identifiesInLimit
    {G : WorkingMCFG N α} {obs : α → M}
    {A : SampleSupportExtractionLearner G obs} {L : Set (Word α)}
    (C : SampleSupportExtractionCharacteristicSample A L) :
    FiniteHypothesisIdentifiesInLimit A.toFiniteHypothesisLearner L := by
  exact SampleExtractedRuleListCharacteristicSample.identifiesInLimit
    C.toSampleExtractedRuleListCharacteristicSample

/-- Pointwise context-membership form of limiting identification. -/
theorem eventuallyCorrectContexts
    {G : WorkingMCFG N α} {obs : α → M}
    {A : SampleSupportExtractionLearner G obs} {L : Set (Word α)}
    (C : SampleSupportExtractionCharacteristicSample A L) :
    FiniteHypothesisEventuallyCorrectContexts A.toFiniteHypothesisLearner L := by
  exact SampleExtractedRuleListCharacteristicSample.eventuallyCorrectContexts
    C.toSampleExtractedRuleListCharacteristicSample

/-- After the threshold, the extracted support is the canonical sample-only
support for the current prefix sample. -/
theorem support_eq_sampleOnly_after
    {G : WorkingMCFG N α} {obs : α → M}
    {A : SampleSupportExtractionLearner G obs} {L : Set (Word α)}
    (C : SampleSupportExtractionCharacteristicSample A L)
    {K : Finset (Word α)}
    (hExt : SampleExtends C.sample K)
    (hPos : PositiveForLanguage K L) :
    (A K).support = sampleOnlySupport K := by
  exact (C.exact_after_extending K hExt hPos).support_eq_sampleOnly

/-- After the threshold, the minimal extracted support has no listed unit edges. -/
theorem support_no_unitEdges_after
    {G : WorkingMCFG N α} {obs : α → M}
    {A : SampleSupportExtractionLearner G obs} {L : Set (Word α)}
    (C : SampleSupportExtractionCharacteristicSample A L)
    {K : Finset (Word α)}
    (hExt : SampleExtends C.sample K)
    (hPos : PositiveForLanguage K L)
    {d : Nat} {x y : Tuple α d} :
    ¬ (A K).support.SupportsUnitEdge x y := by
  exact (C.exact_after_extending K hExt hPos).support_no_unitEdges

/-- After the threshold, the actual refined rule lists contain all ordinary
output-type refinements. -/
theorem actualRuleLists_containsAll_after
    {G : WorkingMCFG N α} {obs : α → M}
    {A : SampleSupportExtractionLearner G obs} {L : Set (Word α)}
    (C : SampleSupportExtractionCharacteristicSample A L)
    {K : Finset (Word α)}
    (hExt : SampleExtends C.sample K)
    (hPos : PositiveForLanguage K L) :
    (A K).concreteRules.toFintypeOutputTypeRefinementCertificate.toOutputTypeRefinedGrammar.ContainsAllOrdinaryRuleRefinements := by
  exact (C.exact_after_extending K hExt hPos).actualRuleLists_containsAll

/-- After the threshold, the actual refined rule lists are supported by the
canonical finite-monoid rule-enumeration plan. -/
theorem actualRuleLists_supportedByPlan_after
    {G : WorkingMCFG N α} {obs : α → M}
    {A : SampleSupportExtractionLearner G obs} {L : Set (Word α)}
    (C : SampleSupportExtractionCharacteristicSample A L)
    {K : Finset (Word α)}
    (hExt : SampleExtends C.sample K)
    (hPos : PositiveForLanguage K L) :
    (A K).concreteRules.grammar.AllRulesSupportedByPlan
      (FiniteRuleEnumerationPlan.ofFintype G obs) := by
  exact (C.exact_after_extending K hExt hPos).actualRuleLists_supportedByPlan

end SampleSupportExtractionCharacteristicSample

/-- Grammar-target characteristic sample abbreviation. -/
abbrev GrammarSampleSupportExtractionCharacteristicSample
    {G : WorkingMCFG N α} {obs : α → M}
    (A : SampleSupportExtractionLearner G obs) :=
  SampleSupportExtractionCharacteristicSample A G.StringLanguage

/-- Grammar-target limiting identification for minimal support-extraction
learners. -/
theorem GrammarSampleSupportExtractionCharacteristicSample.identifiesInLimit
    {G : WorkingMCFG N α} {obs : α → M}
    {A : SampleSupportExtractionLearner G obs}
    (C : GrammarSampleSupportExtractionCharacteristicSample A) :
    FiniteHypothesisIdentifiesGrammarInLimit A.toFiniteHypothesisLearner G := by
  exact SampleSupportExtractionCharacteristicSample.identifiesInLimit C

/-- Grammar-target pointwise context form. -/
theorem GrammarSampleSupportExtractionCharacteristicSample.eventuallyCorrectContexts
    {G : WorkingMCFG N α} {obs : α → M}
    {A : SampleSupportExtractionLearner G obs}
    (C : GrammarSampleSupportExtractionCharacteristicSample A) :
    FiniteHypothesisEventuallyCorrectContexts
      A.toFiniteHypothesisLearner G.StringLanguage := by
  exact SampleSupportExtractionCharacteristicSample.eventuallyCorrectContexts C

end SampleSupportExtractionGold

end FIv21
