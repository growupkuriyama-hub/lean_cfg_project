import LeanCfgProject.MCFG.FI_v2_1_SampleExtractedRuleListsExact

/-!
# FI v2.1 Lean experiment: Gold wrapper for sample-extracted actual rule lists

This file packages a sample-indexed extractor returning
`SampleExtractedRuleLists`.  Its grammar-side refined rule lists are actual
finite-monoid lists generated from the base grammar; the remaining sample-side
support and exactness obligations are still certificate fields.
-/

namespace FIv21

universe u v w

section SampleExtractedRuleListsGold

variable {N : Type w} {α : Type u}
variable [DecidableEq α]
variable {M : Type v} [Monoid M] [Fintype M]

/-- A learner that maps each finite sample to sample-extracted actual rule-list
data. -/
abbrev SampleExtractedRuleListLearner
    (G : WorkingMCFG N α) (obs : α → M) :=
  (K : Finset (Word α)) → SampleExtractedRuleLists G obs K

/-- Forget a sample-extracted rule-list learner to the older concrete
extracted-sample learner interface. -/
noncomputable def SampleExtractedRuleListLearner.toConcreteExtractedSampleLearner
    {G : WorkingMCFG N α} {obs : α → M}
    (A : SampleExtractedRuleListLearner G obs) :
    ConcreteExtractedSampleLearner G obs :=
  fun K => (A K).toConcreteExtractedSampleData

/-- Forget a sample-extracted rule-list learner to the finite-hypothesis learner
interface. -/
noncomputable def SampleExtractedRuleListLearner.toFiniteHypothesisLearner
    {G : WorkingMCFG N α} {obs : α → M}
    (A : SampleExtractedRuleListLearner G obs) :
    FiniteHypothesisLearner α M :=
  A.toConcreteExtractedSampleLearner.toFiniteHypothesisLearner

/-- Characteristic sample certificate for a sample-extracted rule-list learner. -/
structure SampleExtractedRuleListCharacteristicSample
    {G : WorkingMCFG N α} {obs : α → M}
    (A : SampleExtractedRuleListLearner G obs) (L : Set (Word α)) where
  sample : Finset (Word α)
  positive : PositiveForLanguage sample L
  exact_after_extending :
    ∀ K : Finset (Word α),
      SampleExtends sample K →
      PositiveForLanguage K L →
        SampleExtractedRuleListsExactForLanguage (A K) L

namespace SampleExtractedRuleListCharacteristicSample

/-- Forget to the concrete extracted-sample characteristic-sample interface. -/
noncomputable def toConcreteExtractedSampleCharacteristicSample
    {G : WorkingMCFG N α} {obs : α → M}
    {A : SampleExtractedRuleListLearner G obs} {L : Set (Word α)}
    (C : SampleExtractedRuleListCharacteristicSample A L) :
    ConcreteExtractedSampleCharacteristicSample
      A.toConcreteExtractedSampleLearner L :=
  { sample := C.sample
    positive := C.positive
    exact_after_extending := by
      intro K hExt hPos
      exact (C.exact_after_extending K hExt hPos).concreteExact }

/-- Sample-extracted actual rule-list characteristic samples identify the target
at the transported-context distribution level. -/
theorem identifiesInLimit
    {G : WorkingMCFG N α} {obs : α → M}
    {A : SampleExtractedRuleListLearner G obs} {L : Set (Word α)}
    (C : SampleExtractedRuleListCharacteristicSample A L) :
    FiniteHypothesisIdentifiesInLimit A.toFiniteHypothesisLearner L := by
  exact ConcreteExtractedSampleCharacteristicSample.identifiesInLimit
    C.toConcreteExtractedSampleCharacteristicSample

/-- Pointwise context-membership form of limiting identification. -/
theorem eventuallyCorrectContexts
    {G : WorkingMCFG N α} {obs : α → M}
    {A : SampleExtractedRuleListLearner G obs} {L : Set (Word α)}
    (C : SampleExtractedRuleListCharacteristicSample A L) :
    FiniteHypothesisEventuallyCorrectContexts A.toFiniteHypothesisLearner L := by
  exact ConcreteExtractedSampleCharacteristicSample.eventuallyCorrectContexts
    C.toConcreteExtractedSampleCharacteristicSample

/-- After the characteristic sample threshold, the actual refined rule lists
contain all ordinary output-type refinements. -/
theorem actualRuleLists_containsAll_after
    {G : WorkingMCFG N α} {obs : α → M}
    {A : SampleExtractedRuleListLearner G obs} {L : Set (Word α)}
    (C : SampleExtractedRuleListCharacteristicSample A L)
    {K : Finset (Word α)}
    (hExt : SampleExtends C.sample K)
    (hPos : PositiveForLanguage K L) :
    (A K).concreteRules.toFintypeOutputTypeRefinementCertificate.toOutputTypeRefinedGrammar.ContainsAllOrdinaryRuleRefinements := by
  exact (C.exact_after_extending K hExt hPos).actualRuleLists_containsAll

/-- After the characteristic sample threshold, the actual refined rule lists are
supported by the canonical finite-monoid rule-enumeration plan. -/
theorem actualRuleLists_supportedByPlan_after
    {G : WorkingMCFG N α} {obs : α → M}
    {A : SampleExtractedRuleListLearner G obs} {L : Set (Word α)}
    (C : SampleExtractedRuleListCharacteristicSample A L)
    {K : Finset (Word α)}
    (hExt : SampleExtends C.sample K)
    (hPos : PositiveForLanguage K L) :
    (A K).concreteRules.grammar.AllRulesSupportedByPlan
      (FiniteRuleEnumerationPlan.ofFintype G obs) := by
  exact (C.exact_after_extending K hExt hPos).actualRuleLists_supportedByPlan

end SampleExtractedRuleListCharacteristicSample

/-- Grammar-target characteristic sample abbreviation. -/
abbrev GrammarSampleExtractedRuleListCharacteristicSample
    {G : WorkingMCFG N α} {obs : α → M}
    (A : SampleExtractedRuleListLearner G obs) :=
  SampleExtractedRuleListCharacteristicSample A G.StringLanguage

/-- Grammar-target limiting identification for sample-extracted actual rule-list
learners. -/
theorem GrammarSampleExtractedRuleListCharacteristicSample.identifiesInLimit
    {G : WorkingMCFG N α} {obs : α → M}
    {A : SampleExtractedRuleListLearner G obs}
    (C : GrammarSampleExtractedRuleListCharacteristicSample A) :
    FiniteHypothesisIdentifiesGrammarInLimit A.toFiniteHypothesisLearner G := by
  exact SampleExtractedRuleListCharacteristicSample.identifiesInLimit C

/-- Grammar-target pointwise context form. -/
theorem GrammarSampleExtractedRuleListCharacteristicSample.eventuallyCorrectContexts
    {G : WorkingMCFG N α} {obs : α → M}
    {A : SampleExtractedRuleListLearner G obs}
    (C : GrammarSampleExtractedRuleListCharacteristicSample A) :
    FiniteHypothesisEventuallyCorrectContexts
      A.toFiniteHypothesisLearner G.StringLanguage := by
  exact SampleExtractedRuleListCharacteristicSample.eventuallyCorrectContexts C

end SampleExtractedRuleListsGold

end FIv21
