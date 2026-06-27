import LeanCfgProject.MCFG.FI_v2_1_ObservedSampleAtomsExact

/-!
# FI v2.1 Lean experiment: Gold wrapper for observed sample atoms

This file packages a learner returning `ObservedSampleAtoms` data.  Compared
with the minimal support-extraction layer, the learner now returns explicit
finite tuple/context/unit-edge atom lists from which its `FiniteLearnerSupport`
is assembled.
-/

namespace FIv21

universe u v w

section ObservedSampleAtomsGold

variable {N : Type w} {α : Type u}
variable [DecidableEq α]
variable {M : Type v} [Monoid M] [Fintype M]

/-- A learner mapping each finite sample to observed-atom extraction data. -/
abbrev ObservedSampleAtomsLearner
    (G : WorkingMCFG N α) (obs : α → M) :=
  (K : Finset (Word α)) → ObservedSampleAtoms G obs K

/-- Forget an observed-atom learner to the sample-extracted rule-list learner. -/
noncomputable def ObservedSampleAtomsLearner.toSampleExtractedRuleListLearner
    {G : WorkingMCFG N α} {obs : α → M}
    (A : ObservedSampleAtomsLearner G obs) :
    SampleExtractedRuleListLearner G obs :=
  fun K => (A K).toSampleExtractedRuleLists

/-- Forget an observed-atom learner to the concrete extracted-sample learner
interface. -/
noncomputable def ObservedSampleAtomsLearner.toConcreteExtractedSampleLearner
    {G : WorkingMCFG N α} {obs : α → M}
    (A : ObservedSampleAtomsLearner G obs) :
    ConcreteExtractedSampleLearner G obs :=
  A.toSampleExtractedRuleListLearner.toConcreteExtractedSampleLearner

/-- Forget an observed-atom learner to the finite-hypothesis learner interface. -/
noncomputable def ObservedSampleAtomsLearner.toFiniteHypothesisLearner
    {G : WorkingMCFG N α} {obs : α → M}
    (A : ObservedSampleAtomsLearner G obs) :
    FiniteHypothesisLearner α M :=
  A.toSampleExtractedRuleListLearner.toFiniteHypothesisLearner

/-- Characteristic sample certificate for an observed-atom learner. -/
structure ObservedSampleAtomsCharacteristicSample
    {G : WorkingMCFG N α} {obs : α → M}
    (A : ObservedSampleAtomsLearner G obs) (L : Set (Word α)) where
  sample : Finset (Word α)
  positive : PositiveForLanguage sample L
  exact_after_extending :
    ∀ K : Finset (Word α),
      SampleExtends sample K →
      PositiveForLanguage K L →
        ObservedSampleAtomsExactForLanguage (A K) L

namespace ObservedSampleAtomsCharacteristicSample

/-- Forget to the sample-extracted rule-list characteristic-sample interface. -/
noncomputable def toSampleExtractedRuleListCharacteristicSample
    {G : WorkingMCFG N α} {obs : α → M}
    {A : ObservedSampleAtomsLearner G obs} {L : Set (Word α)}
    (C : ObservedSampleAtomsCharacteristicSample A L) :
    SampleExtractedRuleListCharacteristicSample
      A.toSampleExtractedRuleListLearner L :=
  { sample := C.sample
    positive := C.positive
    exact_after_extending := by
      intro K hExt hPos
      exact (C.exact_after_extending K hExt hPos).extractedExact }

/-- Observed-atom characteristic samples identify the target at the transported
context distribution level. -/
theorem identifiesInLimit
    {G : WorkingMCFG N α} {obs : α → M}
    {A : ObservedSampleAtomsLearner G obs} {L : Set (Word α)}
    (C : ObservedSampleAtomsCharacteristicSample A L) :
    FiniteHypothesisIdentifiesInLimit A.toFiniteHypothesisLearner L := by
  exact SampleExtractedRuleListCharacteristicSample.identifiesInLimit
    C.toSampleExtractedRuleListCharacteristicSample

/-- Pointwise context-membership form of limiting identification. -/
theorem eventuallyCorrectContexts
    {G : WorkingMCFG N α} {obs : α → M}
    {A : ObservedSampleAtomsLearner G obs} {L : Set (Word α)}
    (C : ObservedSampleAtomsCharacteristicSample A L) :
    FiniteHypothesisEventuallyCorrectContexts A.toFiniteHypothesisLearner L := by
  exact SampleExtractedRuleListCharacteristicSample.eventuallyCorrectContexts
    C.toSampleExtractedRuleListCharacteristicSample

/-- After the threshold, the support is assembled from the observed atom lists of
the current prefix sample. -/
theorem support_eq_observedAtoms_after
    {G : WorkingMCFG N α} {obs : α → M}
    {A : ObservedSampleAtomsLearner G obs} {L : Set (Word α)}
    (C : ObservedSampleAtomsCharacteristicSample A L)
    {K : Finset (Word α)}
    (hExt : SampleExtends C.sample K)
    (hPos : PositiveForLanguage K L) :
    (A K).support =
      supportOfObservedAtoms K (A K).tupleAtoms (A K).contextAtoms (A K).unitEdgeAtoms := by
  exact (C.exact_after_extending K hExt hPos).support_eq_observedAtoms

/-- After the threshold, tuple support is exactly membership in the listed tuple
atoms. -/
theorem supportsTuple_iff_mem_tupleAtoms_after
    {G : WorkingMCFG N α} {obs : α → M}
    {A : ObservedSampleAtomsLearner G obs} {L : Set (Word α)}
    (C : ObservedSampleAtomsCharacteristicSample A L)
    {K : Finset (Word α)}
    (hExt : SampleExtends C.sample K)
    (hPos : PositiveForLanguage K L)
    {d : Nat} (x : Tuple α d) :
    (A K).support.SupportsTuple x ↔
      (Sigma.mk d x : TupleAtom α) ∈ (A K).tupleAtoms := by
  exact (C.exact_after_extending K hExt hPos).supportsTuple_iff_mem_tupleAtoms x

/-- After the threshold, context support is exactly membership in the listed
context atoms. -/
theorem supportsContext_iff_mem_contextAtoms_after
    {G : WorkingMCFG N α} {obs : α → M}
    {A : ObservedSampleAtomsLearner G obs} {L : Set (Word α)}
    (C : ObservedSampleAtomsCharacteristicSample A L)
    {K : Finset (Word α)}
    (hExt : SampleExtends C.sample K)
    (hPos : PositiveForLanguage K L)
    {d : Nat} (c : NamedSentenceContext α d) :
    (A K).support.SupportsContext c ↔
      (Sigma.mk d c : ContextAtom α) ∈ (A K).contextAtoms := by
  exact (C.exact_after_extending K hExt hPos).supportsContext_iff_mem_contextAtoms c

/-- After the threshold, unit-edge support is exactly membership in the listed
unit-edge atoms. -/
theorem supportsUnitEdge_iff_mem_unitEdgeAtoms_after
    {G : WorkingMCFG N α} {obs : α → M}
    {A : ObservedSampleAtomsLearner G obs} {L : Set (Word α)}
    (C : ObservedSampleAtomsCharacteristicSample A L)
    {K : Finset (Word α)}
    (hExt : SampleExtends C.sample K)
    (hPos : PositiveForLanguage K L)
    {d : Nat} (x y : Tuple α d) :
    (A K).support.SupportsUnitEdge x y ↔
      (Sigma.mk d (x, y) : UnitEdgeAtom α) ∈ (A K).unitEdgeAtoms := by
  exact (C.exact_after_extending K hExt hPos).supportsUnitEdge_iff_mem_unitEdgeAtoms x y

/-- After the threshold, the actual refined rule lists contain all ordinary
output-type refinements. -/
theorem actualRuleLists_containsAll_after
    {G : WorkingMCFG N α} {obs : α → M}
    {A : ObservedSampleAtomsLearner G obs} {L : Set (Word α)}
    (C : ObservedSampleAtomsCharacteristicSample A L)
    {K : Finset (Word α)}
    (hExt : SampleExtends C.sample K)
    (hPos : PositiveForLanguage K L) :
    (A K).concreteRules.toFintypeOutputTypeRefinementCertificate.toOutputTypeRefinedGrammar.ContainsAllOrdinaryRuleRefinements := by
  exact (C.exact_after_extending K hExt hPos).actualRuleLists_containsAll

/-- After the threshold, the actual refined rule lists are supported by the
canonical finite-monoid rule-enumeration plan. -/
theorem actualRuleLists_supportedByPlan_after
    {G : WorkingMCFG N α} {obs : α → M}
    {A : ObservedSampleAtomsLearner G obs} {L : Set (Word α)}
    (C : ObservedSampleAtomsCharacteristicSample A L)
    {K : Finset (Word α)}
    (hExt : SampleExtends C.sample K)
    (hPos : PositiveForLanguage K L) :
    (A K).concreteRules.grammar.AllRulesSupportedByPlan
      (FiniteRuleEnumerationPlan.ofFintype G obs) := by
  exact (C.exact_after_extending K hExt hPos).actualRuleLists_supportedByPlan

end ObservedSampleAtomsCharacteristicSample

/-- Grammar-target characteristic sample abbreviation. -/
abbrev GrammarObservedSampleAtomsCharacteristicSample
    {G : WorkingMCFG N α} {obs : α → M}
    (A : ObservedSampleAtomsLearner G obs) :=
  ObservedSampleAtomsCharacteristicSample A G.StringLanguage

/-- Grammar-target limiting identification for observed-atom learners. -/
theorem GrammarObservedSampleAtomsCharacteristicSample.identifiesInLimit
    {G : WorkingMCFG N α} {obs : α → M}
    {A : ObservedSampleAtomsLearner G obs}
    (C : GrammarObservedSampleAtomsCharacteristicSample A) :
    FiniteHypothesisIdentifiesGrammarInLimit A.toFiniteHypothesisLearner G := by
  exact ObservedSampleAtomsCharacteristicSample.identifiesInLimit C

/-- Grammar-target pointwise context form. -/
theorem GrammarObservedSampleAtomsCharacteristicSample.eventuallyCorrectContexts
    {G : WorkingMCFG N α} {obs : α → M}
    {A : ObservedSampleAtomsLearner G obs}
    (C : GrammarObservedSampleAtomsCharacteristicSample A) :
    FiniteHypothesisEventuallyCorrectContexts
      A.toFiniteHypothesisLearner G.StringLanguage := by
  exact ObservedSampleAtomsCharacteristicSample.eventuallyCorrectContexts C

end ObservedSampleAtomsGold

end FIv21
