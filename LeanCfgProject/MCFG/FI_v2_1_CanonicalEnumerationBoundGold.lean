import LeanCfgProject.MCFG.FI_v2_1_CanonicalEnumerationBoundExact

/-!
# FI v2.1 Lean experiment: Gold wrapper with enumeration bounds

This sixty-first layer adds enumeration-bound certificates to the canonical
rule-list counting Gold wrapper.

The result is still deliberately conservative: the default construction uses
exact counts as bounds.  Later complexity files can replace the tautological
bounds by closed-form or polynomial bounds while reusing the same interface.
-/

namespace FIv21

universe u v w

noncomputable section

section CanonicalEnumerationBoundGold

variable {N : Type w} {α : Type u}
variable [DecidableEq α]
variable {M : Type v} [Monoid M] [Fintype M]

/-- Characteristic-sample certificate whose post-threshold canonical packages
also carry enumeration-bound certificates. -/
structure CanonicalEnumerationBoundCharacteristicSample
    {G : WorkingMCFG N α} {obs : α → M}
    (A : CanonicalLearnerGrammarLearner G obs) where
  base : CanonicalRuleListCountingCharacteristicSample A
  bounds_after :
    ∀ (K : Finset (Word α)),
      SampleExtends base.base.base.startWitness.base.sample K →
      PositiveForLanguage K G.StringLanguage →
      CanonicalEnumerationBounds (A K)

namespace CanonicalEnumerationBoundCharacteristicSample

/-- Any counting characteristic-sample certificate carries the tautological
exact-count bounds after the threshold. -/
def ofCountingCharacteristicSample
    {G : WorkingMCFG N α} {obs : α → M}
    {A : CanonicalLearnerGrammarLearner G obs}
    (C : CanonicalRuleListCountingCharacteristicSample A) :
    CanonicalEnumerationBoundCharacteristicSample A :=
  { base := C
    bounds_after := by
      intro K hExt hPos
      exact CanonicalEnumerationBounds.exactForPackage (A K) }

/-- Forget to the previous counting characteristic-sample certificate. -/
def toCountingCharacteristicSample
    {G : WorkingMCFG N α} {obs : α → M}
    {A : CanonicalLearnerGrammarLearner G obs}
    (C : CanonicalEnumerationBoundCharacteristicSample A) :
    CanonicalRuleListCountingCharacteristicSample A :=
  C.base

/-- Post-threshold exact package with counts and enumeration bounds. -/
def exact_with_bounds_after
    {G : WorkingMCFG N α} {obs : α → M}
    {A : CanonicalLearnerGrammarLearner G obs}
    (C : CanonicalEnumerationBoundCharacteristicSample A)
    (K : Finset (Word α))
    (hExt : SampleExtends C.base.base.base.startWitness.base.sample K)
    (hPos : PositiveForLanguage K G.StringLanguage) :
    CanonicalLearnerGrammarExactWithEnumerationBounds (A K) :=
  { exactWithCounts := C.base.exact_with_counts_after K hExt hPos
    bounds := C.bounds_after K hExt hPos }

/-- Post-threshold exact distribution equality. -/
theorem approxDistribution_exact_after
    {G : WorkingMCFG N α} {obs : α → M}
    {A : CanonicalLearnerGrammarLearner G obs}
    (C : CanonicalEnumerationBoundCharacteristicSample A)
    (K : Finset (Word α))
    (hExt : SampleExtends C.base.base.base.startWitness.base.sample K)
    (hPos : PositiveForLanguage K G.StringLanguage)
    {d : Nat} (x : Tuple α d) :
    (A K).ApproxDistribution x = NamedDistribution G.StringLanguage x := by
  exact (C.exact_with_bounds_after K hExt hPos).approxDistribution_exact x

/-- Post-threshold learner-side generation of a sampled word. -/
theorem sample_word_generated_by_learner_after
    {G : WorkingMCFG N α} {obs : α → M}
    {A : CanonicalLearnerGrammarLearner G obs}
    (C : CanonicalEnumerationBoundCharacteristicSample A)
    (K : Finset (Word α))
    (hExt : SampleExtends C.base.base.base.startWitness.base.sample K)
    (hPos : PositiveForLanguage K G.StringLanguage)
    (w : Word α) (hw : w ∈ K) :
    w ∈ (A K).wordLanguage := by
  exact (C.exact_with_bounds_after K hExt hPos).sample_word_generated_by_learner w hw

/-- Post-threshold target-side start derivation witness for a sampled word. -/
theorem sample_word_start_derives_after
    {G : WorkingMCFG N α} {obs : α → M}
    {A : CanonicalLearnerGrammarLearner G obs}
    (C : CanonicalEnumerationBoundCharacteristicSample A)
    (K : Finset (Word α))
    (hExt : SampleExtends C.base.base.base.startWitness.base.sample K)
    (hPos : PositiveForLanguage K G.StringLanguage)
    (w : Word α) (hw : w ∈ K) :
    ∃ h : 1 = G.arity G.start,
      DerivesTuple G G.start (castTuple h (singletonTuple w)) := by
  exact (C.exact_with_bounds_after K hExt hPos).sample_word_start_derives w hw

/-- Post-threshold rule-list coverage. -/
theorem refinedRuleLists_coverAll_after
    {G : WorkingMCFG N α} {obs : α → M}
    {A : CanonicalLearnerGrammarLearner G obs}
    (C : CanonicalEnumerationBoundCharacteristicSample A)
    (K : Finset (Word α))
    (hExt : SampleExtends C.base.base.base.startWitness.base.sample K)
    (hPos : PositiveForLanguage K G.StringLanguage) :
    (A K).finiteRefinedGrammar.CoversAllOrdinaryRuleRefinements := by
  exact (C.exact_with_bounds_after K hExt hPos).refinedRuleLists_coverAll

/-- Post-threshold plan support for all listed refined rules. -/
theorem refinedRuleLists_supportedByPlan_after
    {G : WorkingMCFG N α} {obs : α → M}
    {A : CanonicalLearnerGrammarLearner G obs}
    (C : CanonicalEnumerationBoundCharacteristicSample A)
    (K : Finset (Word α))
    (hExt : SampleExtends C.base.base.base.startWitness.base.sample K)
    (hPos : PositiveForLanguage K G.StringLanguage) :
    (A K).finiteRefinedGrammar.AllRulesSupportedByPlan
      (A K).ruleEnumerationPlan := by
  exact (C.exact_with_bounds_after K hExt hPos).refinedRuleLists_supportedByPlan

/-- Post-threshold total refined-rule count bound. -/
theorem refinedRuleCount_le_bound_after
    {G : WorkingMCFG N α} {obs : α → M}
    {A : CanonicalLearnerGrammarLearner G obs}
    (C : CanonicalEnumerationBoundCharacteristicSample A)
    (K : Finset (Word α))
    (hExt : SampleExtends C.base.base.base.startWitness.base.sample K)
    (hPos : PositiveForLanguage K G.StringLanguage) :
    (A K).refinedRuleCount ≤
      (C.bounds_after K hExt hPos).totalBound := by
  exact (C.exact_with_bounds_after K hExt hPos).refinedRuleCount_le_bound

/-- Post-threshold terminal refined-rule count bound. -/
theorem refinedTerminalRuleCount_le_bound_after
    {G : WorkingMCFG N α} {obs : α → M}
    {A : CanonicalLearnerGrammarLearner G obs}
    (C : CanonicalEnumerationBoundCharacteristicSample A)
    (K : Finset (Word α))
    (hExt : SampleExtends C.base.base.base.startWitness.base.sample K)
    (hPos : PositiveForLanguage K G.StringLanguage) :
    (A K).refinedTerminalRuleCount ≤
      (C.bounds_after K hExt hPos).terminalBound := by
  exact (C.exact_with_bounds_after K hExt hPos).refinedTerminalRuleCount_le_bound

/-- Post-threshold binary refined-rule count bound. -/
theorem refinedBinaryRuleCount_le_bound_after
    {G : WorkingMCFG N α} {obs : α → M}
    {A : CanonicalLearnerGrammarLearner G obs}
    (C : CanonicalEnumerationBoundCharacteristicSample A)
    (K : Finset (Word α))
    (hExt : SampleExtends C.base.base.base.startWitness.base.sample K)
    (hPos : PositiveForLanguage K G.StringLanguage) :
    (A K).refinedBinaryRuleCount ≤
      (C.bounds_after K hExt hPos).binaryBound := by
  exact (C.exact_with_bounds_after K hExt hPos).refinedBinaryRuleCount_le_bound

/-- Post-threshold start refined-rule count bound. -/
theorem refinedStartRuleCount_le_bound_after
    {G : WorkingMCFG N α} {obs : α → M}
    {A : CanonicalLearnerGrammarLearner G obs}
    (C : CanonicalEnumerationBoundCharacteristicSample A)
    (K : Finset (Word α))
    (hExt : SampleExtends C.base.base.base.startWitness.base.sample K)
    (hPos : PositiveForLanguage K G.StringLanguage) :
    (A K).refinedStartRuleCount ≤
      (C.bounds_after K hExt hPos).startBound := by
  exact (C.exact_with_bounds_after K hExt hPos).refinedStartRuleCount_le_bound

/-- Limiting distributional identification inherited from the counting Gold
wrapper. -/
theorem identifiesInLimit
    {G : WorkingMCFG N α} {obs : α → M}
    {A : CanonicalLearnerGrammarLearner G obs}
    (C : CanonicalEnumerationBoundCharacteristicSample A) :
    FiniteHypothesisIdentifiesGrammarInLimit A.toFiniteHypothesisLearner G := by
  exact C.base.identifiesInLimit

/-- Pointwise limiting context correctness inherited from the counting Gold
wrapper. -/
theorem eventuallyCorrectContexts
    {G : WorkingMCFG N α} {obs : α → M}
    {A : CanonicalLearnerGrammarLearner G obs}
    (C : CanonicalEnumerationBoundCharacteristicSample A) :
    FiniteHypothesisEventuallyCorrectContexts
      A.toFiniteHypothesisLearner G.StringLanguage := by
  exact C.base.eventuallyCorrectContexts

end CanonicalEnumerationBoundCharacteristicSample

end CanonicalEnumerationBoundGold

end

end FIv21
