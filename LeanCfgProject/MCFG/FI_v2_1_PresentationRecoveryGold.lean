import LeanCfgProject.MCFG.FI_v2_1_PresentationRecoveryExact

/-!
# FI v2.1 Lean experiment: presentation-relative recovery Gold wrapper

This seventy-sixth layer adds the Gold-style wrapper for presentation-relative
recovery profiles.

The limiting identification theorem is inherited from the bounded-data recovery
wrapper.  The additional API says that, after the characteristic-sample
threshold, the learner packages also carry a presentation-relative bound
certificate dominating the recovery bound and the finite refined-rule count.
-/

namespace FIv21

universe u v w

noncomputable section

section PresentationRecoveryGold

variable {N : Type w} {α : Type u}
variable [DecidableEq α]
variable {M : Type v} [Monoid M] [Fintype M]

/-- Characteristic-sample certificate whose post-threshold canonical packages
also carry presentation-relative recovery profiles. -/
structure CanonicalPresentationRecoveryCharacteristicSample
    {G : WorkingMCFG N α} {obs : α → M}
    (A : CanonicalLearnerGrammarLearner G obs) where
  base : CanonicalBoundedDataRecoveryCharacteristicSample A
  presentation_after :
    ∀ (K : Finset (Word α)),
      SampleExtends base.base.base.base.base.base.base.base.startWitness.base.sample K →
      PositiveForLanguage K G.StringLanguage →
      CanonicalPresentationRecoveryProfile (A K)
  presentation_recovery_agrees_after :
    ∀ (K : Finset (Word α))
      (hExt : SampleExtends base.base.base.base.base.base.base.base.startWitness.base.sample K)
      (hPos : PositiveForLanguage K G.StringLanguage),
      (presentation_after K hExt hPos).recoveryProfile =
        base.recovery_after K hExt hPos

namespace CanonicalPresentationRecoveryCharacteristicSample

/-- Any bounded-data recovery characteristic-sample certificate carries
 tautological presentation-relative profiles after the threshold. -/
def ofBoundedDataRecoveryCharacteristicSample
    {G : WorkingMCFG N α} {obs : α → M}
    {A : CanonicalLearnerGrammarLearner G obs}
    (C : CanonicalBoundedDataRecoveryCharacteristicSample A) :
    CanonicalPresentationRecoveryCharacteristicSample A :=
  { base := C
    presentation_after := by
      intro K hExt hPos
      exact CanonicalPresentationRecoveryProfile.trivialForRecovery
        (C.recovery_after K hExt hPos)
    presentation_recovery_agrees_after := by
      intro K hExt hPos
      rfl }

/-- Forget to the bounded-data recovery characteristic-sample certificate. -/
def toBoundedDataRecoveryCharacteristicSample
    {G : WorkingMCFG N α} {obs : α → M}
    {A : CanonicalLearnerGrammarLearner G obs}
    (C : CanonicalPresentationRecoveryCharacteristicSample A) :
    CanonicalBoundedDataRecoveryCharacteristicSample A :=
  C.base

/-- Post-threshold exact package with presentation-relative recovery
information. -/
def exact_with_presentation_after
    {G : WorkingMCFG N α} {obs : α → M}
    {A : CanonicalLearnerGrammarLearner G obs}
    (C : CanonicalPresentationRecoveryCharacteristicSample A)
    (K : Finset (Word α))
    (hExt : SampleExtends C.base.base.base.base.base.base.base.base.startWitness.base.sample K)
    (hPos : PositiveForLanguage K G.StringLanguage) :
    CanonicalLearnerGrammarExactWithPresentationRecovery (A K) :=
  { exactWithRecovery := C.base.exact_with_recovery_after K hExt hPos
    presentationProfile := C.presentation_after K hExt hPos
    presentation_recovery_agrees :=
      C.presentation_recovery_agrees_after K hExt hPos }

/-- Post-threshold exact distribution equality. -/
theorem approxDistribution_exact_after
    {G : WorkingMCFG N α} {obs : α → M}
    {A : CanonicalLearnerGrammarLearner G obs}
    (C : CanonicalPresentationRecoveryCharacteristicSample A)
    (K : Finset (Word α))
    (hExt : SampleExtends C.base.base.base.base.base.base.base.base.startWitness.base.sample K)
    (hPos : PositiveForLanguage K G.StringLanguage)
    {d : Nat} (x : Tuple α d) :
    (A K).ApproxDistribution x = NamedDistribution G.StringLanguage x := by
  exact (C.exact_with_presentation_after K hExt hPos).approxDistribution_exact x

/-- Post-threshold learner-side generation of a sampled word. -/
theorem sample_word_generated_by_learner_after
    {G : WorkingMCFG N α} {obs : α → M}
    {A : CanonicalLearnerGrammarLearner G obs}
    (C : CanonicalPresentationRecoveryCharacteristicSample A)
    (K : Finset (Word α))
    (hExt : SampleExtends C.base.base.base.base.base.base.base.base.startWitness.base.sample K)
    (hPos : PositiveForLanguage K G.StringLanguage)
    (w : Word α) (hw : w ∈ K) :
    w ∈ (A K).wordLanguage := by
  exact (C.exact_with_presentation_after K hExt hPos).sample_word_generated_by_learner w hw

/-- Post-threshold target-side start derivation witness for a sampled word. -/
theorem sample_word_start_derives_after
    {G : WorkingMCFG N α} {obs : α → M}
    {A : CanonicalLearnerGrammarLearner G obs}
    (C : CanonicalPresentationRecoveryCharacteristicSample A)
    (K : Finset (Word α))
    (hExt : SampleExtends C.base.base.base.base.base.base.base.base.startWitness.base.sample K)
    (hPos : PositiveForLanguage K G.StringLanguage)
    (w : Word α) (hw : w ∈ K) :
    ∃ h : 1 = G.arity G.start,
      DerivesTuple G G.start (castTuple h (singletonTuple w)) := by
  exact (C.exact_with_presentation_after K hExt hPos).sample_word_start_derives w hw

/-- Post-threshold rule-list coverage. -/
theorem refinedRuleLists_coverAll_after
    {G : WorkingMCFG N α} {obs : α → M}
    {A : CanonicalLearnerGrammarLearner G obs}
    (C : CanonicalPresentationRecoveryCharacteristicSample A)
    (K : Finset (Word α))
    (hExt : SampleExtends C.base.base.base.base.base.base.base.base.startWitness.base.sample K)
    (hPos : PositiveForLanguage K G.StringLanguage) :
    (A K).finiteRefinedGrammar.CoversAllOrdinaryRuleRefinements := by
  exact (C.exact_with_presentation_after K hExt hPos).refinedRuleLists_coverAll

/-- Post-threshold plan support for all listed refined rules. -/
theorem refinedRuleLists_supportedByPlan_after
    {G : WorkingMCFG N α} {obs : α → M}
    {A : CanonicalLearnerGrammarLearner G obs}
    (C : CanonicalPresentationRecoveryCharacteristicSample A)
    (K : Finset (Word α))
    (hExt : SampleExtends C.base.base.base.base.base.base.base.base.startWitness.base.sample K)
    (hPos : PositiveForLanguage K G.StringLanguage) :
    (A K).finiteRefinedGrammar.AllRulesSupportedByPlan
      (A K).ruleEnumerationPlan := by
  exact (C.exact_with_presentation_after K hExt hPos).refinedRuleLists_supportedByPlan

/-- Post-threshold refined-rule count bounded by the total presentation bound. -/
theorem refinedRuleCount_le_totalPresentationBound_after
    {G : WorkingMCFG N α} {obs : α → M}
    {A : CanonicalLearnerGrammarLearner G obs}
    (C : CanonicalPresentationRecoveryCharacteristicSample A)
    (K : Finset (Word α))
    (hExt : SampleExtends C.base.base.base.base.base.base.base.base.startWitness.base.sample K)
    (hPos : PositiveForLanguage K G.StringLanguage) :
    (A K).refinedRuleCount ≤
      (C.presentation_after K hExt hPos).totalPresentationBound := by
  exact (C.exact_with_presentation_after K hExt hPos).refinedRuleCount_le_totalPresentationBound

/-- Post-threshold recovery bound bounded by the total presentation bound. -/
theorem totalRecoveryBound_le_totalPresentationBound_after
    {G : WorkingMCFG N α} {obs : α → M}
    {A : CanonicalLearnerGrammarLearner G obs}
    (C : CanonicalPresentationRecoveryCharacteristicSample A)
    (K : Finset (Word α))
    (hExt : SampleExtends C.base.base.base.base.base.base.base.base.startWitness.base.sample K)
    (hPos : PositiveForLanguage K G.StringLanguage) :
    (C.presentation_after K hExt hPos).recoveryProfile.totalRecoveryBound ≤
      (C.presentation_after K hExt hPos).totalPresentationBound := by
  exact (C.exact_with_presentation_after K hExt hPos).totalRecoveryBound_le_totalPresentationBound

/-- Post-threshold sample-size parameter equals the current finite sample size. -/
theorem sampleSize_eq_card_after
    {G : WorkingMCFG N α} {obs : α → M}
    {A : CanonicalLearnerGrammarLearner G obs}
    (C : CanonicalPresentationRecoveryCharacteristicSample A)
    (K : Finset (Word α))
    (hExt : SampleExtends C.base.base.base.base.base.base.base.base.startWitness.base.sample K)
    (hPos : PositiveForLanguage K G.StringLanguage) :
    (C.presentation_after K hExt hPos).recoveryProfile.shapeProfile.parameterProfile.sampleSize =
      K.card := by
  exact (C.exact_with_presentation_after K hExt hPos).sampleSize_eq_card

/-- Post-threshold monoid-cardinality parameter equals `Fintype.card M`. -/
theorem monoidCardinality_eq_fintypeCard_after
    {G : WorkingMCFG N α} {obs : α → M}
    {A : CanonicalLearnerGrammarLearner G obs}
    (C : CanonicalPresentationRecoveryCharacteristicSample A)
    (K : Finset (Word α))
    (hExt : SampleExtends C.base.base.base.base.base.base.base.base.startWitness.base.sample K)
    (hPos : PositiveForLanguage K G.StringLanguage) :
    (C.presentation_after K hExt hPos).recoveryProfile.shapeProfile.parameterProfile.monoidCardinality =
      Fintype.card M := by
  exact (C.exact_with_presentation_after K hExt hPos).monoidCardinality_eq_fintypeCard

/-- The post-threshold total presentation bound carries an abstract polynomial
witness. -/
def totalPresentationPolynomialWitness_after
    {G : WorkingMCFG N α} {obs : α → M}
    {A : CanonicalLearnerGrammarLearner G obs}
    (C : CanonicalPresentationRecoveryCharacteristicSample A)
    (K : Finset (Word α))
    (hExt : SampleExtends C.base.base.base.base.base.base.base.base.startWitness.base.sample K)
    (hPos : PositiveForLanguage K G.StringLanguage) :
    PolynomialBoundWitness
      (C.presentation_after K hExt hPos).totalPresentationBound :=
  (C.presentation_after K hExt hPos).totalPresentationPolynomialWitness

/-- Limiting distributional identification inherited from the bounded-data
recovery Gold wrapper. -/
theorem identifiesInLimit
    {G : WorkingMCFG N α} {obs : α → M}
    {A : CanonicalLearnerGrammarLearner G obs}
    (C : CanonicalPresentationRecoveryCharacteristicSample A) :
    FiniteHypothesisIdentifiesGrammarInLimit A.toFiniteHypothesisLearner G := by
  exact C.base.identifiesInLimit

/-- Pointwise limiting context correctness inherited from the bounded-data
recovery Gold wrapper. -/
theorem eventuallyCorrectContexts
    {G : WorkingMCFG N α} {obs : α → M}
    {A : CanonicalLearnerGrammarLearner G obs}
    (C : CanonicalPresentationRecoveryCharacteristicSample A) :
    FiniteHypothesisEventuallyCorrectContexts
      A.toFiniteHypothesisLearner G.StringLanguage := by
  exact C.base.eventuallyCorrectContexts

end CanonicalPresentationRecoveryCharacteristicSample

end PresentationRecoveryGold

end

end FIv21
