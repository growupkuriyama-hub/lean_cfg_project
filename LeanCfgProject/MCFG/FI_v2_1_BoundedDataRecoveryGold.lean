import LeanCfgProject.MCFG.FI_v2_1_BoundedDataRecoveryExact

/-!
# FI v2.1 Lean experiment: Gold wrapper with bounded-data recovery profiles

This seventy-third layer attaches bounded-data recovery profiles to the
post-threshold canonical learner packages in the Gold-style wrapper.

The limiting identification theorem is inherited from the shape-profile wrapper.
The additional API says that, after the characteristic-sample threshold, the
learner packages also expose recovery bounds dominating their finite refined
rule lists.
-/

namespace FIv21

universe u v w

noncomputable section

section BoundedDataRecoveryGold

variable {N : Type w} {α : Type u}
variable [DecidableEq α]
variable {M : Type v} [Monoid M] [Fintype M]

/-- Characteristic-sample certificate whose post-threshold canonical packages
also carry bounded-data recovery profiles. -/
structure CanonicalBoundedDataRecoveryCharacteristicSample
    {G : WorkingMCFG N α} {obs : α → M}
    (A : CanonicalLearnerGrammarLearner G obs) where
  base : CanonicalShapeProfileCharacteristicSample A
  recovery_after :
    ∀ (K : Finset (Word α)),
      SampleExtends base.base.base.base.base.base.startWitness.base.sample K →
      PositiveForLanguage K G.StringLanguage →
      CanonicalBoundedDataRecoveryProfile (A K)
  recovery_shape_agrees_after :
    ∀ (K : Finset (Word α))
      (hExt : SampleExtends base.base.base.base.base.base.startWitness.base.sample K)
      (hPos : PositiveForLanguage K G.StringLanguage),
      (recovery_after K hExt hPos).shapeProfile =
        base.shape_after K hExt hPos

namespace CanonicalBoundedDataRecoveryCharacteristicSample

/-- Any shape-profile characteristic-sample certificate carries tautological
bounded-data recovery profiles after the threshold. -/
def ofShapeProfileCharacteristicSample
    {G : WorkingMCFG N α} {obs : α → M}
    {A : CanonicalLearnerGrammarLearner G obs}
    (C : CanonicalShapeProfileCharacteristicSample A) :
    CanonicalBoundedDataRecoveryCharacteristicSample A :=
  { base := C
    recovery_after := by
      intro K hExt hPos
      exact CanonicalBoundedDataRecoveryProfile.trivialForShape
        (C.shape_after K hExt hPos)
    recovery_shape_agrees_after := by
      intro K hExt hPos
      rfl }

/-- Forget to the shape-profile characteristic-sample certificate. -/
def toShapeProfileCharacteristicSample
    {G : WorkingMCFG N α} {obs : α → M}
    {A : CanonicalLearnerGrammarLearner G obs}
    (C : CanonicalBoundedDataRecoveryCharacteristicSample A) :
    CanonicalShapeProfileCharacteristicSample A :=
  C.base

/-- Post-threshold exact package with bounded-data recovery information. -/
def exact_with_recovery_after
    {G : WorkingMCFG N α} {obs : α → M}
    {A : CanonicalLearnerGrammarLearner G obs}
    (C : CanonicalBoundedDataRecoveryCharacteristicSample A)
    (K : Finset (Word α))
    (hExt : SampleExtends C.base.base.base.base.base.base.startWitness.base.sample K)
    (hPos : PositiveForLanguage K G.StringLanguage) :
    CanonicalLearnerGrammarExactWithBoundedDataRecovery (A K) :=
  { exactWithShapeProfile := C.base.exact_with_shape_profile_after K hExt hPos
    recoveryProfile := C.recovery_after K hExt hPos
    recovery_shape_agrees := C.recovery_shape_agrees_after K hExt hPos }

/-- Post-threshold exact distribution equality. -/
theorem approxDistribution_exact_after
    {G : WorkingMCFG N α} {obs : α → M}
    {A : CanonicalLearnerGrammarLearner G obs}
    (C : CanonicalBoundedDataRecoveryCharacteristicSample A)
    (K : Finset (Word α))
    (hExt : SampleExtends C.base.base.base.base.base.base.startWitness.base.sample K)
    (hPos : PositiveForLanguage K G.StringLanguage)
    {d : Nat} (x : Tuple α d) :
    (A K).ApproxDistribution x = NamedDistribution G.StringLanguage x := by
  exact (C.exact_with_recovery_after K hExt hPos).approxDistribution_exact x

/-- Post-threshold learner-side generation of a sampled word. -/
theorem sample_word_generated_by_learner_after
    {G : WorkingMCFG N α} {obs : α → M}
    {A : CanonicalLearnerGrammarLearner G obs}
    (C : CanonicalBoundedDataRecoveryCharacteristicSample A)
    (K : Finset (Word α))
    (hExt : SampleExtends C.base.base.base.base.base.base.startWitness.base.sample K)
    (hPos : PositiveForLanguage K G.StringLanguage)
    (w : Word α) (hw : w ∈ K) :
    w ∈ (A K).wordLanguage := by
  exact (C.exact_with_recovery_after K hExt hPos).sample_word_generated_by_learner w hw

/-- Post-threshold target-side start derivation witness for a sampled word. -/
theorem sample_word_start_derives_after
    {G : WorkingMCFG N α} {obs : α → M}
    {A : CanonicalLearnerGrammarLearner G obs}
    (C : CanonicalBoundedDataRecoveryCharacteristicSample A)
    (K : Finset (Word α))
    (hExt : SampleExtends C.base.base.base.base.base.base.startWitness.base.sample K)
    (hPos : PositiveForLanguage K G.StringLanguage)
    (w : Word α) (hw : w ∈ K) :
    ∃ h : 1 = G.arity G.start,
      DerivesTuple G G.start (castTuple h (singletonTuple w)) := by
  exact (C.exact_with_recovery_after K hExt hPos).sample_word_start_derives w hw

/-- Post-threshold rule-list coverage. -/
theorem refinedRuleLists_coverAll_after
    {G : WorkingMCFG N α} {obs : α → M}
    {A : CanonicalLearnerGrammarLearner G obs}
    (C : CanonicalBoundedDataRecoveryCharacteristicSample A)
    (K : Finset (Word α))
    (hExt : SampleExtends C.base.base.base.base.base.base.startWitness.base.sample K)
    (hPos : PositiveForLanguage K G.StringLanguage) :
    (A K).finiteRefinedGrammar.CoversAllOrdinaryRuleRefinements := by
  exact (C.exact_with_recovery_after K hExt hPos).refinedRuleLists_coverAll

/-- Post-threshold plan support for all listed refined rules. -/
theorem refinedRuleLists_supportedByPlan_after
    {G : WorkingMCFG N α} {obs : α → M}
    {A : CanonicalLearnerGrammarLearner G obs}
    (C : CanonicalBoundedDataRecoveryCharacteristicSample A)
    (K : Finset (Word α))
    (hExt : SampleExtends C.base.base.base.base.base.base.startWitness.base.sample K)
    (hPos : PositiveForLanguage K G.StringLanguage) :
    (A K).finiteRefinedGrammar.AllRulesSupportedByPlan
      (A K).ruleEnumerationPlan := by
  exact (C.exact_with_recovery_after K hExt hPos).refinedRuleLists_supportedByPlan

/-- Post-threshold refined-rule count bounded by the total recovery bound. -/
theorem refinedRuleCount_le_totalRecoveryBound_after
    {G : WorkingMCFG N α} {obs : α → M}
    {A : CanonicalLearnerGrammarLearner G obs}
    (C : CanonicalBoundedDataRecoveryCharacteristicSample A)
    (K : Finset (Word α))
    (hExt : SampleExtends C.base.base.base.base.base.base.startWitness.base.sample K)
    (hPos : PositiveForLanguage K G.StringLanguage) :
    (A K).refinedRuleCount ≤
      (C.recovery_after K hExt hPos).totalRecoveryBound := by
  exact (C.exact_with_recovery_after K hExt hPos).refinedRuleCount_le_totalRecoveryBound

/-- Post-threshold refined-rule count bounded by the underlying shape bound. -/
theorem refinedRuleCount_le_totalShapeBound_after
    {G : WorkingMCFG N α} {obs : α → M}
    {A : CanonicalLearnerGrammarLearner G obs}
    (C : CanonicalBoundedDataRecoveryCharacteristicSample A)
    (K : Finset (Word α))
    (hExt : SampleExtends C.base.base.base.base.base.base.startWitness.base.sample K)
    (hPos : PositiveForLanguage K G.StringLanguage) :
    (A K).refinedRuleCount ≤
      (C.recovery_after K hExt hPos).shapeProfile.totalShapeBound := by
  exact (C.exact_with_recovery_after K hExt hPos).refinedRuleCount_le_totalShapeBound

/-- Post-threshold sample-size parameter equals the current finite sample size. -/
theorem sampleSize_eq_card_after
    {G : WorkingMCFG N α} {obs : α → M}
    {A : CanonicalLearnerGrammarLearner G obs}
    (C : CanonicalBoundedDataRecoveryCharacteristicSample A)
    (K : Finset (Word α))
    (hExt : SampleExtends C.base.base.base.base.base.base.startWitness.base.sample K)
    (hPos : PositiveForLanguage K G.StringLanguage) :
    (C.recovery_after K hExt hPos).shapeProfile.parameterProfile.sampleSize =
      K.card := by
  exact (C.exact_with_recovery_after K hExt hPos).sampleSize_eq_card

/-- Post-threshold monoid-cardinality parameter equals `Fintype.card M`. -/
theorem monoidCardinality_eq_fintypeCard_after
    {G : WorkingMCFG N α} {obs : α → M}
    {A : CanonicalLearnerGrammarLearner G obs}
    (C : CanonicalBoundedDataRecoveryCharacteristicSample A)
    (K : Finset (Word α))
    (hExt : SampleExtends C.base.base.base.base.base.base.startWitness.base.sample K)
    (hPos : PositiveForLanguage K G.StringLanguage) :
    (C.recovery_after K hExt hPos).shapeProfile.parameterProfile.monoidCardinality =
      Fintype.card M := by
  exact (C.exact_with_recovery_after K hExt hPos).monoidCardinality_eq_fintypeCard

/-- The post-threshold total recovery bound carries an abstract polynomial
witness. -/
def totalRecoveryPolynomialWitness_after
    {G : WorkingMCFG N α} {obs : α → M}
    {A : CanonicalLearnerGrammarLearner G obs}
    (C : CanonicalBoundedDataRecoveryCharacteristicSample A)
    (K : Finset (Word α))
    (hExt : SampleExtends C.base.base.base.base.base.base.startWitness.base.sample K)
    (hPos : PositiveForLanguage K G.StringLanguage) :
    PolynomialBoundWitness
      (C.recovery_after K hExt hPos).totalRecoveryBound :=
  (C.recovery_after K hExt hPos).totalRecoveryPolynomialWitness

/-- Limiting distributional identification inherited from the shape-profile Gold
wrapper. -/
theorem identifiesInLimit
    {G : WorkingMCFG N α} {obs : α → M}
    {A : CanonicalLearnerGrammarLearner G obs}
    (C : CanonicalBoundedDataRecoveryCharacteristicSample A) :
    FiniteHypothesisIdentifiesGrammarInLimit A.toFiniteHypothesisLearner G := by
  exact C.base.identifiesInLimit

/-- Pointwise limiting context correctness inherited from the shape-profile Gold
wrapper. -/
theorem eventuallyCorrectContexts
    {G : WorkingMCFG N α} {obs : α → M}
    {A : CanonicalLearnerGrammarLearner G obs}
    (C : CanonicalBoundedDataRecoveryCharacteristicSample A) :
    FiniteHypothesisEventuallyCorrectContexts
      A.toFiniteHypothesisLearner G.StringLanguage := by
  exact C.base.eventuallyCorrectContexts

end CanonicalBoundedDataRecoveryCharacteristicSample

end BoundedDataRecoveryGold

end

end FIv21
