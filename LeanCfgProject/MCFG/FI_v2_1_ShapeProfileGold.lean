import LeanCfgProject.MCFG.FI_v2_1_ShapeProfileExact

/-!
# FI v2.1 Lean experiment: Gold wrapper with shape profiles

This seventieth layer attaches the shape-profile interface to the
post-threshold canonical learner packages in the Gold-style wrapper.

The limiting identification theorem is inherited from the parameter-profile
Gold wrapper.  The additional API says that, after the characteristic sample
threshold, the learner packages also expose placeholder shape bounds and a total
shape bound dominating the refined-rule count.
-/

namespace FIv21

universe u v w

noncomputable section

section ShapeProfileGold

variable {N : Type w} {α : Type u}
variable [DecidableEq α]
variable {M : Type v} [Monoid M] [Fintype M]

/-- Characteristic-sample certificate whose post-threshold canonical packages
also carry shape profiles. -/
structure CanonicalShapeProfileCharacteristicSample
    {G : WorkingMCFG N α} {obs : α → M}
    (A : CanonicalLearnerGrammarLearner G obs) where
  base : CanonicalParameterProfileCharacteristicSample A
  shape_after :
    ∀ (K : Finset (Word α)),
      SampleExtends base.base.base.base.base.startWitness.base.sample K →
      PositiveForLanguage K G.StringLanguage →
      CanonicalShapeProfile (A K)
  shape_parameter_agrees_after :
    ∀ (K : Finset (Word α))
      (hExt : SampleExtends base.base.base.base.base.startWitness.base.sample K)
      (hPos : PositiveForLanguage K G.StringLanguage),
      (shape_after K hExt hPos).parameterProfile =
        base.profile_after K hExt hPos

namespace CanonicalShapeProfileCharacteristicSample

/-- Any parameter-profile characteristic-sample certificate carries tautological
shape profiles after the threshold. -/
def ofParameterProfileCharacteristicSample
    {G : WorkingMCFG N α} {obs : α → M}
    {A : CanonicalLearnerGrammarLearner G obs}
    (C : CanonicalParameterProfileCharacteristicSample A) :
    CanonicalShapeProfileCharacteristicSample A :=
  { base := C
    shape_after := by
      intro K hExt hPos
      exact CanonicalShapeProfile.trivialForProfile
        (C.profile_after K hExt hPos)
    shape_parameter_agrees_after := by
      intro K hExt hPos
      rfl }

/-- Forget to the parameter-profile characteristic-sample certificate. -/
def toParameterProfileCharacteristicSample
    {G : WorkingMCFG N α} {obs : α → M}
    {A : CanonicalLearnerGrammarLearner G obs}
    (C : CanonicalShapeProfileCharacteristicSample A) :
    CanonicalParameterProfileCharacteristicSample A :=
  C.base

/-- Post-threshold exact package with a shape profile. -/
def exact_with_shape_profile_after
    {G : WorkingMCFG N α} {obs : α → M}
    {A : CanonicalLearnerGrammarLearner G obs}
    (C : CanonicalShapeProfileCharacteristicSample A)
    (K : Finset (Word α))
    (hExt : SampleExtends C.base.base.base.base.base.startWitness.base.sample K)
    (hPos : PositiveForLanguage K G.StringLanguage) :
    CanonicalLearnerGrammarExactWithShapeProfile (A K) :=
  { exactWithParameterProfile :=
      C.base.exact_with_parameter_profile_after K hExt hPos
    shapeProfile := C.shape_after K hExt hPos
    parameterProfile_agrees := C.shape_parameter_agrees_after K hExt hPos }

/-- Post-threshold exact distribution equality. -/
theorem approxDistribution_exact_after
    {G : WorkingMCFG N α} {obs : α → M}
    {A : CanonicalLearnerGrammarLearner G obs}
    (C : CanonicalShapeProfileCharacteristicSample A)
    (K : Finset (Word α))
    (hExt : SampleExtends C.base.base.base.base.base.startWitness.base.sample K)
    (hPos : PositiveForLanguage K G.StringLanguage)
    {d : Nat} (x : Tuple α d) :
    (A K).ApproxDistribution x = NamedDistribution G.StringLanguage x := by
  exact (C.exact_with_shape_profile_after K hExt hPos).approxDistribution_exact x

/-- Post-threshold learner-side generation of a sampled word. -/
theorem sample_word_generated_by_learner_after
    {G : WorkingMCFG N α} {obs : α → M}
    {A : CanonicalLearnerGrammarLearner G obs}
    (C : CanonicalShapeProfileCharacteristicSample A)
    (K : Finset (Word α))
    (hExt : SampleExtends C.base.base.base.base.base.startWitness.base.sample K)
    (hPos : PositiveForLanguage K G.StringLanguage)
    (w : Word α) (hw : w ∈ K) :
    w ∈ (A K).wordLanguage := by
  exact (C.exact_with_shape_profile_after K hExt hPos).sample_word_generated_by_learner w hw

/-- Post-threshold target-side start derivation witness for a sampled word. -/
theorem sample_word_start_derives_after
    {G : WorkingMCFG N α} {obs : α → M}
    {A : CanonicalLearnerGrammarLearner G obs}
    (C : CanonicalShapeProfileCharacteristicSample A)
    (K : Finset (Word α))
    (hExt : SampleExtends C.base.base.base.base.base.startWitness.base.sample K)
    (hPos : PositiveForLanguage K G.StringLanguage)
    (w : Word α) (hw : w ∈ K) :
    ∃ h : 1 = G.arity G.start,
      DerivesTuple G G.start (castTuple h (singletonTuple w)) := by
  exact (C.exact_with_shape_profile_after K hExt hPos).sample_word_start_derives w hw

/-- Post-threshold rule-list coverage. -/
theorem refinedRuleLists_coverAll_after
    {G : WorkingMCFG N α} {obs : α → M}
    {A : CanonicalLearnerGrammarLearner G obs}
    (C : CanonicalShapeProfileCharacteristicSample A)
    (K : Finset (Word α))
    (hExt : SampleExtends C.base.base.base.base.base.startWitness.base.sample K)
    (hPos : PositiveForLanguage K G.StringLanguage) :
    (A K).finiteRefinedGrammar.CoversAllOrdinaryRuleRefinements := by
  exact (C.exact_with_shape_profile_after K hExt hPos).refinedRuleLists_coverAll

/-- Post-threshold plan support for all listed refined rules. -/
theorem refinedRuleLists_supportedByPlan_after
    {G : WorkingMCFG N α} {obs : α → M}
    {A : CanonicalLearnerGrammarLearner G obs}
    (C : CanonicalShapeProfileCharacteristicSample A)
    (K : Finset (Word α))
    (hExt : SampleExtends C.base.base.base.base.base.startWitness.base.sample K)
    (hPos : PositiveForLanguage K G.StringLanguage) :
    (A K).finiteRefinedGrammar.AllRulesSupportedByPlan
      (A K).ruleEnumerationPlan := by
  exact (C.exact_with_shape_profile_after K hExt hPos).refinedRuleLists_supportedByPlan

/-- Post-threshold refined-rule count bounded by the total shape bound. -/
theorem refinedRuleCount_le_totalShapeBound_after
    {G : WorkingMCFG N α} {obs : α → M}
    {A : CanonicalLearnerGrammarLearner G obs}
    (C : CanonicalShapeProfileCharacteristicSample A)
    (K : Finset (Word α))
    (hExt : SampleExtends C.base.base.base.base.base.startWitness.base.sample K)
    (hPos : PositiveForLanguage K G.StringLanguage) :
    (A K).refinedRuleCount ≤
      (C.shape_after K hExt hPos).totalShapeBound := by
  exact (C.exact_with_shape_profile_after K hExt hPos).refinedRuleCount_le_totalShapeBound

/-- Post-threshold sample-size parameter equals the current finite sample size. -/
theorem sampleSize_eq_card_after
    {G : WorkingMCFG N α} {obs : α → M}
    {A : CanonicalLearnerGrammarLearner G obs}
    (C : CanonicalShapeProfileCharacteristicSample A)
    (K : Finset (Word α))
    (hExt : SampleExtends C.base.base.base.base.base.startWitness.base.sample K)
    (hPos : PositiveForLanguage K G.StringLanguage) :
    (C.shape_after K hExt hPos).parameterProfile.sampleSize = K.card := by
  exact (C.shape_after K hExt hPos).sampleSize_eq_card

/-- Post-threshold monoid-cardinality parameter equals `Fintype.card M`. -/
theorem monoidCardinality_eq_fintypeCard_after
    {G : WorkingMCFG N α} {obs : α → M}
    {A : CanonicalLearnerGrammarLearner G obs}
    (C : CanonicalShapeProfileCharacteristicSample A)
    (K : Finset (Word α))
    (hExt : SampleExtends C.base.base.base.base.base.startWitness.base.sample K)
    (hPos : PositiveForLanguage K G.StringLanguage) :
    (C.shape_after K hExt hPos).parameterProfile.monoidCardinality =
      Fintype.card M := by
  exact (C.shape_after K hExt hPos).monoidCardinality_eq_fintypeCard

/-- Limiting distributional identification inherited from the parameter-profile
Gold wrapper. -/
theorem identifiesInLimit
    {G : WorkingMCFG N α} {obs : α → M}
    {A : CanonicalLearnerGrammarLearner G obs}
    (C : CanonicalShapeProfileCharacteristicSample A) :
    FiniteHypothesisIdentifiesGrammarInLimit A.toFiniteHypothesisLearner G := by
  exact C.base.identifiesInLimit

/-- Pointwise limiting context correctness inherited from the parameter-profile
Gold wrapper. -/
theorem eventuallyCorrectContexts
    {G : WorkingMCFG N α} {obs : α → M}
    {A : CanonicalLearnerGrammarLearner G obs}
    (C : CanonicalShapeProfileCharacteristicSample A) :
    FiniteHypothesisEventuallyCorrectContexts
      A.toFiniteHypothesisLearner G.StringLanguage := by
  exact C.base.eventuallyCorrectContexts

end CanonicalShapeProfileCharacteristicSample

end ShapeProfileGold

end

end FIv21
