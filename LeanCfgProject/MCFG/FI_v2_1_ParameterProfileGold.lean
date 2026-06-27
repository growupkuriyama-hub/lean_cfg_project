import LeanCfgProject.MCFG.FI_v2_1_ParameterProfileExact

/-!
# FI v2.1 Lean experiment: Gold wrapper with parameter profiles

This sixty-seventh layer attaches parameter profiles to the post-threshold
canonical learner grammar packages in the Gold-style wrapper.

As before, the limiting identification theorem is inherited from the existing
semantic certificates.  The new contribution is a stable API saying that after
the characteristic sample threshold, the learner packages also expose named
size parameters such as sample size, finite monoid cardinality, and a total
enumeration bound.
-/

namespace FIv21

universe u v w

noncomputable section

section ParameterProfileGold

variable {N : Type w} {α : Type u}
variable [DecidableEq α]
variable {M : Type v} [Monoid M] [Fintype M]

/-- Characteristic-sample certificate whose post-threshold canonical packages
also carry parameter profiles. -/
structure CanonicalParameterProfileCharacteristicSample
    {G : WorkingMCFG N α} {obs : α → M}
    (A : CanonicalLearnerGrammarLearner G obs) where
  base : CanonicalPolynomialBoundCharacteristicSample A
  profile_after :
    ∀ (K : Finset (Word α)),
      SampleExtends base.base.base.base.base.startWitness.base.sample K →
      PositiveForLanguage K G.StringLanguage →
      CanonicalParameterProfile (A K)

namespace CanonicalParameterProfileCharacteristicSample

/-- Any polynomial-bound characteristic-sample certificate carries tautological
parameter profiles after the threshold. -/
def ofPolynomialBoundCharacteristicSample
    {G : WorkingMCFG N α} {obs : α → M}
    {A : CanonicalLearnerGrammarLearner G obs}
    (C : CanonicalPolynomialBoundCharacteristicSample A) :
    CanonicalParameterProfileCharacteristicSample A :=
  { base := C
    profile_after := by
      intro K hExt hPos
      exact CanonicalParameterProfile.trivialForPackage (A K) }

/-- Forget to the polynomial-bound characteristic-sample certificate. -/
def toPolynomialBoundCharacteristicSample
    {G : WorkingMCFG N α} {obs : α → M}
    {A : CanonicalLearnerGrammarLearner G obs}
    (C : CanonicalParameterProfileCharacteristicSample A) :
    CanonicalPolynomialBoundCharacteristicSample A :=
  C.base

/-- Post-threshold exact package with a parameter profile. -/
def exact_with_parameter_profile_after
    {G : WorkingMCFG N α} {obs : α → M}
    {A : CanonicalLearnerGrammarLearner G obs}
    (C : CanonicalParameterProfileCharacteristicSample A)
    (K : Finset (Word α))
    (hExt : SampleExtends C.base.base.base.base.base.startWitness.base.sample K)
    (hPos : PositiveForLanguage K G.StringLanguage) :
    CanonicalLearnerGrammarExactWithParameterProfile (A K) :=
  { exactWithPolynomialBounds := C.base.exact_with_polynomial_bounds_after K hExt hPos
    profile := C.profile_after K hExt hPos }

/-- Post-threshold exact distribution equality. -/
theorem approxDistribution_exact_after
    {G : WorkingMCFG N α} {obs : α → M}
    {A : CanonicalLearnerGrammarLearner G obs}
    (C : CanonicalParameterProfileCharacteristicSample A)
    (K : Finset (Word α))
    (hExt : SampleExtends C.base.base.base.base.base.startWitness.base.sample K)
    (hPos : PositiveForLanguage K G.StringLanguage)
    {d : Nat} (x : Tuple α d) :
    (A K).ApproxDistribution x = NamedDistribution G.StringLanguage x := by
  exact (C.exact_with_parameter_profile_after K hExt hPos).approxDistribution_exact x

/-- Post-threshold learner-side generation of a sampled word. -/
theorem sample_word_generated_by_learner_after
    {G : WorkingMCFG N α} {obs : α → M}
    {A : CanonicalLearnerGrammarLearner G obs}
    (C : CanonicalParameterProfileCharacteristicSample A)
    (K : Finset (Word α))
    (hExt : SampleExtends C.base.base.base.base.base.startWitness.base.sample K)
    (hPos : PositiveForLanguage K G.StringLanguage)
    (w : Word α) (hw : w ∈ K) :
    w ∈ (A K).wordLanguage := by
  exact (C.exact_with_parameter_profile_after K hExt hPos).sample_word_generated_by_learner w hw

/-- Post-threshold target-side start derivation witness for a sampled word. -/
theorem sample_word_start_derives_after
    {G : WorkingMCFG N α} {obs : α → M}
    {A : CanonicalLearnerGrammarLearner G obs}
    (C : CanonicalParameterProfileCharacteristicSample A)
    (K : Finset (Word α))
    (hExt : SampleExtends C.base.base.base.base.base.startWitness.base.sample K)
    (hPos : PositiveForLanguage K G.StringLanguage)
    (w : Word α) (hw : w ∈ K) :
    ∃ h : 1 = G.arity G.start,
      DerivesTuple G G.start (castTuple h (singletonTuple w)) := by
  exact (C.exact_with_parameter_profile_after K hExt hPos).sample_word_start_derives w hw

/-- Post-threshold rule-list coverage. -/
theorem refinedRuleLists_coverAll_after
    {G : WorkingMCFG N α} {obs : α → M}
    {A : CanonicalLearnerGrammarLearner G obs}
    (C : CanonicalParameterProfileCharacteristicSample A)
    (K : Finset (Word α))
    (hExt : SampleExtends C.base.base.base.base.base.startWitness.base.sample K)
    (hPos : PositiveForLanguage K G.StringLanguage) :
    (A K).finiteRefinedGrammar.CoversAllOrdinaryRuleRefinements := by
  exact (C.exact_with_parameter_profile_after K hExt hPos).refinedRuleLists_coverAll

/-- Post-threshold plan support for all listed refined rules. -/
theorem refinedRuleLists_supportedByPlan_after
    {G : WorkingMCFG N α} {obs : α → M}
    {A : CanonicalLearnerGrammarLearner G obs}
    (C : CanonicalParameterProfileCharacteristicSample A)
    (K : Finset (Word α))
    (hExt : SampleExtends C.base.base.base.base.base.startWitness.base.sample K)
    (hPos : PositiveForLanguage K G.StringLanguage) :
    (A K).finiteRefinedGrammar.AllRulesSupportedByPlan
      (A K).ruleEnumerationPlan := by
  exact (C.exact_with_parameter_profile_after K hExt hPos).refinedRuleLists_supportedByPlan

/-- Post-threshold refined-rule count bounded by the displayed profile bound. -/
theorem refinedRuleCount_le_totalEnumerationBound_after
    {G : WorkingMCFG N α} {obs : α → M}
    {A : CanonicalLearnerGrammarLearner G obs}
    (C : CanonicalParameterProfileCharacteristicSample A)
    (K : Finset (Word α))
    (hExt : SampleExtends C.base.base.base.base.base.startWitness.base.sample K)
    (hPos : PositiveForLanguage K G.StringLanguage) :
    (A K).refinedRuleCount ≤
      (C.profile_after K hExt hPos).totalEnumerationBound := by
  exact (C.exact_with_parameter_profile_after K hExt hPos).refinedRuleCount_le_totalEnumerationBound

/-- Post-threshold sample-size parameter equals the current finite sample size. -/
theorem sampleSize_eq_card_after
    {G : WorkingMCFG N α} {obs : α → M}
    {A : CanonicalLearnerGrammarLearner G obs}
    (C : CanonicalParameterProfileCharacteristicSample A)
    (K : Finset (Word α))
    (hExt : SampleExtends C.base.base.base.base.base.startWitness.base.sample K)
    (hPos : PositiveForLanguage K G.StringLanguage) :
    (C.profile_after K hExt hPos).sampleSize = K.card := by
  exact (C.profile_after K hExt hPos).sampleSize_eq_card

/-- Post-threshold monoid-cardinality parameter equals `Fintype.card M`. -/
theorem monoidCardinality_eq_fintypeCard_after
    {G : WorkingMCFG N α} {obs : α → M}
    {A : CanonicalLearnerGrammarLearner G obs}
    (C : CanonicalParameterProfileCharacteristicSample A)
    (K : Finset (Word α))
    (hExt : SampleExtends C.base.base.base.base.base.startWitness.base.sample K)
    (hPos : PositiveForLanguage K G.StringLanguage) :
    (C.profile_after K hExt hPos).monoidCardinality = Fintype.card M := by
  exact (C.profile_after K hExt hPos).monoidCardinality_eq_fintypeCard

/-- Limiting distributional identification inherited from the polynomial-bound
Gold wrapper. -/
theorem identifiesInLimit
    {G : WorkingMCFG N α} {obs : α → M}
    {A : CanonicalLearnerGrammarLearner G obs}
    (C : CanonicalParameterProfileCharacteristicSample A) :
    FiniteHypothesisIdentifiesGrammarInLimit A.toFiniteHypothesisLearner G := by
  exact C.base.identifiesInLimit

/-- Pointwise limiting context correctness inherited from the polynomial-bound
Gold wrapper. -/
theorem eventuallyCorrectContexts
    {G : WorkingMCFG N α} {obs : α → M}
    {A : CanonicalLearnerGrammarLearner G obs}
    (C : CanonicalParameterProfileCharacteristicSample A) :
    FiniteHypothesisEventuallyCorrectContexts
      A.toFiniteHypothesisLearner G.StringLanguage := by
  exact C.base.eventuallyCorrectContexts

end CanonicalParameterProfileCharacteristicSample

end ParameterProfileGold

end

end FIv21
