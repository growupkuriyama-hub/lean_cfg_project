import LeanCfgProject.MCFG.FI_v2_1_PolynomialBoundExact

/-!
# FI v2.1 Lean experiment: Gold wrapper with polynomial-bound witnesses

This sixty-fourth layer attaches abstract polynomial-bound witnesses to the
post-threshold canonical enumeration-bound Gold wrapper.

The result remains conservative: it inherits the already checked distributional
Gold identification theorem and adds only an opaque polynomial-bound witness
interface for the finite enumeration data.
-/

namespace FIv21

universe u v w

noncomputable section

section PolynomialBoundGold

variable {N : Type w} {α : Type u}
variable [DecidableEq α]
variable {M : Type v} [Monoid M] [Fintype M]

/-- Characteristic-sample certificate whose post-threshold canonical packages
also carry abstract polynomial-bound witnesses. -/
structure CanonicalPolynomialBoundCharacteristicSample
    {G : WorkingMCFG N α} {obs : α → M}
    (A : CanonicalLearnerGrammarLearner G obs) where
  base : CanonicalEnumerationBoundCharacteristicSample A
  polynomial_after :
    ∀ (K : Finset (Word α)),
      SampleExtends base.base.base.base.startWitness.base.sample K →
      PositiveForLanguage K G.StringLanguage →
      CanonicalPolynomialBounds (A K)

namespace CanonicalPolynomialBoundCharacteristicSample

/-- Any enumeration-bound characteristic-sample certificate carries tautological
polynomial witnesses after the threshold. -/
def ofEnumerationBoundCharacteristicSample
    {G : WorkingMCFG N α} {obs : α → M}
    {A : CanonicalLearnerGrammarLearner G obs}
    (C : CanonicalEnumerationBoundCharacteristicSample A) :
    CanonicalPolynomialBoundCharacteristicSample A :=
  { base := C
    polynomial_after := by
      intro K hExt hPos
      exact CanonicalPolynomialBounds.trivialForPackage (A K) }

/-- Forget to the enumeration-bound characteristic-sample certificate. -/
def toEnumerationBoundCharacteristicSample
    {G : WorkingMCFG N α} {obs : α → M}
    {A : CanonicalLearnerGrammarLearner G obs}
    (C : CanonicalPolynomialBoundCharacteristicSample A) :
    CanonicalEnumerationBoundCharacteristicSample A :=
  C.base

/-- Post-threshold exact package with abstract polynomial-bound witnesses. -/
def exact_with_polynomial_bounds_after
    {G : WorkingMCFG N α} {obs : α → M}
    {A : CanonicalLearnerGrammarLearner G obs}
    (C : CanonicalPolynomialBoundCharacteristicSample A)
    (K : Finset (Word α))
    (hExt : SampleExtends C.base.base.base.base.startWitness.base.sample K)
    (hPos : PositiveForLanguage K G.StringLanguage) :
    CanonicalLearnerGrammarExactWithPolynomialBounds (A K) :=
  { exactWithBounds := C.base.exact_with_bounds_after K hExt hPos
    polynomialBounds := C.polynomial_after K hExt hPos }

/-- Post-threshold exact distribution equality. -/
theorem approxDistribution_exact_after
    {G : WorkingMCFG N α} {obs : α → M}
    {A : CanonicalLearnerGrammarLearner G obs}
    (C : CanonicalPolynomialBoundCharacteristicSample A)
    (K : Finset (Word α))
    (hExt : SampleExtends C.base.base.base.base.startWitness.base.sample K)
    (hPos : PositiveForLanguage K G.StringLanguage)
    {d : Nat} (x : Tuple α d) :
    (A K).ApproxDistribution x = NamedDistribution G.StringLanguage x := by
  exact (C.exact_with_polynomial_bounds_after K hExt hPos).approxDistribution_exact x

/-- Post-threshold learner-side generation of a sampled word. -/
theorem sample_word_generated_by_learner_after
    {G : WorkingMCFG N α} {obs : α → M}
    {A : CanonicalLearnerGrammarLearner G obs}
    (C : CanonicalPolynomialBoundCharacteristicSample A)
    (K : Finset (Word α))
    (hExt : SampleExtends C.base.base.base.base.startWitness.base.sample K)
    (hPos : PositiveForLanguage K G.StringLanguage)
    (w : Word α) (hw : w ∈ K) :
    w ∈ (A K).wordLanguage := by
  exact (C.exact_with_polynomial_bounds_after K hExt hPos).sample_word_generated_by_learner w hw

/-- Post-threshold target-side start derivation witness for a sampled word. -/
theorem sample_word_start_derives_after
    {G : WorkingMCFG N α} {obs : α → M}
    {A : CanonicalLearnerGrammarLearner G obs}
    (C : CanonicalPolynomialBoundCharacteristicSample A)
    (K : Finset (Word α))
    (hExt : SampleExtends C.base.base.base.base.startWitness.base.sample K)
    (hPos : PositiveForLanguage K G.StringLanguage)
    (w : Word α) (hw : w ∈ K) :
    ∃ h : 1 = G.arity G.start,
      DerivesTuple G G.start (castTuple h (singletonTuple w)) := by
  exact (C.exact_with_polynomial_bounds_after K hExt hPos).sample_word_start_derives w hw

/-- Post-threshold rule-list coverage. -/
theorem refinedRuleLists_coverAll_after
    {G : WorkingMCFG N α} {obs : α → M}
    {A : CanonicalLearnerGrammarLearner G obs}
    (C : CanonicalPolynomialBoundCharacteristicSample A)
    (K : Finset (Word α))
    (hExt : SampleExtends C.base.base.base.base.startWitness.base.sample K)
    (hPos : PositiveForLanguage K G.StringLanguage) :
    (A K).finiteRefinedGrammar.CoversAllOrdinaryRuleRefinements := by
  exact (C.exact_with_polynomial_bounds_after K hExt hPos).refinedRuleLists_coverAll

/-- Post-threshold plan support for all listed refined rules. -/
theorem refinedRuleLists_supportedByPlan_after
    {G : WorkingMCFG N α} {obs : α → M}
    {A : CanonicalLearnerGrammarLearner G obs}
    (C : CanonicalPolynomialBoundCharacteristicSample A)
    (K : Finset (Word α))
    (hExt : SampleExtends C.base.base.base.base.startWitness.base.sample K)
    (hPos : PositiveForLanguage K G.StringLanguage) :
    (A K).finiteRefinedGrammar.AllRulesSupportedByPlan
      (A K).ruleEnumerationPlan := by
  exact (C.exact_with_polynomial_bounds_after K hExt hPos).refinedRuleLists_supportedByPlan

/-- Post-threshold total refined-rule count bound with an abstract polynomial
witness attached to the bound. -/
theorem refinedRuleCount_le_polynomialBound_after
    {G : WorkingMCFG N α} {obs : α → M}
    {A : CanonicalLearnerGrammarLearner G obs}
    (C : CanonicalPolynomialBoundCharacteristicSample A)
    (K : Finset (Word α))
    (hExt : SampleExtends C.base.base.base.base.startWitness.base.sample K)
    (hPos : PositiveForLanguage K G.StringLanguage) :
    (A K).refinedRuleCount ≤
      (C.polynomial_after K hExt hPos).bounds.totalBound := by
  exact (C.exact_with_polynomial_bounds_after K hExt hPos).refinedRuleCount_le_polynomialBound

/-- The post-threshold total bound carries an abstract polynomial witness. -/
def totalPolynomialWitness_after
    {G : WorkingMCFG N α} {obs : α → M}
    {A : CanonicalLearnerGrammarLearner G obs}
    (C : CanonicalPolynomialBoundCharacteristicSample A)
    (K : Finset (Word α))
    (hExt : SampleExtends C.base.base.base.base.startWitness.base.sample K)
    (hPos : PositiveForLanguage K G.StringLanguage) :
    PolynomialBoundWitness
      ((C.polynomial_after K hExt hPos).bounds.totalBound) :=
  (C.polynomial_after K hExt hPos).totalPolynomialWitness

/-- Limiting distributional identification inherited from the enumeration-bound
Gold wrapper. -/
theorem identifiesInLimit
    {G : WorkingMCFG N α} {obs : α → M}
    {A : CanonicalLearnerGrammarLearner G obs}
    (C : CanonicalPolynomialBoundCharacteristicSample A) :
    FiniteHypothesisIdentifiesGrammarInLimit A.toFiniteHypothesisLearner G := by
  exact C.base.identifiesInLimit

/-- Pointwise limiting context correctness inherited from the enumeration-bound
Gold wrapper. -/
theorem eventuallyCorrectContexts
    {G : WorkingMCFG N α} {obs : α → M}
    {A : CanonicalLearnerGrammarLearner G obs}
    (C : CanonicalPolynomialBoundCharacteristicSample A) :
    FiniteHypothesisEventuallyCorrectContexts
      A.toFiniteHypothesisLearner G.StringLanguage := by
  exact C.base.eventuallyCorrectContexts

end CanonicalPolynomialBoundCharacteristicSample

end PolynomialBoundGold

end

end FIv21
