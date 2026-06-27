import LeanCfgProject.MCFG.FI_v2_1_CanonicalRuleListSpecificationExact

/-!
# FI v2.1 Lean experiment: Gold wrapper with canonical rule-list specs

This fifty-fifth layer adds the rule-list specification to the sample-indexed
canonical learner grammar Gold wrapper.

The result is still not the final canonical learner grammar construction.  It
says that once the sample-indexed learner package has the previous
characteristic-sample witness, every post-threshold sample also has an exact
canonical package whose refined rule lists cover all ordinary output-type
refinements and are supported by the canonical finite-monoid rule-enumeration
plan.
-/

namespace FIv21

universe u v w

noncomputable section

section CanonicalRuleListSpecificationGold

variable {N : Type w} {α : Type u}
variable [DecidableEq α]
variable {M : Type v} [Monoid M] [Fintype M]

/-- Characteristic-sample certificate for canonical learner grammar packages,
with the rule-list specification made explicit. -/
structure CanonicalRuleListCharacteristicSample
    {G : WorkingMCFG N α} {obs : α → M}
    (A : CanonicalLearnerGrammarLearner G obs) where
  base : CanonicalLearnerGrammarCharacteristicSample A

namespace CanonicalRuleListCharacteristicSample

/-- Any previous canonical learner grammar characteristic-sample certificate
can be viewed as a rule-list characteristic-sample certificate, because the
rule-list specification is automatic from the concrete refined-rule
enumeration carried by each package. -/
def ofCanonicalLearnerGrammarCharacteristicSample
    {G : WorkingMCFG N α} {obs : α → M}
    {A : CanonicalLearnerGrammarLearner G obs}
    (C : CanonicalLearnerGrammarCharacteristicSample A) :
    CanonicalRuleListCharacteristicSample A :=
  { base := C }

/-- Forget to the previous characteristic-sample certificate. -/
def toCanonicalLearnerGrammarCharacteristicSample
    {G : WorkingMCFG N α} {obs : α → M}
    {A : CanonicalLearnerGrammarLearner G obs}
    (C : CanonicalRuleListCharacteristicSample A) :
    CanonicalLearnerGrammarCharacteristicSample A :=
  C.base

/-- Post-threshold exact canonical package with explicit rule-list
specification. -/
def exact_with_rulelists_after
    {G : WorkingMCFG N α} {obs : α → M}
    {A : CanonicalLearnerGrammarLearner G obs}
    (C : CanonicalRuleListCharacteristicSample A)
    (K : Finset (Word α))
    (hExt : SampleExtends C.base.startWitness.base.sample K)
    (hPos : PositiveForLanguage K G.StringLanguage) :
    CanonicalLearnerGrammarExactWithRuleLists (A K) :=
  { exactPackage :=
      { exact_start :=
          (C.base.exact_with_word_semantics_after K hExt hPos).exact_start }
    ruleLists := CanonicalRuleListSpecification.ofPackage (A K) }

/-- Post-threshold exact distribution equality. -/
theorem approxDistribution_exact_after
    {G : WorkingMCFG N α} {obs : α → M}
    {A : CanonicalLearnerGrammarLearner G obs}
    (C : CanonicalRuleListCharacteristicSample A)
    (K : Finset (Word α))
    (hExt : SampleExtends C.base.startWitness.base.sample K)
    (hPos : PositiveForLanguage K G.StringLanguage)
    {d : Nat} (x : Tuple α d) :
    (A K).ApproxDistribution x = NamedDistribution G.StringLanguage x := by
  exact (C.exact_with_rulelists_after K hExt hPos).approxDistribution_exact x

/-- Post-threshold target-side start derivation witness for a sampled word. -/
theorem sample_word_start_derives_after
    {G : WorkingMCFG N α} {obs : α → M}
    {A : CanonicalLearnerGrammarLearner G obs}
    (C : CanonicalRuleListCharacteristicSample A)
    (K : Finset (Word α))
    (hExt : SampleExtends C.base.startWitness.base.sample K)
    (hPos : PositiveForLanguage K G.StringLanguage)
    (w : Word α) (hw : w ∈ K) :
    ∃ h : 1 = G.arity G.start,
      DerivesTuple G G.start (castTuple h (singletonTuple w)) := by
  exact (C.exact_with_rulelists_after K hExt hPos).sample_word_start_derives w hw

/-- Post-threshold learner-side generation of a sampled word. -/
theorem sample_word_generated_by_learner_after
    {G : WorkingMCFG N α} {obs : α → M}
    {A : CanonicalLearnerGrammarLearner G obs}
    (C : CanonicalRuleListCharacteristicSample A)
    (K : Finset (Word α))
    (hExt : SampleExtends C.base.startWitness.base.sample K)
    (hPos : PositiveForLanguage K G.StringLanguage)
    (w : Word α) (hw : w ∈ K) :
    w ∈ (A K).wordLanguage := by
  exact (C.exact_with_rulelists_after K hExt hPos).sample_word_generated_by_learner w hw

/-- Post-threshold rule-list coverage. -/
theorem refinedRuleLists_coverAll_after
    {G : WorkingMCFG N α} {obs : α → M}
    {A : CanonicalLearnerGrammarLearner G obs}
    (C : CanonicalRuleListCharacteristicSample A)
    (K : Finset (Word α))
    (hExt : SampleExtends C.base.startWitness.base.sample K)
    (hPos : PositiveForLanguage K G.StringLanguage) :
    (A K).finiteRefinedGrammar.CoversAllOrdinaryRuleRefinements := by
  exact (C.exact_with_rulelists_after K hExt hPos).refinedRuleLists_coverAll

/-- Post-threshold support of all listed refined rules by the canonical finite
plan. -/
theorem refinedRuleLists_supportedByPlan_after
    {G : WorkingMCFG N α} {obs : α → M}
    {A : CanonicalLearnerGrammarLearner G obs}
    (C : CanonicalRuleListCharacteristicSample A)
    (K : Finset (Word α))
    (hExt : SampleExtends C.base.startWitness.base.sample K)
    (hPos : PositiveForLanguage K G.StringLanguage) :
    (A K).finiteRefinedGrammar.AllRulesSupportedByPlan
      (A K).ruleEnumerationPlan := by
  exact (C.exact_with_rulelists_after K hExt hPos).refinedRuleLists_supportedByPlan

/-- Limiting distributional identification inherited from the previous
canonical learner grammar Gold wrapper. -/
theorem identifiesInLimit
    {G : WorkingMCFG N α} {obs : α → M}
    {A : CanonicalLearnerGrammarLearner G obs}
    (C : CanonicalRuleListCharacteristicSample A) :
    FiniteHypothesisIdentifiesGrammarInLimit A.toFiniteHypothesisLearner G := by
  exact C.base.identifiesInLimit

/-- Pointwise limiting context correctness inherited from the previous wrapper. -/
theorem eventuallyCorrectContexts
    {G : WorkingMCFG N α} {obs : α → M}
    {A : CanonicalLearnerGrammarLearner G obs}
    (C : CanonicalRuleListCharacteristicSample A) :
    FiniteHypothesisEventuallyCorrectContexts
      A.toFiniteHypothesisLearner G.StringLanguage := by
  exact C.base.eventuallyCorrectContexts

end CanonicalRuleListCharacteristicSample

end CanonicalRuleListSpecificationGold

end

end FIv21
