import LeanCfgProject.MCFG.FI_v2_1_MainTheoremInterface

/-!
# FI v2.1 Lean experiment: main-theorem exact-after interface

This seventy-eighth layer exposes the post-threshold exactness statement from
the main-theorem package.  Once a positive sample extends the displayed finite
characteristic sample, the current canonical learner package carries the
presentation-relative exact recovery certificate.
-/

namespace FIv21

universe u v w

noncomputable section

section MainTheoremExact

variable {N : Type w} {α : Type u}
variable [DecidableEq α]
variable {M : Type v} [Monoid M] [Fintype M]

/-- A post-threshold sample for the main-theorem package. -/
structure FixedMonoidMCFGLearningPostThresholdSample
    {G : WorkingMCFG N α} {obs : α → M}
    (C : FixedMonoidMCFGLearningMainPackage G obs)
    (K : Finset (Word α)) where
  extends : SampleExtends C.characteristicSample K
  positive : PositiveForLanguage K G.StringLanguage

namespace FixedMonoidMCFGLearningPostThresholdSample

/-- The exact presentation-relative package obtained after the threshold. -/
def exactWithPresentation
    {G : WorkingMCFG N α} {obs : α → M}
    {C : FixedMonoidMCFGLearningMainPackage G obs}
    {K : Finset (Word α)}
    (S : FixedMonoidMCFGLearningPostThresholdSample C K) :
    CanonicalLearnerGrammarExactWithPresentationRecovery (C.learner K) :=
  C.characteristic.exact_with_presentation_after K S.extends S.positive

/-- Exact equality of the learner approximate distribution and the target named
context distribution after the threshold. -/
theorem approxDistribution_exact
    {G : WorkingMCFG N α} {obs : α → M}
    {C : FixedMonoidMCFGLearningMainPackage G obs}
    {K : Finset (Word α)}
    (S : FixedMonoidMCFGLearningPostThresholdSample C K)
    {d : Nat} (x : Tuple α d) :
    (C.learner K).ApproxDistribution x = NamedDistribution G.StringLanguage x := by
  exact S.exactWithPresentation.approxDistribution_exact x

/-- Post-threshold learner-side generation of every sampled word. -/
theorem sample_word_generated_by_learner
    {G : WorkingMCFG N α} {obs : α → M}
    {C : FixedMonoidMCFGLearningMainPackage G obs}
    {K : Finset (Word α)}
    (S : FixedMonoidMCFGLearningPostThresholdSample C K)
    (w : Word α) (hw : w ∈ K) :
    w ∈ (C.learner K).wordLanguage := by
  exact S.exactWithPresentation.sample_word_generated_by_learner w hw

/-- Post-threshold target-side start derivation witness for every sampled word. -/
theorem sample_word_start_derives
    {G : WorkingMCFG N α} {obs : α → M}
    {C : FixedMonoidMCFGLearningMainPackage G obs}
    {K : Finset (Word α)}
    (S : FixedMonoidMCFGLearningPostThresholdSample C K)
    (w : Word α) (hw : w ∈ K) :
    ∃ h : 1 = G.arity G.start,
      DerivesTuple G G.start (castTuple h (singletonTuple w)) := by
  exact S.exactWithPresentation.sample_word_start_derives w hw

/-- Post-threshold refined-rule lists cover all ordinary output-type
refinements. -/
theorem refinedRuleLists_coverAll
    {G : WorkingMCFG N α} {obs : α → M}
    {C : FixedMonoidMCFGLearningMainPackage G obs}
    {K : Finset (Word α)}
    (S : FixedMonoidMCFGLearningPostThresholdSample C K) :
    (C.learner K).finiteRefinedGrammar.CoversAllOrdinaryRuleRefinements := by
  exact S.exactWithPresentation.refinedRuleLists_coverAll

/-- Post-threshold refined-rule lists are supported by the canonical finite
rule-enumeration plan. -/
theorem refinedRuleLists_supportedByPlan
    {G : WorkingMCFG N α} {obs : α → M}
    {C : FixedMonoidMCFGLearningMainPackage G obs}
    {K : Finset (Word α)}
    (S : FixedMonoidMCFGLearningPostThresholdSample C K) :
    (C.learner K).finiteRefinedGrammar.AllRulesSupportedByPlan
      (C.learner K).ruleEnumerationPlan := by
  exact S.exactWithPresentation.refinedRuleLists_supportedByPlan

/-- Post-threshold refined-rule count bounded by the presentation profile. -/
theorem refinedRuleCount_le_totalPresentationBound
    {G : WorkingMCFG N α} {obs : α → M}
    {C : FixedMonoidMCFGLearningMainPackage G obs}
    {K : Finset (Word α)}
    (S : FixedMonoidMCFGLearningPostThresholdSample C K) :
    (C.learner K).refinedRuleCount ≤
      S.exactWithPresentation.presentationProfile.totalPresentationBound := by
  exact S.exactWithPresentation.refinedRuleCount_le_totalPresentationBound

/-- The post-threshold presentation bound has an abstract polynomial witness. -/
def totalPresentationPolynomialWitness
    {G : WorkingMCFG N α} {obs : α → M}
    {C : FixedMonoidMCFGLearningMainPackage G obs}
    {K : Finset (Word α)}
    (S : FixedMonoidMCFGLearningPostThresholdSample C K) :
    PolynomialBoundWitness
      S.exactWithPresentation.presentationProfile.totalPresentationBound :=
  S.exactWithPresentation.totalPresentationPolynomialWitness

end FixedMonoidMCFGLearningPostThresholdSample

end MainTheoremExact

end

end FIv21
