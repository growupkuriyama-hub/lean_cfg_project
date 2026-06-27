import LeanCfgProject.MCFG.FI_v2_1_MainTheoremExact

/-!
# FI v2.1 Lean experiment: main-theorem Gold summary

This seventy-ninth layer gives a compact theorem-style summary of the current
formalization frontier.  It packages the existing presentation-relative
characteristic-sample certificate into a single conservative statement: once
such a certificate is supplied, the sample-indexed canonical learner identifies
the target grammar in the current distributional Gold sense, and every
post-threshold positive sample has the exact presentation-recovery package.
-/

namespace FIv21

universe u v w

noncomputable section

section MainTheoremGold

variable {N : Type w} {α : Type u}
variable [DecidableEq α]
variable {M : Type v} [Monoid M] [Fintype M]

/-- Final conservative theorem-style certificate at the current frontier.

This is intentionally a wrapper around the already checked presentation-recovery
certificate.  It should be read as a *main theorem interface*, not as the yet
missing construction of that certificate. -/
structure FixedMonoidMCFGLearningGoldTheorem
    (G : WorkingMCFG N α) (obs : α → M) where
  package : FixedMonoidMCFGLearningMainPackage G obs

namespace FixedMonoidMCFGLearningGoldTheorem

/-- The sample-indexed canonical learner. -/
def learner
    {G : WorkingMCFG N α} {obs : α → M}
    (T : FixedMonoidMCFGLearningGoldTheorem G obs) :
    CanonicalLearnerGrammarLearner G obs :=
  T.package.learner

/-- The finite characteristic sample displayed by the theorem package. -/
def characteristicSample
    {G : WorkingMCFG N α} {obs : α → M}
    (T : FixedMonoidMCFGLearningGoldTheorem G obs) :
    Finset (Word α) :=
  T.package.characteristicSample

/-- The finite-hypothesis learner underlying the canonical learner. -/
def toFiniteHypothesisLearner
    {G : WorkingMCFG N α} {obs : α → M}
    (T : FixedMonoidMCFGLearningGoldTheorem G obs) :
    FiniteHypothesisLearner α :=
  T.package.toFiniteHypothesisLearner

/-- Main conservative Gold-style identification statement. -/
theorem identifiesInLimit
    {G : WorkingMCFG N α} {obs : α → M}
    (T : FixedMonoidMCFGLearningGoldTheorem G obs) :
    FiniteHypothesisIdentifiesGrammarInLimit T.package.learner.toFiniteHypothesisLearner G := by
  exact T.package.identifiesInLimit

/-- Eventual correctness of named-context distributions. -/
theorem eventuallyCorrectContexts
    {G : WorkingMCFG N α} {obs : α → M}
    (T : FixedMonoidMCFGLearningGoldTheorem G obs) :
    FiniteHypothesisEventuallyCorrectContexts
      T.package.learner.toFiniteHypothesisLearner G.StringLanguage := by
  exact T.package.eventuallyCorrectContexts

/-- Produce the post-threshold exactness wrapper from extension and positivity
of a finite sample. -/
def postThresholdSample
    {G : WorkingMCFG N α} {obs : α → M}
    (T : FixedMonoidMCFGLearningGoldTheorem G obs)
    (K : Finset (Word α))
    (hExt : SampleExtends T.characteristicSample K)
    (hPos : PositiveForLanguage K G.StringLanguage) :
    FixedMonoidMCFGLearningPostThresholdSample T.package K :=
  { extends := hExt
    positive := hPos }

/-- Post-threshold exact distribution equality, theorem-style form. -/
theorem approxDistribution_exact_after
    {G : WorkingMCFG N α} {obs : α → M}
    (T : FixedMonoidMCFGLearningGoldTheorem G obs)
    (K : Finset (Word α))
    (hExt : SampleExtends T.characteristicSample K)
    (hPos : PositiveForLanguage K G.StringLanguage)
    {d : Nat} (x : Tuple α d) :
    (T.learner K).ApproxDistribution x = NamedDistribution G.StringLanguage x := by
  exact (T.postThresholdSample K hExt hPos).approxDistribution_exact x

/-- Post-threshold learner-side generation of sampled words, theorem-style form. -/
theorem sample_word_generated_by_learner_after
    {G : WorkingMCFG N α} {obs : α → M}
    (T : FixedMonoidMCFGLearningGoldTheorem G obs)
    (K : Finset (Word α))
    (hExt : SampleExtends T.characteristicSample K)
    (hPos : PositiveForLanguage K G.StringLanguage)
    (w : Word α) (hw : w ∈ K) :
    w ∈ (T.learner K).wordLanguage := by
  exact (T.postThresholdSample K hExt hPos).sample_word_generated_by_learner w hw

/-- Post-threshold target-side start derivation of sampled words, theorem-style
form. -/
theorem sample_word_start_derives_after
    {G : WorkingMCFG N α} {obs : α → M}
    (T : FixedMonoidMCFGLearningGoldTheorem G obs)
    (K : Finset (Word α))
    (hExt : SampleExtends T.characteristicSample K)
    (hPos : PositiveForLanguage K G.StringLanguage)
    (w : Word α) (hw : w ∈ K) :
    ∃ h : 1 = G.arity G.start,
      DerivesTuple G G.start (castTuple h (singletonTuple w)) := by
  exact (T.postThresholdSample K hExt hPos).sample_word_start_derives w hw

/-- Post-threshold refined-rule coverage, theorem-style form. -/
theorem refinedRuleLists_coverAll_after
    {G : WorkingMCFG N α} {obs : α → M}
    (T : FixedMonoidMCFGLearningGoldTheorem G obs)
    (K : Finset (Word α))
    (hExt : SampleExtends T.characteristicSample K)
    (hPos : PositiveForLanguage K G.StringLanguage) :
    (T.learner K).finiteRefinedGrammar.CoversAllOrdinaryRuleRefinements := by
  exact (T.postThresholdSample K hExt hPos).refinedRuleLists_coverAll

/-- Post-threshold refined-rule count bound, theorem-style form. -/
theorem refinedRuleCount_le_totalPresentationBound_after
    {G : WorkingMCFG N α} {obs : α → M}
    (T : FixedMonoidMCFGLearningGoldTheorem G obs)
    (K : Finset (Word α))
    (hExt : SampleExtends T.characteristicSample K)
    (hPos : PositiveForLanguage K G.StringLanguage) :
    (T.learner K).refinedRuleCount ≤
      ((T.postThresholdSample K hExt hPos).exactWithPresentation).presentationProfile.totalPresentationBound := by
  exact (T.postThresholdSample K hExt hPos).refinedRuleCount_le_totalPresentationBound

end FixedMonoidMCFGLearningGoldTheorem

end MainTheoremGold

end

end FIv21
