import LeanCfgProject.MCFG.FI_v2_1_CanonicalRuleListCountingExact

/-!
# FI v2.1 Lean experiment: Gold wrapper with rule-list counting summaries

This fifty-eighth layer adds the rule-counting summary to the canonical
rule-list Gold wrapper.

The theorem does not prove asymptotic complexity bounds.  It says that after
the characteristic sample threshold, the sample-indexed canonical learner
package is exact and carries explicit finite rule-list counts in addition to
coverage and finite-plan support.  Later files can refine this into actual
upper bounds once concrete list-generation code is introduced.
-/

namespace FIv21

universe u v w

noncomputable section

section CanonicalRuleListCountingGold

variable {N : Type w} {α : Type u}
variable [DecidableEq α]
variable {M : Type v} [Monoid M] [Fintype M]

/-- Characteristic-sample certificate with explicit rule-list counting
summaries for every post-threshold canonical learner package. -/
structure CanonicalRuleListCountingCharacteristicSample
    {G : WorkingMCFG N α} {obs : α → M}
    (A : CanonicalLearnerGrammarLearner G obs) where
  base : CanonicalRuleListCharacteristicSample A

namespace CanonicalRuleListCountingCharacteristicSample

/-- Any rule-list characteristic-sample certificate can be viewed as carrying
counting summaries, because the counts are definitional for the listed finite
rules. -/
def ofCanonicalRuleListCharacteristicSample
    {G : WorkingMCFG N α} {obs : α → M}
    {A : CanonicalLearnerGrammarLearner G obs}
    (C : CanonicalRuleListCharacteristicSample A) :
    CanonicalRuleListCountingCharacteristicSample A :=
  { base := C }

/-- Forget to the previous rule-list characteristic-sample certificate. -/
def toCanonicalRuleListCharacteristicSample
    {G : WorkingMCFG N α} {obs : α → M}
    {A : CanonicalLearnerGrammarLearner G obs}
    (C : CanonicalRuleListCountingCharacteristicSample A) :
    CanonicalRuleListCharacteristicSample A :=
  C.base

/-- Post-threshold exact package with rule-list coverage, support, and counts. -/
def exact_with_counts_after
    {G : WorkingMCFG N α} {obs : α → M}
    {A : CanonicalLearnerGrammarLearner G obs}
    (C : CanonicalRuleListCountingCharacteristicSample A)
    (K : Finset (Word α))
    (hExt : SampleExtends C.base.base.startWitness.base.sample K)
    (hPos : PositiveForLanguage K G.StringLanguage) :
    CanonicalLearnerGrammarExactWithCounts (A K) :=
  CanonicalLearnerGrammarExactWithCounts.ofExactWithRuleLists
    (C.base.exact_with_rulelists_after K hExt hPos)

/-- Post-threshold exact distribution equality. -/
theorem approxDistribution_exact_after
    {G : WorkingMCFG N α} {obs : α → M}
    {A : CanonicalLearnerGrammarLearner G obs}
    (C : CanonicalRuleListCountingCharacteristicSample A)
    (K : Finset (Word α))
    (hExt : SampleExtends C.base.base.startWitness.base.sample K)
    (hPos : PositiveForLanguage K G.StringLanguage)
    {d : Nat} (x : Tuple α d) :
    (A K).ApproxDistribution x = NamedDistribution G.StringLanguage x := by
  exact (C.exact_with_counts_after K hExt hPos).approxDistribution_exact x

/-- Post-threshold learner-side generation of a sampled word. -/
theorem sample_word_generated_by_learner_after
    {G : WorkingMCFG N α} {obs : α → M}
    {A : CanonicalLearnerGrammarLearner G obs}
    (C : CanonicalRuleListCountingCharacteristicSample A)
    (K : Finset (Word α))
    (hExt : SampleExtends C.base.base.startWitness.base.sample K)
    (hPos : PositiveForLanguage K G.StringLanguage)
    (w : Word α) (hw : w ∈ K) :
    w ∈ (A K).wordLanguage := by
  exact (C.exact_with_counts_after K hExt hPos).sample_word_generated_by_learner w hw

/-- Post-threshold rule-list coverage. -/
theorem refinedRuleLists_coverAll_after
    {G : WorkingMCFG N α} {obs : α → M}
    {A : CanonicalLearnerGrammarLearner G obs}
    (C : CanonicalRuleListCountingCharacteristicSample A)
    (K : Finset (Word α))
    (hExt : SampleExtends C.base.base.startWitness.base.sample K)
    (hPos : PositiveForLanguage K G.StringLanguage) :
    (A K).finiteRefinedGrammar.CoversAllOrdinaryRuleRefinements := by
  exact (C.exact_with_counts_after K hExt hPos).refinedRuleLists_coverAll

/-- Post-threshold support of all listed refined rules by the canonical finite
plan. -/
theorem refinedRuleLists_supportedByPlan_after
    {G : WorkingMCFG N α} {obs : α → M}
    {A : CanonicalLearnerGrammarLearner G obs}
    (C : CanonicalRuleListCountingCharacteristicSample A)
    (K : Finset (Word α))
    (hExt : SampleExtends C.base.base.startWitness.base.sample K)
    (hPos : PositiveForLanguage K G.StringLanguage) :
    (A K).finiteRefinedGrammar.AllRulesSupportedByPlan
      (A K).ruleEnumerationPlan := by
  exact (C.exact_with_counts_after K hExt hPos).refinedRuleLists_supportedByPlan

/-- Post-threshold refined terminal-rule count is the listed terminal-rule
length. -/
theorem refinedTerminalRuleCount_eq_length_after
    {G : WorkingMCFG N α} {obs : α → M}
    {A : CanonicalLearnerGrammarLearner G obs}
    (C : CanonicalRuleListCountingCharacteristicSample A)
    (K : Finset (Word α))
    (hExt : SampleExtends C.base.base.startWitness.base.sample K)
    (hPos : PositiveForLanguage K G.StringLanguage) :
    (A K).refinedTerminalRuleCount =
      (A K).finiteRefinedGrammar.terminalRules.length := by
  exact (C.exact_with_counts_after K hExt hPos).refinedTerminalRuleCount_eq_length

/-- Post-threshold refined binary-rule count is the listed binary-rule length. -/
theorem refinedBinaryRuleCount_eq_length_after
    {G : WorkingMCFG N α} {obs : α → M}
    {A : CanonicalLearnerGrammarLearner G obs}
    (C : CanonicalRuleListCountingCharacteristicSample A)
    (K : Finset (Word α))
    (hExt : SampleExtends C.base.base.startWitness.base.sample K)
    (hPos : PositiveForLanguage K G.StringLanguage) :
    (A K).refinedBinaryRuleCount =
      (A K).finiteRefinedGrammar.binaryRules.length := by
  exact (C.exact_with_counts_after K hExt hPos).refinedBinaryRuleCount_eq_length

/-- Post-threshold refined start-rule count is the listed start-rule length. -/
theorem refinedStartRuleCount_eq_length_after
    {G : WorkingMCFG N α} {obs : α → M}
    {A : CanonicalLearnerGrammarLearner G obs}
    (C : CanonicalRuleListCountingCharacteristicSample A)
    (K : Finset (Word α))
    (hExt : SampleExtends C.base.base.startWitness.base.sample K)
    (hPos : PositiveForLanguage K G.StringLanguage) :
    (A K).refinedStartRuleCount =
      (A K).finiteRefinedGrammar.startRules.length := by
  exact (C.exact_with_counts_after K hExt hPos).refinedStartRuleCount_eq_length

/-- Post-threshold total refined-rule count is the sum of terminal, binary, and
start refined-rule counts. -/
theorem refinedRuleCount_eq_sum_after
    {G : WorkingMCFG N α} {obs : α → M}
    {A : CanonicalLearnerGrammarLearner G obs}
    (C : CanonicalRuleListCountingCharacteristicSample A)
    (K : Finset (Word α))
    (hExt : SampleExtends C.base.base.startWitness.base.sample K)
    (hPos : PositiveForLanguage K G.StringLanguage) :
    (A K).refinedRuleCount =
      (A K).refinedTerminalRuleCount +
      (A K).refinedBinaryRuleCount +
      (A K).refinedStartRuleCount := by
  exact (C.exact_with_counts_after K hExt hPos).refinedRuleCount_eq_sum

/-- Limiting distributional identification inherited from the rule-list Gold
wrapper. -/
theorem identifiesInLimit
    {G : WorkingMCFG N α} {obs : α → M}
    {A : CanonicalLearnerGrammarLearner G obs}
    (C : CanonicalRuleListCountingCharacteristicSample A) :
    FiniteHypothesisIdentifiesGrammarInLimit A.toFiniteHypothesisLearner G := by
  exact C.base.identifiesInLimit

/-- Pointwise limiting context correctness inherited from the rule-list Gold
wrapper. -/
theorem eventuallyCorrectContexts
    {G : WorkingMCFG N α} {obs : α → M}
    {A : CanonicalLearnerGrammarLearner G obs}
    (C : CanonicalRuleListCountingCharacteristicSample A) :
    FiniteHypothesisEventuallyCorrectContexts
      A.toFiniteHypothesisLearner G.StringLanguage := by
  exact C.base.eventuallyCorrectContexts

end CanonicalRuleListCountingCharacteristicSample

end CanonicalRuleListCountingGold

end

end FIv21
