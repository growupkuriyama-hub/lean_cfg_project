import LeanCfgProject.MCFG.FI_v2_1_CanonicalRuleListCounting

/-!
# FI v2.1 Lean experiment: exact canonical packages with counting summaries

This fifty-seventh layer combines exact canonical learner grammar packages with
both the rule-list specification and the elementary rule-counting summary.

The exactness statements are inherited from the previous rule-list exact layer;
the new content is that the same exact package exposes stable count names for
ordinary and refined rule lists.  This is a safe preparation for later
complexity and bounded-data layers.
-/

namespace FIv21

universe u v w

noncomputable section

section CanonicalRuleListCountingExact

variable {N : Type w} {α : Type u}
variable [DecidableEq α]
variable {M : Type v} [Monoid M] [Fintype M]

/-- Exact canonical learner grammar package together with a rule-list counting
summary. -/
structure CanonicalLearnerGrammarExactWithCounts
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (P : CanonicalLearnerGrammarPackage G obs K) where
  exactWithRuleLists : CanonicalLearnerGrammarExactWithRuleLists P
  counts : CanonicalRuleListCountingSpecification P

namespace CanonicalLearnerGrammarExactWithCounts

/-- Any exact package with explicit rule lists automatically carries the
counting summary. -/
def ofExactWithRuleLists
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {P : CanonicalLearnerGrammarPackage G obs K}
    (C : CanonicalLearnerGrammarExactWithRuleLists P) :
    CanonicalLearnerGrammarExactWithCounts P :=
  { exactWithRuleLists := C
    counts := CanonicalRuleListCountingSpecification.ofPackage P }

/-- Any exact canonical package automatically carries both rule-list and count
summaries. -/
def ofExactPackage
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {P : CanonicalLearnerGrammarPackage G obs K}
    (C : CanonicalLearnerGrammarExactForGrammar P) :
    CanonicalLearnerGrammarExactWithCounts P :=
  ofExactWithRuleLists
    (CanonicalLearnerGrammarExactWithRuleLists.ofExactPackage C)

/-- Forget to the exact-with-rule-lists certificate. -/
def toExactWithRuleLists
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {P : CanonicalLearnerGrammarPackage G obs K}
    (C : CanonicalLearnerGrammarExactWithCounts P) :
    CanonicalLearnerGrammarExactWithRuleLists P :=
  C.exactWithRuleLists

/-- Forget to the previous exact package. -/
def toExactPackage
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {P : CanonicalLearnerGrammarPackage G obs K}
    (C : CanonicalLearnerGrammarExactWithCounts P) :
    CanonicalLearnerGrammarExactForGrammar P :=
  C.exactWithRuleLists.toExactPackage

/-- Exact equality of package-level approximate distributions and target
named-context distributions. -/
theorem approxDistribution_exact
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {P : CanonicalLearnerGrammarPackage G obs K}
    (C : CanonicalLearnerGrammarExactWithCounts P)
    {d : Nat} (x : Tuple α d) :
    P.ApproxDistribution x = NamedDistribution G.StringLanguage x := by
  exact C.exactWithRuleLists.approxDistribution_exact x

/-- Target-side start derivation witness for a sampled word. -/
theorem sample_word_start_derives
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {P : CanonicalLearnerGrammarPackage G obs K}
    (C : CanonicalLearnerGrammarExactWithCounts P)
    (w : Word α) (hw : w ∈ K) :
    ∃ h : 1 = G.arity G.start,
      DerivesTuple G G.start (castTuple h (singletonTuple w)) := by
  exact C.exactWithRuleLists.sample_word_start_derives w hw

/-- Learner-side generation of a sampled word. -/
theorem sample_word_generated_by_learner
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {P : CanonicalLearnerGrammarPackage G obs K}
    (C : CanonicalLearnerGrammarExactWithCounts P)
    (w : Word α) (hw : w ∈ K) :
    w ∈ P.wordLanguage := by
  exact C.exactWithRuleLists.sample_word_generated_by_learner w hw

/-- Rule-list coverage. -/
theorem refinedRuleLists_coverAll
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {P : CanonicalLearnerGrammarPackage G obs K}
    (C : CanonicalLearnerGrammarExactWithCounts P) :
    P.finiteRefinedGrammar.CoversAllOrdinaryRuleRefinements := by
  exact C.counts.refinedRuleLists_coverAll

/-- Rule-list plan support. -/
theorem refinedRuleLists_supportedByPlan
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {P : CanonicalLearnerGrammarPackage G obs K}
    (C : CanonicalLearnerGrammarExactWithCounts P) :
    P.finiteRefinedGrammar.AllRulesSupportedByPlan P.ruleEnumerationPlan := by
  exact C.counts.refinedRuleLists_supportedByPlan

/-- Refined terminal-rule count is the terminal-list length. -/
theorem refinedTerminalRuleCount_eq_length
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {P : CanonicalLearnerGrammarPackage G obs K}
    (C : CanonicalLearnerGrammarExactWithCounts P) :
    P.refinedTerminalRuleCount = P.finiteRefinedGrammar.terminalRules.length := by
  exact C.counts.terminal_count_eq_length

/-- Refined binary-rule count is the binary-list length. -/
theorem refinedBinaryRuleCount_eq_length
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {P : CanonicalLearnerGrammarPackage G obs K}
    (C : CanonicalLearnerGrammarExactWithCounts P) :
    P.refinedBinaryRuleCount = P.finiteRefinedGrammar.binaryRules.length := by
  exact C.counts.binary_count_eq_length

/-- Refined start-rule count is the start-list length. -/
theorem refinedStartRuleCount_eq_length
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {P : CanonicalLearnerGrammarPackage G obs K}
    (C : CanonicalLearnerGrammarExactWithCounts P) :
    P.refinedStartRuleCount = P.finiteRefinedGrammar.startRules.length := by
  exact C.counts.start_count_eq_length

/-- Total refined-rule count is the sum of the three refined-rule counts. -/
theorem refinedRuleCount_eq_sum
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {P : CanonicalLearnerGrammarPackage G obs K}
    (C : CanonicalLearnerGrammarExactWithCounts P) :
    P.refinedRuleCount =
      P.refinedTerminalRuleCount +
      P.refinedBinaryRuleCount +
      P.refinedStartRuleCount := by
  exact C.counts.total_count_eq_sum

end CanonicalLearnerGrammarExactWithCounts

end CanonicalRuleListCountingExact

end

end FIv21
