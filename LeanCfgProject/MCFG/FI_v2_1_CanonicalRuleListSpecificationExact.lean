import LeanCfgProject.MCFG.FI_v2_1_CanonicalRuleListSpecification

/-!
# FI v2.1 Lean experiment: exact canonical learner packages with rule-list specs

This fifty-fourth layer combines exact canonical learner grammar packages with
explicit rule-list specifications.

The exactness component is the previously checked distributional/context/word
start-witness package.  The new rule-list component records that the package's
finite refined rule lists cover all ordinary output-type refinements and are
supported by the canonical finite-monoid enumeration plan.
-/

namespace FIv21

universe u v w

noncomputable section

section CanonicalRuleListSpecificationExact

variable {N : Type w} {α : Type u}
variable [DecidableEq α]
variable {M : Type v} [Monoid M] [Fintype M]

/-- Exact canonical learner grammar package together with its rule-list
specification. -/
structure CanonicalLearnerGrammarExactWithRuleLists
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (P : CanonicalLearnerGrammarPackage G obs K) where
  exactPackage : CanonicalLearnerGrammarExactForGrammar P
  ruleLists : CanonicalRuleListSpecification P

namespace CanonicalLearnerGrammarExactWithRuleLists

/-- Any exact canonical package automatically carries the rule-list
specification from its concrete refined-rule enumeration. -/
def ofExactPackage
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {P : CanonicalLearnerGrammarPackage G obs K}
    (C : CanonicalLearnerGrammarExactForGrammar P) :
    CanonicalLearnerGrammarExactWithRuleLists P :=
  { exactPackage := C
    ruleLists := CanonicalRuleListSpecification.ofPackage P }

/-- Forget the bundled certificate to the previous exact package. -/
def toExactPackage
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {P : CanonicalLearnerGrammarPackage G obs K}
    (C : CanonicalLearnerGrammarExactWithRuleLists P) :
    CanonicalLearnerGrammarExactForGrammar P :=
  C.exactPackage

/-- Forget the bundled certificate to the rule-list specification. -/
def toRuleListSpecification
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {P : CanonicalLearnerGrammarPackage G obs K}
    (C : CanonicalLearnerGrammarExactWithRuleLists P) :
    CanonicalRuleListSpecification P :=
  C.ruleLists

/-- Exact equality of package-level approximate distributions and target
named-context distributions. -/
theorem approxDistribution_exact
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {P : CanonicalLearnerGrammarPackage G obs K}
    (C : CanonicalLearnerGrammarExactWithRuleLists P)
    {d : Nat} (x : Tuple α d) :
    P.ApproxDistribution x = NamedDistribution G.StringLanguage x := by
  exact C.exactPackage.approxDistribution_exact x

/-- Context-membership exactness form. -/
theorem licensed_iff_target_context
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {P : CanonicalLearnerGrammarPackage G obs K}
    (C : CanonicalLearnerGrammarExactWithRuleLists P)
    {d : Nat} (x : Tuple α d) (c : NamedSentenceContext α d) :
    c ∈ P.ApproxDistribution x ↔ c ∈ NamedDistribution G.StringLanguage x := by
  exact C.exactPackage.licensed_iff_target_context x c

/-- Target-side membership of a sampled word. -/
theorem sample_word_in_target
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {P : CanonicalLearnerGrammarPackage G obs K}
    (C : CanonicalLearnerGrammarExactWithRuleLists P)
    (w : Word α) (hw : w ∈ K) :
    w ∈ G.StringLanguage := by
  exact C.exactPackage.sample_word_in_target w hw

/-- Target-side start-symbol derivation witness for a sampled word. -/
theorem sample_word_start_derives
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {P : CanonicalLearnerGrammarPackage G obs K}
    (C : CanonicalLearnerGrammarExactWithRuleLists P)
    (w : Word α) (hw : w ∈ K) :
    ∃ h : 1 = G.arity G.start,
      DerivesTuple G G.start (castTuple h (singletonTuple w)) := by
  exact C.exactPackage.sample_word_start_derives w hw

/-- Learner-side generation of a sampled word by the package semantics. -/
theorem sample_word_generated_by_learner
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {P : CanonicalLearnerGrammarPackage G obs K}
    (C : CanonicalLearnerGrammarExactWithRuleLists P)
    (w : Word α) (hw : w ∈ K) :
    w ∈ P.wordLanguage := by
  exact C.exactPackage.sample_word_generated_by_learner w hw

/-- The exact package's refined-rule lists cover all ordinary output-type rule
refinements. -/
theorem refinedRuleLists_coverAll
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {P : CanonicalLearnerGrammarPackage G obs K}
    (C : CanonicalLearnerGrammarExactWithRuleLists P) :
    P.finiteRefinedGrammar.CoversAllOrdinaryRuleRefinements := by
  exact C.ruleLists.coversAll

/-- The exact package's refined-rule lists are supported by the canonical
finite-monoid plan. -/
theorem refinedRuleLists_supportedByPlan
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {P : CanonicalLearnerGrammarPackage G obs K}
    (C : CanonicalLearnerGrammarExactWithRuleLists P) :
    P.finiteRefinedGrammar.AllRulesSupportedByPlan P.ruleEnumerationPlan := by
  exact C.ruleLists.supportedByPlan

/-- A listed terminal refined rule is plan-supported. -/
theorem listed_refinedTerminal_supported
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {P : CanonicalLearnerGrammarPackage G obs K}
    (C : CanonicalLearnerGrammarExactWithRuleLists P)
    (ρ : RefinedTerminalRule G obs)
    (hρ : ρ ∈ P.finiteRefinedGrammar.terminalRules) :
    P.ruleEnumerationPlan.SupportsRefinedTerminalRule ρ := by
  exact C.ruleLists.listed_terminal_supported ρ hρ

/-- A listed binary refined rule is plan-supported. -/
theorem listed_refinedBinary_supported
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {P : CanonicalLearnerGrammarPackage G obs K}
    (C : CanonicalLearnerGrammarExactWithRuleLists P)
    (ρ : RefinedBinaryRule G obs)
    (hρ : ρ ∈ P.finiteRefinedGrammar.binaryRules) :
    P.ruleEnumerationPlan.SupportsRefinedBinaryRule ρ := by
  exact C.ruleLists.listed_binary_supported ρ hρ

/-- A listed start refined rule is plan-supported. -/
theorem listed_refinedStart_supported
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {P : CanonicalLearnerGrammarPackage G obs K}
    (C : CanonicalLearnerGrammarExactWithRuleLists P)
    (ρ : RefinedStartRule G obs)
    (hρ : ρ ∈ P.finiteRefinedGrammar.startRules) :
    P.ruleEnumerationPlan.SupportsRefinedStartRule ρ := by
  exact C.ruleLists.listed_start_supported ρ hρ

end CanonicalLearnerGrammarExactWithRuleLists

end CanonicalRuleListSpecificationExact

end

end FIv21
