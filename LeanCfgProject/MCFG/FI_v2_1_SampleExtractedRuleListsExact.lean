import LeanCfgProject.MCFG.FI_v2_1_SampleExtractedRuleLists

/-!
# FI v2.1 Lean experiment: exactness for sample-extracted actual rule lists

This file lifts the existing concrete-extraction exactness interface to the
new `SampleExtractedRuleLists` structure.  The exactness assumptions are still
certificate assumptions, but the grammar-side refined rule lists are now the
actual finite-monoid lists generated from the base grammar.
-/

namespace FIv21

universe u v w

section SampleExtractedRuleListsExact

variable {N : Type w} {α : Type u}
variable [DecidableEq α]
variable {M : Type v} [Monoid M] [Fintype M]

/-- Exactness of sample-extracted actual rule-list data for an abstract target
language. -/
structure SampleExtractedRuleListsExactForLanguage
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (E : SampleExtractedRuleLists G obs K) (L : Set (Word α)) : Prop where
  concreteExact : ConcreteExtractedSampleExactForLanguage
    E.toConcreteExtractedSampleData L

namespace SampleExtractedRuleListsExactForLanguage

/-- Forget to the concrete extracted-data exactness certificate. -/
theorem toConcreteExact
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {E : SampleExtractedRuleLists G obs K} {L : Set (Word α)}
    (C : SampleExtractedRuleListsExactForLanguage E L) :
    ConcreteExtractedSampleExactForLanguage E.toConcreteExtractedSampleData L := by
  exact C.concreteExact

/-- Forget to the finite-hypothesis exactness certificate. -/
theorem hypExact
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {E : SampleExtractedRuleLists G obs K} {L : Set (Word α)}
    (C : SampleExtractedRuleListsExactForLanguage E L) :
    FiniteLearnerHypothesis.ExactForLanguage E.toFiniteLearnerHypothesis L := by
  exact C.concreteExact.hypExact

/-- Positivity part of exactness. -/
theorem positive
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {E : SampleExtractedRuleLists G obs K} {L : Set (Word α)}
    (C : SampleExtractedRuleListsExactForLanguage E L) :
    PositiveForLanguage E.toFiniteLearnerHypothesis.sampleSet L := by
  exact C.concreteExact.positive

/-- Fixed-substitutability part of exactness. -/
theorem substitutable
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {E : SampleExtractedRuleLists G obs K} {L : Set (Word α)}
    (C : SampleExtractedRuleListsExactForLanguage E L) :
    FixedNamedTupleSubstitutable E.f obs L := by
  exact C.concreteExact.substitutable

/-- Completeness part of exactness. -/
theorem complete
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {E : SampleExtractedRuleLists G obs K} {L : Set (Word α)}
    (C : SampleExtractedRuleListsExactForLanguage E L) :
    E.toFiniteLearnerHypothesis.CompleteForLanguage L := by
  exact C.concreteExact.complete

/-- Exact equality of the sample-extracted approximation and the target
distribution. -/
theorem approxDistribution_exact
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {E : SampleExtractedRuleLists G obs K} {L : Set (Word α)}
    (C : SampleExtractedRuleListsExactForLanguage E L)
    {d : Nat} (x : Tuple α d) :
    E.ApproxDistribution x = NamedDistribution L x := by
  exact C.concreteExact.approxDistribution_exact x

/-- Pointwise context-membership exactness. -/
theorem licensed_iff_target_context
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {E : SampleExtractedRuleLists G obs K} {L : Set (Word α)}
    (C : SampleExtractedRuleListsExactForLanguage E L)
    {d : Nat} (x : Tuple α d) (c : NamedSentenceContext α d) :
    c ∈ E.ApproxDistribution x ↔ c ∈ NamedDistribution L x := by
  exact C.concreteExact.licensed_iff_target_context x c

/-- The actual refined rule lists contain all ordinary output-type rule
refinements. -/
theorem actualRuleLists_containsAll
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {E : SampleExtractedRuleLists G obs K} {L : Set (Word α)}
    (_C : SampleExtractedRuleListsExactForLanguage E L) :
    E.concreteRules.toFintypeOutputTypeRefinementCertificate.toOutputTypeRefinedGrammar.ContainsAllOrdinaryRuleRefinements := by
  exact E.concrete_containsAllOrdinaryRuleRefinements

/-- The actual refined rule lists are supported by the canonical finite-monoid
rule-enumeration plan. -/
theorem actualRuleLists_supportedByPlan
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {E : SampleExtractedRuleLists G obs K} {L : Set (Word α)}
    (_C : SampleExtractedRuleListsExactForLanguage E L) :
    E.concreteRules.grammar.AllRulesSupportedByPlan
      (FiniteRuleEnumerationPlan.ofFintype G obs) := by
  exact E.concreteRules_supportedByPlan

end SampleExtractedRuleListsExactForLanguage

/-- Grammar-target exactness abbreviation for sample-extracted actual rule-list
data. -/
abbrev SampleExtractedRuleListsExactForGrammar
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (E : SampleExtractedRuleLists G obs K) :=
  SampleExtractedRuleListsExactForLanguage E G.StringLanguage

end SampleExtractedRuleListsExact

end FIv21
