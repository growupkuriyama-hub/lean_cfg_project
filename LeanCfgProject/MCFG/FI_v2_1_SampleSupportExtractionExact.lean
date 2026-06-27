import LeanCfgProject.MCFG.FI_v2_1_SampleSupportExtraction

/-!
# FI v2.1 Lean experiment: exactness for minimal sample-support extraction

This file lifts the exactness interface from `SampleExtractedRuleLists` to the
new `SampleSupportExtraction` layer.  The support is now the canonical
sample-only support; exactness remains a certificate assumption because empty
support is not complete for arbitrary targets.
-/

namespace FIv21

universe u v w

section SampleSupportExtractionExact

variable {N : Type w} {α : Type u}
variable [DecidableEq α]
variable {M : Type v} [Monoid M] [Fintype M]

/-- Exactness of minimal sample-support extraction for an abstract target
language. -/
structure SampleSupportExtractionExactForLanguage
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (E : SampleSupportExtraction G obs K) (L : Set (Word α)) : Prop where
  extractedExact : SampleExtractedRuleListsExactForLanguage
    E.toSampleExtractedRuleLists L

namespace SampleSupportExtractionExactForLanguage

/-- Forget to exactness of the previous sample-extracted rule-list layer. -/
theorem toSampleExtractedRuleListsExact
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {E : SampleSupportExtraction G obs K} {L : Set (Word α)}
    (C : SampleSupportExtractionExactForLanguage E L) :
    SampleExtractedRuleListsExactForLanguage E.toSampleExtractedRuleLists L := by
  exact C.extractedExact

/-- Forget to finite-hypothesis exactness. -/
theorem hypExact
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {E : SampleSupportExtraction G obs K} {L : Set (Word α)}
    (C : SampleSupportExtractionExactForLanguage E L) :
    FiniteLearnerHypothesis.ExactForLanguage E.toFiniteLearnerHypothesis L := by
  exact C.extractedExact.hypExact

/-- Positivity part of exactness. -/
theorem positive
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {E : SampleSupportExtraction G obs K} {L : Set (Word α)}
    (C : SampleSupportExtractionExactForLanguage E L) :
    PositiveForLanguage E.toFiniteLearnerHypothesis.sampleSet L := by
  exact C.extractedExact.positive

/-- Fixed-substitutability part of exactness. -/
theorem substitutable
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {E : SampleSupportExtraction G obs K} {L : Set (Word α)}
    (C : SampleSupportExtractionExactForLanguage E L) :
    FixedNamedTupleSubstitutable E.f obs L := by
  exact C.extractedExact.substitutable

/-- Completeness part of exactness. -/
theorem complete
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {E : SampleSupportExtraction G obs K} {L : Set (Word α)}
    (C : SampleSupportExtractionExactForLanguage E L) :
    E.toFiniteLearnerHypothesis.CompleteForLanguage L := by
  exact C.extractedExact.complete

/-- Exact equality of the minimal-support approximation and the target
distribution. -/
theorem approxDistribution_exact
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {E : SampleSupportExtraction G obs K} {L : Set (Word α)}
    (C : SampleSupportExtractionExactForLanguage E L)
    {d : Nat} (x : Tuple α d) :
    E.ApproxDistribution x = NamedDistribution L x := by
  exact C.extractedExact.approxDistribution_exact x

/-- Pointwise context-membership exactness. -/
theorem licensed_iff_target_context
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {E : SampleSupportExtraction G obs K} {L : Set (Word α)}
    (C : SampleSupportExtractionExactForLanguage E L)
    {d : Nat} (x : Tuple α d) (c : NamedSentenceContext α d) :
    c ∈ E.ApproxDistribution x ↔ c ∈ NamedDistribution L x := by
  exact C.extractedExact.licensed_iff_target_context x c

/-- The underlying support is the canonical sample-only support. -/
theorem support_eq_sampleOnly
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {E : SampleSupportExtraction G obs K} {L : Set (Word α)}
    (_C : SampleSupportExtractionExactForLanguage E L) :
    E.support = sampleOnlySupport K := by
  rfl

/-- The underlying support has no listed unit edges. -/
theorem support_no_unitEdges
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {E : SampleSupportExtraction G obs K} {L : Set (Word α)}
    (_C : SampleSupportExtractionExactForLanguage E L)
    {d : Nat} {x y : Tuple α d} :
    ¬ E.support.SupportsUnitEdge x y := by
  exact E.support_no_unitEdges

/-- The actual refined rule lists contain all ordinary output-type refinements. -/
theorem actualRuleLists_containsAll
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {E : SampleSupportExtraction G obs K} {L : Set (Word α)}
    (_C : SampleSupportExtractionExactForLanguage E L) :
    E.concreteRules.toFintypeOutputTypeRefinementCertificate.toOutputTypeRefinedGrammar.ContainsAllOrdinaryRuleRefinements := by
  exact E.concrete_containsAllOrdinaryRuleRefinements

/-- The actual refined rule lists are supported by the canonical finite-monoid
rule-enumeration plan. -/
theorem actualRuleLists_supportedByPlan
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {E : SampleSupportExtraction G obs K} {L : Set (Word α)}
    (_C : SampleSupportExtractionExactForLanguage E L) :
    E.concreteRules.grammar.AllRulesSupportedByPlan
      (FiniteRuleEnumerationPlan.ofFintype G obs) := by
  exact E.concreteRules_supportedByPlan

end SampleSupportExtractionExactForLanguage

/-- Grammar-target exactness abbreviation for minimal sample-support extraction. -/
abbrev SampleSupportExtractionExactForGrammar
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (E : SampleSupportExtraction G obs K) :=
  SampleSupportExtractionExactForLanguage E G.StringLanguage

end SampleSupportExtractionExact

end FIv21
