import LeanCfgProject.MCFG.FI_v2_1_ObservedSampleAtoms

/-!
# FI v2.1 Lean experiment: exactness for observed sample atoms

This file lifts the exactness interface from `SampleExtractedRuleLists` to the
observed-atom extraction layer.  The support is now assembled from explicit
sample-observed tuple, context, and unit-edge atoms.
-/

namespace FIv21

universe u v w

section ObservedSampleAtomsExact

variable {N : Type w} {α : Type u}
variable [DecidableEq α]
variable {M : Type v} [Monoid M] [Fintype M]

/-- Exactness of observed-atom extraction for an abstract target language. -/
structure ObservedSampleAtomsExactForLanguage
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (E : ObservedSampleAtoms G obs K) (L : Set (Word α)) : Prop where
  extractedExact : SampleExtractedRuleListsExactForLanguage
    E.toSampleExtractedRuleLists L

namespace ObservedSampleAtomsExactForLanguage

/-- Forget to exactness of the sample-extracted rule-list layer. -/
theorem toSampleExtractedRuleListsExact
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {E : ObservedSampleAtoms G obs K} {L : Set (Word α)}
    (C : ObservedSampleAtomsExactForLanguage E L) :
    SampleExtractedRuleListsExactForLanguage E.toSampleExtractedRuleLists L := by
  exact C.extractedExact

/-- Forget to finite-hypothesis exactness. -/
theorem hypExact
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {E : ObservedSampleAtoms G obs K} {L : Set (Word α)}
    (C : ObservedSampleAtomsExactForLanguage E L) :
    FiniteLearnerHypothesis.ExactForLanguage E.toFiniteLearnerHypothesis L := by
  exact C.extractedExact.hypExact

/-- Positivity part of exactness. -/
theorem positive
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {E : ObservedSampleAtoms G obs K} {L : Set (Word α)}
    (C : ObservedSampleAtomsExactForLanguage E L) :
    PositiveForLanguage E.toFiniteLearnerHypothesis.sampleSet L := by
  exact C.extractedExact.positive

/-- Fixed-substitutability part of exactness. -/
theorem substitutable
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {E : ObservedSampleAtoms G obs K} {L : Set (Word α)}
    (C : ObservedSampleAtomsExactForLanguage E L) :
    FixedNamedTupleSubstitutable E.f obs L := by
  exact C.extractedExact.substitutable

/-- Completeness part of exactness. -/
theorem complete
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {E : ObservedSampleAtoms G obs K} {L : Set (Word α)}
    (C : ObservedSampleAtomsExactForLanguage E L) :
    E.toFiniteLearnerHypothesis.CompleteForLanguage L := by
  exact C.extractedExact.complete

/-- Exact equality of the observed-atom approximation and the target
distribution. -/
theorem approxDistribution_exact
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {E : ObservedSampleAtoms G obs K} {L : Set (Word α)}
    (C : ObservedSampleAtomsExactForLanguage E L)
    {d : Nat} (x : Tuple α d) :
    E.ApproxDistribution x = NamedDistribution L x := by
  exact C.extractedExact.approxDistribution_exact x

/-- Pointwise context-membership exactness. -/
theorem licensed_iff_target_context
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {E : ObservedSampleAtoms G obs K} {L : Set (Word α)}
    (C : ObservedSampleAtomsExactForLanguage E L)
    {d : Nat} (x : Tuple α d) (c : NamedSentenceContext α d) :
    c ∈ E.ApproxDistribution x ↔ c ∈ NamedDistribution L x := by
  exact C.extractedExact.licensed_iff_target_context x c

/-- The underlying finite support is assembled from the listed observed atoms. -/
theorem support_eq_observedAtoms
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {E : ObservedSampleAtoms G obs K} {L : Set (Word α)}
    (_C : ObservedSampleAtomsExactForLanguage E L) :
    E.support = supportOfObservedAtoms K E.tupleAtoms E.contextAtoms E.unitEdgeAtoms := by
  rfl

/-- Tuple support is exactly membership in the extracted tuple-atom list. -/
theorem supportsTuple_iff_mem_tupleAtoms
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {E : ObservedSampleAtoms G obs K} {L : Set (Word α)}
    (_C : ObservedSampleAtomsExactForLanguage E L)
    {d : Nat} (x : Tuple α d) :
    E.support.SupportsTuple x ↔ (Sigma.mk d x : TupleAtom α) ∈ E.tupleAtoms := by
  rfl

/-- Context support is exactly membership in the extracted context-atom list. -/
theorem supportsContext_iff_mem_contextAtoms
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {E : ObservedSampleAtoms G obs K} {L : Set (Word α)}
    (_C : ObservedSampleAtomsExactForLanguage E L)
    {d : Nat} (c : NamedSentenceContext α d) :
    E.support.SupportsContext c ↔ (Sigma.mk d c : ContextAtom α) ∈ E.contextAtoms := by
  rfl

/-- Unit-edge support is exactly membership in the extracted unit-edge atom list. -/
theorem supportsUnitEdge_iff_mem_unitEdgeAtoms
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {E : ObservedSampleAtoms G obs K} {L : Set (Word α)}
    (_C : ObservedSampleAtomsExactForLanguage E L)
    {d : Nat} (x y : Tuple α d) :
    E.support.SupportsUnitEdge x y ↔
      (Sigma.mk d (x, y) : UnitEdgeAtom α) ∈ E.unitEdgeAtoms := by
  rfl

/-- The actual refined rule lists contain all ordinary output-type refinements. -/
theorem actualRuleLists_containsAll
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {E : ObservedSampleAtoms G obs K} {L : Set (Word α)}
    (_C : ObservedSampleAtomsExactForLanguage E L) :
    E.concreteRules.toFintypeOutputTypeRefinementCertificate.toOutputTypeRefinedGrammar.ContainsAllOrdinaryRuleRefinements := by
  exact E.concrete_containsAllOrdinaryRuleRefinements

/-- The actual refined rule lists are supported by the canonical finite-monoid
rule-enumeration plan. -/
theorem actualRuleLists_supportedByPlan
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {E : ObservedSampleAtoms G obs K} {L : Set (Word α)}
    (_C : ObservedSampleAtomsExactForLanguage E L) :
    E.concreteRules.grammar.AllRulesSupportedByPlan
      (FiniteRuleEnumerationPlan.ofFintype G obs) := by
  exact E.concreteRules_supportedByPlan

end ObservedSampleAtomsExactForLanguage

/-- Grammar-target exactness abbreviation for observed-atom extraction. -/
abbrev ObservedSampleAtomsExactForGrammar
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (E : ObservedSampleAtoms G obs K) :=
  ObservedSampleAtomsExactForLanguage E G.StringLanguage

end ObservedSampleAtomsExact

end FIv21
