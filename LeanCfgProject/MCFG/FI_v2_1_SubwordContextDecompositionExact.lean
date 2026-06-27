import LeanCfgProject.MCFG.FI_v2_1_SubwordContextDecomposition

/-!
# FI v2.1 Lean experiment: exactness wrappers for subword decompositions

This file lifts exactness from the raw-decomposition layer to the more concrete
subword-context decomposition layer.  The new content is modest but useful: a
listed two-sided subword decomposition is enough to obtain supported tuple and
context facts through the already checked raw-decomposition pipeline.
-/

namespace FIv21

universe u v w

section SubwordContextDecompositionExact

variable {N : Type w} {α : Type u}
variable [DecidableEq α]
variable {M : Type v} [Monoid M] [Fintype M]

/-- Exactness of subword-context decomposition data for an abstract target
language. -/
structure SubwordContextDecompositionExactForLanguage
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (D : SubwordContextDecompositionData G obs K) (L : Set (Word α)) : Prop where
  rawExact : RawSampleDecompositionExactForLanguage D.toRawSampleDecompositionData L

namespace SubwordContextDecompositionExactForLanguage

/-- Forget to raw-decomposition exactness. -/
theorem toRawExact
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {D : SubwordContextDecompositionData G obs K} {L : Set (Word α)}
    (C : SubwordContextDecompositionExactForLanguage D L) :
    RawSampleDecompositionExactForLanguage D.toRawSampleDecompositionData L := by
  exact C.rawExact

/-- Forget to observed-atom exactness. -/
theorem toObservedExact
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {D : SubwordContextDecompositionData G obs K} {L : Set (Word α)}
    (C : SubwordContextDecompositionExactForLanguage D L) :
    ObservedSampleAtomsExactForLanguage D.toObservedSampleAtoms L := by
  exact C.rawExact.toObservedSampleAtomsExact

/-- Exact equality of approximate and target named distributions. -/
theorem approxDistribution_exact
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {D : SubwordContextDecompositionData G obs K} {L : Set (Word α)}
    (C : SubwordContextDecompositionExactForLanguage D L)
    {d : Nat} (x : Tuple α d) :
    D.ApproxDistribution x = NamedDistribution L x := by
  exact C.rawExact.approxDistribution_exact x

/-- A listed subword decomposition contributes a supported singleton tuple. -/
theorem supportsTuple_of_subword_mem
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {D : SubwordContextDecompositionData G obs K} {L : Set (Word α)}
    (_C : SubwordContextDecompositionExactForLanguage D L)
    {S : SubwordSampleDecomposition (α := α) K}
    (hS : S ∈ D.subwordDecompositions) :
    D.support.SupportsTuple S.tuple := by
  exact D.supportsTuple_of_subword_mem hS

/-- A listed subword decomposition contributes a supported two-sided context. -/
theorem supportsContext_of_subword_mem
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {D : SubwordContextDecompositionData G obs K} {L : Set (Word α)}
    (_C : SubwordContextDecompositionExactForLanguage D L)
    {S : SubwordSampleDecomposition (α := α) K}
    (hS : S ∈ D.subwordDecompositions) :
    D.support.SupportsContext S.context := by
  exact D.supportsContext_of_subword_mem hS

/-- A listed subword decomposition gives sample-distribution membership for its
exposed context. -/
theorem subword_context_mem_sampleDistribution
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {D : SubwordContextDecompositionData G obs K} {L : Set (Word α)}
    (_C : SubwordContextDecompositionExactForLanguage D L)
    {S : SubwordSampleDecomposition (α := α) K}
    (hS : S ∈ D.subwordDecompositions) :
    S.context ∈ SampleNamedDistribution K S.tuple := by
  exact D.subword_context_mem_sampleDistribution hS

/-- The actual refined rule lists contain all ordinary output-type refinements. -/
theorem actualRuleLists_containsAll
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {D : SubwordContextDecompositionData G obs K} {L : Set (Word α)}
    (_C : SubwordContextDecompositionExactForLanguage D L) :
    D.toObservedSampleAtoms.concreteRules.toFintypeOutputTypeRefinementCertificate.toOutputTypeRefinedGrammar.ContainsAllOrdinaryRuleRefinements := by
  exact D.concrete_containsAllOrdinaryRuleRefinements

/-- Whole-word data exactness is compatible with the support theorem for each
sampled word. -/
theorem wholeWord_supported_sample_word_exact
    (G : WorkingMCFG N α) (obs : α → M) (K : Finset (Word α))
    (f : Nat) (hG : G.SemanticWorkingConditions)
    {L : Set (Word α)}
    (_C : SubwordContextDecompositionExactForLanguage
      (wholeWordSubwordContextDecompositionData G obs K f hG) L)
    {w : Word α} (hw : w ∈ K) :
    ∃ S : SubwordSampleDecomposition (α := α) K,
      S ∈ (wholeWordSubwordContextDecompositionData G obs K f hG).subwordDecompositions ∧
      S.sampleWord = w ∧
      (wholeWordSubwordContextDecompositionData G obs K f hG).support.SupportsTuple S.tuple ∧
      (wholeWordSubwordContextDecompositionData G obs K f hG).support.SupportsContext S.context ∧
      S.context ∈ SampleNamedDistribution K S.tuple := by
  exact wholeWordSubwordContextDecompositionData_supported_sample_word G obs K f hG hw

end SubwordContextDecompositionExactForLanguage

/-- Grammar-target exactness abbreviation for subword-context data. -/
abbrev SubwordContextDecompositionExactForGrammar
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (D : SubwordContextDecompositionData G obs K) :=
  SubwordContextDecompositionExactForLanguage D G.StringLanguage

end SubwordContextDecompositionExact

end FIv21
