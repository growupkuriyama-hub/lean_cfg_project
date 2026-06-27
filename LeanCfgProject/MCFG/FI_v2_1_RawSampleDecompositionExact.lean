import LeanCfgProject.MCFG.FI_v2_1_RawSampleDecomposition

/-!
# FI v2.1 Lean experiment: exactness for raw sample decompositions

This file lifts exactness from the observed-atom layer to the raw decomposition
layer.  It records that the atom lists used by the finite learner support are
not arbitrary: they are generated from explicit `namedFill` decompositions of
sampled words and explicit sample-safe unit-edge witnesses.
-/

namespace FIv21

universe u v w

section RawSampleDecompositionExact

variable {N : Type w} {α : Type u}
variable [DecidableEq α]
variable {M : Type v} [Monoid M] [Fintype M]

/-- Exactness of raw sample decomposition data for an abstract target language. -/
structure RawSampleDecompositionExactForLanguage
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (D : RawSampleDecompositionData G obs K) (L : Set (Word α)) : Prop where
  observedExact : ObservedSampleAtomsExactForLanguage D.toObservedSampleAtoms L

namespace RawSampleDecompositionExactForLanguage

/-- Forget to observed-atom exactness. -/
theorem toObservedSampleAtomsExact
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {D : RawSampleDecompositionData G obs K} {L : Set (Word α)}
    (C : RawSampleDecompositionExactForLanguage D L) :
    ObservedSampleAtomsExactForLanguage D.toObservedSampleAtoms L := by
  exact C.observedExact

/-- Forget to finite-hypothesis exactness. -/
theorem hypExact
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {D : RawSampleDecompositionData G obs K} {L : Set (Word α)}
    (C : RawSampleDecompositionExactForLanguage D L) :
    FiniteLearnerHypothesis.ExactForLanguage D.toFiniteLearnerHypothesis L := by
  exact C.observedExact.hypExact

/-- Positivity part of exactness. -/
theorem positive
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {D : RawSampleDecompositionData G obs K} {L : Set (Word α)}
    (C : RawSampleDecompositionExactForLanguage D L) :
    PositiveForLanguage D.toFiniteLearnerHypothesis.sampleSet L := by
  exact C.observedExact.positive

/-- Fixed-substitutability part of exactness. -/
theorem substitutable
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {D : RawSampleDecompositionData G obs K} {L : Set (Word α)}
    (C : RawSampleDecompositionExactForLanguage D L) :
    FixedNamedTupleSubstitutable D.f obs L := by
  exact C.observedExact.substitutable

/-- Exact equality of the raw-decomposition approximation and the target
distribution. -/
theorem approxDistribution_exact
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {D : RawSampleDecompositionData G obs K} {L : Set (Word α)}
    (C : RawSampleDecompositionExactForLanguage D L)
    {d : Nat} (x : Tuple α d) :
    D.ApproxDistribution x = NamedDistribution L x := by
  exact C.observedExact.approxDistribution_exact x

/-- Pointwise context-membership exactness. -/
theorem licensed_iff_target_context
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {D : RawSampleDecompositionData G obs K} {L : Set (Word α)}
    (C : RawSampleDecompositionExactForLanguage D L)
    {d : Nat} (x : Tuple α d) (c : NamedSentenceContext α d) :
    c ∈ D.ApproxDistribution x ↔ c ∈ NamedDistribution L x := by
  exact C.observedExact.licensed_iff_target_context x c

/-- The support is assembled from raw decomposition and unit-edge witness lists. -/
theorem support_eq_rawDecompositions
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {D : RawSampleDecompositionData G obs K} {L : Set (Word α)}
    (_C : RawSampleDecompositionExactForLanguage D L) :
    D.support = supportOfObservedAtoms K D.tupleAtoms D.contextAtoms D.unitEdgeAtoms := by
  rfl

/-- A listed raw decomposition contributes a supported tuple. -/
theorem supportsTuple_of_decomposition_mem
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {D : RawSampleDecompositionData G obs K} {L : Set (Word α)}
    (_C : RawSampleDecompositionExactForLanguage D L)
    {R : RawSampleDecomposition (α := α) K}
    (hR : R ∈ D.decompositions) :
    D.support.SupportsTuple R.tuple := by
  exact D.supportsTuple_of_decomposition_mem hR

/-- A listed raw decomposition contributes a supported context. -/
theorem supportsContext_of_decomposition_mem
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {D : RawSampleDecompositionData G obs K} {L : Set (Word α)}
    (_C : RawSampleDecompositionExactForLanguage D L)
    {R : RawSampleDecomposition (α := α) K}
    (hR : R ∈ D.decompositions) :
    D.support.SupportsContext R.context := by
  exact D.supportsContext_of_decomposition_mem hR

/-- A listed raw unit-edge witness contributes a supported unit edge. -/
theorem supportsUnitEdge_of_witness_mem
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {D : RawSampleDecompositionData G obs K} {L : Set (Word α)}
    (_C : RawSampleDecompositionExactForLanguage D L)
    {E : RawSampleUnitEdgeWitness (α := α) K obs D.f}
    (hE : E ∈ D.unitEdgeWitnesses) :
    D.support.SupportsUnitEdge E.src E.tgt := by
  exact D.supportsUnitEdge_of_witness_mem hE

/-- A listed raw decomposition gives a sample-distribution context for its tuple. -/
theorem decomposition_context_mem_sampleDistribution
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {D : RawSampleDecompositionData G obs K} {L : Set (Word α)}
    (_C : RawSampleDecompositionExactForLanguage D L)
    {R : RawSampleDecomposition (α := α) K}
    (_hR : R ∈ D.decompositions) :
    R.context ∈ SampleNamedDistribution K R.tuple := by
  exact R.context_mem_sampleDistribution

/-- A listed raw unit-edge witness gives the sample-safe merge predicate. -/
theorem witness_sampleSafeMerge
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {D : RawSampleDecompositionData G obs K} {L : Set (Word α)}
    (_C : RawSampleDecompositionExactForLanguage D L)
    {E : RawSampleUnitEdgeWitness (α := α) K obs D.f}
    (_hE : E ∈ D.unitEdgeWitnesses) :
    SampleSafeMerge K obs E.src E.tgt := by
  exact E.sampleSafeMerge

/-- The actual refined rule lists contain all ordinary output-type refinements. -/
theorem actualRuleLists_containsAll
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {D : RawSampleDecompositionData G obs K} {L : Set (Word α)}
    (_C : RawSampleDecompositionExactForLanguage D L) :
    D.toObservedSampleAtoms.concreteRules.toFintypeOutputTypeRefinementCertificate.toOutputTypeRefinedGrammar.ContainsAllOrdinaryRuleRefinements := by
  exact D.concrete_containsAllOrdinaryRuleRefinements

/-- The actual refined rule lists are supported by the canonical finite-monoid
rule-enumeration plan. -/
theorem actualRuleLists_supportedByPlan
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {D : RawSampleDecompositionData G obs K} {L : Set (Word α)}
    (_C : RawSampleDecompositionExactForLanguage D L) :
    D.toObservedSampleAtoms.concreteRules.grammar.AllRulesSupportedByPlan
      (FiniteRuleEnumerationPlan.ofFintype G obs) := by
  exact D.concreteRules_supportedByPlan

end RawSampleDecompositionExactForLanguage

/-- Grammar-target exactness abbreviation for raw sample decomposition data. -/
abbrev RawSampleDecompositionExactForGrammar
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (D : RawSampleDecompositionData G obs K) :=
  RawSampleDecompositionExactForLanguage D G.StringLanguage

end RawSampleDecompositionExact

end FIv21
