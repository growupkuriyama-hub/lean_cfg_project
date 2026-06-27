import LeanCfgProject.MCFG.FI_v2_1_RawSampleDecompositionGeneration

/-!
# FI v2.1 Lean experiment: exactness consequences of raw decomposition generation

This file lifts the generation facts from raw decomposition data through the
existing exactness wrapper.  The mathematical content is intentionally modest
but useful: after exactness is available, the same raw witnesses can be used as
support facts, sample-distribution facts, unit-reachability facts, and exact
context-membership facts.
-/

namespace FIv21

universe u v w

section RawSampleDecompositionGenerationExact

variable {N : Type w} {α : Type u}
variable [DecidableEq α]
variable {M : Type v} [Monoid M] [Fintype M]

namespace RawSampleDecompositionExactForLanguage

/-- Exact raw decomposition data carries a generated-support certificate. -/
theorem generatedSupport
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {D : RawSampleDecompositionData G obs K} {L : Set (Word α)}
    (_C : RawSampleDecompositionExactForLanguage D L) :
    RawSampleGeneratedSupport D := by
  exact D.generatedSupport

/-- A listed raw decomposition gives both supported atoms under exactness. -/
theorem decomposition_supported_atoms
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {D : RawSampleDecompositionData G obs K} {L : Set (Word α)}
    (_C : RawSampleDecompositionExactForLanguage D L)
    {R : RawSampleDecomposition (α := α) K}
    (hR : R ∈ D.decompositions) :
    D.support.SupportsTuple R.tuple ∧
      D.support.SupportsContext R.context := by
  exact D.decomposition_supported hR

/-- A listed raw decomposition is sample-licensed under exactness. -/
theorem decomposition_sample_licensed_exact
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {D : RawSampleDecompositionData G obs K} {L : Set (Word α)}
    (_C : RawSampleDecompositionExactForLanguage D L)
    {R : RawSampleDecomposition (α := α) K}
    (hR : R ∈ D.decompositions) :
    R.context ∈ SampleNamedDistribution K R.tuple := by
  exact D.decomposition_sample_licensed hR

/-- A listed raw decomposition has its filled word in the support sample under
exactness. -/
theorem decomposition_filled_mem_support_sample_exact
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {D : RawSampleDecompositionData G obs K} {L : Set (Word α)}
    (_C : RawSampleDecompositionExactForLanguage D L)
    {R : RawSampleDecomposition (α := α) K}
    (hR : R ∈ D.decompositions) :
    namedFill R.d R.context R.tuple ∈ D.support.sample := by
  exact D.decomposition_filled_mem_support_sample hR

/-- A listed raw unit-edge witness gives supported edge plus safe merge under
exactness. -/
theorem unitEdge_supported_and_safe_exact
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {D : RawSampleDecompositionData G obs K} {L : Set (Word α)}
    (_C : RawSampleDecompositionExactForLanguage D L)
    {E : RawSampleUnitEdgeWitness (α := α) K obs D.f}
    (hE : E ∈ D.unitEdgeWitnesses) :
    D.support.SupportsUnitEdge E.src E.tgt ∧
      SampleSafeMerge K obs E.src E.tgt := by
  exact D.unitEdge_supported_and_safe hE

/-- A listed raw unit-edge witness reaches in the induced sample-extracted data
under exactness. -/
theorem unitEdge_reaches_in_sampleExtractedRuleLists_exact
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {D : RawSampleDecompositionData G obs K} {L : Set (Word α)}
    (_C : RawSampleDecompositionExactForLanguage D L)
    {E : RawSampleUnitEdgeWitness (α := α) K obs D.f}
    (hE : E ∈ D.unitEdgeWitnesses) :
    D.toSampleExtractedRuleLists.UnitReach E.src E.tgt := by
  exact D.unitEdge_reaches_in_sampleExtractedRuleLists hE

/-- The source side of a listed unit-edge witness is sample-licensed under
exactness. -/
theorem unitEdge_src_context_mem_sampleDistribution_exact
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {D : RawSampleDecompositionData G obs K} {L : Set (Word α)}
    (_C : RawSampleDecompositionExactForLanguage D L)
    {E : RawSampleUnitEdgeWitness (α := α) K obs D.f}
    (_hE : E ∈ D.unitEdgeWitnesses) :
    E.context ∈ SampleNamedDistribution K E.src := by
  exact E.src_context_mem_sampleDistribution

/-- The target side of a listed unit-edge witness is sample-licensed under
exactness. -/
theorem unitEdge_tgt_context_mem_sampleDistribution_exact
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {D : RawSampleDecompositionData G obs K} {L : Set (Word α)}
    (_C : RawSampleDecompositionExactForLanguage D L)
    {E : RawSampleUnitEdgeWitness (α := α) K obs D.f}
    (_hE : E ∈ D.unitEdgeWitnesses) :
    E.context ∈ SampleNamedDistribution K E.tgt := by
  exact E.tgt_context_mem_sampleDistribution

end RawSampleDecompositionExactForLanguage

end RawSampleDecompositionGenerationExact

end FIv21
