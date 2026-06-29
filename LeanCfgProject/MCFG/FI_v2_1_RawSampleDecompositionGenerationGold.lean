import LeanCfgProject.MCFG.FI_v2_1_RawSampleDecompositionGenerationExact

/-!
# FI v2.1 Lean experiment: Gold wrapper for raw decomposition generation facts

This file pushes the raw-witness generation facts through the Gold-style
characteristic-sample wrapper.  After the characteristic sample is contained in
the observed sample, listed raw decompositions and raw unit-edge witnesses carry
support, sample-distribution, unit-reachability, and exact target-distribution
facts.
-/

namespace FIv21

universe u v w

section RawSampleDecompositionGenerationGold

variable {N : Type w} {α : Type u}
variable [DecidableEq α]
variable {M : Type v} [Monoid M] [Fintype M]

namespace RawSampleDecompositionCharacteristicSample

/-- After the threshold, raw decomposition data carries a generated-support
certificate. -/
theorem generatedSupport_after
    {G : WorkingMCFG N α} {obs : α → M}
    {A : RawSampleDecompositionLearner G obs} {L : Set (Word α)}
    (C : RawSampleDecompositionCharacteristicSample A L)
    {K : Finset (Word α)}
    (hExt : SampleExtends C.sample K)
    (hPos : PositiveForLanguage K L) :
    RawSampleGeneratedSupport (A K) := by
  exact (C.exact_after_extending K hExt hPos).generatedSupport

/-- After the threshold, a listed raw decomposition gives both supported atoms. -/
theorem decomposition_supported_atoms_after
    {G : WorkingMCFG N α} {obs : α → M}
    {A : RawSampleDecompositionLearner G obs} {L : Set (Word α)}
    (C : RawSampleDecompositionCharacteristicSample A L)
    {K : Finset (Word α)}
    (hExt : SampleExtends C.sample K)
    (hPos : PositiveForLanguage K L)
    {R : RawSampleDecomposition (α := α) K}
    (hR : R ∈ (A K).decompositions) :
    (A K).support.SupportsTuple R.tuple ∧
      (A K).support.SupportsContext R.context := by
  exact (C.exact_after_extending K hExt hPos).decomposition_supported_atoms hR

/-- After the threshold, a listed raw decomposition is sample-licensed. -/
theorem decomposition_sample_licensed_after
    {G : WorkingMCFG N α} {obs : α → M}
    {A : RawSampleDecompositionLearner G obs} {L : Set (Word α)}
    (C : RawSampleDecompositionCharacteristicSample A L)
    {K : Finset (Word α)}
    (hExt : SampleExtends C.sample K)
    (hPos : PositiveForLanguage K L)
    {R : RawSampleDecomposition (α := α) K}
    (hR : R ∈ (A K).decompositions) :
    R.context ∈ SampleNamedDistribution K R.tuple := by
  exact (C.exact_after_extending K hExt hPos).decomposition_sample_licensed_exact hR

/-- After the threshold, a listed raw unit-edge witness gives supported edge plus
sample-safe merge. -/
theorem unitEdge_supported_and_safe_after
    {G : WorkingMCFG N α} {obs : α → M}
    {A : RawSampleDecompositionLearner G obs} {L : Set (Word α)}
    (C : RawSampleDecompositionCharacteristicSample A L)
    {K : Finset (Word α)}
    (hExt : SampleExtends C.sample K)
    (hPos : PositiveForLanguage K L)
    {E : RawSampleUnitEdgeWitness (α := α) K obs (A K).f}
    (hE : E ∈ (A K).unitEdgeWitnesses) :
    (A K).support.SupportsUnitEdge E.src E.tgt ∧
      SampleSafeMerge K obs E.src E.tgt := by
  exact (C.exact_after_extending K hExt hPos).unitEdge_supported_and_safe_exact hE

/-- After the threshold, a listed raw unit-edge witness reaches in the induced
sample-extracted finite hypothesis. -/
theorem unitEdge_reaches_in_sampleExtractedRuleLists_after
    {G : WorkingMCFG N α} {obs : α → M}
    {A : RawSampleDecompositionLearner G obs} {L : Set (Word α)}
    (C : RawSampleDecompositionCharacteristicSample A L)
    {K : Finset (Word α)}
    (hExt : SampleExtends C.sample K)
    (hPos : PositiveForLanguage K L)
    {E : RawSampleUnitEdgeWitness (α := α) K obs (A K).f}
    (hE : E ∈ (A K).unitEdgeWitnesses) :
    (A K).toSampleExtractedRuleLists.UnitReach E.src E.tgt := by
  exact (C.exact_after_extending K hExt hPos).unitEdge_reaches_in_sampleExtractedRuleLists_exact hE

/-- After the threshold, source and target of a listed raw unit-edge witness have
matching observation type. -/
theorem unitEdge_same_type_after
    {G : WorkingMCFG N α} {obs : α → M}
    {A : RawSampleDecompositionLearner G obs} {L : Set (Word α)}
    (C : RawSampleDecompositionCharacteristicSample A L)
    {K : Finset (Word α)}
    (_hExt : SampleExtends C.sample K)
    (_hPos : PositiveForLanguage K L)
    {E : RawSampleUnitEdgeWitness (α := α) K obs (A K).f}
    (_hE : E ∈ (A K).unitEdgeWitnesses) :
    tupleType obs E.src = tupleType obs E.tgt := by
  exact RawSampleUnitEdgeWitness.same_type E

end RawSampleDecompositionCharacteristicSample

/-- Grammar-target characteristic sample abbreviation retaining the generation
facts. -/
abbrev GrammarRawSampleDecompositionGeneratedSupportCharacteristicSample
    {G : WorkingMCFG N α} {obs : α → M}
    (A : RawSampleDecompositionLearner G obs) :=
  RawSampleDecompositionCharacteristicSample A G.StringLanguage

end RawSampleDecompositionGenerationGold

end FIv21
