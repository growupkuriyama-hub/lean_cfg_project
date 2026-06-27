import LeanCfgProject.MCFG.FI_v2_1_RawSampleDecompositionEnumeration

/-!
# FI v2.1 Lean experiment: exactness wrappers for enumerated sample-word decompositions

This file records that the elementary sample-word enumeration introduced in
`RawSampleDecompositionEnumeration` is compatible with the existing exactness
layer.  Exactness is not used to create the trivial decompositions; rather, once
an exactness certificate is present, those listed decompositions can still be
used as supported and sample-licensed atoms.
-/

namespace FIv21

universe u v w

section RawSampleDecompositionEnumerationExact

variable {N : Type w} {α : Type u}
variable [DecidableEq α]
variable {M : Type v} [Monoid M] [Fintype M]

namespace RawSampleDecompositionExactForLanguage

/-- Under exactness, if the raw decomposition list is the singleton-word
enumeration, then every sample word is represented by a listed raw
decomposition. -/
theorem covers_sample_of_singletonDecompositions_exact
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {D : RawSampleDecompositionData G obs K} {L : Set (Word α)}
    (_C : RawSampleDecompositionExactForLanguage D L)
    (hD : D.decompositions = singletonRawSampleDecompositions (α := α) K)
    {w : Word α} (hw : w ∈ K) :
    ∃ R : RawSampleDecomposition (α := α) K,
      R ∈ D.decompositions ∧
      R.sampleWord = w ∧
      namedFill R.d R.context R.tuple = w := by
  exact D.covers_sample_of_singletonDecompositions hD hw

/-- Under exactness, a sample word represented by the singleton-word enumeration
has supported tuple/context atoms and a sample-licensed context. -/
theorem supported_singletonDecomposition_of_sample_mem_exact
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {D : RawSampleDecompositionData G obs K} {L : Set (Word α)}
    (_C : RawSampleDecompositionExactForLanguage D L)
    (hD : D.decompositions = singletonRawSampleDecompositions (α := α) K)
    {w : Word α} (hw : w ∈ K) :
    ∃ R : RawSampleDecomposition (α := α) K,
      R ∈ D.decompositions ∧
      R.sampleWord = w ∧
      D.support.SupportsTuple R.tuple ∧
      D.support.SupportsContext R.context ∧
      R.context ∈ SampleNamedDistribution K R.tuple := by
  exact D.supported_singletonDecomposition_of_sample_mem hD hw

/-- Specialized exactness-compatible coverage theorem for the sample-word-only
data constructor. -/
theorem sampleWordOnly_covers_sample_exact
    (G : WorkingMCFG N α) (obs : α → M) (K : Finset (Word α))
    (f : Nat) (hG : G.SemanticWorkingConditions)
    {L : Set (Word α)}
    (_C : RawSampleDecompositionExactForLanguage
      (sampleWordOnlyRawSampleDecompositionData G obs K f hG) L)
    {w : Word α} (hw : w ∈ K) :
    ∃ R : RawSampleDecomposition (α := α) K,
      R ∈ (sampleWordOnlyRawSampleDecompositionData G obs K f hG).decompositions ∧
      R.sampleWord = w ∧
      namedFill R.d R.context R.tuple = w := by
  exact sampleWordOnlyRawSampleDecompositionData_covers_sample G obs K f hG hw

/-- Specialized exactness-compatible support theorem for the sample-word-only
data constructor. -/
theorem sampleWordOnly_supported_sample_word_exact
    (G : WorkingMCFG N α) (obs : α → M) (K : Finset (Word α))
    (f : Nat) (hG : G.SemanticWorkingConditions)
    {L : Set (Word α)}
    (_C : RawSampleDecompositionExactForLanguage
      (sampleWordOnlyRawSampleDecompositionData G obs K f hG) L)
    {w : Word α} (hw : w ∈ K) :
    ∃ R : RawSampleDecomposition (α := α) K,
      R ∈ (sampleWordOnlyRawSampleDecompositionData G obs K f hG).decompositions ∧
      R.sampleWord = w ∧
      (sampleWordOnlyRawSampleDecompositionData G obs K f hG).support.SupportsTuple R.tuple ∧
      (sampleWordOnlyRawSampleDecompositionData G obs K f hG).support.SupportsContext R.context ∧
      R.context ∈ SampleNamedDistribution K R.tuple := by
  exact sampleWordOnlyRawSampleDecompositionData_supported_sample_word G obs K f hG hw

end RawSampleDecompositionExactForLanguage

end RawSampleDecompositionEnumerationExact

end FIv21
