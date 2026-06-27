import LeanCfgProject.MCFG.FI_v2_1_RawSampleDecompositionGold

/-!
# FI v2.1 Lean experiment: generation facts from raw sample decompositions

This file is the next vertical step after `RawSampleDecomposition`.

The previous layer introduced explicit witnesses of the form
`w = namedFill d c x` for sampled words, and explicit raw unit-edge witnesses.
Here we collect the elementary generation consequences of those witnesses:
listed decompositions generate supported tuple/context atoms and sample
named-distribution facts, while listed unit-edge witnesses generate supported
unit edges, sample-safe merges, and finite-hypothesis unit reachability.

This is still not the full automatic enumeration of all decompositions of a raw
sample.  It is the bridge from witness lists to the support/transport facts that
will be used by the concrete learner-grammar construction.
-/

namespace FIv21

universe u v w

section RawSampleDecompositionGeneration

variable {N : Type w} {α : Type u}
variable [DecidableEq α]
variable {M : Type v} [Monoid M] [Fintype M]

/-- A compact predicate saying that all raw decomposition and unit-edge witness
lists in `D` really generate the support facts used by the learner. -/
structure RawSampleGeneratedSupport
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (D : RawSampleDecompositionData G obs K) : Prop where
  decomposition_supported :
    ∀ R : RawSampleDecomposition (α := α) K,
      R ∈ D.decompositions →
        D.support.SupportsTuple R.tuple ∧
        D.support.SupportsContext R.context
  decomposition_sample_licensed :
    ∀ R : RawSampleDecomposition (α := α) K,
      R ∈ D.decompositions →
        R.context ∈ SampleNamedDistribution K R.tuple
  unitEdge_supported :
    ∀ E : RawSampleUnitEdgeWitness (α := α) K obs D.f,
      E ∈ D.unitEdgeWitnesses →
        D.support.SupportsUnitEdge E.src E.tgt
  unitEdge_safe :
    ∀ E : RawSampleUnitEdgeWitness (α := α) K obs D.f,
      E ∈ D.unitEdgeWitnesses →
        SampleSafeMerge K obs E.src E.tgt

namespace RawSampleGeneratedSupport

/-- A generated-support certificate gives supported tuples. -/
theorem supportsTuple
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {D : RawSampleDecompositionData G obs K}
    (C : RawSampleGeneratedSupport D)
    {R : RawSampleDecomposition (α := α) K}
    (hR : R ∈ D.decompositions) :
    D.support.SupportsTuple R.tuple := by
  exact (C.decomposition_supported R hR).1

/-- A generated-support certificate gives supported contexts. -/
theorem supportsContext
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {D : RawSampleDecompositionData G obs K}
    (C : RawSampleGeneratedSupport D)
    {R : RawSampleDecomposition (α := α) K}
    (hR : R ∈ D.decompositions) :
    D.support.SupportsContext R.context := by
  exact (C.decomposition_supported R hR).2

/-- A generated-support certificate gives sample named-distribution membership. -/
theorem sampleLicensed
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {D : RawSampleDecompositionData G obs K}
    (C : RawSampleGeneratedSupport D)
    {R : RawSampleDecomposition (α := α) K}
    (hR : R ∈ D.decompositions) :
    R.context ∈ SampleNamedDistribution K R.tuple := by
  exact C.decomposition_sample_licensed R hR

/-- A generated-support certificate gives supported unit edges. -/
theorem supportsUnitEdge
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {D : RawSampleDecompositionData G obs K}
    (C : RawSampleGeneratedSupport D)
    {E : RawSampleUnitEdgeWitness (α := α) K obs D.f}
    (hE : E ∈ D.unitEdgeWitnesses) :
    D.support.SupportsUnitEdge E.src E.tgt := by
  exact C.unitEdge_supported E hE

/-- A generated-support certificate gives sample-safe merges. -/
theorem sampleSafeMerge
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {D : RawSampleDecompositionData G obs K}
    (C : RawSampleGeneratedSupport D)
    {E : RawSampleUnitEdgeWitness (α := α) K obs D.f}
    (hE : E ∈ D.unitEdgeWitnesses) :
    SampleSafeMerge K obs E.src E.tgt := by
  exact C.unitEdge_safe E hE

end RawSampleGeneratedSupport

namespace RawSampleDecomposition

/-- The filled word of a raw decomposition belongs to any support whose sample is
`K`.  This is a small but useful rewriting lemma for later sample-consistency
arguments. -/
theorem filled_mem_support_sample
    {K : Finset (Word α)}
    {S : FiniteLearnerSupport α}
    (hS : S.sample = K)
    (R : RawSampleDecomposition (α := α) K) :
    namedFill R.d R.context R.tuple ∈ S.sample := by
  simpa [hS] using R.filled_mem_sample

/-- The recorded sample word of a raw decomposition belongs to any support whose
sample is `K`. -/
theorem sampleWord_mem_support_sample
    {K : Finset (Word α)}
    {S : FiniteLearnerSupport α}
    (hS : S.sample = K)
    (R : RawSampleDecomposition (α := α) K) :
    R.sampleWord ∈ S.sample := by
  simpa [hS] using R.sampleWord_mem

/-- The recorded sample word is the filled word, with the equality oriented for
rewriting from the sample word to `namedFill`. -/
theorem sampleWord_eq_filled
    {K : Finset (Word α)}
    (R : RawSampleDecomposition (α := α) K) :
    R.sampleWord = namedFill R.d R.context R.tuple := by
  exact R.filled_eq.symm

end RawSampleDecomposition

namespace RawSampleUnitEdgeWitness

/-- The source side of a raw unit-edge witness is licensed by the sample
named-distribution. -/
theorem src_context_mem_sampleDistribution
    {K : Finset (Word α)} {obs : α → M} {f : Nat}
    (E : RawSampleUnitEdgeWitness (α := α) K obs f) :
    E.context ∈ SampleNamedDistribution K E.src := by
  exact E.src_mem

/-- The target side of a raw unit-edge witness is licensed by the sample
named-distribution. -/
theorem tgt_context_mem_sampleDistribution
    {K : Finset (Word α)} {obs : α → M} {f : Nat}
    (E : RawSampleUnitEdgeWitness (α := α) K obs f) :
    E.context ∈ SampleNamedDistribution K E.tgt := by
  exact E.tgt_mem

/-- The source filled word belongs to any support whose sample is `K`. -/
theorem src_mem_support_sample
    {K : Finset (Word α)} {obs : α → M} {f : Nat}
    {S : FiniteLearnerSupport α}
    (hS : S.sample = K)
    (E : RawSampleUnitEdgeWitness (α := α) K obs f) :
    namedFill E.d E.context E.src ∈ S.sample := by
  simpa [hS] using E.src_mem

/-- The target filled word belongs to any support whose sample is `K`. -/
theorem tgt_mem_support_sample
    {K : Finset (Word α)} {obs : α → M} {f : Nat}
    {S : FiniteLearnerSupport α}
    (hS : S.sample = K)
    (E : RawSampleUnitEdgeWitness (α := α) K obs f) :
    namedFill E.d E.context E.tgt ∈ S.sample := by
  simpa [hS] using E.tgt_mem

/-- Source and target have the same fixed observation type. -/
theorem same_type
    {K : Finset (Word α)} {obs : α → M} {f : Nat}
    (E : RawSampleUnitEdgeWitness (α := α) K obs f) :
    tupleType obs E.src = tupleType obs E.tgt := by
  exact E.type_eq

end RawSampleUnitEdgeWitness

namespace RawSampleDecompositionData

/-- Raw decomposition data automatically generates its support facts. -/
theorem generatedSupport
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (D : RawSampleDecompositionData G obs K) :
    RawSampleGeneratedSupport D := by
  refine
    { decomposition_supported := ?_
      decomposition_sample_licensed := ?_
      unitEdge_supported := ?_
      unitEdge_safe := ?_ }
  · intro R hR
    exact ⟨D.supportsTuple_of_decomposition_mem hR,
      D.supportsContext_of_decomposition_mem hR⟩
  · intro R _hR
    exact R.context_mem_sampleDistribution
  · intro E hE
    exact D.supportsUnitEdge_of_witness_mem hE
  · intro E _hE
    exact E.sampleSafeMerge

/-- A listed raw decomposition generates a supported tuple and a supported
context. -/
theorem decomposition_supported
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (D : RawSampleDecompositionData G obs K)
    {R : RawSampleDecomposition (α := α) K}
    (hR : R ∈ D.decompositions) :
    D.support.SupportsTuple R.tuple ∧
      D.support.SupportsContext R.context := by
  exact D.generatedSupport.decomposition_supported R hR

/-- A listed raw decomposition is licensed by the finite sample distribution. -/
theorem decomposition_sample_licensed
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (D : RawSampleDecompositionData G obs K)
    {R : RawSampleDecomposition (α := α) K}
    (hR : R ∈ D.decompositions) :
    R.context ∈ SampleNamedDistribution K R.tuple := by
  exact D.generatedSupport.decomposition_sample_licensed R hR

/-- The filled word of a listed raw decomposition belongs to the support sample. -/
theorem decomposition_filled_mem_support_sample
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (D : RawSampleDecompositionData G obs K)
    {R : RawSampleDecomposition (α := α) K}
    (_hR : R ∈ D.decompositions) :
    namedFill R.d R.context R.tuple ∈ D.support.sample := by
  exact RawSampleDecomposition.filled_mem_support_sample D.support_sample_eq R

/-- The recorded sample word of a listed raw decomposition belongs to the
support sample. -/
theorem decomposition_sampleWord_mem_support_sample
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (D : RawSampleDecompositionData G obs K)
    {R : RawSampleDecomposition (α := α) K}
    (_hR : R ∈ D.decompositions) :
    R.sampleWord ∈ D.support.sample := by
  exact RawSampleDecomposition.sampleWord_mem_support_sample D.support_sample_eq R

/-- A listed raw unit-edge witness generates a supported edge and a sample-safe
merge. -/
theorem unitEdge_supported_and_safe
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (D : RawSampleDecompositionData G obs K)
    {E : RawSampleUnitEdgeWitness (α := α) K obs D.f}
    (hE : E ∈ D.unitEdgeWitnesses) :
    D.support.SupportsUnitEdge E.src E.tgt ∧
      SampleSafeMerge K obs E.src E.tgt := by
  exact ⟨D.supportsUnitEdge_of_witness_mem hE, E.sampleSafeMerge⟩

/-- A listed raw unit-edge witness gives reachability in the induced
sample-extracted finite hypothesis. -/
theorem unitEdge_reaches_in_sampleExtractedRuleLists
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (D : RawSampleDecompositionData G obs K)
    {E : RawSampleUnitEdgeWitness (α := α) K obs D.f}
    (hE : E ∈ D.unitEdgeWitnesses) :
    D.toSampleExtractedRuleLists.UnitReach E.src E.tgt := by
  exact D.toSampleExtractedRuleLists.listedEdge_reach
    (D.supportsUnitEdge_of_witness_mem hE)

/-- The source filled word of a listed unit-edge witness belongs to the support
sample. -/
theorem unitEdge_src_mem_support_sample
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (D : RawSampleDecompositionData G obs K)
    {E : RawSampleUnitEdgeWitness (α := α) K obs D.f}
    (_hE : E ∈ D.unitEdgeWitnesses) :
    namedFill E.d E.context E.src ∈ D.support.sample := by
  exact RawSampleUnitEdgeWitness.src_mem_support_sample D.support_sample_eq E

/-- The target filled word of a listed unit-edge witness belongs to the support
sample. -/
theorem unitEdge_tgt_mem_support_sample
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (D : RawSampleDecompositionData G obs K)
    {E : RawSampleUnitEdgeWitness (α := α) K obs D.f}
    (_hE : E ∈ D.unitEdgeWitnesses) :
    namedFill E.d E.context E.tgt ∈ D.support.sample := by
  exact RawSampleUnitEdgeWitness.tgt_mem_support_sample D.support_sample_eq E

end RawSampleDecompositionData

end RawSampleDecompositionGeneration

end FIv21
