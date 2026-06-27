import LeanCfgProject.MCFG.FI_v2_1_RawSampleDecompositionExact

/-!
# FI v2.1 Lean experiment: Gold wrapper for raw sample decompositions

This file packages learners that return raw sample-decomposition data.  The
learner now returns explicit decomposition witnesses `namedFill d c x ∈ K`,
rather than merely arbitrary atom lists.
-/

namespace FIv21

universe u v w

section RawSampleDecompositionGold

variable {N : Type w} {α : Type u}
variable [DecidableEq α]
variable {M : Type v} [Monoid M] [Fintype M]

/-- A learner mapping each finite sample to raw decomposition data. -/
abbrev RawSampleDecompositionLearner
    (G : WorkingMCFG N α) (obs : α → M) :=
  (K : Finset (Word α)) → RawSampleDecompositionData G obs K

/-- Forget a raw-decomposition learner to the observed-atom learner interface. -/
noncomputable def RawSampleDecompositionLearner.toObservedSampleAtomsLearner
    {G : WorkingMCFG N α} {obs : α → M}
    (A : RawSampleDecompositionLearner G obs) :
    ObservedSampleAtomsLearner G obs :=
  fun K => (A K).toObservedSampleAtoms

/-- Forget a raw-decomposition learner to the sample-extracted rule-list learner. -/
noncomputable def RawSampleDecompositionLearner.toSampleExtractedRuleListLearner
    {G : WorkingMCFG N α} {obs : α → M}
    (A : RawSampleDecompositionLearner G obs) :
    SampleExtractedRuleListLearner G obs :=
  A.toObservedSampleAtomsLearner.toSampleExtractedRuleListLearner

/-- Forget a raw-decomposition learner to the finite-hypothesis learner. -/
noncomputable def RawSampleDecompositionLearner.toFiniteHypothesisLearner
    {G : WorkingMCFG N α} {obs : α → M}
    (A : RawSampleDecompositionLearner G obs) :
    FiniteHypothesisLearner α M :=
  A.toObservedSampleAtomsLearner.toFiniteHypothesisLearner

/-- Characteristic sample certificate for a raw-decomposition learner. -/
structure RawSampleDecompositionCharacteristicSample
    {G : WorkingMCFG N α} {obs : α → M}
    (A : RawSampleDecompositionLearner G obs) (L : Set (Word α)) where
  sample : Finset (Word α)
  positive : PositiveForLanguage sample L
  exact_after_extending :
    ∀ K : Finset (Word α),
      SampleExtends sample K →
      PositiveForLanguage K L →
        RawSampleDecompositionExactForLanguage (A K) L

namespace RawSampleDecompositionCharacteristicSample

/-- Forget to the observed-atom characteristic-sample interface. -/
noncomputable def toObservedSampleAtomsCharacteristicSample
    {G : WorkingMCFG N α} {obs : α → M}
    {A : RawSampleDecompositionLearner G obs} {L : Set (Word α)}
    (C : RawSampleDecompositionCharacteristicSample A L) :
    ObservedSampleAtomsCharacteristicSample
      A.toObservedSampleAtomsLearner L :=
  { sample := C.sample
    positive := C.positive
    exact_after_extending := by
      intro K hExt hPos
      exact (C.exact_after_extending K hExt hPos).observedExact }

/-- Forget to the sample-extracted rule-list characteristic-sample interface. -/
noncomputable def toSampleExtractedRuleListCharacteristicSample
    {G : WorkingMCFG N α} {obs : α → M}
    {A : RawSampleDecompositionLearner G obs} {L : Set (Word α)}
    (C : RawSampleDecompositionCharacteristicSample A L) :
    SampleExtractedRuleListCharacteristicSample
      A.toSampleExtractedRuleListLearner L :=
  C.toObservedSampleAtomsCharacteristicSample.toSampleExtractedRuleListCharacteristicSample

/-- Raw-decomposition characteristic samples identify the target at the
transported-context distribution level. -/
theorem identifiesInLimit
    {G : WorkingMCFG N α} {obs : α → M}
    {A : RawSampleDecompositionLearner G obs} {L : Set (Word α)}
    (C : RawSampleDecompositionCharacteristicSample A L) :
    FiniteHypothesisIdentifiesInLimit A.toFiniteHypothesisLearner L := by
  exact ObservedSampleAtomsCharacteristicSample.identifiesInLimit
    C.toObservedSampleAtomsCharacteristicSample

/-- Pointwise context-membership form of limiting identification. -/
theorem eventuallyCorrectContexts
    {G : WorkingMCFG N α} {obs : α → M}
    {A : RawSampleDecompositionLearner G obs} {L : Set (Word α)}
    (C : RawSampleDecompositionCharacteristicSample A L) :
    FiniteHypothesisEventuallyCorrectContexts A.toFiniteHypothesisLearner L := by
  exact ObservedSampleAtomsCharacteristicSample.eventuallyCorrectContexts
    C.toObservedSampleAtomsCharacteristicSample

/-- After the threshold, the finite support is assembled from raw decomposition
and raw unit-edge witness lists. -/
theorem support_eq_rawDecompositions_after
    {G : WorkingMCFG N α} {obs : α → M}
    {A : RawSampleDecompositionLearner G obs} {L : Set (Word α)}
    (C : RawSampleDecompositionCharacteristicSample A L)
    {K : Finset (Word α)}
    (hExt : SampleExtends C.sample K)
    (hPos : PositiveForLanguage K L) :
    (A K).support = supportOfObservedAtoms K
      (A K).tupleAtoms (A K).contextAtoms (A K).unitEdgeAtoms := by
  exact (C.exact_after_extending K hExt hPos).support_eq_rawDecompositions

/-- After the threshold, listed raw decompositions provide supported tuples. -/
theorem supportsTuple_of_decomposition_mem_after
    {G : WorkingMCFG N α} {obs : α → M}
    {A : RawSampleDecompositionLearner G obs} {L : Set (Word α)}
    (C : RawSampleDecompositionCharacteristicSample A L)
    {K : Finset (Word α)}
    (hExt : SampleExtends C.sample K)
    (hPos : PositiveForLanguage K L)
    {R : RawSampleDecomposition (α := α) K}
    (hR : R ∈ (A K).decompositions) :
    (A K).support.SupportsTuple R.tuple := by
  exact (C.exact_after_extending K hExt hPos).supportsTuple_of_decomposition_mem hR

/-- After the threshold, listed raw decompositions provide supported contexts. -/
theorem supportsContext_of_decomposition_mem_after
    {G : WorkingMCFG N α} {obs : α → M}
    {A : RawSampleDecompositionLearner G obs} {L : Set (Word α)}
    (C : RawSampleDecompositionCharacteristicSample A L)
    {K : Finset (Word α)}
    (hExt : SampleExtends C.sample K)
    (hPos : PositiveForLanguage K L)
    {R : RawSampleDecomposition (α := α) K}
    (hR : R ∈ (A K).decompositions) :
    (A K).support.SupportsContext R.context := by
  exact (C.exact_after_extending K hExt hPos).supportsContext_of_decomposition_mem hR

/-- After the threshold, listed unit-edge witnesses provide supported unit
edges. -/
theorem supportsUnitEdge_of_witness_mem_after
    {G : WorkingMCFG N α} {obs : α → M}
    {A : RawSampleDecompositionLearner G obs} {L : Set (Word α)}
    (C : RawSampleDecompositionCharacteristicSample A L)
    {K : Finset (Word α)}
    (hExt : SampleExtends C.sample K)
    (hPos : PositiveForLanguage K L)
    {E : RawSampleUnitEdgeWitness (α := α) K obs (A K).f}
    (hE : E ∈ (A K).unitEdgeWitnesses) :
    (A K).support.SupportsUnitEdge E.src E.tgt := by
  exact (C.exact_after_extending K hExt hPos).supportsUnitEdge_of_witness_mem hE

/-- After the threshold, a listed raw unit-edge witness gives a sample-safe
merge. -/
theorem witness_sampleSafeMerge_after
    {G : WorkingMCFG N α} {obs : α → M}
    {A : RawSampleDecompositionLearner G obs} {L : Set (Word α)}
    (C : RawSampleDecompositionCharacteristicSample A L)
    {K : Finset (Word α)}
    (hExt : SampleExtends C.sample K)
    (hPos : PositiveForLanguage K L)
    {E : RawSampleUnitEdgeWitness (α := α) K obs (A K).f}
    (hE : E ∈ (A K).unitEdgeWitnesses) :
    SampleSafeMerge K obs E.src E.tgt := by
  exact (C.exact_after_extending K hExt hPos).witness_sampleSafeMerge hE

/-- After the threshold, exactness of transported distributions holds. -/
theorem approxDistribution_exact_after
    {G : WorkingMCFG N α} {obs : α → M}
    {A : RawSampleDecompositionLearner G obs} {L : Set (Word α)}
    (C : RawSampleDecompositionCharacteristicSample A L)
    {K : Finset (Word α)}
    (hExt : SampleExtends C.sample K)
    (hPos : PositiveForLanguage K L)
    {d : Nat} (x : Tuple α d) :
    (A K).ApproxDistribution x = NamedDistribution L x := by
  exact (C.exact_after_extending K hExt hPos).approxDistribution_exact x

end RawSampleDecompositionCharacteristicSample

/-- Grammar-target characteristic sample abbreviation. -/
abbrev GrammarRawSampleDecompositionCharacteristicSample
    {G : WorkingMCFG N α} {obs : α → M}
    (A : RawSampleDecompositionLearner G obs) :=
  RawSampleDecompositionCharacteristicSample A G.StringLanguage

end RawSampleDecompositionGold

end FIv21
