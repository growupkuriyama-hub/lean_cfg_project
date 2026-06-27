import LeanCfgProject.MCFG.FI_v2_1_SubwordUnitEdgeEnumeration

/-!
# FI v2.1 Lean experiment: exactness wrapper for subword unit-edge enumeration

This layer records that subword-unit-edge enumeration data can be used wherever
subword-context enumeration data was expected.  The new exactness-facing fact is
that filtered same-context/same-type subword pairs provide unit reachability in
the induced finite hypothesis.
-/

namespace FIv21

universe u v w

section SubwordUnitEdgeEnumerationExact

variable {N : Type w} {α : Type u}
variable [DecidableEq α]
variable {M : Type v} [Monoid M] [Fintype M]

/-- Exactness package for subword-unit-edge enumeration data. -/
structure SubwordUnitEdgeEnumerationExactForLanguage
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (D : SubwordUnitEdgeEnumerationData G obs K) (L : Set (Word α)) where
  base : SubwordContextEnumerationExactForLanguage D.toSubwordContextDecompositionData L

namespace SubwordUnitEdgeEnumerationExactForLanguage

/-- Forget to subword-context enumeration exactness. -/
def toSubwordContextEnumerationExact
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {D : SubwordUnitEdgeEnumerationData G obs K} {L : Set (Word α)}
    (C : SubwordUnitEdgeEnumerationExactForLanguage D L) :
    SubwordContextEnumerationExactForLanguage D.toSubwordContextDecompositionData L :=
  C.base

/-- Forget further to subword-context decomposition exactness. -/
def toSubwordContextDecompositionExact
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {D : SubwordUnitEdgeEnumerationData G obs K} {L : Set (Word α)}
    (C : SubwordUnitEdgeEnumerationExactForLanguage D L) :
    SubwordContextDecompositionExactForLanguage D.toSubwordContextDecompositionData L :=
  C.base.toSubwordExact

/-- Exactness keeps the support fact for listed subword decompositions. -/
theorem supportsTuple_of_subword_mem
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {D : SubwordUnitEdgeEnumerationData G obs K} {L : Set (Word α)}
    (_C : SubwordUnitEdgeEnumerationExactForLanguage D L)
    {S : SubwordSampleDecomposition (α := α) K}
    (hS : S ∈ D.subwordDecompositions) :
    D.support.SupportsTuple S.tuple := by
  exact D.supportsTuple_of_subword_mem hS

/-- Exactness keeps the sample-distribution license for listed subword
contexts. -/
theorem subword_context_mem_sampleDistribution
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {D : SubwordUnitEdgeEnumerationData G obs K} {L : Set (Word α)}
    (_C : SubwordUnitEdgeEnumerationExactForLanguage D L)
    {S : SubwordSampleDecomposition (α := α) K}
    (hS : S ∈ D.subwordDecompositions) :
    S.context ∈ SampleNamedDistribution K S.tuple := by
  exact D.subword_context_mem_sampleDistribution hS

/-- Filtered same-context/same-type pairs give unit reachability in the exact
package. -/
theorem typedPair_unitReach
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {D : SubwordUnitEdgeEnumerationData G obs K} {L : Set (Word α)}
    (_C : SubwordUnitEdgeEnumerationExactForLanguage D L)
    {P : SubwordDecompositionPair (α := α) K}
    (hP : P ∈ typedSameContextSubwordPairs (α := α) obs D.subwordDecompositions) :
    D.toSubwordContextDecompositionData.toSampleExtractedRuleLists.UnitReach
      P.src.tuple P.tgt.tuple := by
  exact D.typedPair_unitReach hP

/-- The concrete enumerated unit-edge data still represents every sampled word
by a supported enumerated subword decomposition. -/
theorem enumerated_supported_sample_word_exact
    (G : WorkingMCFG N α) (obs : α → M) (K : Finset (Word α))
    (f : Nat) (hfanout : 1 ≤ f) (hG : G.SemanticWorkingConditions)
    {L : Set (Word α)}
    (_C : SubwordUnitEdgeEnumerationExactForLanguage
      (enumeratedSubwordUnitEdgeEnumerationData G obs K f hfanout hG) L)
    {w : Word α} (hw : w ∈ K) :
    ∃ S : SubwordSampleDecomposition (α := α) K,
      S ∈ (enumeratedSubwordUnitEdgeEnumerationData G obs K f hfanout hG).subwordDecompositions ∧
      S.sampleWord = w ∧
      (enumeratedSubwordUnitEdgeEnumerationData G obs K f hfanout hG).support.SupportsTuple S.tuple ∧
      (enumeratedSubwordUnitEdgeEnumerationData G obs K f hfanout hG).support.SupportsContext S.context ∧
      S.context ∈ SampleNamedDistribution K S.tuple := by
  exact enumeratedSubwordUnitEdgeEnumerationData_supported_sample_word G obs K f hfanout hG hw

end SubwordUnitEdgeEnumerationExactForLanguage

/-- Grammar-target exactness abbreviation for subword-unit-edge enumeration. -/
abbrev SubwordUnitEdgeEnumerationExactForGrammar
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (D : SubwordUnitEdgeEnumerationData G obs K) :=
  SubwordUnitEdgeEnumerationExactForLanguage D G.StringLanguage

end SubwordUnitEdgeEnumerationExact

end FIv21
