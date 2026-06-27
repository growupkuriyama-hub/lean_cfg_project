import LeanCfgProject.MCFG.FI_v2_1_SubwordContextEnumeration

/-!
# FI v2.1 Lean experiment: exactness wrapper for subword-context enumeration

This layer records that the concrete enumerated subword-context data can be used
where the previous subword-context exactness interface was expected.  The new
content exposed here is the support theorem for the enumerated list: every word
of the finite sample has a listed and supported whole-word representative, while
additional generated subword cuts are also carried by the same support pipeline.
-/

namespace FIv21

universe u v w

section SubwordContextEnumerationExact

variable {N : Type w} {α : Type u}
variable [DecidableEq α]
variable {M : Type v} [Monoid M] [Fintype M]

/-- Exactness package for enumerated subword-context data. -/
structure SubwordContextEnumerationExactForLanguage
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (D : SubwordContextDecompositionData G obs K) (L : Set (Word α)) where
  base : SubwordContextDecompositionExactForLanguage D L

namespace SubwordContextEnumerationExactForLanguage

/-- Forget to the previous subword-context exactness interface. -/
def toSubwordExact
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {D : SubwordContextDecompositionData G obs K} {L : Set (Word α)}
    (C : SubwordContextEnumerationExactForLanguage D L) :
    SubwordContextDecompositionExactForLanguage D L :=
  C.base

/-- Forget further to raw-decomposition exactness. -/
noncomputable def toRawExact
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {D : SubwordContextDecompositionData G obs K} {L : Set (Word α)}
    (C : SubwordContextEnumerationExactForLanguage D L) :
    RawSampleDecompositionExactForLanguage D.toRawSampleDecompositionData L :=
  C.base.toRawExact

/-- Listed generated subword decompositions support their tuple. -/
theorem supportsTuple_of_subword_mem
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {D : SubwordContextDecompositionData G obs K} {L : Set (Word α)}
    (_C : SubwordContextEnumerationExactForLanguage D L)
    {S : SubwordSampleDecomposition (α := α) K}
    (hS : S ∈ D.subwordDecompositions) :
    D.support.SupportsTuple S.tuple := by
  exact D.supportsTuple_of_subword_mem hS

/-- Listed generated subword decompositions support their context. -/
theorem supportsContext_of_subword_mem
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {D : SubwordContextDecompositionData G obs K} {L : Set (Word α)}
    (_C : SubwordContextEnumerationExactForLanguage D L)
    {S : SubwordSampleDecomposition (α := α) K}
    (hS : S ∈ D.subwordDecompositions) :
    D.support.SupportsContext S.context := by
  exact D.supportsContext_of_subword_mem hS

/-- Listed generated subword decompositions are licensed by the sample
distribution. -/
theorem subword_context_mem_sampleDistribution
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {D : SubwordContextDecompositionData G obs K} {L : Set (Word α)}
    (_C : SubwordContextEnumerationExactForLanguage D L)
    {S : SubwordSampleDecomposition (α := α) K}
    (hS : S ∈ D.subwordDecompositions) :
    S.context ∈ SampleNamedDistribution K S.tuple := by
  exact D.subword_context_mem_sampleDistribution hS

/-- Enumeration exactness is compatible with the theorem that every sampled word
has a supported enumerated representative. -/
theorem enumerated_supported_sample_word_exact
    (G : WorkingMCFG N α) (obs : α → M) (K : Finset (Word α))
    (f : Nat) (hG : G.SemanticWorkingConditions)
    {L : Set (Word α)}
    (_C : SubwordContextEnumerationExactForLanguage
      (enumeratedSubwordContextDecompositionData G obs K f hG) L)
    {w : Word α} (hw : w ∈ K) :
    ∃ S : SubwordSampleDecomposition (α := α) K,
      S ∈ (enumeratedSubwordContextDecompositionData G obs K f hG).subwordDecompositions ∧
      S.sampleWord = w ∧
      (enumeratedSubwordContextDecompositionData G obs K f hG).support.SupportsTuple S.tuple ∧
      (enumeratedSubwordContextDecompositionData G obs K f hG).support.SupportsContext S.context ∧
      S.context ∈ SampleNamedDistribution K S.tuple := by
  exact enumeratedSubwordContextDecompositionData_supported_sample_word G obs K f hG hw

end SubwordContextEnumerationExactForLanguage

/-- Grammar-target exactness abbreviation for subword-context enumeration data. -/
abbrev SubwordContextEnumerationExactForGrammar
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (D : SubwordContextDecompositionData G obs K) :=
  SubwordContextEnumerationExactForLanguage D G.StringLanguage

end SubwordContextEnumerationExact

end FIv21
