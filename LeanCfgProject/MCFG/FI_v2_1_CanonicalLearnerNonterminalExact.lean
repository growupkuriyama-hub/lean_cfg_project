import LeanCfgProject.MCFG.FI_v2_1_CanonicalLearnerNonterminal

/-!
# FI v2.1 Lean experiment: exactness wrapper for canonical learner nonterminals

The preceding file introduced a concrete nonterminal universe and finite
nonterminal lists generated from sample support.  This file records that the
exactness packages built earlier preserve those generated nonterminal facts.
-/

namespace FIv21

universe u v w

section CanonicalLearnerNonterminalExact

variable {N : Type w} {α : Type u}
variable [DecidableEq α]
variable {M : Type v} [Monoid M] [Fintype M]

/-- Exactness package plus the generated canonical nonterminal list. -/
structure CanonicalLearnerNonterminalExactForLanguage
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (D : SubwordUnitEdgeEnumerationData G obs K) (L : Set (Word α)) where
  base : SubwordUnitEdgeEnumerationExactForLanguage D L

namespace CanonicalLearnerNonterminalExactForLanguage

/-- Forget to the subword-unit-edge exactness layer. -/
def toSubwordUnitEdgeExact
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {D : SubwordUnitEdgeEnumerationData G obs K} {L : Set (Word α)}
    (C : CanonicalLearnerNonterminalExactForLanguage D L) :
    SubwordUnitEdgeEnumerationExactForLanguage D L :=
  C.base

/-- Listed subword decompositions still produce tuple nonterminals. -/
theorem tupleNonterminal_mem_of_subword_mem
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {D : SubwordUnitEdgeEnumerationData G obs K} {L : Set (Word α)}
    (_C : CanonicalLearnerNonterminalExactForLanguage D L)
    {S : SubwordSampleDecomposition (α := α) K}
    (hS : S ∈ D.subwordDecompositions) :
    CanonicalLearnerNonterminal.tuple 1 S.tuple ∈ D.learnerNonterminals := by
  exact D.tupleNonterminal_mem_of_subword_mem hS

/-- Listed subword decompositions still produce context nonterminals. -/
theorem contextNonterminal_mem_of_subword_mem
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {D : SubwordUnitEdgeEnumerationData G obs K} {L : Set (Word α)}
    (_C : CanonicalLearnerNonterminalExactForLanguage D L)
    {S : SubwordSampleDecomposition (α := α) K}
    (hS : S ∈ D.subwordDecompositions) :
    CanonicalLearnerNonterminal.context 1 S.context ∈ D.learnerNonterminals := by
  exact D.contextNonterminal_mem_of_subword_mem hS

/-- Listed subword decompositions still produce typed nonterminals. -/
theorem typedNonterminal_mem_of_subword_mem
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {D : SubwordUnitEdgeEnumerationData G obs K} {L : Set (Word α)}
    (_C : CanonicalLearnerNonterminalExactForLanguage D L)
    {S : SubwordSampleDecomposition (α := α) K}
    (hS : S ∈ D.subwordDecompositions) :
    CanonicalLearnerNonterminal.typed 1 (tupleType obs S.tuple) ∈
      D.learnerNonterminals := by
  exact D.typedNonterminal_mem_of_subword_mem hS

/-- For the concrete enumerated data, every sampled word gives the corresponding
finite learner nonterminals. -/
theorem enumerated_sample_word_nonterminals_exact
    (G : WorkingMCFG N α) (obs : α → M) (K : Finset (Word α))
    (f : Nat) (hfanout : 1 ≤ f) (hG : G.SemanticWorkingConditions)
    {L : Set (Word α)}
    (_C : CanonicalLearnerNonterminalExactForLanguage
      (enumeratedSubwordUnitEdgeEnumerationData G obs K f hfanout hG) L)
    {w : Word α} (hw : w ∈ K) :
    ∃ S : SubwordSampleDecomposition (α := α) K,
      S ∈ (enumeratedSubwordUnitEdgeEnumerationData G obs K f hfanout hG).subwordDecompositions ∧
      S.sampleWord = w ∧
      CanonicalLearnerNonterminal.tuple 1 S.tuple ∈
        (enumeratedSubwordUnitEdgeEnumerationData G obs K f hfanout hG).learnerNonterminals ∧
      CanonicalLearnerNonterminal.context 1 S.context ∈
        (enumeratedSubwordUnitEdgeEnumerationData G obs K f hfanout hG).learnerNonterminals ∧
      CanonicalLearnerNonterminal.typed 1 (tupleType obs S.tuple) ∈
        (enumeratedSubwordUnitEdgeEnumerationData G obs K f hfanout hG).learnerNonterminals := by
  exact SubwordUnitEdgeEnumerationData.enumerated_sample_word_nonterminals
    G obs K f hfanout hG hw

end CanonicalLearnerNonterminalExactForLanguage

/-- Grammar-target abbreviation. -/
abbrev CanonicalLearnerNonterminalExactForGrammar
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (D : SubwordUnitEdgeEnumerationData G obs K) :=
  CanonicalLearnerNonterminalExactForLanguage D G.StringLanguage

end CanonicalLearnerNonterminalExact

end FIv21
