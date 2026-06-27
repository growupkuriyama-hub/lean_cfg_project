import LeanCfgProject.MCFG.FI_v2_1_CanonicalLearnerNonterminalExact

/-!
# FI v2.1 Lean experiment: Gold wrapper for canonical learner nonterminals

This layer packages learners returning subword-unit-edge enumeration data with
an explicit finite canonical-nonterminal list.  It is still not the full learner
grammar, but the nonterminal universe for the learner-to-be is now generated
from the finite sample data rather than postulated externally.
-/

namespace FIv21

universe u v w

section CanonicalLearnerNonterminalGold

variable {N : Type w} {α : Type u}
variable [DecidableEq α]
variable {M : Type v} [Monoid M] [Fintype M]

/-- A learner that returns data from which canonical learner nonterminals are
generated. -/
abbrev CanonicalLearnerNonterminalLearner
    (G : WorkingMCFG N α) (obs : α → M) :=
  SubwordUnitEdgeEnumerationLearner G obs

namespace CanonicalLearnerNonterminalLearner

/-- Forget to the previous subword-unit-edge learner. -/
def toSubwordUnitEdgeEnumerationLearner
    {G : WorkingMCFG N α} {obs : α → M}
    (A : CanonicalLearnerNonterminalLearner G obs) :
    SubwordUnitEdgeEnumerationLearner G obs :=
  A

/-- The finite nonterminal list returned at a sample. -/
noncomputable def nonterminals
    {G : WorkingMCFG N α} {obs : α → M}
    (A : CanonicalLearnerNonterminalLearner G obs)
    (K : Finset (Word α)) : List (CanonicalLearnerNonterminal α M) :=
  (A K).learnerNonterminals

/-- Forget to the finite-hypothesis learner. -/
noncomputable def toFiniteHypothesisLearner
    {G : WorkingMCFG N α} {obs : α → M}
    (A : CanonicalLearnerNonterminalLearner G obs) :
    FiniteHypothesisLearner α M :=
  A.toSubwordUnitEdgeEnumerationLearner.toFiniteHypothesisLearner

end CanonicalLearnerNonterminalLearner

/-- Characteristic sample certificate for the canonical-nonterminal layer. -/
structure CanonicalLearnerNonterminalCharacteristicSample
    {G : WorkingMCFG N α} {obs : α → M}
    (A : CanonicalLearnerNonterminalLearner G obs) (L : Set (Word α)) where
  sample : Finset (Word α)
  positive : PositiveForLanguage sample L
  exact_after_extending :
    ∀ K : Finset (Word α),
      SampleExtends sample K →
      PositiveForLanguage K L →
        CanonicalLearnerNonterminalExactForLanguage (A K) L

namespace CanonicalLearnerNonterminalCharacteristicSample

/-- Forget to the subword-unit-edge characteristic-sample interface. -/
noncomputable def toSubwordUnitEdgeEnumerationCharacteristicSample
    {G : WorkingMCFG N α} {obs : α → M}
    {A : CanonicalLearnerNonterminalLearner G obs} {L : Set (Word α)}
    (C : CanonicalLearnerNonterminalCharacteristicSample A L) :
    SubwordUnitEdgeEnumerationCharacteristicSample
      A.toSubwordUnitEdgeEnumerationLearner L :=
  { sample := C.sample
    positive := C.positive
    exact_after_extending := by
      intro K hExt hPos
      exact (C.exact_after_extending K hExt hPos).toSubwordUnitEdgeExact }

/-- The canonical-nonterminal characteristic-sample layer still identifies the
target at the finite-hypothesis distribution level. -/
theorem identifiesInLimit
    {G : WorkingMCFG N α} {obs : α → M}
    {A : CanonicalLearnerNonterminalLearner G obs} {L : Set (Word α)}
    (C : CanonicalLearnerNonterminalCharacteristicSample A L) :
    FiniteHypothesisIdentifiesInLimit A.toFiniteHypothesisLearner L := by
  exact C.toSubwordUnitEdgeEnumerationCharacteristicSample.identifiesInLimit

/-- Pointwise context-membership form of limiting identification. -/
theorem eventuallyCorrectContexts
    {G : WorkingMCFG N α} {obs : α → M}
    {A : CanonicalLearnerNonterminalLearner G obs} {L : Set (Word α)}
    (C : CanonicalLearnerNonterminalCharacteristicSample A L) :
    FiniteHypothesisEventuallyCorrectContexts A.toFiniteHypothesisLearner L := by
  exact C.toSubwordUnitEdgeEnumerationCharacteristicSample.eventuallyCorrectContexts

/-- After the threshold, listed subword decompositions still generate tuple,
context, and typed nonterminals. -/
theorem nonterminals_of_subword_mem_after
    {G : WorkingMCFG N α} {obs : α → M}
    {A : CanonicalLearnerNonterminalLearner G obs} {L : Set (Word α)}
    (C : CanonicalLearnerNonterminalCharacteristicSample A L)
    {K : Finset (Word α)}
    (hExt : SampleExtends C.sample K)
    (hPos : PositiveForLanguage K L)
    {S : SubwordSampleDecomposition (α := α) K}
    (hS : S ∈ (A K).subwordDecompositions) :
    CanonicalLearnerNonterminal.tuple 1 S.tuple ∈ (A K).learnerNonterminals ∧
    CanonicalLearnerNonterminal.context 1 S.context ∈ (A K).learnerNonterminals ∧
    CanonicalLearnerNonterminal.typed 1 (tupleType obs S.tuple) ∈ (A K).learnerNonterminals := by
  have Cexact := C.exact_after_extending K hExt hPos
  exact ⟨Cexact.tupleNonterminal_mem_of_subword_mem hS,
    Cexact.contextNonterminal_mem_of_subword_mem hS,
    Cexact.typedNonterminal_mem_of_subword_mem hS⟩

/-- For the concrete enumerated learner, every sampled word is represented by
listed finite nonterminals after the threshold. -/
theorem enumerated_sample_word_nonterminals_after
    {G : WorkingMCFG N α} {obs : α → M} {L : Set (Word α)}
    {f : Nat} {hfanout : 1 ≤ f} {hG : G.SemanticWorkingConditions}
    (C : CanonicalLearnerNonterminalCharacteristicSample
      (enumeratedSubwordUnitEdgeEnumerationLearner G obs f hfanout hG) L)
    {K : Finset (Word α)}
    (hExt : SampleExtends C.sample K)
    (hPos : PositiveForLanguage K L)
    {w : Word α} (hw : w ∈ K) :
    ∃ S : SubwordSampleDecomposition (α := α) K,
      S ∈ ((enumeratedSubwordUnitEdgeEnumerationLearner G obs f hfanout hG) K).subwordDecompositions ∧
      S.sampleWord = w ∧
      CanonicalLearnerNonterminal.tuple 1 S.tuple ∈
        ((enumeratedSubwordUnitEdgeEnumerationLearner G obs f hfanout hG) K).learnerNonterminals ∧
      CanonicalLearnerNonterminal.context 1 S.context ∈
        ((enumeratedSubwordUnitEdgeEnumerationLearner G obs f hfanout hG) K).learnerNonterminals ∧
      CanonicalLearnerNonterminal.typed 1 (tupleType obs S.tuple) ∈
        ((enumeratedSubwordUnitEdgeEnumerationLearner G obs f hfanout hG) K).learnerNonterminals := by
  exact (C.exact_after_extending K hExt hPos).enumerated_sample_word_nonterminals_exact
    G obs K f hfanout hG hw

end CanonicalLearnerNonterminalCharacteristicSample

/-- Grammar-target characteristic-sample abbreviation. -/
abbrev GrammarCanonicalLearnerNonterminalCharacteristicSample
    {G : WorkingMCFG N α} {obs : α → M}
    (A : CanonicalLearnerNonterminalLearner G obs) :=
  CanonicalLearnerNonterminalCharacteristicSample A G.StringLanguage

/-- Grammar-target abbreviation for the concrete enumerated learner. -/
abbrev GrammarEnumeratedCanonicalLearnerNonterminalCharacteristicSample
    {G : WorkingMCFG N α} {obs : α → M}
    (f : Nat) (hfanout : 1 ≤ f) (hG : G.SemanticWorkingConditions) :=
  CanonicalLearnerNonterminalCharacteristicSample
    (enumeratedSubwordUnitEdgeEnumerationLearner G obs f hfanout hG) G.StringLanguage

end CanonicalLearnerNonterminalGold

end FIv21
