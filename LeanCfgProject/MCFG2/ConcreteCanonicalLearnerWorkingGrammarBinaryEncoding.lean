/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG2.ConcreteCanonicalLearnerWorkingGrammarNaturalEncoding

/-!
# ConcreteCanonicalLearnerWorkingGrammarBinaryEncoding.lean

The preceding file encoded every top-level entry of the actual cut-compiled
`WorkingMCFG` by a natural number and bounded the resulting unary
serialization.  This file replaces the unary payload length by an ordinary
binary payload length.

For a natural-number code `n`, define

```lean
binaryNatCodeLength n = n.log2 + 1.
```

Thus zero is represented by one bit, and every nonzero code uses its usual
binary digit length.  The basic arithmetic lemma proved below is:

```lean
n < 2 ^ bitWidth
  -> binaryNatCodeLength n <= bitWidth + 1.
```

The extra one in the uniform bound handles the zero code without requiring a
positivity assumption on `bitWidth`.  Therefore, if every code occurring in a
compiled presentation lies below `2 ^ bitWidth`, then

```lean
E.binaryDescriptionSize dummy
  <= H.compiledGrammarPresentationItemCount * (bitWidth + 1).
```

The previously verified structural and paper-facing presentation-item bounds
are then lifted to explicit total binary-description bounds.

This file still treats the four entry-code functions as supplied data.  The
next construction layer may define concrete injective codes for compiled
nonterminals and rules and bound their values from the finite enumerations.

No target grammar is supplied to the learner.
No `sorry`, `admit`, or `axiom` is used.
-/

namespace MCFG

universe u v

section BinaryNaturalCodeLength

/-- Binary payload length of a natural-number code.  The code zero is assigned
one bit. -/
def binaryNatCodeLength
    (n : Nat) :
    Nat :=
  n.log2 + 1

/-- A code below `2 ^ bitWidth` has binary payload length at most
`bitWidth + 1`.  The slightly relaxed bound uniformly includes the zero code
and the degenerate width `0`. -/
theorem binaryNatCodeLength_le_succ_of_lt_two_pow
    {n bitWidth : Nat}
    (hcode : n < 2 ^ bitWidth) :
    binaryNatCodeLength n <= bitWidth + 1 := by

  by_cases hn : n = 0
  · subst n
    simp [binaryNatCodeLength]

  · have hlog :
        n.log2 < bitWidth :=
      (Nat.log2_lt hn).2 hcode

    have hlogLe :
        n.log2 <= bitWidth :=
      Nat.le_of_lt hlog

    exact
      Nat.add_le_add_right hlogLe 1

end BinaryNaturalCodeLength


section BinaryEncodingOfCompiledEntries

variable {α : Type u}
variable {M : Type v} [Monoid M]
variable {K : Finset (Word α)}
variable {obs : α -> M}
variable {f : Nat}
variable
  {H :
    CorrectedConcreteFiniteHypothesis
      K obs f}

namespace CorrectedConcreteCompiledGrammarNaturalEncoding

/-- Convert natural-number entry codes into the abstract entry-cost model using
binary payload length. -/
def toBinaryEntryCost
    (E :
      CorrectedConcreteCompiledGrammarNaturalEncoding H) :
    CorrectedConcreteCompiledGrammarEntryCost H where

  nonterminal := fun A =>
    binaryNatCodeLength (E.nonterminal A)

  startRule := fun ρ =>
    binaryNatCodeLength (E.startRule ρ)

  terminalRule := fun ρ =>
    binaryNatCodeLength (E.terminalRule ρ)

  binaryRule := fun ρ =>
    binaryNatCodeLength (E.binaryRule ρ)

/-- Total binary payload length of all explicit entries in the actual compiled
presentation. -/
def binaryDescriptionSize
    (E :
      CorrectedConcreteCompiledGrammarNaturalEncoding H)
    (dummy : α) :
    Nat :=
  E.toBinaryEntryCost.descriptionSize dummy

/-- Every natural-number code used in the compiled presentation fits below the
specified binary power. -/
def CodesFitInBits
    (E :
      CorrectedConcreteCompiledGrammarNaturalEncoding H)
    (dummy : α)
    (bitWidth : Nat) :
    Prop :=
  E.CodesBelow dummy (2 ^ bitWidth)

/-- A common binary-width bound gives the uniform per-entry cost needed by the
abstract description-size interface. -/
theorem toBinaryEntryCost_boundedBy_of_codesFitInBits
    (E :
      CorrectedConcreteCompiledGrammarNaturalEncoding H)
    (dummy : α)
    (bitWidth : Nat)
    (hE : E.CodesFitInBits dummy bitWidth) :
    E.toBinaryEntryCost.BoundedBy
      dummy (bitWidth + 1) := by

  rcases hE with
    ⟨hN, hS, hT, hB⟩

  refine ⟨?_, ?_, ?_, ?_⟩

  · intro A hA
    exact
      binaryNatCodeLength_le_succ_of_lt_two_pow
        (hN A hA)

  · intro ρ hρ
    exact
      binaryNatCodeLength_le_succ_of_lt_two_pow
        (hS ρ hρ)

  · intro ρ hρ
    exact
      binaryNatCodeLength_le_succ_of_lt_two_pow
        (hT ρ hρ)

  · intro ρ hρ
    exact
      binaryNatCodeLength_le_succ_of_lt_two_pow
        (hB ρ hρ)

/-- Total binary payload length is bounded by the number of stored presentation
items times the common binary width. -/
theorem binaryDescriptionSize_le_presentationItemCount_mul
    (E :
      CorrectedConcreteCompiledGrammarNaturalEncoding H)
    (dummy : α)
    (bitWidth : Nat)
    (hE : E.CodesFitInBits dummy bitWidth) :
    E.binaryDescriptionSize dummy <=
      H.compiledGrammarPresentationItemCount *
        (bitWidth + 1) := by

  unfold binaryDescriptionSize

  exact
    E.toBinaryEntryCost.descriptionSize_le_presentationItemCount_mul
      dummy
      (bitWidth + 1)
      (E.toBinaryEntryCost_boundedBy_of_codesFitInBits
        dummy bitWidth hE)

/-- Structural binary-description bound obtained from the quadratic bound on
actual compiled presentation items. -/
theorem binaryDescriptionSize_le_structuralSquare_mul
    (E :
      CorrectedConcreteCompiledGrammarNaturalEncoding H)
    (dummy : α)
    (bitWidth : Nat)
    (hE : E.CodesFitInBits dummy bitWidth) :
    E.binaryDescriptionSize dummy <=
      (K.card + 3 * H.ruleCount + 3) ^ 2 *
        (bitWidth + 1) := by

  unfold binaryDescriptionSize

  exact
    E.toBinaryEntryCost.descriptionSize_le_structuralSquare_mul
      dummy
      (bitWidth + 1)
      (E.toBinaryEntryCost_boundedBy_of_codesFitInBits
        dummy bitWidth hE)

/-- Maximum binary payload length among the entries actually stored in the
finite compiled presentation. -/
def maxBinaryEntryCodeLength
    (E :
      CorrectedConcreteCompiledGrammarNaturalEncoding H)
    (dummy : α) :
    Nat :=
  E.toBinaryEntryCost.maxEntryCost dummy

/-- Every finite natural-number encoding has an automatic item-count-times-
maximum-binary-length bound. -/
theorem binaryDescriptionSize_le_presentationItemCount_mul_maxCodeLength
    (E :
      CorrectedConcreteCompiledGrammarNaturalEncoding H)
    (dummy : α) :
    E.binaryDescriptionSize dummy <=
      H.compiledGrammarPresentationItemCount *
        E.maxBinaryEntryCodeLength dummy := by

  unfold binaryDescriptionSize
  unfold maxBinaryEntryCodeLength

  exact
    E.toBinaryEntryCost.descriptionSize_le_presentationItemCount_mul_maxEntryCost
      dummy

/-- Automatic structural binary-description bound for an arbitrary explicit
natural-number encoding. -/
theorem binaryDescriptionSize_le_structuralSquare_mul_maxCodeLength
    (E :
      CorrectedConcreteCompiledGrammarNaturalEncoding H)
    (dummy : α) :
    E.binaryDescriptionSize dummy <=
      (K.card + 3 * H.ruleCount + 3) ^ 2 *
        E.maxBinaryEntryCodeLength dummy := by

  unfold binaryDescriptionSize
  unfold maxBinaryEntryCodeLength

  exact
    E.toBinaryEntryCost.descriptionSize_le_structuralSquare_mul_maxEntryCost
      dummy

end CorrectedConcreteCompiledGrammarNaturalEncoding

end BinaryEncodingOfCompiledEntries


section PaperFacingBinaryDescriptionBound

variable {α : Type u}
variable {M : Type v} [Monoid M]

/-- Paper-facing total binary-description bound obtained from a common bit-width
for all natural-number entry codes. -/
def correctedConcreteCompiledGrammarBinaryDescriptionBound
    (sampleLength f bitWidth : Nat) :
    Nat :=
  correctedConcreteCompiledGrammarPresentationItemBound
      sampleLength f *
    (bitWidth + 1)

/-- The paper-facing presentation-item estimate lifts to every explicit
natural-number encoding whose used codes fit below `2 ^ bitWidth`. -/
theorem correctedConcreteFiniteHypothesis_binaryDescriptionSize_le_paperBound
    (K : Finset (Word α))
    (obs : α -> M)
    (f : Nat)
    (dummy : α)
    (E :
      CorrectedConcreteCompiledGrammarNaturalEncoding
        (correctedConcreteFiniteHypothesis
          K obs f))
    (bitWidth : Nat)
    (hE : E.CodesFitInBits dummy bitWidth) :
    E.binaryDescriptionSize dummy <=
      correctedConcreteCompiledGrammarBinaryDescriptionBound
        (sampleLengthBudget K) f bitWidth := by

  unfold
    CorrectedConcreteCompiledGrammarNaturalEncoding.binaryDescriptionSize

  simpa [
    correctedConcreteCompiledGrammarBinaryDescriptionBound,
    CorrectedConcreteCompiledGrammarNaturalEncoding.toBinaryEntryCost
  ] using
    correctedConcreteFiniteHypothesis_descriptionSize_le_paperBound
      K obs f dummy E.toBinaryEntryCost
      (bitWidth + 1)
      (E.toBinaryEntryCost_boundedBy_of_codesFitInBits
        dummy bitWidth hE)

/-- Fully expanded binary-description bound for the actual finite learner
output, parameterized only by a common bit-width for its entry codes. -/
theorem correctedConcreteFiniteHypothesis_binaryDescriptionSize_le_explicit
    (K : Finset (Word α))
    (obs : α -> M)
    (f : Nat)
    (dummy : α)
    (E :
      CorrectedConcreteCompiledGrammarNaturalEncoding
        (correctedConcreteFiniteHypothesis
          K obs f))
    (bitWidth : Nat)
    (hE : E.CodesFitInBits dummy bitWidth) :
    E.binaryDescriptionSize dummy <=
      (sampleLengthBudget K +
          3 *
            ((4 *
                (sampleLengthBudget K +
                  f + 1)) ^
              (64 *
                (sampleLengthBudget K +
                  f + 1) *
                (sampleLengthBudget K +
                  f + 1))) +
          4) ^ 2 *
        (bitWidth + 1) := by

  unfold
    CorrectedConcreteCompiledGrammarNaturalEncoding.binaryDescriptionSize

  simpa [
    CorrectedConcreteCompiledGrammarNaturalEncoding.toBinaryEntryCost
  ] using
    correctedConcreteFiniteHypothesis_descriptionSize_le_explicit
      K obs f dummy E.toBinaryEntryCost
      (bitWidth + 1)
      (E.toBinaryEntryCost_boundedBy_of_codesFitInBits
        dummy bitWidth hE)

end PaperFacingBinaryDescriptionBound

end MCFG
