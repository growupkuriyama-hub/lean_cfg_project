/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG2.ConcreteCanonicalLearnerWorkingGrammarAutomaticBitWidth

/-!
# ConcreteCanonicalLearnerWorkingGrammarDenseEncoding.lean

The preceding file selected the least positive bit width fitting an arbitrary
natural-number encoding of the entries occurring in one finite compiled
presentation.  Its width was still encoding-dependent.

This file supplies a canonical dense position encoding.  Each nonterminal,
start rule, terminal rule, and binary rule is coded by the position of its first
occurrence in the corresponding finite list stored by the compiled grammar.
For every entry that actually occurs, its code is strictly smaller than the
length of that list and hence strictly smaller than the complete presentation
item count.

Consequently all used dense codes fit in

```lean
binaryNatCodeLength H.compiledGrammarPresentationItemCount
```

bits.  The automatically selected least positive width is therefore at most
that quantity, and the total binary payload satisfies

```lean
binaryDescriptionSize ≤
  presentationItemCount * binaryNatCodeLength presentationItemCount.
```

Substituting the previously verified paper-facing presentation bound yields a
fully target-independent item-count-times-logarithmic-width estimate for the
actual cut-compiled learner output.

The four entry categories are serialized in their separate presentation
sections, so position codes may be reused between categories without ambiguity.
No target grammar is supplied to the learner.
No `sorry`, `admit`, or `axiom` is used.
-/

namespace MCFG

universe u v

section FirstOccurrenceIndex

/-- Position of the first occurrence of `x` in a list.  When `x` is absent,
the recursion returns the list length; only the member case is used by the
dense presentation encoding. -/
def listFirstIndex
    {β : Type u}
    [DecidableEq β]
    (x : β) :
    List β → Nat
  | [] => 0
  | y :: ys =>
      if x = y then 0
      else listFirstIndex x ys + 1

/-- The first-occurrence code of a member is strictly below the list length. -/
theorem listFirstIndex_lt_length_of_mem
    {β : Type u}
    [DecidableEq β]
    (x : β) :
    ∀ xs : List β,
      x ∈ xs →
      listFirstIndex x xs < xs.length

  | [], hx => by
      simp at hx

  | y :: ys, hx => by
      by_cases hxy : x = y

      · simp [listFirstIndex, hxy]

      · have hxys : x ∈ ys := by
          simpa [hxy] using hx

        have hind :
            listFirstIndex x ys < ys.length :=
          listFirstIndex_lt_length_of_mem
            x ys hxys

        simpa [listFirstIndex, hxy] using
          Nat.add_lt_add_right hind 1

end FirstOccurrenceIndex


section ComponentLengths

variable {α : Type u}
variable {M : Type v} [Monoid M]
variable {K : Finset (Word α)}
variable {obs : α → M}
variable {f : Nat}

namespace CorrectedConcreteFiniteHypothesis

variable
  (H :
    CorrectedConcreteFiniteHypothesis
      K obs f)

/-- The explicit nonterminal list is one component of the complete
presentation item count. -/
theorem compiledGrammarNonterminals_length_le_presentationItemCount
    (dummy : α) :
    H.compiledGrammarNonterminals.length ≤
      H.compiledGrammarPresentationItemCount := by

  have hcount :=
    H.toCutWorkingMCFGPresentationItemCount_eq dummy

  unfold
    CorrectedConcreteFiniteHypothesis.toCutWorkingMCFGPresentationItemCount
      at hcount

  omega

/-- The start-rule list is one component of the complete presentation item
count. -/
theorem compiledGrammarStartRules_length_le_presentationItemCount
    (dummy : α) :
    (H.toCutWorkingMCFG dummy).startRules.length ≤
      H.compiledGrammarPresentationItemCount := by

  have hcount :=
    H.toCutWorkingMCFGPresentationItemCount_eq dummy

  unfold
    CorrectedConcreteFiniteHypothesis.toCutWorkingMCFGPresentationItemCount
      at hcount

  omega

/-- The terminal-rule list is one component of the complete presentation item
count. -/
theorem compiledGrammarTerminalRules_length_le_presentationItemCount
    (dummy : α) :
    (H.toCutWorkingMCFG dummy).terminalRules.length ≤
      H.compiledGrammarPresentationItemCount := by

  have hcount :=
    H.toCutWorkingMCFGPresentationItemCount_eq dummy

  unfold
    CorrectedConcreteFiniteHypothesis.toCutWorkingMCFGPresentationItemCount
      at hcount

  omega

/-- The binary-rule list is one component of the complete presentation item
count. -/
theorem compiledGrammarBinaryRules_length_le_presentationItemCount
    (dummy : α) :
    (H.toCutWorkingMCFG dummy).binaryRules.length ≤
      H.compiledGrammarPresentationItemCount := by

  have hcount :=
    H.toCutWorkingMCFGPresentationItemCount_eq dummy

  unfold
    CorrectedConcreteFiniteHypothesis.toCutWorkingMCFGPresentationItemCount
      at hcount

  omega

end CorrectedConcreteFiniteHypothesis

end ComponentLengths


section DenseNaturalEncoding

variable {α : Type u}
variable {M : Type v} [Monoid M]
variable {K : Finset (Word α)}
variable {obs : α → M}
variable {f : Nat}

/-- Canonical dense position encoding of all four top-level entry categories in
one compiled grammar presentation. -/
noncomputable def CorrectedConcreteFiniteHypothesis.denseNaturalEncoding
    (H :
      CorrectedConcreteFiniteHypothesis
        K obs f)
    (dummy : α) :
    CorrectedConcreteCompiledGrammarNaturalEncoding H := by

  classical

  exact
    { nonterminal := fun A =>
        listFirstIndex A
          H.compiledGrammarNonterminals

      startRule := fun ρ =>
        listFirstIndex ρ
          (H.toCutWorkingMCFG dummy).startRules

      terminalRule := fun ρ =>
        listFirstIndex ρ
          (H.toCutWorkingMCFG dummy).terminalRules

      binaryRule := fun ρ =>
        listFirstIndex ρ
          (H.toCutWorkingMCFG dummy).binaryRules }

namespace CorrectedConcreteFiniteHypothesis

variable
  (H :
    CorrectedConcreteFiniteHypothesis
      K obs f)

/-- Every dense position code actually used by the compiled presentation is
strictly below the complete presentation item count. -/
theorem denseNaturalEncoding_codesBelow_presentationItemCount
    (dummy : α) :
    (H.denseNaturalEncoding dummy).CodesBelow
      dummy H.compiledGrammarPresentationItemCount := by

  classical

  refine ⟨?_, ?_, ?_, ?_⟩

  · intro A hA

    exact
      (listFirstIndex_lt_length_of_mem
          A H.compiledGrammarNonterminals hA).trans_le
        (H.compiledGrammarNonterminals_length_le_presentationItemCount
          dummy)

  · intro ρ hρ

    exact
      (listFirstIndex_lt_length_of_mem
          ρ (H.toCutWorkingMCFG dummy).startRules hρ).trans_le
        (H.compiledGrammarStartRules_length_le_presentationItemCount
          dummy)

  · intro ρ hρ

    exact
      (listFirstIndex_lt_length_of_mem
          ρ (H.toCutWorkingMCFG dummy).terminalRules hρ).trans_le
        (H.compiledGrammarTerminalRules_length_le_presentationItemCount
          dummy)

  · intro ρ hρ

    exact
      (listFirstIndex_lt_length_of_mem
          ρ (H.toCutWorkingMCFG dummy).binaryRules hρ).trans_le
        (H.compiledGrammarBinaryRules_length_le_presentationItemCount
          dummy)

/-- The dense codes fit in the binary length of the complete presentation item
count. -/
theorem denseNaturalEncoding_codesFitInBits_presentationItemCount
    (dummy : α) :
    (H.denseNaturalEncoding dummy).CodesFitInBits
      dummy
      (binaryNatCodeLength
        H.compiledGrammarPresentationItemCount) := by

  rcases
    H.denseNaturalEncoding_codesBelow_presentationItemCount dummy with
    ⟨hN, hS, hT, hB⟩

  refine ⟨?_, ?_, ?_, ?_⟩

  · intro A hA
    exact
      (hN A hA).trans
        (natCode_lt_two_pow_binaryNatCodeLength
          H.compiledGrammarPresentationItemCount)

  · intro ρ hρ
    exact
      (hS ρ hρ).trans
        (natCode_lt_two_pow_binaryNatCodeLength
          H.compiledGrammarPresentationItemCount)

  · intro ρ hρ
    exact
      (hT ρ hρ).trans
        (natCode_lt_two_pow_binaryNatCodeLength
          H.compiledGrammarPresentationItemCount)

  · intro ρ hρ
    exact
      (hB ρ hρ).trans
        (natCode_lt_two_pow_binaryNatCodeLength
          H.compiledGrammarPresentationItemCount)

/-- The least automatically selected width of the dense encoding is at most
the binary length of the complete presentation item count. -/
theorem denseNaturalEncoding_automaticBitWidth_le_presentationItemLength
    (dummy : α) :
    (H.denseNaturalEncoding dummy).automaticBitWidth dummy ≤
      binaryNatCodeLength
        H.compiledGrammarPresentationItemCount := by

  apply
    (H.denseNaturalEncoding dummy).automaticBitWidth_le_of_codesFitInBits
      dummy
      (binaryNatCodeLength
        H.compiledGrammarPresentationItemCount)

  · simp [binaryNatCodeLength]

  · exact
      H.denseNaturalEncoding_codesFitInBits_presentationItemCount
        dummy

/-- Dense binary serialization is bounded by item count times the binary
length of item count. -/
theorem denseNaturalEncoding_binaryDescriptionSize_le_itemCount_mul_logWidth
    (dummy : α) :
    (H.denseNaturalEncoding dummy).binaryDescriptionSize dummy ≤
      H.compiledGrammarPresentationItemCount *
        binaryNatCodeLength
          H.compiledGrammarPresentationItemCount := by

  calc
    (H.denseNaturalEncoding dummy).binaryDescriptionSize dummy ≤
        H.compiledGrammarPresentationItemCount *
          (H.denseNaturalEncoding dummy).automaticBitWidth dummy :=
      (H.denseNaturalEncoding dummy).
        binaryDescriptionSize_le_presentationItemCount_mul_automaticBitWidth
          dummy

    _ ≤
        H.compiledGrammarPresentationItemCount *
          binaryNatCodeLength
            H.compiledGrammarPresentationItemCount :=
      Nat.mul_le_mul_left
        H.compiledGrammarPresentationItemCount
        (H.denseNaturalEncoding_automaticBitWidth_le_presentationItemLength
          dummy)

/-- More generally, every upper bound `B` on the presentation item count gives
`B * binaryNatCodeLength B` as a dense binary-description bound. -/
theorem denseNaturalEncoding_binaryDescriptionSize_le_bound_mul_logWidth
    (dummy : α)
    (B : Nat)
    (hB :
      H.compiledGrammarPresentationItemCount ≤ B) :
    (H.denseNaturalEncoding dummy).binaryDescriptionSize dummy ≤
      B * binaryNatCodeLength B := by

  have hfit :
      (H.denseNaturalEncoding dummy).CodesFitInBits
        dummy (binaryNatCodeLength B) := by

    rcases
      H.denseNaturalEncoding_codesBelow_presentationItemCount dummy with
      ⟨hN, hS, hT, hBinary⟩

    refine ⟨?_, ?_, ?_, ?_⟩

    · intro A hA
      exact
        ((hN A hA).trans_le hB).trans
          (natCode_lt_two_pow_binaryNatCodeLength B)

    · intro ρ hρ
      exact
        ((hS ρ hρ).trans_le hB).trans
          (natCode_lt_two_pow_binaryNatCodeLength B)

    · intro ρ hρ
      exact
        ((hT ρ hρ).trans_le hB).trans
          (natCode_lt_two_pow_binaryNatCodeLength B)

    · intro ρ hρ
      exact
        ((hBinary ρ hρ).trans_le hB).trans
          (natCode_lt_two_pow_binaryNatCodeLength B)

  have hwidth :
      (H.denseNaturalEncoding dummy).automaticBitWidth dummy ≤
        binaryNatCodeLength B := by

    apply
      (H.denseNaturalEncoding dummy).automaticBitWidth_le_of_codesFitInBits
        dummy (binaryNatCodeLength B)

    · simp [binaryNatCodeLength]

    · exact hfit

  calc
    (H.denseNaturalEncoding dummy).binaryDescriptionSize dummy ≤
        H.compiledGrammarPresentationItemCount *
          (H.denseNaturalEncoding dummy).automaticBitWidth dummy :=
      (H.denseNaturalEncoding dummy).
        binaryDescriptionSize_le_presentationItemCount_mul_automaticBitWidth
          dummy

    _ ≤
        H.compiledGrammarPresentationItemCount *
          binaryNatCodeLength B :=
      Nat.mul_le_mul_left
        H.compiledGrammarPresentationItemCount hwidth

    _ ≤
        B * binaryNatCodeLength B :=
      Nat.mul_le_mul_right
        (binaryNatCodeLength B) hB

end CorrectedConcreteFiniteHypothesis

end DenseNaturalEncoding


section PaperFacingDenseBinaryDescriptionBound

variable {α : Type u}
variable {M : Type v} [Monoid M]

/-- Paper-facing dense binary-description bound.  The remaining width factor is
now the binary length of the already verified presentation-item bound, rather
than an arbitrary encoding-dependent parameter. -/
theorem correctedConcreteFiniteHypothesis_denseBinaryDescriptionSize_le_paperBound
    (K : Finset (Word α))
    (obs : α → M)
    (f : Nat)
    (dummy : α) :
    let H :=
      correctedConcreteFiniteHypothesis K obs f
    let B :=
      correctedConcreteCompiledGrammarPresentationItemBound
        (sampleLengthBudget K) f
    (H.denseNaturalEncoding dummy).binaryDescriptionSize dummy ≤
      B * binaryNatCodeLength B := by

  dsimp

  exact
    (correctedConcreteFiniteHypothesis K obs f).
      denseNaturalEncoding_binaryDescriptionSize_le_bound_mul_logWidth
        dummy
        (correctedConcreteCompiledGrammarPresentationItemBound
          (sampleLengthBudget K) f)
        (correctedConcreteFiniteHypothesis_presentationItemCount_le_paperBound
          K obs f)

/-- Fully expanded dense binary-description bound for the actual canonical
finite learner output. -/
theorem correctedConcreteFiniteHypothesis_denseBinaryDescriptionSize_le_explicit
    (K : Finset (Word α))
    (obs : α → M)
    (f : Nat)
    (dummy : α) :
    let H :=
      correctedConcreteFiniteHypothesis K obs f
    let B :=
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
          4) ^ 2
    (H.denseNaturalEncoding dummy).binaryDescriptionSize dummy ≤
      B * binaryNatCodeLength B := by

  dsimp

  exact
    (correctedConcreteFiniteHypothesis K obs f).
      denseNaturalEncoding_binaryDescriptionSize_le_bound_mul_logWidth
        dummy
        ((sampleLengthBudget K +
            3 *
              ((4 *
                  (sampleLengthBudget K +
                    f + 1)) ^
                (64 *
                  (sampleLengthBudget K +
                    f + 1) *
                  (sampleLengthBudget K +
                    f + 1))) +
            4) ^ 2)
        (correctedConcreteFiniteHypothesis_presentationItemCount_le_explicit
          K obs f)

end PaperFacingDenseBinaryDescriptionBound

end MCFG
