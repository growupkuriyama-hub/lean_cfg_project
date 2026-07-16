/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG.ConcreteCanonicalLearnerWorkingGrammarBinaryEncoding

/-!
# ConcreteCanonicalLearnerWorkingGrammarAutomaticBitWidth.lean

The preceding binary-encoding layer proved total bit-size bounds from an
externally supplied proposition

```lean
E.CodesFitInBits dummy bitWidth.
```

This file removes that external width premise for every finite compiled output.
For each explicit natural-number encoding, it takes the maximum binary payload
length among the entries actually stored in the compiled presentation and then
forces the width to be positive:

```lean
E.automaticBitWidth dummy = max 1 (E.maxBinaryEntryCodeLength dummy).
```

Every used code is proved to lie below the corresponding power of two.  The
chosen width is moreover least among all positive widths satisfying
`CodesFitInBits`.  Thus the binary serialization of a finite learner output has
an internally selected canonical bit width.

The file also lifts this automatic width to the actual presentation-item,
structural-square, paper-facing, and fully expanded description-size bounds.
The remaining open step is to define a concrete dense encoding whose automatic
width can itself be bounded solely from the finite presentation cardinalities.

No target grammar is supplied to the learner.
No `sorry`, `admit`, or `axiom` is used.
-/

namespace MCFG

universe u v

section BinaryLengthArithmetic

/-- Every natural-number code lies below two raised to its own binary payload
length. -/
theorem natCode_lt_two_pow_binaryNatCodeLength
    (n : Nat) :
    n < 2 ^ binaryNatCodeLength n := by

  simpa [
    binaryNatCodeLength,
    Nat.log2_eq_log_two,
    Nat.succ_eq_add_one
  ] using
    Nat.lt_pow_succ_log_self
      (b := 2) Nat.one_lt_two n

/-- If the binary payload length of a code is at most `bitWidth`, then the code
fits below `2 ^ bitWidth`. -/
theorem natCode_lt_two_pow_of_binaryNatCodeLength_le
    {n bitWidth : Nat}
    (hwidth : binaryNatCodeLength n <= bitWidth) :
    n < 2 ^ bitWidth := by

  exact
    (natCode_lt_two_pow_binaryNatCodeLength n).trans_le
      (Nat.pow_le_pow_right Nat.two_pos hwidth)

/-- The sharper positive-width form of the preceding file's binary-length
estimate.  When `bitWidth` is positive, a code below `2 ^ bitWidth` needs at
most exactly `bitWidth` payload bits. -/
theorem binaryNatCodeLength_le_of_pos_of_lt_two_pow
    {n bitWidth : Nat}
    (hpositive : 0 < bitWidth)
    (hcode : n < 2 ^ bitWidth) :
    binaryNatCodeLength n <= bitWidth := by

  by_cases hn : n = 0
  · subst n
    simpa [binaryNatCodeLength] using hpositive

  · have hlog :
        n.log2 < bitWidth :=
      (Nat.log2_lt hn).2 hcode

    simpa [binaryNatCodeLength] using
      Nat.add_one_le_of_lt hlog

end BinaryLengthArithmetic


section FiniteMaximumUpperBound

/-- If every member of a finite list has cost at most `c`, its recursively
computed maximum cost is also at most `c`. -/
theorem listCostMax_le_of_forall_mem
    {β : Type u}
    (cost : β -> Nat)
    (c : Nat) :
    forall xs : List β,
      (forall x ∈ xs, cost x <= c) ->
      listCostMax cost xs <= c

  | [], _ => by
      simp [listCostMax]

  | x :: xs, hcost => by
      have hx :
          cost x <= c :=
        hcost x (by simp)

      have hxs :
          forall y ∈ xs, cost y <= c := by
        intro y hy
        exact hcost y (by simp [hy])

      exact
        max_le hx
          (listCostMax_le_of_forall_mem
            cost c xs hxs)

end FiniteMaximumUpperBound


section MaximumCompiledEntryCostUpperBound

variable {α : Type u}
variable {M : Type v} [Monoid M]
variable {K : Finset (Word α)}
variable {obs : α -> M}
variable {f : Nat}
variable
  {H :
    CorrectedConcreteFiniteHypothesis
      K obs f}

namespace CorrectedConcreteCompiledGrammarEntryCost

/-- A uniform upper bound on all stored entry costs also bounds the maximum
stored entry cost. -/
theorem maxEntryCost_le_of_boundedBy
    (C :
      CorrectedConcreteCompiledGrammarEntryCost H)
    (dummy : α)
    (c : Nat)
    (hC : C.BoundedBy dummy c) :
    C.maxEntryCost dummy <= c := by

  rcases hC with
    ⟨hN, hS, hT, hB⟩

  unfold maxEntryCost

  exact
    max_le
      (listCostMax_le_of_forall_mem
        C.nonterminal c
        H.compiledGrammarNonterminals hN)
      (max_le
        (listCostMax_le_of_forall_mem
          C.startRule c
          (H.toCutWorkingMCFG dummy).startRules hS)
        (max_le
          (listCostMax_le_of_forall_mem
            C.terminalRule c
            (H.toCutWorkingMCFG dummy).terminalRules hT)
          (listCostMax_le_of_forall_mem
            C.binaryRule c
            (H.toCutWorkingMCFG dummy).binaryRules hB)))

end CorrectedConcreteCompiledGrammarEntryCost

end MaximumCompiledEntryCostUpperBound


section AutomaticBitWidth

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

/-- The canonical positive bit width selected from the codes actually occurring
in the finite compiled presentation. -/
def automaticBitWidth
    (E :
      CorrectedConcreteCompiledGrammarNaturalEncoding H)
    (dummy : α) :
    Nat :=
  max 1 (E.maxBinaryEntryCodeLength dummy)

/-- The automatically selected bit width is always positive, including for an
empty presentation. -/
theorem automaticBitWidth_pos
    (E :
      CorrectedConcreteCompiledGrammarNaturalEncoding H)
    (dummy : α) :
    0 < E.automaticBitWidth dummy := by

  unfold automaticBitWidth

  exact
    Nat.lt_of_lt_of_le
      Nat.zero_lt_one
      (Nat.le_max_left
        1 (E.maxBinaryEntryCodeLength dummy))

/-- Every stored binary entry cost is bounded by the automatic width. -/
theorem toBinaryEntryCost_boundedBy_automaticBitWidth
    (E :
      CorrectedConcreteCompiledGrammarNaturalEncoding H)
    (dummy : α) :
    E.toBinaryEntryCost.BoundedBy
      dummy (E.automaticBitWidth dummy) := by

  rcases
    E.toBinaryEntryCost.boundedBy_maxEntryCost dummy with
    ⟨hN, hS, hT, hB⟩

  refine ⟨?_, ?_, ?_, ?_⟩

  · intro A hA
    exact
      (hN A hA).trans
        (Nat.le_max_right
          1 (E.maxBinaryEntryCodeLength dummy))

  · intro ρ hρ
    exact
      (hS ρ hρ).trans
        (Nat.le_max_right
          1 (E.maxBinaryEntryCodeLength dummy))

  · intro ρ hρ
    exact
      (hT ρ hρ).trans
        (Nat.le_max_right
          1 (E.maxBinaryEntryCodeLength dummy))

  · intro ρ hρ
    exact
      (hB ρ hρ).trans
        (Nat.le_max_right
          1 (E.maxBinaryEntryCodeLength dummy))

/-- Every natural-number code used by the finite compiled presentation fits in
the automatically selected number of bits. -/
theorem codesFitInBits_automaticBitWidth
    (E :
      CorrectedConcreteCompiledGrammarNaturalEncoding H)
    (dummy : α) :
    E.CodesFitInBits
      dummy (E.automaticBitWidth dummy) := by

  rcases
    E.toBinaryEntryCost_boundedBy_automaticBitWidth dummy with
    ⟨hN, hS, hT, hB⟩

  refine ⟨?_, ?_, ?_, ?_⟩

  · intro A hA
    exact
      natCode_lt_two_pow_of_binaryNatCodeLength_le
        (hN A hA)

  · intro ρ hρ
    exact
      natCode_lt_two_pow_of_binaryNatCodeLength_le
        (hS ρ hρ)

  · intro ρ hρ
    exact
      natCode_lt_two_pow_of_binaryNatCodeLength_le
        (hT ρ hρ)

  · intro ρ hρ
    exact
      natCode_lt_two_pow_of_binaryNatCodeLength_le
        (hB ρ hρ)

/-- At every positive width, fitting all stored natural-number codes gives an
exact uniform upper bound on all binary entry costs. -/
theorem toBinaryEntryCost_boundedBy_of_codesFitInBits_pos
    (E :
      CorrectedConcreteCompiledGrammarNaturalEncoding H)
    (dummy : α)
    (bitWidth : Nat)
    (hpositive : 0 < bitWidth)
    (hE : E.CodesFitInBits dummy bitWidth) :
    E.toBinaryEntryCost.BoundedBy
      dummy bitWidth := by

  rcases hE with
    ⟨hN, hS, hT, hB⟩

  refine ⟨?_, ?_, ?_, ?_⟩

  · intro A hA
    exact
      binaryNatCodeLength_le_of_pos_of_lt_two_pow
        hpositive (hN A hA)

  · intro ρ hρ
    exact
      binaryNatCodeLength_le_of_pos_of_lt_two_pow
        hpositive (hS ρ hρ)

  · intro ρ hρ
    exact
      binaryNatCodeLength_le_of_pos_of_lt_two_pow
        hpositive (hT ρ hρ)

  · intro ρ hρ
    exact
      binaryNatCodeLength_le_of_pos_of_lt_two_pow
        hpositive (hB ρ hρ)

/-- Every positive fitting width bounds the maximum binary entry-code length. -/
theorem maxBinaryEntryCodeLength_le_of_codesFitInBits
    (E :
      CorrectedConcreteCompiledGrammarNaturalEncoding H)
    (dummy : α)
    (bitWidth : Nat)
    (hpositive : 0 < bitWidth)
    (hE : E.CodesFitInBits dummy bitWidth) :
    E.maxBinaryEntryCodeLength dummy <= bitWidth := by

  unfold maxBinaryEntryCodeLength

  exact
    E.toBinaryEntryCost.maxEntryCost_le_of_boundedBy
      dummy bitWidth
      (E.toBinaryEntryCost_boundedBy_of_codesFitInBits_pos
        dummy bitWidth hpositive hE)

/-- The automatic width is the least positive width in which all actually used
codes fit. -/
theorem automaticBitWidth_le_of_codesFitInBits
    (E :
      CorrectedConcreteCompiledGrammarNaturalEncoding H)
    (dummy : α)
    (bitWidth : Nat)
    (hpositive : 0 < bitWidth)
    (hE : E.CodesFitInBits dummy bitWidth) :
    E.automaticBitWidth dummy <= bitWidth := by

  unfold automaticBitWidth

  exact
    max_le hpositive
      (E.maxBinaryEntryCodeLength_le_of_codesFitInBits
        dummy bitWidth hpositive hE)

/-- Characterization of the canonical width as the least positive fitting
width. -/
theorem automaticBitWidth_isLeastPositiveFitting
    (E :
      CorrectedConcreteCompiledGrammarNaturalEncoding H)
    (dummy : α) :
    E.CodesFitInBits
        dummy (E.automaticBitWidth dummy) ∧
      0 < E.automaticBitWidth dummy ∧
      forall bitWidth,
        0 < bitWidth ->
        E.CodesFitInBits dummy bitWidth ->
        E.automaticBitWidth dummy <= bitWidth := by

  exact
    ⟨E.codesFitInBits_automaticBitWidth dummy,
      E.automaticBitWidth_pos dummy,
      fun bitWidth hpositive hfit =>
        E.automaticBitWidth_le_of_codesFitInBits
          dummy bitWidth hpositive hfit⟩

/-- Automatic total binary-description bound using the canonical selected bit
width. -/
theorem binaryDescriptionSize_le_presentationItemCount_mul_automaticBitWidth
    (E :
      CorrectedConcreteCompiledGrammarNaturalEncoding H)
    (dummy : α) :
    E.binaryDescriptionSize dummy <=
      H.compiledGrammarPresentationItemCount *
        E.automaticBitWidth dummy := by

  unfold binaryDescriptionSize

  exact
    E.toBinaryEntryCost.descriptionSize_le_presentationItemCount_mul
      dummy
      (E.automaticBitWidth dummy)
      (E.toBinaryEntryCost_boundedBy_automaticBitWidth dummy)

/-- Automatic structural-square binary-description bound. -/
theorem binaryDescriptionSize_le_structuralSquare_mul_automaticBitWidth
    (E :
      CorrectedConcreteCompiledGrammarNaturalEncoding H)
    (dummy : α) :
    E.binaryDescriptionSize dummy <=
      (K.card + 3 * H.ruleCount + 3) ^ 2 *
        E.automaticBitWidth dummy := by

  unfold binaryDescriptionSize

  exact
    E.toBinaryEntryCost.descriptionSize_le_structuralSquare_mul
      dummy
      (E.automaticBitWidth dummy)
      (E.toBinaryEntryCost_boundedBy_automaticBitWidth dummy)

end CorrectedConcreteCompiledGrammarNaturalEncoding

end AutomaticBitWidth


section PaperFacingAutomaticBinaryDescriptionBound

variable {α : Type u}
variable {M : Type v} [Monoid M]

/-- Paper-facing description-size theorem with no externally supplied
`CodesFitInBits` premise.  The finite output itself selects its least positive
fitting bit width. -/
theorem correctedConcreteFiniteHypothesis_binaryDescriptionSize_le_automatic_paperBound
    (K : Finset (Word α))
    (obs : α -> M)
    (f : Nat)
    (dummy : α)
    (E :
      CorrectedConcreteCompiledGrammarNaturalEncoding
        (correctedConcreteFiniteHypothesis
          K obs f)) :
    E.binaryDescriptionSize dummy <=
      correctedConcreteCompiledGrammarPresentationItemBound
          (sampleLengthBudget K) f *
        E.automaticBitWidth dummy := by

  have hdescription :
      E.binaryDescriptionSize dummy <=
        (correctedConcreteFiniteHypothesis
            K obs f).compiledGrammarPresentationItemCount *
          E.automaticBitWidth dummy :=
    E.binaryDescriptionSize_le_presentationItemCount_mul_automaticBitWidth
      dummy

  have hitems :
      (correctedConcreteFiniteHypothesis
          K obs f).compiledGrammarPresentationItemCount <=
        correctedConcreteCompiledGrammarPresentationItemBound
          (sampleLengthBudget K) f :=
    correctedConcreteFiniteHypothesis_presentationItemCount_le_paperBound
      K obs f

  exact
    hdescription.trans
      (Nat.mul_le_mul_right
        (E.automaticBitWidth dummy) hitems)

/-- Fully expanded automatic binary-description bound.  The only remaining
encoding-dependent factor is the internally selected least positive bit width. -/
theorem correctedConcreteFiniteHypothesis_binaryDescriptionSize_le_automatic_explicit
    (K : Finset (Word α))
    (obs : α -> M)
    (f : Nat)
    (dummy : α)
    (E :
      CorrectedConcreteCompiledGrammarNaturalEncoding
        (correctedConcreteFiniteHypothesis
          K obs f)) :
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
        E.automaticBitWidth dummy := by

  unfold
    CorrectedConcreteCompiledGrammarNaturalEncoding.binaryDescriptionSize

  simpa [
    CorrectedConcreteCompiledGrammarNaturalEncoding.toBinaryEntryCost
  ] using
    correctedConcreteFiniteHypothesis_descriptionSize_le_explicit
      K obs f dummy E.toBinaryEntryCost
      (E.automaticBitWidth dummy)
      (E.toBinaryEntryCost_boundedBy_automaticBitWidth dummy)

end PaperFacingAutomaticBinaryDescriptionBound

end MCFG
