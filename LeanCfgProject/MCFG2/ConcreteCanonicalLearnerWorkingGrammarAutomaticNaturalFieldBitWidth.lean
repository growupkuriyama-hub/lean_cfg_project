/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG.ConcreteCanonicalLearnerWorkingGrammarLogarithmicBitBounds

/-!
# ConcreteCanonicalLearnerWorkingGrammarAutomaticNaturalFieldBitWidth.lean

The preceding file proves an explicit logarithmic bit-size bound from an
externally supplied common field width:

```lean
BinaryTreeNaturalFieldStreamFitsInBits fields bitWidth.
```

This file removes that premise.

For any finite natural stream `fields`, define

```lean
automaticNaturalFieldBitWidth fields :=
  maximumBinaryNatCodeLength (fields.length :: fields).
```

The field-count header is deliberately included in the maximum.  The selected
width is therefore positive, contains the field count, and contains every
payload field.  It is also the least positive width with those properties.

For the complete cut-compiled grammar, this gives a canonical internally
selected width

```lean
H.compiledWorkingGrammarAutomaticNaturalFieldBitWidth dummy.
```

No external fit assumption remains.  The complete checked grammar bit stream
satisfies

```text
compiledGrammarBitCount
  ≤
(naturalFieldCount + 1) *
  (2 * automaticNaturalFieldBitWidth + 1).
```

The selected width is exactly the previously defined maximum standard binary
field length, and every other positive fitting width is at least as large.

This closes the automatic-width layer for the complete natural serialization.
The next quantitative layer may inspect the concrete field constructors and
bound this automatic width by sample length and presentation size.

No target grammar is supplied to the learner.
No `sorry`, `admit`, or `axiom` is used.
-/

namespace MCFG

universe u v

section AutomaticFiniteNaturalFieldWidth

/-- The canonical common bit width selected from the field-count header and all
payload fields of a finite natural stream. -/
def automaticNaturalFieldBitWidth
    (fields : List Nat) :
    Nat :=
  maximumBinaryNatCodeLength
    (fields.length :: fields)

/-- Every standard binary payload length is positive. -/
theorem binaryNatCodeLength_pos
    (n : Nat) :
    0 < binaryNatCodeLength n := by

  simp [binaryNatCodeLength]

/-- The automatically selected natural-field width is positive, including for
an empty payload stream, because the field-count header is always present. -/
theorem automaticNaturalFieldBitWidth_pos
    (fields : List Nat) :
    0 < automaticNaturalFieldBitWidth fields := by

  unfold automaticNaturalFieldBitWidth

  have hheader :
      binaryNatCodeLength fields.length <=
        maximumBinaryNatCodeLength
          (fields.length :: fields) :=
    binaryNatCodeLength_le_maximum_of_mem
      fields.length
      (fields.length :: fields)
      (by simp)

  exact
    (binaryNatCodeLength_pos fields.length).trans_le
      hheader

/-- The field-count header fits below two raised to the automatic width. -/
theorem fieldCount_lt_two_pow_automaticNaturalFieldBitWidth
    (fields : List Nat) :
    fields.length <
      2 ^ automaticNaturalFieldBitWidth fields := by

  apply
    natCode_lt_two_pow_of_binaryNatCodeLength_le

  unfold automaticNaturalFieldBitWidth

  exact
    binaryNatCodeLength_le_maximum_of_mem
      fields.length
      (fields.length :: fields)
      (by simp)

/-- Every payload field fits below two raised to the automatic width. -/
theorem field_lt_two_pow_automaticNaturalFieldBitWidth
    (fields : List Nat)
    {n : Nat}
    (hn : n ∈ fields) :
    n <
      2 ^ automaticNaturalFieldBitWidth fields := by

  apply
    natCode_lt_two_pow_of_binaryNatCodeLength_le

  unfold automaticNaturalFieldBitWidth

  exact
    binaryNatCodeLength_le_maximum_of_mem
      n
      (fields.length :: fields)
      (by simp [hn])

/-- The canonical width automatically satisfies the complete natural-field
fitting predicate. -/
theorem automaticNaturalFieldBitWidth_fits
    (fields : List Nat) :
    BinaryTreeNaturalFieldStreamFitsInBits
      fields
      (automaticNaturalFieldBitWidth fields) := by

  exact
    ⟨automaticNaturalFieldBitWidth_pos fields,
      fieldCount_lt_two_pow_automaticNaturalFieldBitWidth
        fields,
      by
        intro n hn
        exact
          field_lt_two_pow_automaticNaturalFieldBitWidth
            fields hn⟩

/-- Every positive fitting width bounds the automatically selected width. -/
theorem automaticNaturalFieldBitWidth_le_of_fitsInBits
    {fields : List Nat}
    {bitWidth : Nat}
    (hfit :
      BinaryTreeNaturalFieldStreamFitsInBits
        fields bitWidth) :
    automaticNaturalFieldBitWidth fields <=
      bitWidth := by

  unfold automaticNaturalFieldBitWidth

  exact
    maximumBinaryNatCodeLength_count_cons_le_of_fitsInBits
      hfit

/-- Conversely, every positive width above the automatic width fits the field
count and every payload field. -/
theorem naturalFieldStreamFitsInBits_of_automaticWidth_le
    {fields : List Nat}
    {bitWidth : Nat}
    (hpositive : 0 < bitWidth)
    (hwidth :
      automaticNaturalFieldBitWidth fields <=
        bitWidth) :
    BinaryTreeNaturalFieldStreamFitsInBits
      fields bitWidth := by

  refine
    ⟨hpositive, ?_, ?_⟩

  · exact
      natCode_lt_two_pow_of_binaryNatCodeLength_le
        ((binaryNatCodeLength_le_maximum_of_mem
            fields.length
            (fields.length :: fields)
            (by simp)).trans hwidth)

  · intro n hn

    exact
      natCode_lt_two_pow_of_binaryNatCodeLength_le
        ((binaryNatCodeLength_le_maximum_of_mem
            n
            (fields.length :: fields)
            (by simp [hn])).trans hwidth)

/-- Exact characterization of the fitting widths. -/
theorem naturalFieldStreamFitsInBits_iff
    {fields : List Nat}
    {bitWidth : Nat} :
    BinaryTreeNaturalFieldStreamFitsInBits
        fields bitWidth ↔
      0 < bitWidth ∧
        automaticNaturalFieldBitWidth fields <=
          bitWidth := by

  constructor

  · intro hfit

    exact
      ⟨hfit.1,
        automaticNaturalFieldBitWidth_le_of_fitsInBits
          hfit⟩

  · rintro ⟨hpositive, hwidth⟩

    exact
      naturalFieldStreamFitsInBits_of_automaticWidth_le
        hpositive hwidth

/-- The automatic width is the least positive fitting width. -/
theorem automaticNaturalFieldBitWidth_isLeastPositiveFitting
    (fields : List Nat) :
    BinaryTreeNaturalFieldStreamFitsInBits
        fields
        (automaticNaturalFieldBitWidth fields) ∧
      ∀ bitWidth : Nat,
        BinaryTreeNaturalFieldStreamFitsInBits
            fields bitWidth →
          automaticNaturalFieldBitWidth fields <=
            bitWidth := by

  exact
    ⟨automaticNaturalFieldBitWidth_fits fields,
      by
        intro bitWidth hfit
        exact
          automaticNaturalFieldBitWidth_le_of_fitsInBits
            hfit⟩

/-- Automatic explicit logarithmic bit bound for every finite natural stream. -/
theorem
    encodeBinaryTreeNatListBits_length_le_automaticNaturalFieldBitWidth
    (fields : List Nat) :
    (encodeBinaryTreeNatListBits fields).length <=
      (fields.length + 1) *
        (2 *
            automaticNaturalFieldBitWidth fields +
          1) := by

  exact
    encodeBinaryTreeNatListBits_length_le_of_fieldsFitInBits
      (automaticNaturalFieldBitWidth_fits fields)

/-- The maximum recursive binary-tree cost is automatically bounded by twice
the selected width plus one. -/
theorem
    maximumBinaryTreeNatBitCost_le_automaticNaturalFieldBitWidth
    (fields : List Nat) :
    maximumBinaryTreeNatBitCost
        (fields.length :: fields) <=
      2 *
          automaticNaturalFieldBitWidth fields +
        1 := by

  exact
    maximumBinaryTreeNatBitCost_count_cons_le_of_fitsInBits
      (automaticNaturalFieldBitWidth_fits fields)

/-- Compact automatic-width package for an arbitrary finite natural stream. -/
theorem automaticNaturalFieldBitWidth_package
    (fields : List Nat) :
    (0 <
      automaticNaturalFieldBitWidth fields) ∧
      BinaryTreeNaturalFieldStreamFitsInBits
        fields
        (automaticNaturalFieldBitWidth fields) ∧
      ((encodeBinaryTreeNatListBits fields).length <=
        (fields.length + 1) *
          (2 *
              automaticNaturalFieldBitWidth fields +
            1)) ∧
      (∀ bitWidth : Nat,
        BinaryTreeNaturalFieldStreamFitsInBits
            fields bitWidth →
          automaticNaturalFieldBitWidth fields <=
            bitWidth) := by

  exact
    ⟨automaticNaturalFieldBitWidth_pos fields,
      automaticNaturalFieldBitWidth_fits fields,
      encodeBinaryTreeNatListBits_length_le_automaticNaturalFieldBitWidth
        fields,
      by
        intro bitWidth hfit
        exact
          automaticNaturalFieldBitWidth_le_of_fitsInBits
            hfit⟩

end AutomaticFiniteNaturalFieldWidth


section CompleteWorkingGrammarAutomaticNaturalFieldWidth

variable {α : Type u}
variable {M : Type v} [Monoid M]
variable {K : Finset (Word α)}
variable {obs : α → M}
variable {f : Nat}

namespace CorrectedConcreteFiniteHypothesis

variable
  (H : CorrectedConcreteFiniteHypothesis K obs f)

/-- Canonical common bit width selected internally from the complete pure-natural
grammar serialization, including its natural-field count. -/
noncomputable def compiledWorkingGrammarAutomaticNaturalFieldBitWidth
    (dummy : α) :
    Nat :=
  automaticNaturalFieldBitWidth
    (H.encodeCompiledWorkingGrammarNaturalList
      dummy)

/-- The automatic grammar field width is exactly the previously defined maximum
standard binary field length. -/
theorem
    compiledWorkingGrammarAutomaticNaturalFieldBitWidth_eq_maximumBinaryFieldLength
    (dummy : α) :
    H.compiledWorkingGrammarAutomaticNaturalFieldBitWidth
        dummy =
      H.compiledWorkingGrammarMaximumBinaryFieldLength
        dummy := by

  rfl

/-- The automatic grammar field width is always positive. -/
theorem
    compiledWorkingGrammarAutomaticNaturalFieldBitWidth_pos
    (dummy : α) :
    0 <
      H.compiledWorkingGrammarAutomaticNaturalFieldBitWidth
        dummy := by

  exact
    automaticNaturalFieldBitWidth_pos
      (H.encodeCompiledWorkingGrammarNaturalList
        dummy)

/-- The complete pure-natural grammar stream fits its automatically selected
width. -/
theorem
    compiledWorkingGrammarNaturalFieldsFitInBits_automatic
    (dummy : α) :
    H.compiledWorkingGrammarNaturalFieldsFitInBits
        dummy
        (H.compiledWorkingGrammarAutomaticNaturalFieldBitWidth
          dummy) := by

  exact
    automaticNaturalFieldBitWidth_fits
      (H.encodeCompiledWorkingGrammarNaturalList
        dummy)

/-- Every positive fitting grammar-field width is at least the automatic one. -/
theorem
    compiledWorkingGrammarAutomaticNaturalFieldBitWidth_le_of_fits
    (dummy : α)
    {bitWidth : Nat}
    (hfit :
      H.compiledWorkingGrammarNaturalFieldsFitInBits
        dummy bitWidth) :
    H.compiledWorkingGrammarAutomaticNaturalFieldBitWidth
        dummy <=
      bitWidth := by

  exact
    automaticNaturalFieldBitWidth_le_of_fitsInBits
      hfit

/-- Exact characterization of fitting widths for the complete grammar natural
serialization. -/
theorem
    compiledWorkingGrammarNaturalFieldsFitInBits_iff
    (dummy : α)
    {bitWidth : Nat} :
    H.compiledWorkingGrammarNaturalFieldsFitInBits
        dummy bitWidth ↔
      0 < bitWidth ∧
        H.compiledWorkingGrammarAutomaticNaturalFieldBitWidth
            dummy <=
          bitWidth := by

  exact
    naturalFieldStreamFitsInBits_iff

/-- The maximum recursive field cost of the complete grammar is bounded by
twice the automatic standard binary width plus one. -/
theorem
    compiledWorkingGrammarMaximumFieldBitCost_le_automaticWidth
    (dummy : α) :
    H.compiledWorkingGrammarMaximumFieldBitCost dummy <=
      2 *
          H.compiledWorkingGrammarAutomaticNaturalFieldBitWidth
            dummy +
        1 := by

  rw [
    H.compiledWorkingGrammarAutomaticNaturalFieldBitWidth_eq_maximumBinaryFieldLength
      dummy
  ]

  exact
    H.compiledWorkingGrammarMaximumFieldBitCost_le_logarithmic
      dummy

/-- Unconditional complete-grammar logarithmic bit-size bound using the
internally selected least fitting width. -/
theorem
    compiledWorkingGrammarLogarithmicBitCount_le_automaticNaturalFieldBitWidth
    (dummy : α) :
    H.compiledWorkingGrammarLogarithmicBitCount dummy <=
      (H.compiledWorkingGrammarNaturalFieldCount dummy + 1) *
        (2 *
            H.compiledWorkingGrammarAutomaticNaturalFieldBitWidth
              dummy +
          1) := by

  exact
    H.compiledWorkingGrammarLogarithmicBitCount_le_of_naturalFieldsFitInBits
      dummy
      (H.compiledWorkingGrammarNaturalFieldsFitInBits_automatic
        dummy)

/-- The automatic grammar width is the least positive fitting width. -/
theorem
    compiledWorkingGrammarAutomaticNaturalFieldBitWidth_isLeastPositiveFitting
    (dummy : α) :
    H.compiledWorkingGrammarNaturalFieldsFitInBits
        dummy
        (H.compiledWorkingGrammarAutomaticNaturalFieldBitWidth
          dummy) ∧
      ∀ bitWidth : Nat,
        H.compiledWorkingGrammarNaturalFieldsFitInBits
            dummy bitWidth →
          H.compiledWorkingGrammarAutomaticNaturalFieldBitWidth
              dummy <=
            bitWidth := by

  exact
    ⟨H.compiledWorkingGrammarNaturalFieldsFitInBits_automatic
        dummy,
      by
        intro bitWidth hfit
        exact
          H.compiledWorkingGrammarAutomaticNaturalFieldBitWidth_le_of_fits
            dummy hfit⟩

/-- Compact actual-grammar automatic-width endpoint: complete round trip,
positive least fitting width, recursive-cost bound, and unconditional total
bit-size bound. -/
theorem
    compiledWorkingGrammarAutomaticNaturalFieldBitWidth_package
    (dummy : α) :
    (H.decodeCompiledWorkingGrammarLogarithmicBitList dummy
        (H.encodeCompiledWorkingGrammarLogarithmicBitList
          dummy) =
      some
        (H.compiledGrammarPresentationEntries dummy)) ∧
      (0 <
        H.compiledWorkingGrammarAutomaticNaturalFieldBitWidth
          dummy) ∧
      H.compiledWorkingGrammarNaturalFieldsFitInBits
        dummy
        (H.compiledWorkingGrammarAutomaticNaturalFieldBitWidth
          dummy) ∧
      (H.compiledWorkingGrammarMaximumFieldBitCost dummy <=
        2 *
            H.compiledWorkingGrammarAutomaticNaturalFieldBitWidth
              dummy +
          1) ∧
      (H.compiledWorkingGrammarLogarithmicBitCount dummy <=
        (H.compiledWorkingGrammarNaturalFieldCount dummy + 1) *
          (2 *
              H.compiledWorkingGrammarAutomaticNaturalFieldBitWidth
                dummy +
            1)) ∧
      (∀ bitWidth : Nat,
        H.compiledWorkingGrammarNaturalFieldsFitInBits
            dummy bitWidth →
          H.compiledWorkingGrammarAutomaticNaturalFieldBitWidth
              dummy <=
            bitWidth) := by

  exact
    ⟨H.decodeCompiledWorkingGrammarLogarithmicBitList_encode
        dummy,
      H.compiledWorkingGrammarAutomaticNaturalFieldBitWidth_pos
        dummy,
      H.compiledWorkingGrammarNaturalFieldsFitInBits_automatic
        dummy,
      H.compiledWorkingGrammarMaximumFieldBitCost_le_automaticWidth
        dummy,
      H.compiledWorkingGrammarLogarithmicBitCount_le_automaticNaturalFieldBitWidth
        dummy,
      by
        intro bitWidth hfit
        exact
          H.compiledWorkingGrammarAutomaticNaturalFieldBitWidth_le_of_fits
            dummy hfit⟩

end CorrectedConcreteFiniteHypothesis

end CompleteWorkingGrammarAutomaticNaturalFieldWidth

end MCFG
