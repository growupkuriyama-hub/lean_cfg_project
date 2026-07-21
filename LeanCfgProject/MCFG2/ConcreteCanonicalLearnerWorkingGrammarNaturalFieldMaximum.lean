/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG.ConcreteCanonicalLearnerWorkingGrammarAutomaticNaturalFieldBitWidth

/-!
# ConcreteCanonicalLearnerWorkingGrammarNaturalFieldMaximum.lean

The preceding file removes every externally supplied natural-field bit width by
selecting the maximum standard binary length among the complete finite field
stream.

This file reduces that selected width to one ordinary natural-number bound.

For a finite natural list `fields`, define

```lean
maximumNaturalFieldValue fields
```

to be the maximum payload value, with value `0` on the empty list.  The single
bound relevant to the complete self-delimiting stream is then

```lean
naturalFieldValueBound fields :=
  max fields.length (maximumNaturalFieldValue fields).
```

It simultaneously bounds

* the field-count header; and
* every natural payload field.

Consequently the standard binary length of this one value is a valid common
width:

```text
BinaryTreeNaturalFieldStreamFitsInBits fields
  (binaryNatCodeLength (naturalFieldValueBound fields)).
```

The automatically selected least fitting width therefore satisfies

```text
automaticNaturalFieldBitWidth fields
  ≤
binaryNatCodeLength (naturalFieldValueBound fields).
```

For the complete cut-compiled grammar this yields the unconditional explicit
bound

```text
grammarBitCount
  ≤
(naturalFieldCount + 1) *
  (2 * binaryNatCodeLength(grammarNaturalFieldValueBound) + 1).
```

Thus all later field-by-field analysis only has to bound one natural quantity:
the largest of the natural-field count and every serialized field value.

The next layer may decompose the concrete serialization and bound
`compiledWorkingGrammarNaturalFieldValueBound` from presentation cardinalities,
sample length, fan-out, template lengths, and finite dense-code ranges.

No target grammar is supplied to the learner.
No `sorry`, `admit`, or `axiom` is used.
-/

namespace MCFG

universe u v

section FiniteNaturalMaximum

/-- Maximum value occurring in a finite natural list.  The empty maximum is
zero. -/
def maximumNaturalFieldValue :
    List Nat → Nat

  | [] =>
      0

  | n :: ns =>
      max n (maximumNaturalFieldValue ns)

/-- Every member of a finite natural list is at most its maximum value. -/
theorem nat_le_maximumNaturalFieldValue_of_mem
    (n : Nat) :
    ∀ fields : List Nat,
      n ∈ fields →
        n <= maximumNaturalFieldValue fields

  | [], hmem => by
      simp at hmem

  | field :: fields, hmem => by
      rcases List.mem_cons.mp hmem with
        hhead | htail

      · subst field

        exact
          Nat.le_max_left
            n
            (maximumNaturalFieldValue fields)

      · exact
          (nat_le_maximumNaturalFieldValue_of_mem
              n fields htail).trans
            (Nat.le_max_right
              field
              (maximumNaturalFieldValue fields))

/-- If every list member is bounded by `bound`, then the finite maximum is also
bounded by `bound`. -/
theorem maximumNaturalFieldValue_le_of_forall_mem
    (bound : Nat) :
    ∀ fields : List Nat,
      (∀ n ∈ fields,
        n <= bound) →
      maximumNaturalFieldValue fields <=
        bound

  | [], hall => by
      simp [maximumNaturalFieldValue]

  | n :: ns, hall => by
      change
        max n (maximumNaturalFieldValue ns) <=
          bound

      apply max_le

      · exact
          hall n (by simp)

      · apply
          maximumNaturalFieldValue_le_of_forall_mem
            bound ns

        intro field hfield

        exact
          hall field
            (by simp [hfield])

/-- Exact maximum law for concatenation. -/
theorem maximumNaturalFieldValue_append :
    ∀ xs ys : List Nat,
      maximumNaturalFieldValue (xs ++ ys) =
        max
          (maximumNaturalFieldValue xs)
          (maximumNaturalFieldValue ys)

  | [], ys => by
      simp [maximumNaturalFieldValue]

  | x :: xs, ys => by
      simp [
        maximumNaturalFieldValue,
        maximumNaturalFieldValue_append xs ys,
        max_assoc
      ]

/-- The maximum of a singleton natural list is its unique value. -/
@[simp] theorem maximumNaturalFieldValue_singleton
    (n : Nat) :
    maximumNaturalFieldValue [n] = n := by

  simp [maximumNaturalFieldValue]

/-- The common value bound for the complete self-delimiting field stream:
include both the number of fields and the largest payload field. -/
def naturalFieldValueBound
    (fields : List Nat) :
    Nat :=
  max fields.length
    (maximumNaturalFieldValue fields)

/-- The field-count header is bounded by the common field-value bound. -/
theorem fieldCount_le_naturalFieldValueBound
    (fields : List Nat) :
    fields.length <=
      naturalFieldValueBound fields := by

  exact
    Nat.le_max_left
      fields.length
      (maximumNaturalFieldValue fields)

/-- Every payload field is bounded by the common field-value bound. -/
theorem field_le_naturalFieldValueBound_of_mem
    (fields : List Nat)
    {n : Nat}
    (hn : n ∈ fields) :
    n <= naturalFieldValueBound fields := by

  exact
    (nat_le_maximumNaturalFieldValue_of_mem
        n fields hn).trans
      (Nat.le_max_right
        fields.length
        (maximumNaturalFieldValue fields))

/-- The common field-value bound is the least natural number simultaneously
bounding the field count and every payload field. -/
theorem naturalFieldValueBound_le_of_count_le_of_all_le
    {fields : List Nat}
    {bound : Nat}
    (hcount :
      fields.length <= bound)
    (hfields :
      ∀ n ∈ fields,
        n <= bound) :
    naturalFieldValueBound fields <=
      bound := by

  unfold naturalFieldValueBound

  apply max_le

  · exact hcount

  · exact
      maximumNaturalFieldValue_le_of_forall_mem
        bound fields hfields

/-- Exact order characterization of the common field-value bound. -/
theorem naturalFieldValueBound_le_iff
    {fields : List Nat}
    {bound : Nat} :
    naturalFieldValueBound fields <= bound ↔
      fields.length <= bound ∧
        ∀ n ∈ fields,
          n <= bound := by

  constructor

  · intro hbound

    exact
      ⟨(fieldCount_le_naturalFieldValueBound
          fields).trans hbound,
        by
          intro n hn

          exact
            (field_le_naturalFieldValueBound_of_mem
                fields hn).trans
              hbound⟩

  · rintro ⟨hcount, hfields⟩

    exact
      naturalFieldValueBound_le_of_count_le_of_all_le
        hcount hfields

end FiniteNaturalMaximum


section MaximumValueCommonBitWidth

/-- The standard binary length of the common maximum value is a valid positive
width for the count header and every payload field. -/
theorem naturalFieldStreamFitsInBits_binaryNatCodeLength_valueBound
    (fields : List Nat) :
    BinaryTreeNaturalFieldStreamFitsInBits
      fields
      (binaryNatCodeLength
        (naturalFieldValueBound fields)) := by

  refine
    ⟨binaryNatCodeLength_pos
        (naturalFieldValueBound fields),
      ?_,
      ?_⟩

  · exact
      (fieldCount_le_naturalFieldValueBound
          fields).trans_lt
        (natCode_lt_two_pow_binaryNatCodeLength
          (naturalFieldValueBound fields))

  · intro n hn

    exact
      (field_le_naturalFieldValueBound_of_mem
          fields hn).trans_lt
        (natCode_lt_two_pow_binaryNatCodeLength
          (naturalFieldValueBound fields))

/-- The least automatically selected common width is at most the binary length
of the single maximum field-value bound. -/
theorem
    automaticNaturalFieldBitWidth_le_binaryNatCodeLength_valueBound
    (fields : List Nat) :
    automaticNaturalFieldBitWidth fields <=
      binaryNatCodeLength
        (naturalFieldValueBound fields) := by

  exact
    automaticNaturalFieldBitWidth_le_of_fitsInBits
      (naturalFieldStreamFitsInBits_binaryNatCodeLength_valueBound
        fields)

/-- The maximum recursive binary-tree field cost is bounded using only the
single maximum field-value bound. -/
theorem
    maximumBinaryTreeNatBitCost_le_binaryNatCodeLength_valueBound
    (fields : List Nat) :
    maximumBinaryTreeNatBitCost
        (fields.length :: fields) <=
      2 *
          binaryNatCodeLength
            (naturalFieldValueBound fields) +
        1 := by

  exact
    maximumBinaryTreeNatBitCost_count_cons_le_of_fitsInBits
      (naturalFieldStreamFitsInBits_binaryNatCodeLength_valueBound
        fields)

/-- Total logarithmic-structure bit length bounded by the number of fields and
the standard binary length of one maximum natural value. -/
theorem
    encodeBinaryTreeNatListBits_length_le_binaryNatCodeLength_valueBound
    (fields : List Nat) :
    (encodeBinaryTreeNatListBits fields).length <=
      (fields.length + 1) *
        (2 *
            binaryNatCodeLength
              (naturalFieldValueBound fields) +
          1) := by

  exact
    encodeBinaryTreeNatListBits_length_le_of_fieldsFitInBits
      (naturalFieldStreamFitsInBits_binaryNatCodeLength_valueBound
        fields)

/-- Compact maximum-value reduction package for any finite natural field
stream. -/
theorem naturalFieldMaximumBitBound_package
    (fields : List Nat) :
    (fields.length <=
      naturalFieldValueBound fields) ∧
      (∀ n ∈ fields,
        n <= naturalFieldValueBound fields) ∧
      (automaticNaturalFieldBitWidth fields <=
        binaryNatCodeLength
          (naturalFieldValueBound fields)) ∧
      ((encodeBinaryTreeNatListBits fields).length <=
        (fields.length + 1) *
          (2 *
              binaryNatCodeLength
                (naturalFieldValueBound fields) +
            1)) := by

  exact
    ⟨fieldCount_le_naturalFieldValueBound fields,
      by
        intro n hn
        exact
          field_le_naturalFieldValueBound_of_mem
            fields hn,
      automaticNaturalFieldBitWidth_le_binaryNatCodeLength_valueBound
        fields,
      encodeBinaryTreeNatListBits_length_le_binaryNatCodeLength_valueBound
        fields⟩

end MaximumValueCommonBitWidth


section CompleteWorkingGrammarNaturalFieldMaximum

variable {α : Type u}
variable {M : Type v} [Monoid M]
variable {K : Finset (Word α)}
variable {obs : α → M}
variable {f : Nat}

namespace CorrectedConcreteFiniteHypothesis

variable
  (H : CorrectedConcreteFiniteHypothesis K obs f)

/-- Largest natural payload value occurring in the complete pure-natural
serialization of the cut-compiled grammar. -/
noncomputable def compiledWorkingGrammarMaximumNaturalFieldValue
    (dummy : α) :
    Nat :=
  maximumNaturalFieldValue
    (H.encodeCompiledWorkingGrammarNaturalList
      dummy)

/-- Single natural value simultaneously bounding the complete grammar's
natural-field count and every serialized natural payload field. -/
noncomputable def compiledWorkingGrammarNaturalFieldValueBound
    (dummy : α) :
    Nat :=
  naturalFieldValueBound
    (H.encodeCompiledWorkingGrammarNaturalList
      dummy)

/-- Expanded form of the grammar field-value bound. -/
theorem compiledWorkingGrammarNaturalFieldValueBound_eq
    (dummy : α) :
    H.compiledWorkingGrammarNaturalFieldValueBound dummy =
      max
        H.compiledWorkingGrammarNaturalFieldCount
        (H.compiledWorkingGrammarMaximumNaturalFieldValue
          dummy) := by

  classical

  unfold
    compiledWorkingGrammarNaturalFieldValueBound
    compiledWorkingGrammarMaximumNaturalFieldValue
    naturalFieldValueBound

  rw [
    H.encodeCompiledWorkingGrammarNaturalList_length
      dummy
  ]

/-- The complete grammar natural-field count is bounded by the single field
value bound. -/
theorem
    compiledWorkingGrammarNaturalFieldCount_le_valueBound
    (dummy : α) :
    H.compiledWorkingGrammarNaturalFieldCount <=
      H.compiledWorkingGrammarNaturalFieldValueBound
        dummy := by

  classical

  rw [
    ← H.encodeCompiledWorkingGrammarNaturalList_length
      dummy
  ]

  exact
    fieldCount_le_naturalFieldValueBound
      (H.encodeCompiledWorkingGrammarNaturalList
        dummy)

/-- Every natural field in the complete grammar serialization is bounded by the
single grammar field-value bound. -/
theorem
    compiledWorkingGrammarNaturalField_le_valueBound_of_mem
    (dummy : α)
    {n : Nat}
    (hn :
      n ∈
        H.encodeCompiledWorkingGrammarNaturalList
          dummy) :
    n <=
      H.compiledWorkingGrammarNaturalFieldValueBound
        dummy := by

  exact
    field_le_naturalFieldValueBound_of_mem
      (H.encodeCompiledWorkingGrammarNaturalList
        dummy)
      hn

/-- The complete grammar natural serialization fits the standard binary length
of its single field-value bound. -/
theorem
    compiledWorkingGrammarNaturalFieldsFitInBits_binaryNatCodeLength_valueBound
    (dummy : α) :
    H.compiledWorkingGrammarNaturalFieldsFitInBits
        dummy
        (binaryNatCodeLength
          (H.compiledWorkingGrammarNaturalFieldValueBound
            dummy)) := by

  exact
    naturalFieldStreamFitsInBits_binaryNatCodeLength_valueBound
      (H.encodeCompiledWorkingGrammarNaturalList
        dummy)

/-- The internally selected least grammar field width is bounded by the binary
length of the single field-value bound. -/
theorem
    compiledWorkingGrammarAutomaticNaturalFieldBitWidth_le_binaryNatCodeLength_valueBound
    (dummy : α) :
    H.compiledWorkingGrammarAutomaticNaturalFieldBitWidth
        dummy <=
      binaryNatCodeLength
        (H.compiledWorkingGrammarNaturalFieldValueBound
          dummy) := by

  exact
    automaticNaturalFieldBitWidth_le_binaryNatCodeLength_valueBound
      (H.encodeCompiledWorkingGrammarNaturalList
        dummy)

/-- Unconditional complete-grammar bit-size bound expressed using only natural
field count and one maximum natural field value. -/
theorem
    compiledWorkingGrammarLogarithmicBitCount_le_binaryNatCodeLength_valueBound
    (dummy : α) :
    H.compiledWorkingGrammarLogarithmicBitCount dummy <=
      (H.compiledWorkingGrammarNaturalFieldCount + 1) *
        (2 *
            binaryNatCodeLength
              (H.compiledWorkingGrammarNaturalFieldValueBound
                dummy) +
          1) := by

  classical

  have hbound :=
    encodeBinaryTreeNatListBits_length_le_binaryNatCodeLength_valueBound
      (H.encodeCompiledWorkingGrammarNaturalList
        dummy)

  rw [
    H.encodeCompiledWorkingGrammarLogarithmicBitList_length
      dummy
  ] at hbound

  simpa [
    H.encodeCompiledWorkingGrammarNaturalList_length
      dummy
  ] using hbound

/-- The maximum recursive field cost is bounded by the same one-value standard
binary width. -/
theorem
    compiledWorkingGrammarMaximumFieldBitCost_le_binaryNatCodeLength_valueBound
    (dummy : α) :
    H.compiledWorkingGrammarMaximumFieldBitCost dummy <=
      2 *
          binaryNatCodeLength
            (H.compiledWorkingGrammarNaturalFieldValueBound
              dummy) +
        1 := by

  exact
    maximumBinaryTreeNatBitCost_le_binaryNatCodeLength_valueBound
      (H.encodeCompiledWorkingGrammarNaturalList
        dummy)

/-- Compact actual-grammar maximum-field reduction endpoint. -/
theorem compiledWorkingGrammarNaturalFieldMaximum_package
    (dummy : α) :
    (H.compiledWorkingGrammarNaturalFieldCount <=
      H.compiledWorkingGrammarNaturalFieldValueBound
        dummy) ∧
      (∀ n ∈
          H.encodeCompiledWorkingGrammarNaturalList
            dummy,
        n <=
          H.compiledWorkingGrammarNaturalFieldValueBound
            dummy) ∧
      (H.compiledWorkingGrammarAutomaticNaturalFieldBitWidth
          dummy <=
        binaryNatCodeLength
          (H.compiledWorkingGrammarNaturalFieldValueBound
            dummy)) ∧
      (H.compiledWorkingGrammarMaximumFieldBitCost dummy <=
        2 *
            binaryNatCodeLength
              (H.compiledWorkingGrammarNaturalFieldValueBound
                dummy) +
          1) ∧
      (H.compiledWorkingGrammarLogarithmicBitCount dummy <=
        (H.compiledWorkingGrammarNaturalFieldCount + 1) *
          (2 *
              binaryNatCodeLength
                (H.compiledWorkingGrammarNaturalFieldValueBound
                  dummy) +
            1)) := by

  exact
    ⟨H.compiledWorkingGrammarNaturalFieldCount_le_valueBound
        dummy,
      by
        intro n hn
        exact
          H.compiledWorkingGrammarNaturalField_le_valueBound_of_mem
            dummy hn,
      H.compiledWorkingGrammarAutomaticNaturalFieldBitWidth_le_binaryNatCodeLength_valueBound
        dummy,
      H.compiledWorkingGrammarMaximumFieldBitCost_le_binaryNatCodeLength_valueBound
        dummy,
      H.compiledWorkingGrammarLogarithmicBitCount_le_binaryNatCodeLength_valueBound
        dummy⟩

end CorrectedConcreteFiniteHypothesis

end CompleteWorkingGrammarNaturalFieldMaximum

end MCFG
