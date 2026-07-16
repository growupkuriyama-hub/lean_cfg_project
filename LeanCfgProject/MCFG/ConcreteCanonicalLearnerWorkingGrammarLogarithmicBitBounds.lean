/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG.ConcreteCanonicalLearnerWorkingGrammarLogarithmicBitSerialization

/-!
# ConcreteCanonicalLearnerWorkingGrammarLogarithmicBitBounds.lean

The preceding file constructs a complete checked self-delimiting bit codec for
the pure-natural serialization of the cut-compiled grammar.  Its exact natural
field cost is the recursively defined value

```lean
binaryTreeNatBitCost n.
```

This file connects that recursive cost to the previously introduced standard
binary payload length

```lean
binaryNatCodeLength n = n.log2 + 1.
```

The key arithmetic statement is first proved in a power-envelope form:

```text
n < 2^b
⇒
binaryTreeNatBitCost n ≤ 2b + 1.
```

This avoids making the proof depend on a delicate recursive rewriting theorem
for `Nat.log2`.  Instantiating the envelope with the already verified fact

```lean
n < 2^(binaryNatCodeLength n)
```

gives the explicit logarithmic estimate

```text
binaryTreeNatBitCost n
  ≤ 2 * binaryNatCodeLength n + 1.
```

For a finite natural stream, we define the maximum standard binary payload
length and prove

```text
maximumBinaryTreeNatBitCost fields
  ≤
2 * maximumBinaryNatCodeLength fields + 1.
```

Finally, if a positive bit width `b` contains both

* the number of natural fields, and
* every natural field value,

then the complete checked bit serialization satisfies

```text
bitLength ≤ (fieldCount + 1) * (2b + 1).
```

The same theorem is packaged for the actual cut-compiled grammar:

```text
compiledGrammarBitCount
  ≤
(naturalFieldCount + 1) * (2b + 1).
```

The next layer may therefore focus only on bounding the concrete natural field
values produced by the grammar serializer.

No target grammar is supplied to the learner.
No `sorry`, `admit`, or `axiom` is used.
-/

namespace MCFG

universe u v

section BinaryTreeCostPowerEnvelope

/-- A natural below `2^bitWidth` has binary-tree self-delimiting code cost at
most `2 * bitWidth + 1`. -/
theorem binaryTreeNatBitCost_le_of_lt_two_pow :
    ∀ (bitWidth n : Nat),
      n < 2 ^ bitWidth →
        binaryTreeNatBitCost n <=
          2 * bitWidth + 1

  | 0, n, hcode => by
      have hn :
          n = 0 := by
        simp at hcode
        omega

      subst n

      simp [binaryTreeNatBitCost]

  | Nat.succ bitWidth, 0, hcode => by
      simp [binaryTreeNatBitCost]

  | Nat.succ bitWidth, Nat.succ n, hcode => by
      have hnBeforePower :
          n < 2 ^ Nat.succ bitWidth :=
        (Nat.lt_succ_self n).trans hcode

      have hnBeforeProduct :
          n < 2 * 2 ^ bitWidth := by
        simpa [
          pow_succ,
          Nat.mul_comm
        ] using hnBeforePower

      have hhalf :
          n / 2 < 2 ^ bitWidth :=
        Nat.div_lt_of_lt_mul hnBeforeProduct

      have hrecursive :
          binaryTreeNatBitCost (n / 2) <=
            2 * bitWidth + 1 :=
        binaryTreeNatBitCost_le_of_lt_two_pow
          bitWidth (n / 2) hhalf

      simp [binaryTreeNatBitCost]

      omega

/-- Explicit logarithmic upper bound for the recursive binary-tree natural
code. -/
theorem
    binaryTreeNatBitCost_le_two_mul_binaryNatCodeLength_add_one
    (n : Nat) :
    binaryTreeNatBitCost n <=
      2 * binaryNatCodeLength n + 1 := by

  exact
    binaryTreeNatBitCost_le_of_lt_two_pow
      (binaryNatCodeLength n)
      n
      (natCode_lt_two_pow_binaryNatCodeLength n)

/-- The actual encoded bit-list length obeys the same standard binary-length
bound. -/
theorem
    encodeBinaryTreeNatBits_length_le_two_mul_binaryNatCodeLength_add_one
    (n : Nat) :
    (encodeBinaryTreeNatBits n).length <=
      2 * binaryNatCodeLength n + 1 := by

  rw [encodeBinaryTreeNatBits_length]

  exact
    binaryTreeNatBitCost_le_two_mul_binaryNatCodeLength_add_one
      n

/-- Compact one-field logarithmic-cost package. -/
theorem binaryTreeNatBitCost_logarithmic_package
    (n : Nat) :
    ((encodeBinaryTreeNatBits n).length =
      binaryTreeNatBitCost n) ∧
      (binaryTreeNatBitCost n <=
        2 * binaryNatCodeLength n + 1) := by

  exact
    ⟨encodeBinaryTreeNatBits_length n,
      binaryTreeNatBitCost_le_two_mul_binaryNatCodeLength_add_one
        n⟩

end BinaryTreeCostPowerEnvelope


section MaximumStandardBinaryFieldLength

/-- Maximum standard binary payload length among a finite natural list. -/
def maximumBinaryNatCodeLength :
    List Nat → Nat

  | [] =>
      0

  | n :: ns =>
      max
        (binaryNatCodeLength n)
        (maximumBinaryNatCodeLength ns)

/-- Every member field has standard binary length at most the list maximum. -/
theorem binaryNatCodeLength_le_maximum_of_mem
    (n : Nat) :
    ∀ (fields : List Nat),
      n ∈ fields →
        binaryNatCodeLength n <=
          maximumBinaryNatCodeLength fields

  | [], hmem => by
      simp at hmem

  | field :: fields, hmem => by
      rcases List.mem_cons.mp hmem with
        hhead | htail

      · subst field

        exact
          Nat.le_max_left
            (binaryNatCodeLength n)
            (maximumBinaryNatCodeLength fields)

      · exact
          (binaryNatCodeLength_le_maximum_of_mem
              n fields htail).trans
            (Nat.le_max_right
              (binaryNatCodeLength field)
              (maximumBinaryNatCodeLength fields))

/-- The maximum recursive binary-tree cost is bounded by twice the maximum
standard binary payload length plus one. -/
theorem
    maximumBinaryTreeNatBitCost_le_two_mul_maximumBinaryNatCodeLength_add_one :
    ∀ fields : List Nat,
      maximumBinaryTreeNatBitCost fields <=
        2 * maximumBinaryNatCodeLength fields + 1

  | [] => by
      simp [
        maximumBinaryTreeNatBitCost,
        maximumBinaryNatCodeLength
      ]

  | n :: ns => by
      change
        max
            (binaryTreeNatBitCost n)
            (maximumBinaryTreeNatBitCost ns) <=
          2 *
              max
                (binaryNatCodeLength n)
                (maximumBinaryNatCodeLength ns) +
            1

      apply max_le

      · exact
          (binaryTreeNatBitCost_le_two_mul_binaryNatCodeLength_add_one
              n).trans
            (Nat.add_le_add_right
              (Nat.mul_le_mul_left
                2
                (Nat.le_max_left
                  (binaryNatCodeLength n)
                  (maximumBinaryNatCodeLength ns)))
              1)

      · exact
          (maximumBinaryTreeNatBitCost_le_two_mul_maximumBinaryNatCodeLength_add_one
              ns).trans
            (Nat.add_le_add_right
              (Nat.mul_le_mul_left
                2
                (Nat.le_max_right
                  (binaryNatCodeLength n)
                  (maximumBinaryNatCodeLength ns)))
              1)

/-- If every field lies below `2^bitWidth` and the width is positive, then the
maximum standard binary payload length is at most `bitWidth`. -/
theorem maximumBinaryNatCodeLength_le_of_pos_of_all_lt_two_pow
    {bitWidth : Nat}
    (hpositive : 0 < bitWidth) :
    ∀ fields : List Nat,
      (∀ n ∈ fields,
        n < 2 ^ bitWidth) →
      maximumBinaryNatCodeLength fields <=
        bitWidth

  | [], hall => by
      simp [maximumBinaryNatCodeLength]

  | n :: ns, hall => by
      change
        max
            (binaryNatCodeLength n)
            (maximumBinaryNatCodeLength ns) <=
          bitWidth

      apply max_le

      · exact
          binaryNatCodeLength_le_of_pos_of_lt_two_pow
            hpositive
            (hall n (by simp))

      · apply
          maximumBinaryNatCodeLength_le_of_pos_of_all_lt_two_pow
            hpositive ns

        intro field hfield

        exact
          hall field
            (by simp [hfield])

end MaximumStandardBinaryFieldLength


section FiniteNaturalStreamLogarithmicBound

/-- A common positive bit width contains a natural-field stream when it contains
both the field count and every field value. -/
def BinaryTreeNaturalFieldStreamFitsInBits
    (fields : List Nat)
    (bitWidth : Nat) :
    Prop :=
  0 < bitWidth ∧
    fields.length < 2 ^ bitWidth ∧
    ∀ n ∈ fields,
      n < 2 ^ bitWidth

/-- Under a common fitting bit width, the maximum standard binary length among
the count header and all payload fields is at most that width. -/
theorem maximumBinaryNatCodeLength_count_cons_le_of_fitsInBits
    {fields : List Nat}
    {bitWidth : Nat}
    (hfit :
      BinaryTreeNaturalFieldStreamFitsInBits
        fields bitWidth) :
    maximumBinaryNatCodeLength
        (fields.length :: fields) <=
      bitWidth := by

  rcases hfit with
    ⟨hpositive, hcount, hfields⟩

  apply
    maximumBinaryNatCodeLength_le_of_pos_of_all_lt_two_pow
      hpositive

  intro n hn

  rcases List.mem_cons.mp hn with
    hhead | htail

  · subst n
    exact hcount

  · exact hfields n htail

/-- Under a common fitting bit width, the maximum recursive binary-tree field
cost is at most `2 * bitWidth + 1`. -/
theorem maximumBinaryTreeNatBitCost_count_cons_le_of_fitsInBits
    {fields : List Nat}
    {bitWidth : Nat}
    (hfit :
      BinaryTreeNaturalFieldStreamFitsInBits
        fields bitWidth) :
    maximumBinaryTreeNatBitCost
        (fields.length :: fields) <=
      2 * bitWidth + 1 := by

  exact
    (maximumBinaryTreeNatBitCost_le_two_mul_maximumBinaryNatCodeLength_add_one
        (fields.length :: fields)).trans
      (Nat.add_le_add_right
        (Nat.mul_le_mul_left
          2
          (maximumBinaryNatCodeLength_count_cons_le_of_fitsInBits
            hfit))
        1)

/-- A complete checked binary-tree natural-list encoding has total bit length
at most `(fieldCount + 1) * (2 * bitWidth + 1)` whenever all fields fit the
common positive width. -/
theorem
    encodeBinaryTreeNatListBits_length_le_of_fieldsFitInBits
    {fields : List Nat}
    {bitWidth : Nat}
    (hfit :
      BinaryTreeNaturalFieldStreamFitsInBits
        fields bitWidth) :
    (encodeBinaryTreeNatListBits fields).length <=
      (fields.length + 1) *
        (2 * bitWidth + 1) := by

  exact
    (encodeBinaryTreeNatListBits_length_le_count_mul_maximum
        fields).trans
      (Nat.mul_le_mul_left
        (fields.length + 1)
        (maximumBinaryTreeNatBitCost_count_cons_le_of_fitsInBits
          hfit))

/-- Compact finite-stream logarithmic bound package. -/
theorem binaryTreeNaturalFieldStream_logarithmic_package
    {fields : List Nat}
    {bitWidth : Nat}
    (hfit :
      BinaryTreeNaturalFieldStreamFitsInBits
        fields bitWidth) :
    (maximumBinaryNatCodeLength
        (fields.length :: fields) <=
      bitWidth) ∧
      (maximumBinaryTreeNatBitCost
          (fields.length :: fields) <=
        2 * bitWidth + 1) ∧
      ((encodeBinaryTreeNatListBits fields).length <=
        (fields.length + 1) *
          (2 * bitWidth + 1)) := by

  exact
    ⟨maximumBinaryNatCodeLength_count_cons_le_of_fitsInBits
        hfit,
      maximumBinaryTreeNatBitCost_count_cons_le_of_fitsInBits
        hfit,
      encodeBinaryTreeNatListBits_length_le_of_fieldsFitInBits
        hfit⟩

end FiniteNaturalStreamLogarithmicBound


section CompleteWorkingGrammarExplicitLogarithmicBound

variable {α : Type u}
variable {M : Type v} [Monoid M]
variable {K : Finset (Word α)}
variable {obs : α → M}
variable {f : Nat}

namespace CorrectedConcreteFiniteHypothesis

variable
  (H : CorrectedConcreteFiniteHypothesis K obs f)

/-- A positive bit width contains the complete pure-natural grammar
serialization when it contains its field count and every serialized natural
field. -/
noncomputable def compiledWorkingGrammarNaturalFieldsFitInBits
    (dummy : α)
    (bitWidth : Nat) :
    Prop :=
  BinaryTreeNaturalFieldStreamFitsInBits
    (H.encodeCompiledWorkingGrammarNaturalList
      dummy)
    bitWidth

/-- The maximum standard binary payload length used by the complete grammar
natural serialization. -/
noncomputable def compiledWorkingGrammarMaximumBinaryFieldLength
    (dummy : α) :
    Nat :=
  let fields :=
    H.encodeCompiledWorkingGrammarNaturalList
      dummy

  maximumBinaryNatCodeLength
    (fields.length :: fields)

/-- The recursive maximum field cost is bounded by twice the maximum standard
binary field length plus one. -/
theorem
    compiledWorkingGrammarMaximumFieldBitCost_le_logarithmic
    (dummy : α) :
    H.compiledWorkingGrammarMaximumFieldBitCost dummy <=
      2 *
          H.compiledWorkingGrammarMaximumBinaryFieldLength
            dummy +
        1 := by

  classical

  unfold
    compiledWorkingGrammarMaximumFieldBitCost
    compiledWorkingGrammarMaximumBinaryFieldLength

  exact
    maximumBinaryTreeNatBitCost_le_two_mul_maximumBinaryNatCodeLength_add_one
      ((H.encodeCompiledWorkingGrammarNaturalList
        dummy).length ::
        H.encodeCompiledWorkingGrammarNaturalList
          dummy)

/-- Explicit whole-grammar `fieldCount × bitWidth` bound. -/
theorem
    compiledWorkingGrammarLogarithmicBitCount_le_of_naturalFieldsFitInBits
    (dummy : α)
    {bitWidth : Nat}
    (hfit :
      H.compiledWorkingGrammarNaturalFieldsFitInBits
        dummy bitWidth) :
    H.compiledWorkingGrammarLogarithmicBitCount dummy <=
      (H.compiledWorkingGrammarNaturalFieldCount dummy + 1) *
        (2 * bitWidth + 1) := by

  classical

  have hstream :
      (encodeBinaryTreeNatListBits
          (H.encodeCompiledWorkingGrammarNaturalList
            dummy)).length <=
        ((H.encodeCompiledWorkingGrammarNaturalList
            dummy).length + 1) *
          (2 * bitWidth + 1) :=
    encodeBinaryTreeNatListBits_length_le_of_fieldsFitInBits
      hfit

  rw [
    H.encodeCompiledWorkingGrammarLogarithmicBitList_length
      dummy
  ] at hstream

  simpa [
    H.encodeCompiledWorkingGrammarNaturalList_length
      dummy
  ] using hstream

/-- Compact actual-grammar explicit logarithmic-size package. -/
theorem compiledWorkingGrammarExplicitLogarithmicBitBound_package
    (dummy : α)
    {bitWidth : Nat}
    (hfit :
      H.compiledWorkingGrammarNaturalFieldsFitInBits
        dummy bitWidth) :
    (H.decodeCompiledWorkingGrammarLogarithmicBitList dummy
        (H.encodeCompiledWorkingGrammarLogarithmicBitList
          dummy) =
      some
        (H.compiledGrammarPresentationEntries dummy)) ∧
      (H.compiledWorkingGrammarMaximumFieldBitCost dummy <=
        2 *
            H.compiledWorkingGrammarMaximumBinaryFieldLength
              dummy +
          1) ∧
      (H.compiledWorkingGrammarLogarithmicBitCount dummy <=
        (H.compiledWorkingGrammarNaturalFieldCount dummy + 1) *
          (2 * bitWidth + 1)) := by

  exact
    ⟨H.decodeCompiledWorkingGrammarLogarithmicBitList_encode
        dummy,
      H.compiledWorkingGrammarMaximumFieldBitCost_le_logarithmic
        dummy,
      H.compiledWorkingGrammarLogarithmicBitCount_le_of_naturalFieldsFitInBits
        dummy hfit⟩

end CorrectedConcreteFiniteHypothesis

end CompleteWorkingGrammarExplicitLogarithmicBound

end MCFG
