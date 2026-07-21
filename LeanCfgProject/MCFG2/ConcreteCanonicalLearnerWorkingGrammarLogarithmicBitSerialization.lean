/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG2.ConcreteCanonicalLearnerWorkingGrammarUnaryBitSerialization

/-!
# ConcreteCanonicalLearnerWorkingGrammarLogarithmicBitSerialization.lean

The preceding file gives a complete checked unary bit codec for the pure-natural
serialization of the cut-compiled grammar.  This file replaces the unary code
of each natural field by a binary-tree self-delimiting code.

The code is defined recursively by

```text
code(0)     = 1
code(n + 1) = 0 · code(n / 2) · parity(n).
```

The decoder first reads the leading constructor bit.  In the successor case it
recursively decodes the quotient and then consumes exactly one parity bit.  The
reconstruction equation is

```text
n = 2 * (n / 2) + (n mod 2).
```

The exact code cost satisfies

```text
L(0)     = 1
L(n + 1) = L(n / 2) + 2.
```

Thus every two constructor levels remove one binary digit rather than one unary
unit.  The present file proves the complete structural codec and its exact
recursive cost.  The separate next arithmetic layer may identify this cost with
an explicit `Nat.log2` upper bound.

A finite natural list is encoded by first encoding its field count and then
concatenating the field codes.  The decoder recovers exactly the declared number
of fields and rejects trailing bits.  The complete learner output therefore has
a checked logarithmic-structure bit serialization.

For a field list `fields`, define the largest recursive field cost among the
count header and all payload fields.  The bit length is bounded by

```text
(fields.length + 1) * maximumFieldCost.
```

The complete compiled-grammar bound is consequently

```text
(naturalFieldCount + 1) * compiledMaximumFieldCost.
```

No target grammar is supplied to the learner.
No `sorry`, `admit`, or `axiom` is used.
-/

namespace MCFG

universe u v

section BinaryTreeNaturalCodecArithmetic

/-- Numerical value of one payload bit. -/
def naturalValueOfBool :
    Bool → Nat

  | false =>
      0

  | true =>
      1

/-- The parity bit used by the binary-tree natural codec. -/
def naturalParityBit
    (n : Nat) :
    Bool :=
  decide (n % 2 = 1)

/-- The numerical value of the parity bit is exactly the remainder modulo two. -/
@[simp] theorem naturalValueOfBool_naturalParityBit
    (n : Nat) :
    naturalValueOfBool (naturalParityBit n) =
      n % 2 := by

  have hmodLt :
      n % 2 < 2 :=
    Nat.mod_lt n (by decide)

  have hcases :
      n % 2 = 0 ∨ n % 2 = 1 := by
    omega

  rcases hcases with hzero | hone

  · simp [
      naturalParityBit,
      naturalValueOfBool,
      hzero
    ]

  · simp [
      naturalParityBit,
      naturalValueOfBool,
      hone
    ]

/-- Quotient and parity reconstruct the predecessor used by the successor code. -/
theorem binaryTreeNatural_reconstruction
    (n : Nat) :
    2 * (n / 2) +
          naturalValueOfBool (naturalParityBit n) +
        1 =
      n + 1 := by

  rw [naturalValueOfBool_naturalParityBit]

  have hdivision :
      n % 2 + 2 * (n / 2) = n :=
    Nat.mod_add_div n 2

  omega

end BinaryTreeNaturalCodecArithmetic


section BinaryTreeNaturalBitCodec

/-- Self-delimiting binary-tree encoding of one natural number.

Zero is a leaf.  A successor stores a constructor bit, recursively stores the
half-sized predecessor, and finally stores its parity bit. -/
def encodeBinaryTreeNatBits :
    (n : Nat) → List Bool

  | 0 =>
      [true]

  | Nat.succ n =>
      false ::
        (encodeBinaryTreeNatBits (n / 2) ++
          [naturalParityBit n])

termination_by n => n
decreasing_by
  omega

/-- Checked decoder for one binary-tree natural code, retaining the unconsumed
bit suffix. -/
def decodeBinaryTreeNatBits :
    List Bool → Option (Nat × List Bool)

  | [] =>
      none

  | true :: suffix =>
      some (0, suffix)

  | false :: rest =>
      match decodeBinaryTreeNatBits rest with

      | none =>
          none

      | some (_, []) =>
          none

      | some (quotient, parity :: suffix) =>
          some
            (2 * quotient +
                naturalValueOfBool parity +
              1,
              suffix)

/-- Decoding an encoded natural number consumes exactly its code and preserves
an arbitrary following suffix. -/
theorem decodeBinaryTreeNatBits_encode_append :
    ∀ (n : Nat) (suffix : List Bool),
      decodeBinaryTreeNatBits
          (encodeBinaryTreeNatBits n ++ suffix) =
        some (n, suffix)

  | 0, suffix => by
      rfl

  | Nat.succ n, suffix => by
      have hrecursive :
          decodeBinaryTreeNatBits
              (encodeBinaryTreeNatBits (n / 2) ++
                naturalParityBit n :: suffix) =
            some
              (n / 2,
                naturalParityBit n :: suffix) :=
        decodeBinaryTreeNatBits_encode_append
          (n / 2)
          (naturalParityBit n :: suffix)

      simp [
        encodeBinaryTreeNatBits,
        decodeBinaryTreeNatBits,
        List.append_assoc,
        hrecursive,
        binaryTreeNatural_reconstruction
      ]

termination_by n suffix => n
decreasing_by
  omega

/-- Recursive exact cost of the binary-tree natural code. -/
def binaryTreeNatBitCost :
    (n : Nat) → Nat

  | 0 =>
      1

  | Nat.succ n =>
      binaryTreeNatBitCost (n / 2) + 2

termination_by n => n
decreasing_by
  omega

/-- The recursive cost is exactly the actual bit-list length. -/
@[simp] theorem encodeBinaryTreeNatBits_length :
    ∀ n : Nat,
      (encodeBinaryTreeNatBits n).length =
        binaryTreeNatBitCost n

  | 0 => by
      rfl

  | Nat.succ n => by
      simp [
        encodeBinaryTreeNatBits,
        binaryTreeNatBitCost,
        encodeBinaryTreeNatBits_length (n / 2),
        Nat.add_assoc,
        Nat.add_comm,
        Nat.add_left_comm
      ]

termination_by n => n
decreasing_by
  omega

/-- Every binary-tree natural code is nonempty. -/
theorem encodeBinaryTreeNatBits_ne_nil
    (n : Nat) :
    encodeBinaryTreeNatBits n ≠ [] := by

  intro hnil

  have hlength :
      (encodeBinaryTreeNatBits n).length = 0 := by
    simpa [hnil]

  rw [encodeBinaryTreeNatBits_length] at hlength

  cases n with

  | zero =>
      simp [binaryTreeNatBitCost] at hlength

  | succ n =>
      simp [binaryTreeNatBitCost] at hlength

/-- Exact decoding makes the binary-tree natural code injective. -/
theorem encodeBinaryTreeNatBits_injective
    {m n : Nat}
    (hcode :
      encodeBinaryTreeNatBits m =
        encodeBinaryTreeNatBits n) :
    m = n := by

  have hm :
      decodeBinaryTreeNatBits
          (encodeBinaryTreeNatBits m) =
        some (m, []) := by

    simpa using
      decodeBinaryTreeNatBits_encode_append
        m []

  have hn :
      decodeBinaryTreeNatBits
          (encodeBinaryTreeNatBits n) =
        some (n, []) := by

    simpa using
      decodeBinaryTreeNatBits_encode_append
        n []

  rw [hcode] at hm
  rw [hn] at hm

  injection hm

/-- Compact standalone natural-code package. -/
theorem binaryTreeNatBitCodec_package
    (n : Nat) :
    (decodeBinaryTreeNatBits
        (encodeBinaryTreeNatBits n) =
      some (n, [])) ∧
      ((encodeBinaryTreeNatBits n).length =
        binaryTreeNatBitCost n) := by

  constructor

  · simpa using
      decodeBinaryTreeNatBits_encode_append
        n []

  · exact
      encodeBinaryTreeNatBits_length n

end BinaryTreeNaturalBitCodec


section BinaryTreeNaturalListBitCodec

/-- Concatenate binary-tree codes for an ordered list of natural fields. -/
def encodeBinaryTreeNatListPayload :
    List Nat → List Bool

  | [] =>
      []

  | n :: ns =>
      encodeBinaryTreeNatBits n ++
        encodeBinaryTreeNatListPayload ns

/-- Decode exactly the prescribed number of binary-tree natural fields,
retaining the unconsumed bit suffix. -/
def decodeBinaryTreeNatListPayloadAux :
    Nat → List Bool →
      Option (List Nat × List Bool)

  | 0, bits =>
      some ([], bits)

  | Nat.succ _, [] =>
      none

  | Nat.succ fieldCount, bits =>
      match decodeBinaryTreeNatBits bits with

      | none =>
          none

      | some (n, rest) =>
          match
              decodeBinaryTreeNatListPayloadAux
                fieldCount rest with

          | none =>
              none

          | some (ns, suffix) =>
              some (n :: ns, suffix)

/-- Decoding an encoded field payload consumes exactly that payload and
preserves an arbitrary following suffix. -/
theorem
    decodeBinaryTreeNatListPayloadAux_encode_append :
    ∀ (fields : List Nat) (suffix : List Bool),
      decodeBinaryTreeNatListPayloadAux
          fields.length
          (encodeBinaryTreeNatListPayload fields ++ suffix) =
        some (fields, suffix)

  | [], suffix => by
      rfl

  | n :: ns, suffix => by
      simp [
        encodeBinaryTreeNatListPayload,
        decodeBinaryTreeNatListPayloadAux,
        List.append_assoc,
        decodeBinaryTreeNatBits_encode_append,
        decodeBinaryTreeNatListPayloadAux_encode_append
          ns suffix
      ]

/-- Exact bit length of the concatenated field payload. -/
@[simp] theorem encodeBinaryTreeNatListPayload_length :
    ∀ fields : List Nat,
      (encodeBinaryTreeNatListPayload fields).length =
        (fields.map binaryTreeNatBitCost).sum

  | [] => by
      rfl

  | n :: ns => by
      simp [
        encodeBinaryTreeNatListPayload,
        encodeBinaryTreeNatListPayload_length ns,
        Nat.add_assoc
      ]

/-- Complete self-delimiting encoding of a finite natural list.

The number of following fields is encoded first. -/
def encodeBinaryTreeNatListBits
    (fields : List Nat) :
    List Bool :=
  encodeBinaryTreeNatBits fields.length ++
    encodeBinaryTreeNatListPayload fields

/-- Checked complete decoder.  The field-count code is read first, exactly that
many fields must follow, and trailing bits are rejected. -/
def decodeBinaryTreeNatListBits
    (bits : List Bool) :
    Option (List Nat) :=

  match decodeBinaryTreeNatBits bits with

  | none =>
      none

  | some (fieldCount, payload) =>
      match
          decodeBinaryTreeNatListPayloadAux
            fieldCount payload with

      | some (fields, []) =>
          some fields

      | _ =>
          none

/-- Complete natural-list round trip for the binary-tree bit codec. -/
@[simp] theorem decodeBinaryTreeNatListBits_encode
    (fields : List Nat) :
    decodeBinaryTreeNatListBits
        (encodeBinaryTreeNatListBits fields) =
      some fields := by

  unfold
    encodeBinaryTreeNatListBits
    decodeBinaryTreeNatListBits

  rw [
    decodeBinaryTreeNatBits_encode_append
      fields.length
      (encodeBinaryTreeNatListPayload fields)
  ]

  have hpayload :
      decodeBinaryTreeNatListPayloadAux
          fields.length
          (encodeBinaryTreeNatListPayload fields) =
        some (fields, []) := by

    simpa using
      decodeBinaryTreeNatListPayloadAux_encode_append
        fields []

  rw [hpayload]

/-- Exact bit length of a complete encoded natural list. -/
@[simp] theorem encodeBinaryTreeNatListBits_length
    (fields : List Nat) :
    (encodeBinaryTreeNatListBits fields).length =
      binaryTreeNatBitCost fields.length +
        (fields.map binaryTreeNatBitCost).sum := by

  simp [
    encodeBinaryTreeNatListBits,
    Nat.add_assoc
  ]

/-- The complete field-list code is injective. -/
theorem encodeBinaryTreeNatListBits_injective
    {xs ys : List Nat}
    (hcode :
      encodeBinaryTreeNatListBits xs =
        encodeBinaryTreeNatListBits ys) :
    xs = ys := by

  have hx :
      decodeBinaryTreeNatListBits
          (encodeBinaryTreeNatListBits xs) =
        some xs := by
    simp

  have hy :
      decodeBinaryTreeNatListBits
          (encodeBinaryTreeNatListBits ys) =
        some ys := by
    simp

  rw [hcode] at hx
  rw [hy] at hx

  injection hx

end BinaryTreeNaturalListBitCodec


section MaximumBinaryTreeFieldCost

/-- Maximum recursive binary-tree code cost in a finite natural list. -/
def maximumBinaryTreeNatBitCost :
    List Nat → Nat

  | [] =>
      0

  | n :: ns =>
      max
        (binaryTreeNatBitCost n)
        (maximumBinaryTreeNatBitCost ns)

/-- Every member field cost is bounded by the list maximum. -/
theorem binaryTreeNatBitCost_le_maximum_of_mem
    (n : Nat) :
    ∀ (fields : List Nat),
      n ∈ fields →
        binaryTreeNatBitCost n <=
          maximumBinaryTreeNatBitCost fields

  | [], hmem => by
      simp at hmem

  | field :: fields, hmem => by
      rcases List.mem_cons.mp hmem with
        hhead | htail

      · subst field
        exact
          Nat.le_max_left
            (binaryTreeNatBitCost n)
            (maximumBinaryTreeNatBitCost fields)

      · exact
          (binaryTreeNatBitCost_le_maximum_of_mem
              n fields htail).trans
            (Nat.le_max_right
              (binaryTreeNatBitCost field)
              (maximumBinaryTreeNatBitCost fields))

/-- The sum of field costs is at most the number of fields times their maximum
cost. -/
theorem sum_binaryTreeNatBitCost_le_length_mul_maximum :
    ∀ fields : List Nat,
      (fields.map binaryTreeNatBitCost).sum <=
        fields.length *
          maximumBinaryTreeNatBitCost fields

  | [] => by
      simp [maximumBinaryTreeNatBitCost]

  | n :: ns => by
      have htail :
          (ns.map binaryTreeNatBitCost).sum <=
            ns.length *
              maximumBinaryTreeNatBitCost ns :=
        sum_binaryTreeNatBitCost_le_length_mul_maximum
          ns

      have htailMax :
          ns.length *
              maximumBinaryTreeNatBitCost ns <=
            ns.length *
              max
                (binaryTreeNatBitCost n)
                (maximumBinaryTreeNatBitCost ns) :=
        Nat.mul_le_mul_left
          ns.length
          (Nat.le_max_right
            (binaryTreeNatBitCost n)
            (maximumBinaryTreeNatBitCost ns))

      have hhead :
          binaryTreeNatBitCost n <=
            max
              (binaryTreeNatBitCost n)
              (maximumBinaryTreeNatBitCost ns) :=
        Nat.le_max_left
          (binaryTreeNatBitCost n)
          (maximumBinaryTreeNatBitCost ns)

      have hsum :
          binaryTreeNatBitCost n +
              (ns.map binaryTreeNatBitCost).sum <=
            max
                (binaryTreeNatBitCost n)
                (maximumBinaryTreeNatBitCost ns) +
              ns.length *
                max
                  (binaryTreeNatBitCost n)
                  (maximumBinaryTreeNatBitCost ns) :=
        Nat.add_le_add
          hhead
          (htail.trans htailMax)

      simpa [
        maximumBinaryTreeNatBitCost,
        Nat.succ_mul,
        Nat.add_assoc,
        Nat.add_comm,
        Nat.add_left_comm
      ] using hsum

/-- A complete natural-list bit stream is bounded by the number of encoded
fields, including the count header, times the largest field cost. -/
theorem encodeBinaryTreeNatListBits_length_le_count_mul_maximum
    (fields : List Nat) :
    (encodeBinaryTreeNatListBits fields).length <=
      (fields.length + 1) *
        maximumBinaryTreeNatBitCost
          (fields.length :: fields) := by

  rw [encodeBinaryTreeNatListBits_length]

  have hsum :
      ((fields.length :: fields).map
          binaryTreeNatBitCost).sum <=
        (fields.length :: fields).length *
          maximumBinaryTreeNatBitCost
            (fields.length :: fields) :=
    sum_binaryTreeNatBitCost_le_length_mul_maximum
      (fields.length :: fields)

  simpa [
    Nat.add_assoc,
    Nat.add_comm,
    Nat.add_left_comm
  ] using hsum

/-- Compact finite-list logarithmic-structure codec package. -/
theorem binaryTreeNatListBitCodec_package
    (fields : List Nat) :
    (decodeBinaryTreeNatListBits
        (encodeBinaryTreeNatListBits fields) =
      some fields) ∧
      ((encodeBinaryTreeNatListBits fields).length =
        binaryTreeNatBitCost fields.length +
          (fields.map binaryTreeNatBitCost).sum) ∧
      ((encodeBinaryTreeNatListBits fields).length <=
        (fields.length + 1) *
          maximumBinaryTreeNatBitCost
            (fields.length :: fields)) := by

  exact
    ⟨decodeBinaryTreeNatListBits_encode fields,
      encodeBinaryTreeNatListBits_length fields,
      encodeBinaryTreeNatListBits_length_le_count_mul_maximum
        fields⟩

end MaximumBinaryTreeFieldCost


section CompleteWorkingGrammarLogarithmicBitCodec

variable {α : Type u}
variable {M : Type v} [Monoid M]
variable {K : Finset (Word α)}
variable {obs : α → M}
variable {f : Nat}

namespace CorrectedConcreteFiniteHypothesis

variable
  (H : CorrectedConcreteFiniteHypothesis K obs f)

/-- Complete binary-tree bit serialization of the actual cut-compiled grammar. -/
noncomputable def encodeCompiledWorkingGrammarLogarithmicBitList
    (dummy : α) :
    List Bool :=
  encodeBinaryTreeNatListBits
    (H.encodeCompiledWorkingGrammarNaturalList
      dummy)

/-- Decode the binary-tree bit stream and then invoke the already verified
checked pure-natural grammar decoder. -/
noncomputable def decodeCompiledWorkingGrammarLogarithmicBitList
    (dummy : α)
    (bits : List Bool) :
    Option
      (List
        (CorrectedConcreteCompiledGrammarPresentationEntry H)) :=

  match decodeBinaryTreeNatListBits bits with

  | none =>
      none

  | some fields =>
      H.decodeCompiledWorkingGrammarNaturalList
        dummy fields

/-- Exact bit count of the complete binary-tree grammar serialization. -/
noncomputable def compiledWorkingGrammarLogarithmicBitCount
    (dummy : α) :
    Nat :=
  let fields :=
    H.encodeCompiledWorkingGrammarNaturalList
      dummy

  binaryTreeNatBitCost fields.length +
    (fields.map binaryTreeNatBitCost).sum

/-- Largest recursive code cost among the natural-field count header and all
natural payload fields of the compiled grammar. -/
noncomputable def compiledWorkingGrammarMaximumFieldBitCost
    (dummy : α) :
    Nat :=
  let fields :=
    H.encodeCompiledWorkingGrammarNaturalList
      dummy

  maximumBinaryTreeNatBitCost
    (fields.length :: fields)

/-- Complete cut-compiled grammar round trip through the logarithmic-structure
bit stream. -/
@[simp] theorem
    decodeCompiledWorkingGrammarLogarithmicBitList_encode
    (dummy : α) :
    H.decodeCompiledWorkingGrammarLogarithmicBitList dummy
        (H.encodeCompiledWorkingGrammarLogarithmicBitList
          dummy) =
      some
        (H.compiledGrammarPresentationEntries dummy) := by

  classical

  unfold
    encodeCompiledWorkingGrammarLogarithmicBitList
    decodeCompiledWorkingGrammarLogarithmicBitList

  rw [
    decodeBinaryTreeNatListBits_encode
      (H.encodeCompiledWorkingGrammarNaturalList
        dummy)
  ]

  exact
    H.decodeCompiledWorkingGrammarNaturalList_encode
      dummy

/-- The defined exact grammar bit count is the actual bit-list length. -/
@[simp] theorem
    encodeCompiledWorkingGrammarLogarithmicBitList_length
    (dummy : α) :
    (H.encodeCompiledWorkingGrammarLogarithmicBitList
        dummy).length =
      H.compiledWorkingGrammarLogarithmicBitCount
        dummy := by

  classical

  unfold
    encodeCompiledWorkingGrammarLogarithmicBitList
    compiledWorkingGrammarLogarithmicBitCount

  exact
    encodeBinaryTreeNatListBits_length
      (H.encodeCompiledWorkingGrammarNaturalList
        dummy)

/-- The complete grammar bit count is bounded by natural-field count times the
largest recursive field-code cost. -/
theorem
    compiledWorkingGrammarLogarithmicBitCount_le_fieldCount_mul_maximum
    (dummy : α) :
    H.compiledWorkingGrammarLogarithmicBitCount dummy <=
      (H.compiledWorkingGrammarNaturalFieldCount dummy + 1) *
        H.compiledWorkingGrammarMaximumFieldBitCost dummy := by

  classical

  have hbound :=
    encodeBinaryTreeNatListBits_length_le_count_mul_maximum
      (H.encodeCompiledWorkingGrammarNaturalList
        dummy)

  rw [
    H.encodeCompiledWorkingGrammarLogarithmicBitList_length
      dummy
  ] at hbound

  simpa [
    compiledWorkingGrammarMaximumFieldBitCost,
    H.encodeCompiledWorkingGrammarNaturalList_length
      dummy
  ] using hbound

/-- Compact whole-grammar logarithmic-structure bit-codec endpoint. -/
theorem compiledWorkingGrammarLogarithmicBitCodec_package
    (dummy : α) :
    (H.decodeCompiledWorkingGrammarLogarithmicBitList dummy
        (H.encodeCompiledWorkingGrammarLogarithmicBitList
          dummy) =
      some
        (H.compiledGrammarPresentationEntries dummy)) ∧
      ((H.encodeCompiledWorkingGrammarLogarithmicBitList
          dummy).length =
        H.compiledWorkingGrammarLogarithmicBitCount
          dummy) ∧
      (H.compiledWorkingGrammarLogarithmicBitCount dummy <=
        (H.compiledWorkingGrammarNaturalFieldCount dummy + 1) *
          H.compiledWorkingGrammarMaximumFieldBitCost
            dummy) := by

  exact
    ⟨H.decodeCompiledWorkingGrammarLogarithmicBitList_encode
        dummy,
      H.encodeCompiledWorkingGrammarLogarithmicBitList_length
        dummy,
      H.compiledWorkingGrammarLogarithmicBitCount_le_fieldCount_mul_maximum
        dummy⟩

end CorrectedConcreteFiniteHypothesis

end CompleteWorkingGrammarLogarithmicBitCodec

end MCFG
