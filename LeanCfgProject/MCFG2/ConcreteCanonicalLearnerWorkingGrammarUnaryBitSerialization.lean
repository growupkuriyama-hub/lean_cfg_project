/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG2.ConcreteCanonicalLearnerWorkingGrammarPresentationNaturalSerialization

/-!
# ConcreteCanonicalLearnerWorkingGrammarUnaryBitSerialization.lean

The preceding file constructs a complete checked `List Nat` serialization of
the actual cut-compiled grammar.  This file turns that finite natural stream into
an actual self-delimiting bit stream.

The first concrete bit codec is deliberately elementary and fully structural:

```text
0       ↦ 1
n + 1   ↦ 0 · code(n).
```

Equivalently, the natural number `n` is encoded as `n` false bits followed by
one true bit.  The code is prefix-free and its exact length is `n + 1`.

A finite natural list is encoded by first encoding the number of fields and
then concatenating the unary code of every field.  The decoder first recovers
the field count, decodes exactly that many fields, and rejects every trailing
bit.  Thus malformed truncations and trailing payloads are not silently
accepted.

The complete cut-compiled grammar bit stream is obtained by applying this list
codec to

```lean
H.encodeCompiledWorkingGrammarNaturalList dummy.
```

The main theorem is the exact whole-grammar round trip:

```lean
H.decodeCompiledWorkingGrammarUnaryBitList dummy
    (H.encodeCompiledWorkingGrammarUnaryBitList dummy)
  =
some (H.compiledGrammarPresentationEntries dummy).
```

The exact bit length is also proved.  If the pure-natural grammar stream is
`fields`, then

```text
bitLength
  =
(fields.length + 1)
  +
Σ (n in fields), (n + 1)
  =
1 + 2 * fields.length + fields.sum.
```

This unary bit layer is not yet the final asymptotically efficient encoding.
Its role is to close the first genuine bit-level, prefix-free, checked codec for
the complete learner output.  A later layer can replace the per-natural unary
payload by a logarithmic self-delimiting binary code while reusing the complete
grammar serialization proved here.

No target grammar is supplied to the learner.
No `sorry`, `admit`, or `axiom` is used.
-/

namespace MCFG

universe u v

section UnaryNaturalBitCodec

/-- Prefix-free unary bit encoding of one natural number.

`n` is represented by `n` false bits followed by one true bit. -/
def encodeUnaryNatBits :
    Nat → List Bool

  | 0 =>
      [true]

  | Nat.succ n =>
      false :: encodeUnaryNatBits n

/-- Decode one unary natural code, retaining the unconsumed bit suffix. -/
def decodeUnaryNatBits :
    List Bool → Option (Nat × List Bool)

  | [] =>
      none

  | true :: suffix =>
      some (0, suffix)

  | false :: rest =>
      match decodeUnaryNatBits rest with

      | none =>
          none

      | some (n, suffix) =>
          some (Nat.succ n, suffix)

/-- Decoding an encoded natural number consumes exactly its code and preserves
an arbitrary following suffix. -/
theorem decodeUnaryNatBits_encode_append :
    ∀ (n : Nat) (suffix : List Bool),
      decodeUnaryNatBits
          (encodeUnaryNatBits n ++ suffix) =
        some (n, suffix)

  | 0, suffix => by
      rfl

  | Nat.succ n, suffix => by
      simp [
        encodeUnaryNatBits,
        decodeUnaryNatBits,
        decodeUnaryNatBits_encode_append n suffix
      ]

/-- Exact unary bit length of one natural code. -/
@[simp] theorem encodeUnaryNatBits_length :
    ∀ n : Nat,
      (encodeUnaryNatBits n).length =
        n + 1

  | 0 => by
      rfl

  | Nat.succ n => by
      simp [
        encodeUnaryNatBits,
        encodeUnaryNatBits_length n,
        Nat.succ_eq_add_one,
        Nat.add_assoc
      ]

/-- Every unary natural code is nonempty. -/
theorem encodeUnaryNatBits_ne_nil
    (n : Nat) :
    encodeUnaryNatBits n ≠ [] := by

  intro h

  have hlength :
      (encodeUnaryNatBits n).length = 0 := by
    simpa [h]

  rw [encodeUnaryNatBits_length] at hlength
  omega

/-- Exact decoding determines the encoded natural number. -/
theorem encodeUnaryNatBits_injective
    {m n : Nat}
    (h :
      encodeUnaryNatBits m =
        encodeUnaryNatBits n) :
    m = n := by

  have hm :
      decodeUnaryNatBits
          (encodeUnaryNatBits m) =
        some (m, []) := by

    simpa using
      decodeUnaryNatBits_encode_append
        m []

  have hn :
      decodeUnaryNatBits
          (encodeUnaryNatBits n) =
        some (n, []) := by

    simpa using
      decodeUnaryNatBits_encode_append
        n []

  rw [h] at hm
  rw [hn] at hm

  injection hm

end UnaryNaturalBitCodec


section UnaryNaturalListBitCodec

/-- Concatenate the unary codes of an ordered natural list.  The number of
fields is encoded separately by `encodeUnaryNatListBits`. -/
def encodeUnaryNatListPayload :
    List Nat → List Bool

  | [] =>
      []

  | n :: ns =>
      encodeUnaryNatBits n ++
        encodeUnaryNatListPayload ns

/-- Decode exactly the prescribed number of unary natural fields, retaining the
unconsumed bit suffix. -/
def decodeUnaryNatListPayloadAux :
    Nat → List Bool →
      Option (List Nat × List Bool)

  | 0, bits =>
      some ([], bits)

  | Nat.succ _, [] =>
      none

  | Nat.succ fieldCount, bits =>
      match decodeUnaryNatBits bits with

      | none =>
          none

      | some (n, rest) =>
          match
              decodeUnaryNatListPayloadAux
                fieldCount rest with

          | none =>
              none

          | some (ns, suffix) =>
              some (n :: ns, suffix)

/-- Decoding the encoded payload of a natural list consumes exactly that
payload and preserves an arbitrary following suffix. -/
theorem decodeUnaryNatListPayloadAux_encode_append :
    ∀ (fields : List Nat) (suffix : List Bool),
      decodeUnaryNatListPayloadAux
          fields.length
          (encodeUnaryNatListPayload fields ++ suffix) =
        some (fields, suffix)

  | [], suffix => by
      rfl

  | n :: ns, suffix => by
      simp [
        encodeUnaryNatListPayload,
        decodeUnaryNatListPayloadAux,
        List.append_assoc,
        decodeUnaryNatBits_encode_append,
        decodeUnaryNatListPayloadAux_encode_append
          ns suffix
      ]

/-- Exact bit length of the concatenated unary field payload. -/
@[simp] theorem encodeUnaryNatListPayload_length :
    ∀ fields : List Nat,
      (encodeUnaryNatListPayload fields).length =
        (fields.map
          (fun n => n + 1)).sum

  | [] => by
      rfl

  | n :: ns => by
      simp [
        encodeUnaryNatListPayload,
        encodeUnaryNatListPayload_length ns,
        Nat.add_assoc
      ]

/-- Encode a complete natural list as a self-delimiting bit stream.

The field count is encoded first, followed by the concatenated field payloads. -/
def encodeUnaryNatListBits
    (fields : List Nat) :
    List Bool :=
  encodeUnaryNatBits fields.length ++
    encodeUnaryNatListPayload fields

/-- Checked decoder for a complete unary-bit natural list.

The declared field count must be decoded successfully, exactly that many fields
must follow, and no trailing bit may remain. -/
def decodeUnaryNatListBits
    (bits : List Bool) :
    Option (List Nat) :=

  match decodeUnaryNatBits bits with

  | none =>
      none

  | some (fieldCount, payload) =>
      match
          decodeUnaryNatListPayloadAux
            fieldCount payload with

      | some (fields, []) =>
          some fields

      | _ =>
          none

/-- Complete natural-list unary-bit round trip. -/
@[simp] theorem decodeUnaryNatListBits_encode
    (fields : List Nat) :
    decodeUnaryNatListBits
        (encodeUnaryNatListBits fields) =
      some fields := by

  unfold
    encodeUnaryNatListBits
    decodeUnaryNatListBits

  rw [
    decodeUnaryNatBits_encode_append
      fields.length
      (encodeUnaryNatListPayload fields)
  ]

  have hpayload :
      decodeUnaryNatListPayloadAux
          fields.length
          (encodeUnaryNatListPayload fields) =
        some (fields, []) := by

    simpa using
      decodeUnaryNatListPayloadAux_encode_append
        fields []

  rw [hpayload]

/-- Exact bit length of a complete encoded natural list. -/
@[simp] theorem encodeUnaryNatListBits_length
    (fields : List Nat) :
    (encodeUnaryNatListBits fields).length =
      fields.length + 1 +
        (fields.map
          (fun n => n + 1)).sum := by

  simp [
    encodeUnaryNatListBits,
    Nat.add_assoc
  ]

/-- Summing successor field lengths separates into the natural-field sum and
the number of fields. -/
theorem sum_map_nat_succ :
    ∀ fields : List Nat,
      (fields.map
          (fun n => n + 1)).sum =
        fields.sum + fields.length

  | [] => by
      rfl

  | n :: ns => by
      simp [
        sum_map_nat_succ ns,
        Nat.add_assoc,
        Nat.add_comm,
        Nat.add_left_comm
      ]

/-- Equivalent closed form for the complete unary-bit length. -/
theorem encodeUnaryNatListBits_length_closed
    (fields : List Nat) :
    (encodeUnaryNatListBits fields).length =
      1 + 2 * fields.length + fields.sum := by

  rw [encodeUnaryNatListBits_length]
  rw [sum_map_nat_succ]
  omega

/-- The complete natural-list bit codec is injective. -/
theorem encodeUnaryNatListBits_injective
    {xs ys : List Nat}
    (h :
      encodeUnaryNatListBits xs =
        encodeUnaryNatListBits ys) :
    xs = ys := by

  have hx :
      decodeUnaryNatListBits
          (encodeUnaryNatListBits xs) =
        some xs := by
    simp

  have hy :
      decodeUnaryNatListBits
          (encodeUnaryNatListBits ys) =
        some ys := by
    simp

  rw [h] at hx
  rw [hy] at hx

  injection hx

/-- Compact standalone unary-bit natural-list codec package. -/
theorem unaryNatListBitCodec_package
    (fields : List Nat) :
    (decodeUnaryNatListBits
        (encodeUnaryNatListBits fields) =
      some fields) ∧
      ((encodeUnaryNatListBits fields).length =
        1 + 2 * fields.length + fields.sum) := by

  exact
    ⟨decodeUnaryNatListBits_encode fields,
      encodeUnaryNatListBits_length_closed fields⟩

end UnaryNaturalListBitCodec


section CompleteWorkingGrammarUnaryBitCodec

variable {α : Type u}
variable {M : Type v} [Monoid M]
variable {K : Finset (Word α)}
variable {obs : α → M}
variable {f : Nat}

namespace CorrectedConcreteFiniteHypothesis

variable
  (H : CorrectedConcreteFiniteHypothesis K obs f)

/-- Complete self-delimiting unary-bit serialization of the actual cut-compiled
grammar. -/
noncomputable def encodeCompiledWorkingGrammarUnaryBitList
    (dummy : α) :
    List Bool :=
  encodeUnaryNatListBits
    (H.encodeCompiledWorkingGrammarNaturalList
      dummy)

/-- Decode a complete unary-bit grammar serialization and then invoke the
previous checked pure-natural grammar decoder. -/
noncomputable def decodeCompiledWorkingGrammarUnaryBitList
    (dummy : α)
    (bits : List Bool) :
    Option
      (List
        (CorrectedConcreteCompiledGrammarPresentationEntry H)) :=

  match decodeUnaryNatListBits bits with

  | none =>
      none

  | some fields =>
      H.decodeCompiledWorkingGrammarNaturalList
        dummy fields

/-- Exact bit count of the complete unary-bit compiled grammar serialization. -/
noncomputable def compiledWorkingGrammarUnaryBitCount
    (dummy : α) :
    Nat :=
  let fields :=
    H.encodeCompiledWorkingGrammarNaturalList
      dummy

  1 + 2 * fields.length + fields.sum

/-- Complete cut-compiled grammar unary-bit round trip. -/
@[simp] theorem decodeCompiledWorkingGrammarUnaryBitList_encode
    (dummy : α) :
    H.decodeCompiledWorkingGrammarUnaryBitList dummy
        (H.encodeCompiledWorkingGrammarUnaryBitList dummy) =
      some
        (H.compiledGrammarPresentationEntries dummy) := by

  classical

  unfold
    encodeCompiledWorkingGrammarUnaryBitList
    decodeCompiledWorkingGrammarUnaryBitList

  rw [
    decodeUnaryNatListBits_encode
      (H.encodeCompiledWorkingGrammarNaturalList
        dummy)
  ]

  exact
    H.decodeCompiledWorkingGrammarNaturalList_encode
      dummy

/-- The defined grammar bit count is exactly the actual serialized bit-list
length. -/
@[simp] theorem encodeCompiledWorkingGrammarUnaryBitList_length
    (dummy : α) :
    (H.encodeCompiledWorkingGrammarUnaryBitList dummy).length =
      H.compiledWorkingGrammarUnaryBitCount dummy := by

  classical

  unfold
    encodeCompiledWorkingGrammarUnaryBitList
    compiledWorkingGrammarUnaryBitCount

  exact
    encodeUnaryNatListBits_length_closed
      (H.encodeCompiledWorkingGrammarNaturalList
        dummy)

/-- Exact bit-count formula exposing the previously verified natural-field
count of the complete grammar serialization. -/
theorem compiledWorkingGrammarUnaryBitCount_eq
    (dummy : α) :
    H.compiledWorkingGrammarUnaryBitCount dummy =
      1 +
        2 *
          H.compiledWorkingGrammarNaturalFieldCount dummy +
        (H.encodeCompiledWorkingGrammarNaturalList
          dummy).sum := by

  classical

  unfold
    compiledWorkingGrammarUnaryBitCount

  rw [
    H.encodeCompiledWorkingGrammarNaturalList_length
      dummy
  ]

/-- The complete bit stream is nonempty. -/
theorem encodeCompiledWorkingGrammarUnaryBitList_ne_nil
    (dummy : α) :
    H.encodeCompiledWorkingGrammarUnaryBitList dummy ≠ [] := by

  unfold
    encodeCompiledWorkingGrammarUnaryBitList
    encodeUnaryNatListBits

  exact
    List.append_ne_nil_of_left_ne_nil
      (encodeUnaryNatBits_ne_nil
        (H.encodeCompiledWorkingGrammarNaturalList
          dummy).length)

/-- Compact actual-grammar bit-codec endpoint. -/
theorem compiledWorkingGrammarUnaryBitCodec_package
    (dummy : α) :
    (H.decodeCompiledWorkingGrammarUnaryBitList dummy
        (H.encodeCompiledWorkingGrammarUnaryBitList dummy) =
      some
        (H.compiledGrammarPresentationEntries dummy)) ∧
      ((H.encodeCompiledWorkingGrammarUnaryBitList dummy).length =
        H.compiledWorkingGrammarUnaryBitCount dummy) ∧
      (H.compiledWorkingGrammarUnaryBitCount dummy =
        1 +
          2 *
            H.compiledWorkingGrammarNaturalFieldCount dummy +
          (H.encodeCompiledWorkingGrammarNaturalList
            dummy).sum) := by

  exact
    ⟨H.decodeCompiledWorkingGrammarUnaryBitList_encode dummy,
      H.encodeCompiledWorkingGrammarUnaryBitList_length dummy,
      H.compiledWorkingGrammarUnaryBitCount_eq dummy⟩

end CorrectedConcreteFiniteHypothesis

end CompleteWorkingGrammarUnaryBitCodec

end MCFG
