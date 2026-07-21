/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG.ConcreteCanonicalLearnerWorkingGrammarCheckedBitRepresentation

/-!
# ConcreteCanonicalLearnerWorkingGrammarFiniteCodeUniverse.lean

The preceding file equips every actual learner output and every
characteristic-sample target witness with a checked bit presentation whose
length is bounded by

```lean
correctedConcreteCompiledGrammarPaperPowerBitBound n f.
```

It is tempting to conclude that the corresponding language class at level `n`
is finite.  That conclusion is not valid under the present assumptions:

* the ambient terminal type `α` need not be finite; and
* the abstract checked representation structure permits its presentation type
  and decoder to vary with the represented grammar.

What is uniformly finite is the set of admissible bit strings at each fixed
budget.

This file constructs that finite code universe explicitly.

## Exact-length Boolean lists

```lean
boolListsOfLength k
```

enumerates every Boolean list of length exactly `k`.  We prove

```text
bits ∈ boolListsOfLength k ↔ bits.length = k
```

and

```text
(boolListsOfLength k).length = 2^k.
```

## Bounded-length Boolean lists

```lean
boolListsUpTo N
```

enumerates every Boolean list of length at most `N`.  We prove

```text
bits ∈ boolListsUpTo N ↔ bits.length ≤ N
```

and the simple finite cardinality estimate

```text
(boolListsUpTo N).length ≤ 2^(N+1).
```

The list is used as a finite code universe; no no-duplicate property is needed
for the upper bound or membership results.

## Grammar code universe

At sample-length level `n` and fan-out `f`, define

```lean
correctedConcreteCompiledGrammarCheckedBitCodeUniverse n f
```

to be all Boolean lists of length at most the final paper-power bit budget.

Every checked bit-bounded representation stores a code in this universe.
In particular, the actual canonical learner's checked logarithmic bit list lies
in the code universe at level `sampleLengthBudget K`, and its fixed decoder
accepts that code.

The code universes are monotone in `n`, and their enumeration-list lengths are
bounded by

```text
2 ^
  (correctedConcreteCompiledGrammarPaperPowerBitBound n f + 1).
```

Finally, every semantic start-rooted target has a finite positive sample and a
checked accepted code in the corresponding finite universe.

This is the precise finite-code statement available without adding a global
finite-alphabet assumption or a globally fixed decoder for the whole language
class.

No target grammar is supplied to the learner.
No `sorry`, `admit`, or `axiom` is used.
-/

namespace MCFG

universe u v w z


section ExactLengthBooleanCodeEnumeration

/-- Explicit enumeration of all Boolean lists of one exact length. -/
def boolListsOfLength :
    Nat → List (List Bool)

  | 0 =>
      [[]]

  | n + 1 =>
      (boolListsOfLength n).map
          (fun bits => false :: bits) ++
        (boolListsOfLength n).map
          (fun bits => true :: bits)

/-- Every enumerated exact-length Boolean list has the specified length. -/
theorem length_eq_of_mem_boolListsOfLength :
    ∀
      {n : Nat}
      {bits : List Bool},
      bits ∈ boolListsOfLength n →
        bits.length = n

  | 0, bits, hbits => by
      simp [boolListsOfLength] at hbits
      subst bits
      rfl

  | n + 1, bits, hbits => by
      rcases List.mem_append.mp hbits with
        hfalse | htrue

      · rcases List.mem_map.mp hfalse with
          ⟨tail, htail, rfl⟩

        simp [
          length_eq_of_mem_boolListsOfLength
            htail
        ]

      · rcases List.mem_map.mp htrue with
          ⟨tail, htail, rfl⟩

        simp [
          length_eq_of_mem_boolListsOfLength
            htail
        ]

/-- Every Boolean list occurs in the enumeration indexed by its own length. -/
theorem mem_boolListsOfLength_self :
    ∀ bits : List Bool,
      bits ∈ boolListsOfLength bits.length

  | [] => by
      simp [boolListsOfLength]

  | false :: bits => by
      simp [
        boolListsOfLength,
        mem_boolListsOfLength_self bits
      ]

  | true :: bits => by
      simp [
        boolListsOfLength,
        mem_boolListsOfLength_self bits
      ]

/-- Exact characterization of membership in the exact-length Boolean-list
enumeration. -/
@[simp] theorem mem_boolListsOfLength_iff_length_eq
    (bits : List Bool)
    (n : Nat) :
    bits ∈ boolListsOfLength n ↔
      bits.length = n := by

  constructor

  · exact
      length_eq_of_mem_boolListsOfLength

  · intro hlength

    have hself :
        bits ∈
          boolListsOfLength bits.length :=
      mem_boolListsOfLength_self bits

    simpa [hlength] using hself

/-- The exact-length Boolean-list enumeration has size `2^n`. -/
@[simp] theorem boolListsOfLength_length :
    ∀ n : Nat,
      (boolListsOfLength n).length =
        2 ^ n

  | 0 => by
      simp [boolListsOfLength]

  | n + 1 => by
      rw [
        boolListsOfLength,
        List.length_append,
        List.length_map,
        List.length_map,
        boolListsOfLength_length n,
        pow_succ
      ]

      omega

end ExactLengthBooleanCodeEnumeration


section BoundedLengthBooleanCodeEnumeration

/-- Explicit finite enumeration of all Boolean lists of length at most `N`. -/
def boolListsUpTo :
    Nat → List (List Bool)

  | 0 =>
      boolListsOfLength 0

  | n + 1 =>
      boolListsUpTo n ++
        boolListsOfLength (n + 1)

/-- Every Boolean list whose length is at most `N` occurs in
`boolListsUpTo N`. -/
theorem mem_boolListsUpTo_of_length_le :
    ∀
      {N : Nat}
      {bits : List Bool},
      bits.length <= N →
        bits ∈ boolListsUpTo N

  | 0, bits, hlength => by
      have hzero :
          bits.length = 0 :=
        Nat.eq_zero_of_le_zero hlength

      have hself :
          bits ∈
            boolListsOfLength bits.length :=
        mem_boolListsOfLength_self bits

      simpa [
        boolListsUpTo,
        hzero
      ] using hself

  | N + 1, bits, hlength => by
      by_cases hprevious :
          bits.length <= N

      · exact
          List.mem_append.mpr
            (Or.inl
              (mem_boolListsUpTo_of_length_le
                hprevious))

      · have hexact :
            bits.length = N + 1 := by
          omega

        exact
          List.mem_append.mpr
            (Or.inr
              ((mem_boolListsOfLength_iff_length_eq
                  bits
                  (N + 1)).mpr
                hexact))

/-- Every Boolean list occurring in `boolListsUpTo N` has length at most `N`. -/
theorem length_le_of_mem_boolListsUpTo :
    ∀
      {N : Nat}
      {bits : List Bool},
      bits ∈ boolListsUpTo N →
        bits.length <= N

  | 0, bits, hbits => by
      have hexact :
          bits.length = 0 := by

        exact
          (mem_boolListsOfLength_iff_length_eq
            bits 0).mp
            (by
              simpa [boolListsUpTo] using hbits)

      omega

  | N + 1, bits, hbits => by
      rcases
          List.mem_append.mp
            (by
              simpa [boolListsUpTo] using hbits) with
        hprevious | hexact

      · have hle :
            bits.length <= N :=
          length_le_of_mem_boolListsUpTo
            hprevious

        omega

      · have heq :
            bits.length = N + 1 :=
          (mem_boolListsOfLength_iff_length_eq
            bits
            (N + 1)).mp
            hexact

        omega

/-- Exact membership characterization of the bounded Boolean-list code
universe. -/
@[simp] theorem mem_boolListsUpTo_iff_length_le
    (bits : List Bool)
    (N : Nat) :
    bits ∈ boolListsUpTo N ↔
      bits.length <= N := by

  exact
    ⟨length_le_of_mem_boolListsUpTo,
      mem_boolListsUpTo_of_length_le⟩

/-- The bounded-length enumeration list has length at most `2^(N+1)`. -/
theorem boolListsUpTo_length_le_two_pow_succ :
    ∀ N : Nat,
      (boolListsUpTo N).length <=
        2 ^ (N + 1)

  | 0 => by
      norm_num [
        boolListsUpTo,
        boolListsOfLength
      ]

  | N + 1 => by
      have ih :
          (boolListsUpTo N).length <=
            2 ^ (N + 1) :=
        boolListsUpTo_length_le_two_pow_succ
          N

      calc
        (boolListsUpTo (N + 1)).length =
            (boolListsUpTo N).length +
              (boolListsOfLength (N + 1)).length := by
          simp [boolListsUpTo]
        _ <=
            2 ^ (N + 1) +
              2 ^ (N + 1) := by
          exact
            Nat.add_le_add_right
              ih
              (2 ^ (N + 1))
        _ =
            2 ^ ((N + 1) + 1) := by
          rw [pow_succ]
          omega

/-- Membership in the bounded Boolean-list universe is monotone in the length
budget. -/
theorem boolListsUpTo_mem_mono
    {N P : Nat}
    (hNP : N <= P)
    {bits : List Bool}
    (hbits :
      bits ∈ boolListsUpTo N) :
    bits ∈ boolListsUpTo P := by

  apply
    mem_boolListsUpTo_of_length_le

  exact
    (length_le_of_mem_boolListsUpTo
        hbits).trans
      hNP

end BoundedLengthBooleanCodeEnumeration


section CheckedGrammarCodeUniverse

/-- Finite list containing every admissible checked grammar code at
sample-length level `n` and fan-out `f`. -/
def correctedConcreteCompiledGrammarCheckedBitCodeUniverse
    (n f : Nat) :
    List (List Bool) :=
  boolListsUpTo
    (correctedConcreteCompiledGrammarPaperPowerBitBound
      n f)

/-- Exact characterization of membership in the checked grammar code
universe. -/
@[simp] theorem
    mem_correctedConcreteCompiledGrammarCheckedBitCodeUniverse_iff
    (bits : List Bool)
    (n f : Nat) :
    bits ∈
        correctedConcreteCompiledGrammarCheckedBitCodeUniverse
          n f ↔
      bits.length <=
        correctedConcreteCompiledGrammarPaperPowerBitBound
          n f := by

  simp [
    correctedConcreteCompiledGrammarCheckedBitCodeUniverse
  ]

/-- The finite enumeration-list length of the checked grammar code universe is
bounded by `2^(budget+1)`. -/
theorem
    correctedConcreteCompiledGrammarCheckedBitCodeUniverse_length_le
    (n f : Nat) :
    (correctedConcreteCompiledGrammarCheckedBitCodeUniverse
        n f).length <=
      2 ^
        (correctedConcreteCompiledGrammarPaperPowerBitBound
            n f +
          1) := by

  exact
    boolListsUpTo_length_le_two_pow_succ
      (correctedConcreteCompiledGrammarPaperPowerBitBound
        n f)

/-- Checked grammar code-universe membership is monotone in the sample-length
level. -/
theorem
    correctedConcreteCompiledGrammarCheckedBitCodeUniverse_mem_mono
    {n m f : Nat}
    (hnm : n <= m)
    {bits : List Bool}
    (hbits :
      bits ∈
        correctedConcreteCompiledGrammarCheckedBitCodeUniverse
          n f) :
    bits ∈
      correctedConcreteCompiledGrammarCheckedBitCodeUniverse
        m f := by

  apply
    (mem_correctedConcreteCompiledGrammarCheckedBitCodeUniverse_iff
      bits m f).mpr

  have hlength :
      bits.length <=
        correctedConcreteCompiledGrammarPaperPowerBitBound
          n f :=
    (mem_correctedConcreteCompiledGrammarCheckedBitCodeUniverse_iff
      bits n f).mp
      hbits

  exact
    hlength.trans
      (correctedConcreteCompiledGrammarPaperPowerBitBound_mono_sampleLength
        hnm)

end CheckedGrammarCodeUniverse


section RepresentationCodeMembership

variable {α : Type u}

/-- Every checked bit-bounded representation stores a code in the finite code
universe at its declared budget level. -/
theorem
    CheckedBitBoundedCutCompiledWorkingGrammarRepresentation.bits_mem_codeUniverse
    {f n : Nat}
    {L : Set (Word α)}
    (R :
      CheckedBitBoundedCutCompiledWorkingGrammarRepresentation
        (w := w) (z := z) α f n L) :
    R.bits ∈
      correctedConcreteCompiledGrammarCheckedBitCodeUniverse
        n f := by

  exact
    (mem_correctedConcreteCompiledGrammarCheckedBitCodeUniverse_iff
      R.bits n f).mpr
      R.bitLength_le

/-- Every checked bit-bounded representation has one accepted code in the
finite code universe at its declared level. -/
theorem
    CheckedBitBoundedCutCompiledWorkingGrammarRepresentation.exists_accepted_code_in_universe
    {f n : Nat}
    {L : Set (Word α)}
    (R :
      CheckedBitBoundedCutCompiledWorkingGrammarRepresentation
        (w := w) (z := z) α f n L) :
    ∃ bits,
      bits ∈
          correctedConcreteCompiledGrammarCheckedBitCodeUniverse
            n f ∧
        R.decode bits =
          some R.presentation := by

  exact
    ⟨R.bits,
      R.bits_mem_codeUniverse,
      R.decode_bits⟩

/-- Raising a representation budget keeps the same code and places it in the
larger finite universe. -/
theorem
    CheckedBitBoundedCutCompiledWorkingGrammarRepresentation.bits_mem_codeUniverse_raiseBudget
    {f n m : Nat}
    {L : Set (Word α)}
    (R :
      CheckedBitBoundedCutCompiledWorkingGrammarRepresentation
        (w := w) (z := z) α f n L)
    (hnm : n <= m) :
    R.bits ∈
      correctedConcreteCompiledGrammarCheckedBitCodeUniverse
        m f := by

  exact
    correctedConcreteCompiledGrammarCheckedBitCodeUniverse_mem_mono
      hnm
      R.bits_mem_codeUniverse

end RepresentationCodeMembership


section CanonicalLearnerFiniteCodeUniverse

variable {α : Type u}
variable {M : Type v}
variable [Fintype M]
variable [DecidableEq α]
variable [DecidableEq M]
variable [Monoid M]

/-- The actual canonical learner's checked logarithmic bit list belongs to the
finite code universe at the total length of its input sample. -/
theorem
    correctedConcreteWorkingGrammarLearnerLogarithmicBitList_mem_codeUniverse
    (hα : Nonempty α)
    (obs : α → M)
    (f : Nat)
    (K : Finset (Word α)) :
    correctedConcreteWorkingGrammarLearnerLogarithmicBitList
        hα obs f K ∈
      correctedConcreteCompiledGrammarCheckedBitCodeUniverse
        (sampleLengthBudget K)
        f := by

  exact
    (mem_correctedConcreteCompiledGrammarCheckedBitCodeUniverse_iff
      (correctedConcreteWorkingGrammarLearnerLogarithmicBitList
        hα obs f K)
      (sampleLengthBudget K)
      f).mpr
      (correctedConcreteWorkingGrammarLearnerLogarithmicBitList_length_le_paperPower
        hα obs f K)

/-- The learner output has an accepted checked code in its finite code
universe. -/
theorem
    correctedConcreteWorkingGrammarLearner_exists_accepted_code_in_universe
    (hα : Nonempty α)
    (obs : α → M)
    (f : Nat)
    (K : Finset (Word α)) :
    ∃ bits,
      bits ∈
          correctedConcreteCompiledGrammarCheckedBitCodeUniverse
            (sampleLengthBudget K)
            f ∧
        correctedConcreteWorkingGrammarLearnerLogarithmicBitDecode
            hα obs f K bits =
          some
            ((correctedConcreteFiniteHypothesis K obs f).
              compiledGrammarPresentationEntries
                (Classical.choice hα)) := by

  exact
    ⟨correctedConcreteWorkingGrammarLearnerLogarithmicBitList
        hα obs f K,
      correctedConcreteWorkingGrammarLearnerLogarithmicBitList_mem_codeUniverse
        hα obs f K,
      correctedConcreteWorkingGrammarLearnerLogarithmicBitDecode_encode
        hα obs f K⟩

/-- The checked representation object constructed from the learner stores a
member of the finite code universe. -/
theorem
    correctedConcreteWorkingGrammarLearner_checkedRepresentation_bits_mem_codeUniverse
    (hα : Nonempty α)
    (obs : α → M)
    (f : Nat)
    (K : Finset (Word α)) :
    (correctedConcreteWorkingGrammarLearner_checkedBitBoundedRepresentation
        hα obs f K).bits ∈
      correctedConcreteCompiledGrammarCheckedBitCodeUniverse
        (sampleLengthBudget K)
        f := by

  exact
    (correctedConcreteWorkingGrammarLearner_checkedBitBoundedRepresentation
      hα obs f K).bits_mem_codeUniverse

/-- Compact finite-code-universe package for one actual learner output. -/
theorem
    correctedConcreteWorkingGrammarLearner_finiteCodeUniverse_package
    (hα : Nonempty α)
    (obs : α → M)
    (f : Nat)
    (K : Finset (Word α)) :
    ((correctedConcreteCompiledGrammarCheckedBitCodeUniverse
        (sampleLengthBudget K)
        f).length <=
      2 ^
        (correctedConcreteCompiledGrammarPaperPowerBitBound
            (sampleLengthBudget K)
            f +
          1)) ∧
      (correctedConcreteWorkingGrammarLearnerLogarithmicBitList
          hα obs f K ∈
        correctedConcreteCompiledGrammarCheckedBitCodeUniverse
          (sampleLengthBudget K)
          f) ∧
      (correctedConcreteWorkingGrammarLearnerLogarithmicBitDecode
          hα obs f K
          (correctedConcreteWorkingGrammarLearnerLogarithmicBitList
            hα obs f K) =
        some
          ((correctedConcreteFiniteHypothesis K obs f).
            compiledGrammarPresentationEntries
              (Classical.choice hα))) := by

  exact
    ⟨correctedConcreteCompiledGrammarCheckedBitCodeUniverse_length_le
        (sampleLengthBudget K)
        f,
      correctedConcreteWorkingGrammarLearnerLogarithmicBitList_mem_codeUniverse
        hα obs f K,
      correctedConcreteWorkingGrammarLearnerLogarithmicBitDecode_encode
        hα obs f K⟩

end CanonicalLearnerFiniteCodeUniverse


section TargetFiniteCodeWitnesses

variable {α : Type u}
variable {M : Type v}
variable [Fintype M]
variable [DecidableEq α]
variable [DecidableEq M]
variable [Monoid M]

/-- Every checked bit-bounded target witness stores an accepted code in the
finite code universe determined by its positive sample. -/
theorem
    CorrectedConcreteCheckedBitBoundedWorkingGrammarTargetWitness.exists_accepted_code_in_universe
    {hα : Nonempty α}
    {obs : α → M}
    {f : Nat}
    {L : Set (Word α)}
    (W :
      CorrectedConcreteCheckedBitBoundedWorkingGrammarTargetWitness
        hα obs f L) :
    ∃ bits,
      bits ∈
          correctedConcreteCompiledGrammarCheckedBitCodeUniverse
            (sampleLengthBudget W.sample)
            f ∧
        W.representation.decode bits =
          some W.representation.presentation := by

  exact
    W.representation.exists_accepted_code_in_universe

/-- A characteristic sample yields an accepted checked target code in the
corresponding finite universe. -/
theorem
    target_exists_accepted_code_in_universe_of_characteristicSample
    (hα : Nonempty α)
    (obs : α → M)
    (f : Nat)
    (S : Finset (Word α))
    (L : Set (Word α))
    (hS :
      CharacteristicSample
        (correctedConcreteWorkingGrammarHypLanguage
          obs f)
        (correctedConcreteWorkingGrammarLearner
          hα obs f)
        S L) :
    ∃
      (R :
        CheckedBitBoundedCutCompiledWorkingGrammarRepresentation
          (w := max u v)
          (z := max u v)
          α f
          (sampleLengthBudget S)
          L)
      (bits : List Bool),
      bits ∈
          correctedConcreteCompiledGrammarCheckedBitCodeUniverse
            (sampleLengthBudget S)
            f ∧
        R.decode bits =
          some R.presentation := by

  let W :=
    correctedConcreteCheckedBitBoundedWorkingGrammarTargetWitness_of_characteristicSample
      hα obs f S L hS

  exact
    ⟨W.representation,
      W.representation.bits,
      W.representation.bits_mem_codeUniverse,
      W.representation.decode_bits⟩

end TargetFiniteCodeWitnesses


section StartRootedFiniteCodeConclusion

variable {α : Type u}
variable {M : Type v}
variable [Fintype M]
variable [DecidableEq α]
variable [DecidableEq M]
variable [Monoid M]
variable (hα : Nonempty α)
variable (obs : α → M)
variable (f : Nat)

/-- Every semantic start-rooted target has a finite positive sample and an
accepted checked code in the finite universe at that sample's total length. -/
theorem
    startRootedTarget_exists_positive_finiteCodeWitness
    {L : Set (Word α)}
    (hL :
      L ∈ StartRootedCorrectedConcreteTargetClass
        (v := w) α M obs f) :
    ∃
      (S : Finset (Word α))
      (R :
        CheckedBitBoundedCutCompiledWorkingGrammarRepresentation
          (w := max u v)
          (z := max u v)
          α f
          (sampleLengthBudget S)
          L)
      (bits : List Bool),
      (S : Set (Word α)) ⊆ L ∧
        bits ∈
          correctedConcreteCompiledGrammarCheckedBitCodeUniverse
            (sampleLengthBudget S)
            f ∧
        R.decode bits =
          some R.presentation := by

  rcases
      correctedConcreteWorkingGrammarLearner_exists_checkedBitBoundedTargetWitness
        (v := w) hα obs f hL with
    ⟨W⟩

  exact
    ⟨W.sample,
      W.representation,
      W.representation.bits,
      W.sample_positive,
      W.representation.bits_mem_codeUniverse,
      W.representation.decode_bits⟩

/-- Final finite-code statement paired with positive-data identification.

This deliberately asserts finiteness of the admissible code universe, not
finiteness of the whole language class at a budget level. -/
theorem
    correctedConcreteWorkingGrammarLearner_identification_finiteCodeUniverse_package :
    IdentifiesClassFromPositiveData
        (correctedConcreteWorkingGrammarHypLanguage
          obs f)
        (correctedConcreteWorkingGrammarLearner
          hα obs f)
        (StartRootedCorrectedConcreteTargetClass
          (v := w) α M obs f) ∧
      (∀ n : Nat,
        (correctedConcreteCompiledGrammarCheckedBitCodeUniverse
            n f).length <=
          2 ^
            (correctedConcreteCompiledGrammarPaperPowerBitBound
                n f +
              1)) ∧
      (∀ K : Finset (Word α),
        correctedConcreteWorkingGrammarLearnerLogarithmicBitList
            hα obs f K ∈
          correctedConcreteCompiledGrammarCheckedBitCodeUniverse
            (sampleLengthBudget K)
            f) ∧
      (∀ L : Set (Word α),
        L ∈ StartRootedCorrectedConcreteTargetClass
            (v := w) α M obs f →
        ∃
          (S : Finset (Word α))
          (R :
            CheckedBitBoundedCutCompiledWorkingGrammarRepresentation
              (w := max u v)
              (z := max u v)
              α f
              (sampleLengthBudget S)
              L)
          (bits : List Bool),
          (S : Set (Word α)) ⊆ L ∧
            bits ∈
              correctedConcreteCompiledGrammarCheckedBitCodeUniverse
                (sampleLengthBudget S)
                f ∧
            R.decode bits =
              some R.presentation) := by

  exact
    ⟨correctedConcreteWorkingGrammarLearner_identifies_startRootedTargetClass
        (v := w) hα obs f,
      fun n =>
        correctedConcreteCompiledGrammarCheckedBitCodeUniverse_length_le
          n f,
      correctedConcreteWorkingGrammarLearnerLogarithmicBitList_mem_codeUniverse
        hα obs f,
      fun L hL =>
        startRootedTarget_exists_positive_finiteCodeWitness
          (v := w) hα obs f hL⟩

end StartRootedFiniteCodeConclusion

end MCFG
